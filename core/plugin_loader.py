import importlib, os, yaml
from .api import PluginAPI

def _iter_plugin_manifests(base_dir: str):
    plug_dir = os.path.join(base_dir, "plugins")
    if not os.path.isdir(plug_dir):
        return
    for name in os.listdir(plug_dir):
        man = os.path.join(plug_dir, name, "plugin.yaml")
        if os.path.isfile(man):
            yield man

def load_all_plugins(api: PluginAPI, base_dir: str = None):
    base_dir = base_dir or os.path.dirname(os.path.dirname(__file__))
    for manifest_path in _iter_plugin_manifests(base_dir):
        with open(manifest_path, "r", encoding="utf-8") as f:
            man = yaml.safe_load(f)
        module_path = man.get("module")
        register_sym = man.get("register", "register")
        mod = importlib.import_module(module_path)
        reg = getattr(mod, register_sym)
        reg(api)
