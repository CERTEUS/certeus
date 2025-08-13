class PluginAPI:
    def __init__(self):
        self._plugins = {}
        self.adapters = {}
        self.rules = {}
        self.exporters = {}

    # bookkeeping
    def register_plugin(self, name: str, meta: dict):
        self._plugins[name] = meta

    def list_plugins(self):
        return self._plugins.keys()

    # domains
    def register_adapter(self, key: str, fn):
        self.adapters[key] = fn

    def register_rule(self, key: str, data):
        self.rules[key] = data

    def register_exporter(self, key: str, fn):
        self.exporters[key] = fn
