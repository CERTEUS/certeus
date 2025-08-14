from core.plugin_loader import load_all_plugins
from core.api import PluginAPI


def test_plugins_loaded():
    api = PluginAPI()
    load_all_plugins(api)
    # Plugins registered
    assert "lexlog_rules_pl" in api.list_plugins()
    assert "tpl_diff_pl" in api.list_plugins()
    assert "exporter_pl" in api.list_plugins()
    assert "isap_adapter_pl" in api.list_plugins()
    # Adapters/Exporters visible
    assert "tpl.diff.pl" in api.adapters
    assert "isap.pl.snapshot" in api.adapters
    assert "pl.exporter.docx_pdf" in api.exporters
