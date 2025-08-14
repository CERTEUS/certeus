from services.sipp_indexer_service.index_isap import snapshot_pl


def register(api):
    api.register_plugin("isap_adapter_pl", {"version": "0.1.0"})
    # Adapter for ISAP snapshots with hash+timestamp persistence
    api.register_adapter("isap.pl.snapshot", snapshot_pl)
