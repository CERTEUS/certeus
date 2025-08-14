def register(api):
    api.register_plugin("lexlog_rules_pl", {"version": "0.1.0"})
    # przykładowa reguła i adapter
    api.register_rule("pl.kk.286", {"desc": "Szkic przesłanek 286 k.k."})
    api.register_adapter("isap.pl", lambda act_id: {"act_id": act_id, "version": "v1"})
