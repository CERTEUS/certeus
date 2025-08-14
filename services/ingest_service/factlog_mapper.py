def to_factlog(items):
    return [{"id": i, "role": "stub"} for i, _ in enumerate(items)]
