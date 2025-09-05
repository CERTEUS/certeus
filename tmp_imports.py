import sys

sys.path.insert(0, '.')
mods = [
    'services',
    'services.api_gateway',
    'services.api_gateway.routers',
    'services.api_gateway.routers.billing',
    'services.api_gateway.routers.fin_tokens_api',
]
for m in mods:
    try:
        __import__(m)
        print('OK', m)
    except Exception as e:
        print('ERR', m, e)
