from pathlib import Path

p = Path('services') / 'api_gateway' / 'routers' / 'fin_tokens_api.py'
print('exists?', p.exists(), 'path=', p)
print('cwd=', Path('.').resolve())
