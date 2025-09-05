import importlib.util

spec = importlib.util.spec_from_file_location('fin_tokens_api', 'services/api_gateway/routers/fin_tokens_api.py')
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
print('loaded', mod.router)
