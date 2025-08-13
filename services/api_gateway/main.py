import uvicorn
from fastapi import FastAPI
from services.api_gateway.routers import verify, mismatch, ledger, export
from core.plugin_loader import load_all_plugins, PluginAPI

app = FastAPI(title="CERTEUS API")
app.include_router(verify.router, prefix="")
app.include_router(mismatch.router, prefix="")
app.include_router(ledger.router, prefix="")
app.include_router(export.router, prefix="")

# Plugin API registry
plugin_api = PluginAPI()

@app.on_event("startup")
def _load_plugins():
    load_all_plugins(plugin_api)

@app.get("/health")
def health():
    return {"status": "ok", "plugins": list(plugin_api.list_plugins())}

if __name__ == "__main__":
    uvicorn.run(app, host="0.0.0.0", port=8000)
