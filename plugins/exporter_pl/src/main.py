from services.exporter_service.exporter import export_answer

def register(api):
    api.register_plugin("exporter_pl", {"version": "0.1.0"})
    # Register a concrete exporter that maps AnswerContract -> DOCX/PDF (stub uses exporter_service)
    api.register_exporter("pl.exporter.docx_pdf", export_answer)
