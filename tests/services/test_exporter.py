from services.exporter_service.exporter import export_answer
def test_exporter_creates_files(tmp_path):
    out = export_answer("pl-286kk-0001", out_dir=tmp_path)
    assert (tmp_path / "pl-286kk-0001.docx").exists()
    assert (tmp_path / "pl-286kk-0001.pdf").exists()
