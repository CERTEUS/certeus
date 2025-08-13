from pathlib import Path

def export_answer(case_id: str, out_dir: str = "out"):
    Path(out_dir).mkdir(parents=True, exist_ok=True)
    out = Path(out_dir) / f"{case_id}.docx"
    out.write_bytes(b"DOCX_PLACEHOLDER")
    (Path(out_dir) / f"{case_id}.pdf").write_bytes(b"%PDF-1.4\n% placeholder\n")
    return {"docx": str(out), "pdf": str(Path(out_dir) / f"{case_id}.pdf")}

if __name__ == "__main__":
    print(export_answer("pl-286kk-0001"))
