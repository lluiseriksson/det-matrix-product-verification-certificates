"""Build SHA-256 manifest for paper81-det-matrix-product-verification-certificates."""

from __future__ import annotations

import hashlib
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]
EXCLUDE_DIRS = {".git", ".lake", "__pycache__", ".pytest_cache", ".venv"}
EXCLUDE_SUFFIXES = {".aux", ".bbl", ".blg", ".log", ".out", ".toc", ".fls", ".fdb_latexmk", ".synctex.gz"}


def main() -> int:
    entries: list[tuple[str, str]] = []
    for p in sorted(ROOT.rglob("*")):
        if not p.is_file():
            continue
        rel = p.relative_to(ROOT)
        if any(part in EXCLUDE_DIRS for part in rel.parts):
            continue
        if rel.name == "MANIFEST.sha256" or p.suffix in EXCLUDE_SUFFIXES:
            continue
        digest = hashlib.sha256(p.read_bytes()).hexdigest()
        entries.append((digest, rel.as_posix()))
    out = ROOT / "MANIFEST.sha256"
    out.write_text("\n".join(f"{h}  {r}" for h, r in entries) + "\n", encoding="utf-8")
    print(f"Wrote MANIFEST.sha256 with {len(entries)} files.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
