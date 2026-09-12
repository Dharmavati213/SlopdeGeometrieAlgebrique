#!/usr/bin/env python3
"""Check that English SGA 2 TeX contains every expected non-index source label.

Reads translation/SGA2/expected-labels.json (extracted from the corrected
SMF body) and the shipped English fragments. Exit 0 iff every expected
label appears as \\label{...} in the corresponding exposé directory,
each landed PDF is a non-empty %PDF, and pdftotext of that PDF contains
no '??' (undefined \\ref/\\Ref/\\pageref must print the source key).
This drives the shipped translation files, not a re-implementation.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")

DIRS = {
    "Introduction": ROOT / "Introduction",
    "I": ROOT / "ExposeI",
    "II": ROOT / "ExposeII",
    "III": ROOT / "ExposeIII",
    "IV": ROOT / "ExposeIV",
    "V": ROOT / "ExposeV",
    "VI": ROOT / "ExposeVI",
    "VII": ROOT / "ExposeVII",
    "VIII": ROOT / "ExposeVIII",
    "IX": ROOT / "ExposeIX",
    "X": ROOT / "ExposeX",
    "XI": ROOT / "ExposeXI",
    "XII": ROOT / "ExposeXII",
    "XIII": ROOT / "ExposeXIII",
    "XIV": ROOT / "ExposeXIV",
}

PDFS = {
    "Introduction": ROOT / "Introduction" / "SGA2-Intro.pdf",
    "I": ROOT / "ExposeI" / "SGA2-I.pdf",
    "II": ROOT / "ExposeII" / "SGA2-II.pdf",
    "III": ROOT / "ExposeIII" / "SGA2-III.pdf",
    "IV": ROOT / "ExposeIV" / "SGA2-IV.pdf",
    "V": ROOT / "ExposeV" / "SGA2-V.pdf",
    "VI": ROOT / "ExposeVI" / "SGA2-VI.pdf",
    "VII": ROOT / "ExposeVII" / "SGA2-VII.pdf",
    "VIII": ROOT / "ExposeVIII" / "SGA2-VIII.pdf",
    "IX": ROOT / "ExposeIX" / "SGA2-IX.pdf",
    "X": ROOT / "ExposeX" / "SGA2-X.pdf",
    "XI": ROOT / "ExposeXI" / "SGA2-XI.pdf",
    "XII": ROOT / "ExposeXII" / "SGA2-XII.pdf",
    "XIII": ROOT / "ExposeXIII" / "SGA2-XIII.pdf",
    "XIV": ROOT / "ExposeXIV" / "SGA2-XIV.pdf",
}

ENV_NEEDLES = (
    r"\begin{theorem",
    r"\begin{proposition",
    r"\begin{lemma",
    r"\begin{corollary",
    r"\begin{definition",
    r"\begin{remark",
    r"\begin{example",
    r"\begin{supproposition",
    r"\begin{suptheorem",
    r"\begin{suplemma",
    r"\begin{supcorollary",
    r"\begin{enonce*",
    r"\begin{problem",
    r"\begin{conjecture",
    r"\section{",
    r"\chapter{",
    r"\chapter*{",
)


def labels_in(dirpath: Path) -> set[str]:
    found: set[str] = set()
    for p in dirpath.glob("*.tex"):
        text = p.read_text(encoding="utf-8", errors="replace")
        found.update(LABEL_RE.findall(text))
    return found


def body_text(dirpath: Path) -> str:
    parts = []
    for p in sorted(dirpath.glob("en-*.tex")):
        parts.append(p.read_text(encoding="utf-8", errors="replace"))
    return "\n".join(parts)


def pdftotext(pdf: Path) -> str:
    """Extract text from a shipped PDF via poppler pdftotext (the real binary)."""
    proc = subprocess.run(
        ["pdftotext", "-layout", str(pdf), "-"],
        check=False,
        capture_output=True,
    )
    if proc.returncode != 0:
        err = proc.stderr.decode("utf-8", errors="replace")
        raise RuntimeError(f"pdftotext failed on {pdf}: {err or proc.returncode}")
    return proc.stdout.decode("utf-8", errors="replace")


def main() -> int:
    expected = json.loads((ROOT / "expected-labels.json").read_text(encoding="utf-8"))
    missing_all: dict[str, list[str]] = {}
    empty_body: list[str] = []
    no_env: list[str] = []
    ok = True
    lines = []
    for name, keys in expected.items():
        d = DIRS[name]
        if not d.is_dir():
            print(f"FAIL {name}: missing directory {d}", file=sys.stderr)
            ok = False
            continue
        body = body_text(d)
        if len(body.strip()) < 200:
            empty_body.append(name)
            ok = False
        if name != "Introduction" and not any(n in body for n in ENV_NEEDLES):
            no_env.append(name)
            ok = False
        have = labels_in(d)
        missing = [k for k in keys if k not in have]
        extra_note = len(have)
        lines.append(
            f"{name:14} expected={len(keys):3} found={extra_note:3} missing={len(missing):3}"
        )
        if missing:
            missing_all[name] = missing
            ok = False
        pdf = PDFS[name]
        if not pdf.is_file():
            print(f"FAIL {name}: missing PDF {pdf}", file=sys.stderr)
            ok = False
        else:
            magic = pdf.read_bytes()[:5]
            size = pdf.stat().st_size
            if magic != b"%PDF-" or size < 50000:
                print(
                    f"FAIL {name}: PDF is not a real non-empty PDF "
                    f"(magic={magic!r}, size={size})",
                    file=sys.stderr,
                )
                ok = False
            else:
                lines[-1] += f"  pdf={size}"
            try:
                text = pdftotext(pdf)
            except RuntimeError as exc:
                print(f"FAIL {name}: {exc}", file=sys.stderr)
                ok = False
            else:
                n_qq = text.count("??")
                if n_qq:
                    print(
                        f"FAIL {name}: pdftotext of {pdf.name} contains {n_qq} '??' "
                        "(undefined \\Ref/\\ref; cross-exposé keys should print)",
                        file=sys.stderr,
                    )
                    ok = False
                else:
                    lines[-1] += "  no-??"
    report = "\n".join(lines) + "\n"
    print(report, end="")
    if empty_body:
        print("empty/short bodies:", ", ".join(empty_body), file=sys.stderr)
    if no_env:
        print("no theorem/section environments:", ", ".join(no_env), file=sys.stderr)
    if missing_all:
        for name, miss in missing_all.items():
            print(f"MISSING {name}: {miss}", file=sys.stderr)
    if not ok:
        return 1
    print("OK: all expected labels present; bodies non-empty")
    return 0


if __name__ == "__main__":
    sys.exit(main())
