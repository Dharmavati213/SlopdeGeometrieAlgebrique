#!/usr/bin/env python3
"""Check draft coverage and TeX structure; this does not certify translation fidelity."""

import argparse
import collections
import json
import re
import subprocess
import unicodedata
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expose", help="Check one exposé (e.g. IV or Intro)")
    parser.add_argument("--source-dir", type=Path, help="Optionally compare local French PDF statement headings")
    parser.add_argument("--require-pdf", action="store_true", help="Require a current, nonempty compiled PDF")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "manifest.json").read_text())
    if args.expose:
        manifest = [entry for entry in manifest if entry["id"] == args.expose]
        if not manifest:
            parser.error("Unknown exposé")
    problems = 0
    total = done = 0
    for entry in manifest:
        folder = root / entry["folder"]
        fragments = [folder / f"en-{chunk['k']}.tex" for chunk in entry["chunks"]]
        pending = []
        bodies = []
        for fragment in fragments:
            total += 1
            raw = fragment.read_text() if fragment.exists() else ""
            body = re.sub(r"(?<!\\)%[^\n]*", "", raw)
            if not body.strip() or "pending translation:" in raw:
                pending.append(fragment.name)
            else:
                done += 1
            bodies.append(body)
        body = "\n".join(bodies)
        issues = ["pending: " + ", ".join(pending)] if pending else []
        labels = re.findall(r"\\label\{([^}]+)\}", body)
        duplicates = [key for key, count in collections.Counter(labels).items() if count > 1]
        if duplicates:
            issues.append("duplicate labels: " + ", ".join(duplicates))
        stack = []
        for kind, name in re.findall(r"\\(begin|end)\{([^}]+)\}", body):
            if kind == "begin":
                stack.append(name)
            elif not stack or stack.pop() != name:
                issues.append("unmatched environment end: " + name)
        if stack:
            issues.append("unclosed environments: " + ", ".join(stack))
        wrapper = folder / f"SGA3-{entry['id']}.tex"
        inputs = re.findall(r"\\input\{([^}]+)\}", wrapper.read_text())
        if inputs != [fragment.name for fragment in fragments]:
            issues.append("wrapper inputs differ from manifest")
        if args.require_pdf:
            pdf = wrapper.with_suffix(".pdf")
            newest = max(p.stat().st_mtime for p in [wrapper, root / "sga3-en.sty", *fragments])
            if not pdf.exists() or not pdf.stat().st_size:
                issues.append("missing or empty PDF")
            elif pdf.stat().st_mtime < newest:
                issues.append("PDF is stale")
        if args.source_dir:
            pdf = args.source_dir / entry["pdf"]
            french = unicodedata.normalize("NFC", subprocess.check_output(
                ["pdftotext", "-layout", str(pdf), "-"], text=True))
            headings = re.findall(
                r"(?m)^\s*(?:Proposition(?: et définition)?|Définition|Théorème|Lemme|Corollaire|Remarque|Scholie)\s+(\d[\d.]*[A-Za-z]*)",
                french,
            )
            missing = sorted({f"{entry['id']}.{n.rstrip('.')}" for n in headings} - set(labels))
            if missing:
                issues.append("source headings without labels: " + ", ".join(missing))
        print(f"{entry['id']:>5}: {len(fragments)-len(pending):2}/{len(fragments):2} fragments; "
              + ("; ".join(issues) if issues else "structural checks pass"))
        problems += bool(issues)
    if not args.expose:
        master = (root / "SGA3-English.tex").read_text()
        expected = [f"{entry['folder']}/en-{chunk['k']}.tex"
                    for entry in manifest for chunk in entry["chunks"]]
        if re.findall(r"\\input\{([^}]+)\}", master) != expected:
            print("Book: input sequence differs from manifest")
            problems += 1
        if master.count(r"\begin{cbunit}") != len(manifest):
            print("Book: chapter-local bibliography scope count differs from manifest")
            problems += 1
    print(f"{done}/{total} fragments populated. Sentence-level and mathematical review is separate.")
    return int(bool(problems))


if __name__ == "__main__":
    raise SystemExit(main())
