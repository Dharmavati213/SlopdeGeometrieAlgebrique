#!/usr/bin/env python3
"""Generate per-exposé wrappers, Makefiles, latexmkrc, and stub READMEs."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent

EXPOSES = [
    {
        "key": "Introduction",
        "dir": "Introduction",
        "tex": "SGA2-Intro.tex",
        "pdf": "SGA2-Intro.pdf",
        "chapter": None,
        "title": "Introduction",
        "title_tex": r"Introduction",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-body.tex"],
        "short": "Grothendieck's introduction to SGA 2",
    },
    {
        "key": "I",
        "dir": "ExposeI",
        "tex": "SGA2-I.tex",
        "pdf": "SGA2-I.pdf",
        "chapter": 1,
        "title": "Global and local cohomological invariants relative to a closed subspace",
        "title_tex": r"Global and local cohomological invariants relative to a closed subspace",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-01.tex", "en-02.tex"],
        "short": "Exposé I",
    },
    {
        "key": "II",
        "dir": "ExposeII",
        "tex": "SGA2-II.tex",
        "pdf": "SGA2-II.pdf",
        "chapter": 2,
        "title": "Application to quasi-coherent sheaves on preschemes",
        "title_tex": r"Application to quasi-coherent sheaves on preschemes",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-body.tex"],
        "short": "Exposé II",
    },
    {
        "key": "III",
        "dir": "ExposeIII",
        "tex": "SGA2-III.tex",
        "pdf": "SGA2-III.pdf",
        "chapter": 3,
        "title": "Cohomological invariants and depth",
        "title_tex": r"Cohomological invariants and depth",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-1.tex", "en-2.tex"],
        "short": "Exposé III",
    },
    {
        "key": "IV",
        "dir": "ExposeIV",
        "tex": "SGA2-IV.tex",
        "pdf": "SGA2-IV.pdf",
        "chapter": 4,
        "title": "Dualizing modules and functors",
        "title_tex": r"Dualizing modules and functors",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-1.tex", "en-2.tex"],
        "short": "Exposé IV",
    },
    {
        "key": "V",
        "dir": "ExposeV",
        "tex": "SGA2-V.tex",
        "pdf": "SGA2-V.pdf",
        "chapter": 5,
        "title": "Local duality and structure of the $H^i(M)$",
        "title_tex": r"Local duality and structure of the $\mathrm{H}^i(M)$",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-1.tex", "en-2.tex"],
        "short": "Exposé V",
    },
    {
        "key": "VI",
        "dir": "ExposeVI",
        "tex": "SGA2-VI.tex",
        "pdf": "SGA2-VI.pdf",
        "chapter": 6,
        "title": r"The functors $\mathrm{Ext}^{\bullet}_Z(X;F,G)$ and $\underline{\mathrm{Ext}}^{\bullet}_Z(F,G)$",
        "title_tex": r"The functors $\protect\Ext^{\protect\boule}_Z(X;F, G)$ and $\protect\SheafExt^{\protect\boule}_Z(F, G)$",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-body.tex"],
        "short": "Exposé VI",
    },
    {
        "key": "VII",
        "dir": "ExposeVII",
        "tex": "SGA2-VII.tex",
        "pdf": "SGA2-VII.pdf",
        "chapter": 7,
        "title": r"Vanishing criteria, coherence of $\underline{\mathrm{Ext}}^i_Y(F,G)$",
        "title_tex": r"Vanishing criteria, coherence conditions for the sheaves $\SheafExt^{i}_{Y}(F, G)$",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-body.tex"],
        "short": "Exposé VII",
    },
    {
        "key": "VIII",
        "dir": "ExposeVIII",
        "tex": "SGA2-VIII.tex",
        "pdf": "SGA2-VIII.pdf",
        "chapter": 8,
        "title": "The finiteness theorem",
        "title_tex": r"The finiteness theorem",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-1.tex", "en-2.tex"],
        "short": "Exposé VIII",
    },
    {
        "key": "IX",
        "dir": "ExposeIX",
        "tex": "SGA2-IX.tex",
        "pdf": "SGA2-IX.pdf",
        "chapter": 9,
        "title": "Algebraic geometry and formal geometry",
        "title_tex": r"Algebraic geometry and formal geometry",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-1.tex", "en-2.tex"],
        "short": "Exposé IX",
    },
    {
        "key": "X",
        "dir": "ExposeX",
        "tex": "SGA2-X.tex",
        "pdf": "SGA2-X.pdf",
        "chapter": 10,
        "title": "Application to the fundamental group",
        "title_tex": r"Application to the fundamental group",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-body.tex"],
        "short": "Exposé X",
    },
    {
        "key": "XI",
        "dir": "ExposeXI",
        "tex": "SGA2-XI.tex",
        "pdf": "SGA2-XI.pdf",
        "chapter": 11,
        "title": "Application to the Picard group",
        "title_tex": r"Application to the Picard group",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-body.tex"],
        "short": "Exposé XI",
    },
    {
        "key": "XII",
        "dir": "ExposeXII",
        "tex": "SGA2-XII.tex",
        "pdf": "SGA2-XII.pdf",
        "chapter": 12,
        "title": "Applications to projective algebraic schemes",
        "title_tex": r"Applications to projective algebraic schemes",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-1.tex", "en-2.tex", "en-3.tex", "en-4.tex"],
        "short": "Exposé XII",
    },
    {
        "key": "XIII",
        "dir": "ExposeXIII",
        "tex": "SGA2-XIII.tex",
        "pdf": "SGA2-XIII.pdf",
        "chapter": 13,
        "title": "Problems and conjectures",
        "title_tex": r"Problems and conjectures",
        "author": r"A.\ Grothendieck",
        "inputs": ["en-1.tex", "en-2.tex"],
        "short": "Exposé XIII",
    },
    {
        "key": "XIV",
        "dir": "ExposeXIV",
        "tex": "SGA2-XIV.tex",
        "pdf": "SGA2-XIV.pdf",
        "chapter": 14,
        "title": "Depth and Lefschetz theorems in étale cohomology",
        "title_tex": r"Depth and Lefschetz theorems in \'etale cohomology",
        "author": r"M.\ Raynaud",
        "inputs": [
            "en-0.tex",
            "en-1a.tex",
            "en-1b.tex",
            "en-2.tex",
            "en-3.tex",
            "en-4a.tex",
            "en-4b.tex",
            "en-5.tex",
            "en-6.tex",
        ],
        "short": "Exposé XIV (M. Raynaud)",
    },
]


WRAPPER = r'''\documentclass[11pt,a4paper,oneside]{{amsbook}}
\usepackage[T1]{{fontenc}}
\usepackage[utf8]{{inputenc}}
\usepackage{{lmodern}}
\usepackage[american]{{babel}}
\usepackage{{microtype}}
\usepackage{{geometry}}
\geometry{{margin=1.1in}}
\makeatletter
\def\input@path{{../}}
\makeatother
\usepackage{{sga2-en}}
\usepackage[hidelinks]{{hyperref}}

\addto\captionsamerican{{\renewcommand{{\chaptername}}{{Expos\'e}}}}

\title[SGA~2, {short} (English draft)]{{{title_tex}\\
{{\normalsize SGA~2, {short}\\English draft}}}}
\author{{{author}}}
\date{{}}
\hypersetup{{
  pdftitle={{SGA 2, {short} (English draft)}},
  pdfauthor={{Alexander Grothendieck}},
  pdfsubject={{Unofficial English translation of SGA 2, {short}}}
}}

\begin{{document}}
\frontmatter
\maketitle

\chapter*{{About this draft}}
This is an unofficial English translation of {about},
from SGA~2. The source volume is A.\ Grothendieck
(notes by a group of auditors), with an expos\'e by M.\ Raynaud,
\textit{{Cohomologie locale des faisceaux coh\'erents et th\'eor\`emes
de Lefschetz locaux et globaux}} (SGA~2), S\'eminaire de g\'eom\'etrie
alg\'ebrique du Bois Marie, 1962. It follows the slightly corrected
SMF recomposition,
\href{{https://arxiv.org/abs/math/0511279}}{{arXiv:math/0511279}}.

This draft contains the assigned body of the source, including proofs,
original footnotes, and editor notes (N.D.E.). Statement numbering and
mathematical notation follow the source. References to material outside
this draft retain their original numbers. Apparent mathematical
misprints in the source have been retained; they are recorded in the
accompanying README, separately from the translated text. Scholarly
proofreading remains outstanding.

The translator's contribution is licensed under
\href{{https://creativecommons.org/licenses/by-sa/4.0/}}{{CC BY-SA 4.0}}.
The French original remains copyright of its authors and publishers.

\tableofcontents
\mainmatter
{setcounter}{inputs}
\end{{document}}
'''

MAKEFILE = """TEX := {tex}

.PHONY: all pdf clean

all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(TEX)

clean:
	latexmk -C $(TEX)
"""

LATEXMKRC = """$pdf_mode = 1;
$interaction = 'nonstopmode';
$pdflatex = 'pdflatex -file-line-error -synctex=1 %O %S';
"""


def main() -> None:
    for ex in EXPOSES:
        d = ROOT / ex["dir"]
        d.mkdir(parents=True, exist_ok=True)
        if ex["chapter"] is None:
            setcounter = ""
            about = "Grothendieck's Introduction"
            inputs = "\n".join(rf"\input{{{name}}}" for name in ex["inputs"])
        else:
            setcounter = rf"\setcounter{{chapter}}{{{ex['chapter'] - 1}}}" + "\n"
            about = rf"Expos\'e~{ex['key']}, ``{ex['title']}''"
            inputs = "\n".join(rf"\input{{{name}}}" for name in ex["inputs"])
        tex = WRAPPER.format(
            short=ex["short"],
            title_tex=ex["title_tex"],
            author=ex["author"],
            about=about,
            setcounter=setcounter,
            inputs=inputs,
        )
        (d / ex["tex"]).write_text(tex, encoding="utf-8")
        (d / "Makefile").write_text(MAKEFILE.format(tex=ex["tex"]), encoding="utf-8")
        (d / "latexmkrc").write_text(LATEXMKRC, encoding="utf-8")
        readme = f"""# SGA 2, {ex['short']}

Unofficial English draft of {ex['title']}.
Scholarly proofreading remains outstanding.

Build: `make -C translation/SGA2/{ex['dir']}` from the repository root.

Source: corrected SMF branch (`orig = false`) of
[arXiv:math/0511279](https://arxiv.org/abs/math/0511279).
The French TeX and PDF are not included in this repository.

License: [`../../LICENSE`](../../LICENSE) (CC BY-SA 4.0 for the
translator's contribution).
"""
        (d / "README.md").write_text(readme, encoding="utf-8")
        for name in ex["inputs"]:
            p = d / name
            if not p.exists():
                p.write_text(
                    f"% English body fragment for SGA 2 {ex['key']} ({name})\n",
                    encoding="utf-8",
                )
    print(f"generated {len(EXPOSES)} exposé wrappers")


if __name__ == "__main__":
    main()
