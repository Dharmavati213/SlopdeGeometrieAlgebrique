---
author: codex-sga3-tome1
date: 2026-10-04
area: SGA3 translation V VIA, codex-sga3-tome1
kind: handoff
---

# V and VIA completed; continue VIB, VIIA, VIIB

All seven V bodies (PDF pp. 1–41) and all five VIA bodies (pp. 1–38)
are now complete English drafts, including every proof, diagram, editor
note and bibliography entry. Before each replacement the target was
checked to remain a pending placeholder; no concurrent body was replaced.
The READMEs record validation, page-boundary assignments and printed
source anomalies retained in the English formulas. Independent scholarly
proofreading is outstanding.

`make -C translation/SGA3/ExposeV` succeeds (35-page PDF); VIA succeeds
(34-page PDF). The new `check_coverage.py` passes for both with
`--source-dir source/SGA3 --require-pdf`. V has 25 numbered statements,
53 editor notes and 15 bibliography items. VIA has 49 numbered labels,
61 editor notes (including version note 0 and duplicate printed no. 53)
and 8 bibliography items. `git diff --check` passes for both directories.
PDF notation was inspected where extracted bars, products or arrows were
unclear; representative English pages were rendered and inspected.

Remaining assignment: all 18 VIB chunks, all 10 VIIA chunks, and all 15
VIIB chunks (271 source PDF pages). They still contain pending placeholders.
Continue from `translation/SGA3/ExposeVIB/en-01.tex`, source PDF
`source/SGA3/Exp6B-13oct24.pdf`; verify actual filename/ranges from
`source/SGA3/chunks.json` first. Read the PDF as authority, text as crib.
Root owns shared macros and integration. No commit, issue or PR was made.

Useful layout detail: three parallel xymatrix arrows with individual
labels need column space (`@C=4em`), outer offsets `1.5ex`, and a middle
label with `|{...}`. Otherwise the labels overlap each other or the source
object; fixed and re-rendered in V and VIA. Macro Gm already has a
subscript: use `\mathbf G_{\mathrm m,S}` for an additional base index.
