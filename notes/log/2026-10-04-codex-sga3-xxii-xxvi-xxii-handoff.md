---
author: codex-sga3-xxii-xxvi
date: 2026-10-04
area: SGA3 translation XXII–XXVI, XVII, codex-sga3-xxii-xxvi
kind: handoff
---

Completed all 12 XXII bodies (68 source pages) and its README. All source
pages rendered and read; every sentence, proof, formula, diagram, note
0–65 and all five bibliography items translated. Repeated marks 5, 25,
58 and 64 share one note text each. Source slips retained with comments;
README lists them. Independent sentence-level review remains outstanding.

`make -C translation/SGA3/ExposeXXII` succeeds (58 PDF pages).
`python3 translation/SGA3/check_coverage.py --expose XXII --source-dir
source/SGA3 --require-pdf` passes; `git diff --check` for XXII passes.
English diagrams, long formulas, selected footnote pages and bibliography
visually checked. No overfull horizontal boxes or clipped contents; one
1.33786 pt vertical box warning on main p. 31 has fully visible text and
footnotes. No shared macros, wrappers, source staging, commit or PR changed.

Clean context-capacity continuation: `translation/SGA3/ExposeXXIII/en-01.tex`,
`source/SGA3/Exp23-13oct24.pdf` pp. **1–8** (verified placeholder unchanged).
XXIII–XXVI remain untouched pending placeholders; no proof/environment is
open across this boundary. The root also reserved XVII after XXII–XXVI
for this stream; XVII is `Expo17.pdf`, first chunk pp. 1–5, but confirm
ownership with the root before taking that later allocation. Root owns
shared style/integration; other agents own VIB and the Tome 2 work.

Notation traps: source extraction loses root bars, geometric-point bars,
underlined functors, coproduct glyphs, and the hat in U_{hat alpha}.
Root-data scheme uses mathcal R, the attached abstract datum mathscr R.
Use explicit G_{m,S}/G_{a,S} to avoid double subscripts. PDFs and English
QA images are under `/tmp/sga3-xxii/` for this run; PDF source is authority.
Before every pending-fragment write recheck the placeholder to preserve
concurrent substantive translations. Follow `manifest.json` for page ranges.
