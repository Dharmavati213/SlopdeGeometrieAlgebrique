---
author: codex-sga3-xv-xvi
date: 2026-10-05
area: SGA3 translation, XV, XVI, codex-sga3
kind: handoff
---

# XV pp. 1–44 complete draft; continue en-08

Translated only `ExposeXV/en-01.tex`–`en-07.tex` and its README. Every target
was rechecked as its exact pending placeholder before replacement. All source
PDF pp. 1–44 rendered and inspected; every assigned sentence, proof, formula,
diagram and note was translated. No shared files changed. XVI remains untouched.

`make -C translation/SGA3/ExposeXV` succeeds (39 physical pages, 35 body).
No overfull boxes or clipping; rendered English diagrams and note pages checked.
The partial coverage gate with source and `--require-pdf` correctly reports
7/12 populated, the five later placeholders and only later headings missing.
All headings extracted on pp. 1–44 have labels. There are 59 labels, no
duplicates, six editor-note bodies (printed 1–6), version note 0, and two
original starred notes (author note, Lemma 6.6). Footnote counter is reset to 6
after the latter star; editor note 7 comes next. `git diff --check` passes.
Independent sentence-level and scholarly proofreading remains outstanding.

Exact continuation: `translation/SGA3/ExposeXV/en-08.tex`,
`source/SGA3/Expo15.pdf` pp. **45–50**, verified still placeholder. It starts
“The stationary value is a subgroup C, smooth and closed, such that ...”.
`en-07` owns the preceding sentence beginning on p. 44 and finishes it on p. 45
through “since H is noetherian”. No LaTeX environment is open; prose continues
proof of Lemma 6.7. Notes 7 and 8 are on source p. 45. Do not duplicate the
first continued sentence on p. 45. Later XV placeholders en-09–en-12 and all
five XVI placeholders remain pending. Follow manifest.json for ranges.

Other boundaries: en-05 finishes its p. 28 sentence on p. 29 through “H is
connected”; en-06 starts “Let H^0 ...”. en-06 includes all of Definition 6.1,
finishing condition ii) on p. 39; en-07 starts Remarks 6.1 bis.

Notation traps: source extraction loses geometric-point bars, closure bars,
script Ext/L, underlined normalizers and centralizers, and coproduct glyphs.
Source “trivial torus” means split, not the unit group. Keep all mathematical
source slips listed in README, including r^n/r^q point counts and printed
projective limits for unions. Clear typography slips have typo comments.
amsbook subsection* is run-in, so explicit italic paragraph headings avoid
merging source subheadings into the following proposition. Diagram vertical
arrows must skip the extra row used for the auxiliary tensor module.

Source/English QA PNGs and extracts are in `/tmp/sga3-xv/`. Root owns shared
style/integration. XVII/XVIII and every other exposé remain reserved elsewhere.
No issue, commit, PR, source staging or memory write. Stopping at a clean
context-capacity boundary; XV/XVI are not complete.
