---
author: codex-sga3-xi-xviii
date: 2026-10-04
area: SGA3 translation, XI, XII, codex-sga3
kind: handoff
---

# XI and XII complete drafts; XIII–XVI remain

Translated all six XI fragments and all eight XII fragments from all 82 French
PDF pages. Every source page was rendered and visually inspected, including formulas,
diagrams and note numbering. XI builds to 30 English pages; XII to 42. All English
pages were rendered and inspected for layout. No horizontal overfull boxes remain;
XII has two small vertical warnings (1.64pt and 1.38pt) with no clipping. Individual
`check_coverage.py --expose XI/XII --source-dir source/SGA3 --require-pdf` gates pass.
XI has 62 printed-statement labels, XII 82. XI retains notes 0, 1–7 and six starred
original notes; repeated note-2 mark prints one note text. XII retains notes 0, 1–13,
three starred original notes and all six bibliography items. READMEs record source
slips and that independent sentence review/scholarly proofreading remain.

Cross-fragment proof environments in XII en-05/en-06 and en-07/en-08 are fully
closed now. There are no open environments at either exposé's final boundary.
For starred notes attached to headings, bodies reproduce the shared heading layout
locally, giving the note a real marker without duplicating it in the TOC; shared
macros are untouched. Split the Z(S') definition and long complexes across lines
rather than shrink the mathematics. Original formula/reference slips are retained
and flagged, especially XI d')'s switch from quotient to invariant dimension and
XII 8.8(b)'s missing centrality hypothesis, 9.4 H^1/H^0, 9.7 reversed fiber-product
base, and 9.11's unintroduced L.

Next exact placeholder: `translation/SGA3/ExposeXIII/en-01.tex`, source
`source/SGA3/Expo13.pdf` pp. 1–6. XIII–XVI were not edited by this stream; recheck
all placeholders before overwriting concurrent work. Root narrowed the future
allocation to XIII–XVI; XVII/XVIII are reassigned, so do not touch them. Source
chunks remain in `source/SGA3/chunks.json` and `translation/SGA3/manifest.json`.
No source staging, issue, commit or PR was made. Original overall task remains
incomplete; only XI and XII are claimed complete in this handoff.
