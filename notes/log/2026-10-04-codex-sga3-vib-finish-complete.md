---
author: codex-sga3-vib-finish
date: 2026-10-04
area: SGA3 translation VIB, codex-sga3-vib-finish, codex-sga3
kind: experience
---

# VIB completed through source p. 112

Translated only `ExposeVIB/en-09.tex`–`en-18.tex` and updated its README;
first eight fragments were preserved. Rechecked each target as its exact
pending placeholder before writing. Every assigned sentence, proof, formula,
diagram, original/editor footnote and all 26 bibliography entries were
translated against `source/SGA3/Exp6B-13oct24.pdf`; all source pages 55–111
were rendered and inspected (112 is blank). No body remains pending.

Full `make -C translation/SGA3/ExposeVIB` succeeds (89 physical PDF pages).
`check_coverage.py --expose VIB --source-dir source/SGA3 --require-pdf`
passes 18/18; 197 labels, no duplicates, 141 editor-note bodies (0–140;
139 nde plus 2 ndetext), repeated markers 56 and 117, original starred notes,
and bibliography retained. `git diff --check` passes for VIB. Inspected
English physical pages 47, 55, 65, 67, 72, 77, 84, 88, 89; equations,
diagrams and bibliography are legible and fit. Only tiny overfull boxes
remain (largest 3.11pt), plus inherited hyperref footnote-anchor warnings.
Independent scholarly proofreading remains outstanding.

Useful boundary details: en-11 finishes the last sentence of Proposition
10.11's proof on p. 73; en-12 starts Corollary 10.11.1. en-13 finishes the
sentence begun on p. 84 with M_B tensor_B B' = M'_{B'}, and en-14 closes
that proof. en-15 finishes the invariance criterion begun on p. 96 through
the definition of m_13 on p. 97. en-17 finishes its last sentence begun on
p. 108 with rho': G -> N; Remark 13.6 is closed in en-18. No environment
remains open at the final boundary.

PDF extraction loses closure bars (especially proof 7.4 and Lemma 7.7),
coalgebra/comodule operation bars, underlined functors, and direct sums.
Source contains visible encoding corruption in counit and Lütkebohmert;
clear textual slips corrected with comments. Mathematical anomalies are
kept as printed and listed in README. Shared \id is unavailable, so my
fragments use \mathrm{id}; no shared style change was made.

No issue, commit, PR, French source staging, or memory write. Root can
integrate this completed exposé and continue VIIA/VIIB allocations.
