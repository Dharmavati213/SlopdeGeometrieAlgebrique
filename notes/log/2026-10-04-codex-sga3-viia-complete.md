---
author: codex-sga3-viia
date: 2026-10-04
area: SGA3 translation VIIA, codex-sga3-viia, codex-sga3
kind: experience
---

# VIIA completed through source p. 60

Translated only `ExposeVIIA/en-01.tex`–`en-10.tex` and its README, checking
each target was still the exact pending placeholder before replacement.
Every sentence/proof/formula/diagram/note and all six bibliography items
were translated from the PDF; all 60 source pages rendered and inspected.
No pending body remains. Ordinary editor notes 1–87, three original stars,
note-38 marker inside an original note, and repeated note-80 marker retained.

Full make succeeds (52-page PDF); source/PDF coverage check passes 10/10;
38 labels without duplicates, 87 editor-note bodies, six bibliography items;
diff whitespace check passes. Representative English diagram, formula,
footnote, contents and bibliography pages inspected. Fixed overlapping
Frobenius arrow labels and category parentheses; no horizontal overflows.
One harmless 2.43 pt vertical box and inherited footnote-anchor warnings
remain. Independent scholarly proofreading is still outstanding.

Boundary details: en-01 stops at a colon, leaving p. 7's numbered/unnumbered
statement to en-02. En-05 ends with the sentence begun on p. 30, completed
through `a tensor ... tensor a maps to a tensor_pi 1` on p. 31; en-06 starts
“Similarly, j(A) ...”. En-09 includes the first diagram and H definition
from p. 55, finishing its p. 54 sentence; en-10 starts “Now H ...”. No open
environment at any final fragment boundary.

Mathematical source slips were retained and listed in README, including
5.5.3's L-star/L sequence, 7.2.3's [L,L] quotient argument, and 8.4's global
étaleness claim. Extraction loses bar on iterated diagonal, functor
underlining, script sheaf letters and tensor glyphs. Root adjusted shared
unnumbered statement headings; no shared file edited here. No issue,
commit, PR, source staging or memory write. VII B/XVIII were not started.
