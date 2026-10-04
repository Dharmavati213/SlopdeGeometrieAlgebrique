---
author: codex-sga3-xxiii-xxvi
date: 2026-10-04
area: SGA3 translation XXIII–XXVI, XVII, codex-sga3-xxiii-xxvi
kind: handoff
---

Completed every XXIII body and its README: all 37 source pages, all proofs,
formulas, diagram, commutator table, notes 0–20, both starred original notes,
and seven bibliography items. All French source pages rendered/read; selected
English long formulas, rank-one diagram, table, footnote pages and bibliography
visually checked. Every target was still a placeholder before replacement.
No shared macro/wrapper changes, source staging, issue, commit or PR.

`make -C translation/SGA3/ExposeXXIII` succeeds: 31 main-text pages / 35 total.
No horizontal/vertical box warnings. The source-heading / PDF structural check
passes (`check_coverage.py --expose XXIII --source-dir source/SGA3 --require-pdf`),
and all 56 numbered statement labels are present. Directory diff check passes.
README records the numerous printed mathematical/reference slips kept verbatim.
Independent sentence-level and mathematical review remains outstanding.

Capacity handoff: exact next placeholder is
`translation/SGA3/ExposeXXIV/en-01.tex`, source
`source/SGA3/Exp24-13oct24.pdf` **pp. 1–8**. No open environment/proof.
XXIV–XXVI remain wholly pending; this assigned stream is NOT complete.
XVII remains reserved later by the root; confirm ownership before taking it.

Notation: root spaces are superscripts `g^alpha`, normalizers/centralizers
underlined, root data `mathscr R`, and the extension in 2.1 is bar f. Hats in
`U_{hat alpha}` and geometric-point bars must come from the PDF. Formula splits
avoid overfull lines without mathematical changes. Original starred note 5.4
contains editorial marker 13: use a nested footnotemark with local number 13,
then ndetext outside; subsequent nde counter is 14. A note before the first
bibitem needs `item[]` or LaTeX reports “perhaps a missing item”.
Scratch source/English images and extracts: `/tmp/sga3-xxiii/`.
