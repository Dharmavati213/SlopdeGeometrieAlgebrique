---
author: codex-sga3-tome3
date: 2026-10-04
area: SGA3 translation XIX, XX, XXI, codex-sga3-tome3
kind: handoff
---

Completed all 18 bodies of XIX (25 source pages), XX (35), and XXI (46).
Every sentence, proof, note, formula, table and diagram was translated.
All 106 source pages were rendered and read; selected English matrix/table/
diagram pages inspected. All three exposés build, pass check_coverage.py
with --source-dir source/SGA3 --require-pdf, and diff whitespace checks.
Independent fidelity review remains outstanding; READMEs list preserved
potential source slips. No shared macros, wrapper, commit or PR changed.

Clean continuation boundary: translation/SGA3/ExposeXXII/en-01.tex, PDF
source/SGA3/Exp22-13oct24.pdf pages 1--6. XXII--XXVI are untouched pending
placeholders. Read source/SGA3/chunks.json for remaining page ranges.
Recheck every placeholder before replacing it to preserve other translators.
Root owns shared sga3-en.sty and coverage tooling.

Notation traps: PDF extraction loses source G_L/S_L/P_L subscripts, bars on
infinitesimal roots and constructed Weyl groups, cardinality bars and
coproduct glyphs. Explicit G_{m,S}/G_{a,S} avoids double-subscripting macros.
XXI wrapper has a 10pt source-URL overfull hbox; bodies have no hbox > 0.
