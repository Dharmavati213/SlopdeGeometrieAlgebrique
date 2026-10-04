---
author: codex-sga3-xxiv-xxvi
date: 2026-10-04
area: SGA3 translation XXIV–XXVI, XVII, codex-sga3-xxiv-xxvi
kind: handoff
---

# XXIV complete draft; fresh continuation at XXV

Translated all eight XXIV bodies from all 54 source PDF pages. Every source
page rendered and inspected; all sentences/proofs/formulas/diagrams, notes
0–50 (51 bodies), repeated note-24 marker, original starred note at 8.1,
and all ten bibliography entries retained. Each target was checked as the
exact pending placeholder before replacement. No shared macros/wrappers,
source staging, issue, commit, PR or memory writes.

`make -C translation/SGA3/ExposeXXIV` succeeds: 43 main-text / 47 total pages.
Source-heading/PDF coverage gate passes 8/8; all 168 labels are unique;
104 numbered statement environments. Directory `git diff --check` passes.
English long formulas, long notes, equivalence/decomposition diagrams,
appendix and bibliography inspected as rendered pages. No horizontal box
warnings remain. Two vertical warnings of 1.61 and 1.79 pt have no clipping.
README documents preserved mathematical/source-reference slips and obvious
typography corrected. Independent sentence-level/mathematical review remains.

Cross-fragment environments are all closed. en-02 completes the final
sentence begun on p.14 through “G_Si is splittable” on p.15; en-03 starts
“Reasoning as before ...”. Proposition 3.13's initial sentence finishes
on p.21 in en-03; its next sentence is in en-04. 4.2.4's proof and 5.5's
statement similarly span fragments. Editor note 24 has one body plus the
second marker; original star before note47 decrements the ordinary counter.

Exact next placeholder: `translation/SGA3/ExposeXXV/en-01.tex`, source
`source/SGA3/Exp25-13oct24.pdf` **pp.1–8**. No open environment.
XXV/en-02.tex is pp.9–11. XXVI remains wholly pending (53 source pages,
nine chunks as in manifest.json). XVII remains reserved later by root;
confirm ownership/dispatch before taking it. The XXIV–XXVI block is NOT
complete. This is a clean context-capacity handoff for continued work.

Most delicate retained slips: 6.2 ±x and E(1,x)E(1,−x), 6.6 bottom Aut(G),
7.1.4 alpha(t)alpha(t') coefficient, 7.2.2 T'=T∩G without prime,
7.3.5 bottom Z¹(G,h), 7.4 entrywise power formulas including n=0,
8.3 unprimed P and 8.5 reference8.2. Use the PDF, not extraction, for
barG/barS, script root data/Dynkin scheme, and Fraktur Lie algebras.

Scratch source extracts/renderings and English QA images:
`/tmp/sga3-xxiv/`. Root has been notified of completion and continuation.
