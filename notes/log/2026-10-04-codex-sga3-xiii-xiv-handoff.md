---
author: codex-sga3-xiii-xvi
date: 2026-10-04
area: SGA3 translation, XIII, XIV, XV, XVI, codex-sga3
kind: handoff
---

# XIII and XIV complete drafts; XV and XVI remain

Translated all five XIII and all six XIV fragments from all 66 source PDF
pages; source and English pages were rendered and inspected. XIII builds to
26 English pages (22 body), XIV to 30 (26 body). Individual coverage gates
with `--source-dir source/SGA3 --require-pdf` pass. XIII has 42 statement
labels; XIV has 79 including its unnumbered appendix theorem and lemmas 1–5.
XIII has editor notes 1–11 plus version 0; XIV has editor notes 1–9, four
starred original notes, two appendix original notes, version 0. Neither has
a bibliography. There are no open environments at the final boundaries.

No horizontal overfull boxes or clipping. XIV retains one 3.11pt vertical
warning on body p. 9; rendered page is clean. Added struts to the appendix
Dynkin table so curved automorphism arrows do not overlap the preceding
paragraph; all four diagrams were checked against the French. The three-cycle
in D4 needs outer curved arrows (`@/_.../`) to avoid crossing the spokes.

Retained mathematical source slips are listed in each README; clear grammar
slips have typo comments. Editorial note XIV.8's complete Bruhat proof is
translated; appendix original notes restart at 1 and 2 while editor note 9
keeps its own number. Independent sentence review/scholarly proofreading
remain: structural checks alone do not certify full fidelity.

Exact next placeholder: `translation/SGA3/ExposeXV/en-01.tex`,
`source/SGA3/Expo15.pdf` pp. 1–6. XV (12 fragments, 68 pages) and XVI
(5 fragments, 24 pages) were not touched by this worker. Recheck every target
for a still-pending placeholder before overwriting. XV starts with no open
environments. Allocation remains XV–XVI only; XVII/XVIII are assigned elsewhere.
Root owns shared macros/integration. No source staging, issue, commit or PR.
