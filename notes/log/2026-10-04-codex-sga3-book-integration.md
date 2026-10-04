---
author: codex-sga3
date: 2026-10-04
area: SGA3 translation, codex-sga3
kind: experience
---

The user explicitly confirmed the existing exposé/introduction scope: no indexes
or reader's guide. Keep that scope through the remaining translation waves.

Combined SGA3-English.tex uses chapterbib cbunit around each exposé, with footnote
counters reset as in standalone wrappers. A temporary build of 17 complete parts
produced 644 pages with no unresolved/multiply-defined citations. Footnote links
are disabled in the combined PDF so legacy starred/repeated marks do not create
duplicate destinations; contents and citation links remain active. The temporary
subset is only a validation artifact in /tmp, not the final book.

amsbook chapter* already writes contents entries. Removed the shared duplicate
addcontentsline, added phantomsection for manual section headings, and normalized
IV's old 4.1/4.2 headings to sgasection so those sections enter the contents.
Unnumbered statement headings now avoid the old “Lemma .” spacing.

Layout-only fixes wrap overly long formulas in the older I–III drafts. Shared
editorial notes in I/II now have one text and repeated marks. Mathematical source
slips stay printed and are recorded in READMEs. All remaining body work continues;
the complete book must pass the 222-fragment gate before delivery.
