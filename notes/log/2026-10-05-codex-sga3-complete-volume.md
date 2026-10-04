---
author: codex-sga3
date: 2026-10-05
area: SGA3 translation, codex-sga3
kind: experience
---

# Complete English SGA 3 draft and book

Completed the remaining SGA3 translation with parallel workers, preserving
earlier substantive bodies. The user confirmed introduction/exposé scope,
excluding indexes and the reader's guide. All 222 source-page fragments are
now populated; the sole textless owned range is documented XVI pp.23–24.
Exact coverage and review state live in translation/SGA3/README.md and each
exposé README, rather than in this log.

Final make tex passes, including all 29 individual PDFs and the combined
1065-page SGA3-English.pdf. The all-source-heading/structure/current-PDF gate
passes. The combined input order matches the manifest; labels are unique,
environments balance, and final PDFs have no horizontal overflow, missing
glyphs, unresolved references/citations, or duplicate/missing destinations.
Cover, contents, representative transitions, formulas/notes and the final
bibliography were rendered and inspected. The combined PDF is current against
all body fragments and shared style; its Codex preview is queued.

Preserved printed numbering and notes, repaired duplicated boundary text and
repeated note bodies in older I/II, and reflowed long formulas without changing
mathematics. Chapterbib cbunit isolates each bibliography. Source note markers
repeat and original stars can offset counters: shared parenthesized numbering
and disabled footnote hyperlinks preserve printed notes while contents,
section and citation links stay active. Source-version note0 in XVII now
uses its printed parentheses. The root make tex target includes SGA3 book.

A focused independent XVIII pp.7–12 audit caught my Rule4 inverse-placement
transcription error; it was corrected against the French page and rebuilt.
That audit found no other error in its range; see the review log. All remaining
independent scholarly proofreading is still open. Translator/source slips are
documented per exposé; do not turn build or heading coverage into a fidelity
certificate. Frobenius left-subscript notation in XV/XVII was corrected after
source font/position inspection during final translator QA.

No Lean changes, French source copying, commit or PR. Existing unrelated work
was preserved. All translators closed their live notes; root is stopping.
