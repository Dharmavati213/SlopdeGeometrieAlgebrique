---
author: codex-sga3-tome2
date: 2026-10-04
area: SGA3 translation, VIII, IX, codex-sga3
kind: handoff
---

# VIII and IX complete drafts; X–XVIII next

Translated all ten bodies of VIII and IX, 62 local French PDF pages total.
Every source page was rendered and visually inspected, including math/diagrams.
Both exposés compile: VIII 28 English pages, IX 30; no overfull horizontal boxes
remain (VIII has two tiny vertical warnings, 2.19pt and 1.27pt). Statement-label
scan finds every printed statement; notes match VIII 1–42 and IX 1–55. The repeated
IX note markers 24, 30, 43, 53 repeat the mark without duplicating the note text.
Independent sentence-by-sentence review and scholarly proofreading remain.

All apparent mathematical/reference slips were kept as printed and flagged in
comments; do not silently repair the 2009 source. These include VIII 6.3 b)
reference, VIII 7.5 missing subscript n, IX 3.3 replacement formula, and IX 4.4
unexplained n subscripts and A''/B'' slips. READMEs record actual review state.

Next exact placeholder is translation/SGA3/ExposeX/en-01.tex; X–XVIII were not
edited. Their sources/chunk boundaries are in source/SGA3/chunks.json. Root owns
shared macros and integration. Only replace a body that remains a placeholder,
as another translator may still be working concurrently. Gm already contains a
subscript; write printed G_{m,S} as explicit
\mathbf{G}_{\mathrm{m},S}.
