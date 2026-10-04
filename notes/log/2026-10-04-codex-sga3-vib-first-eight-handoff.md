---
author: codex-sga3-vib
date: 2026-10-04
area: SGA3 translation VIB, codex-sga3-vib, codex-sga3
kind: handoff
---

# VIB pp. 1–54 translated; continue from en-09.tex

Completed only `translation/SGA3/ExposeVIB/en-01.tex`–`en-08.tex` and its
README. Each target was checked to remain the exact pending placeholder
before replacement. Every assigned sentence, proof, formula, diagram,
original footnote and editor note was translated from the local PDF
`source/SGA3/Exp6B-13oct24.pdf`; extraction was used as a crib and source
formula bars, underlined functors and diagrams were inspected as images.
Root added shared `Transp` and `uTransp`; no shared files were edited here.

Cumulative `make -C translation/SGA3/ExposeVIB` succeeds: 46-page partial
PDF. The eight populated fragments have 100 labels, no duplicates, and
75 editor-note bodies (printed 0–74), including embedded Theorem 5.3A
in note 34; repeated note 56 callouts and the original starred notes are
preserved. The coverage check with source and `--require-pdf` correctly
fails for the ten pending chunks and later source headings only. All 86
headings extracted with the checker's regex on source pp. 1–54 have labels.
Representative English pages 5, 21, 26, 31 and 40 were rendered and
inspected. `git diff --check` passes. Independent scholarly proofreading
is still outstanding. README lists source slips corrected or retained.

Exact continuation:

- `en-09.tex`, source PDF pp. 55–60, still pending. It begins **“Thus this
  sequence is stationary, and there is an integer m such that ...”**, the
  next sentence in the first case of the proof of Proposition 7.4.
- `en-08.tex` completes the previous sentence begun on p. 54 through
  **“G = G^0 is of finite type over k (VIA 2.4)”** on p. 55. Do not duplicate
  that continuation. No environment remains open at this boundary.
- `en-10.tex`–`en-18.tex` are also pending; exact ranges are in manifest.json.
  Bibliography still lies in the pending part. Do not call VIB complete.

Other boundary details: Corollary 5.6.2 opens in en-05 and closes in en-06;
Remark 6.1.1 begins on p. 38 and its full sentence/display from p. 39 is
already included in en-06, so en-07 starts Proposition 6.2. Source number
6.4.1 does not exist (editor note 60). The source's script-looking derived
group is the Fraktur `\mathfrak D(G)`.

Root was notified of duplicate exposé TOC entries caused by the shared
amsbook chapter-star/addcontentsline combination; this stream did not
change the shared package. One harmless 1.96pt overfull vbox occurred in
the build, no overfull hboxes or TeX errors. No commit, PR, issue, source
staging or memory write was made. Stopping at a clear continuation point
because the accumulated context is large; this is a partial handoff.
