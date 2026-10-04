---
author: codex-sga3-viib
date: 2026-10-05
area: SGA3 translation VIIB, codex-sga3-viib, codex-sga3
kind: handoff
---

# VII B first ten fragments complete; five remain

Translated `ExposeVIIB/en-01.tex`–`en-10.tex`, source PDF pp. 1–62, every
sentence/proof/formula/diagram/editor note. Every target was rechecked as
its exact pending placeholder in the patch. All 62 source pages rendered
and read, plus p. 63 for the final sentence; all material math/diagrams
checked against images. README records source slips retained and typography
repairs. Notes 0–112: 113 editor-note bodies; repeated 12 and 92 markers print
one text. No original starred notes occur in this translated portion.

Cumulative `make` succeeds: partial 51-page PDF, 56 unique labels, no open
environments; directory whitespace check passes. No horizontal warnings;
1.82pt and 1.68pt vertical warnings show no clipping. English physical pages
14, 29, 31, 40, 41, 44, 48, 51 inspected (snake map, filtered coalgebra,
quotient diagrams, Cartier duality, semidirect product, Lie universal property).
Leftward parallel-arrow labels and snake routing repaired through layout only;
accented etale category superscripts use `text{ét}` to remove math-accent warnings.
Bibliography is still pending, so citations remain unresolved. Coverage is
10/15, NOT complete. Independent sentence review/scholarly proofreading remain.

**Next exact placeholder:** `translation/SGA3/ExposeVIIB/en-11.tex`,
`source/SGA3/Exp7B-13oct24.pdf` **pp. 63–70**. Start on p. 63 at the second
sentence, “We shall say that the formal monoid M is infinitesimal if ε_M
induces a bijection of the underlying sets.” The opening continuation
sentence defining ε_M, begun on p. 62, is already in en-10. No open proof or
other environment. en-11–en-15 remain exact placeholders. Begin next editor
note at **113** (version 0 included in count).

Boundary details: en-02 finishes the sentence on p. 15 before Definition
0.4.2; en-04 finishes p. 26's sentence and notes 56–57 on p. 27 before the
flatness lemma. en-05 includes “is injective” from p. 33; en-06 resumes “On
the other hand...” and closes the 1.3.6.A proof before Lemma 1.3.6.B.
en-09 includes p. 57's opening exact sequence as completion of p. 56's last
sentence; en-10 starts “In what follows...”.

The original coverage regex truncates uppercase suffixes (0.2.B, 1.2.3.A
etc.), giving false missing labels; root notified to repair the shared
checker. A local check with `[A-Za-z]*` finds no missing statement labels
through source p. 62. All shared tools/macros left to root. No source
staging, issue, commit, PR or memory write. XVIII not started or claimed.

Scratch source images/extract and English checks: `/tmp/sga3-viib/`.
French text `source.txt` has one form-feed-separated entry per PDF page;
`p-63.png` is already rendered. PDF marker was already run by root: do not
repeat. Root continues the user's overall task; this handoff requests a
fresh worker/context for the remaining five VIIB fragments.
