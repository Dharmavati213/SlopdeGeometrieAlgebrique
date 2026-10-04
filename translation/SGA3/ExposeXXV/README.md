# SGA 3, XXV

The existence theorem. Author: M. Demazure.

French source (local only): `source/SGA3/Exp25-13oct24.pdf` (11 pages),
the Gille–Polo recomposition of 13 October 2024.

| | |
| --- | --- |
| Status | Complete English draft; independent sentence-level review and scholarly proofreading remain outstanding. |
| Chunks | en-01.tex (pp. 1–8), en-02.tex (pp. 9–11) |
| Verification | All source pages rendered and inspected; English PDF inspected; make and source-heading/PDF structural check pass. |

Every sentence, proof, formula, diagram, editorial note 0–12 and all eight
bibliography entries are translated. No environment remains open at the
fragment boundary. The first fragment ends with Lemma 3.2; the second begins
“Now one has”. The bibliography environment supplies its heading.

Build: `make -C translation/SGA3/ExposeXXV` (14 physical PDF pages, 10 body
pages). Coverage: `python3 translation/SGA3/check_coverage.py --expose XXV
--source-dir source/SGA3 --require-pdf`. One 2.04 pt vertical box warning has
no clipping; there are no horizontal overflows or unresolved citations.
Structural checks do not certify sentence-level or mathematical correctness.

Typographical corrections are marked `% typo:` in the body: the extra
closing parenthesis in the formula defining `(v'',t'',u'')` in 2.9 was removed.
Mathematical/reference anomalies are retained and marked `% typo?:`:

- 2.4 starts the arguments of `Q_i` with `x_i`, followed by `...,x_{i-1}`.
- 2.7 declares `d:Omega -> Spec(Z)` while evaluating `d(u)` as a function;
  the printed formula `b(u)=t alpha*(d(u))` is retained as well.
- The proof of 2.8 cites 2.8 for its construction conditions.
- 2.9 uses unprimed `v` in the condition following the formula with `v'`.
- The explanation of 2.10 cites `2.10 (iii)`.

The printed coproduct symbol in 3.3 denotes the direct sum described in the
prose. All underlined group functors, identity sections and barred Weyl
representatives were checked from the PDF, rather than the text extraction.
