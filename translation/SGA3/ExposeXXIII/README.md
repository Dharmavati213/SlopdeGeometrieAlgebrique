# SGA 3, XXIII

Reductive groups: uniqueness of pinned groups.

Author of the exposé: M. Demazure.

French source (local only): `source/SGA3/Exp23-13oct24.pdf` (37 pages),
the Gille–Polo recomposition.

| | |
| --- | --- |
| Status | Complete English draft; independent sentence-level review outstanding. |
| Chunks | en-01.tex (pp. 1--8), en-02.tex (pp. 9--14), en-03.tex (pp. 15--20), en-04.tex (pp. 21--25), en-05.tex (pp. 26--30), en-06.tex (pp. 31--37) |

All six body fragments translate the complete source, including every proof,
formula, diagram, table, editorial note 0–20, both starred original footnotes,
and all seven bibliography entries. Every French source page was rendered and
read; selected English pages covering long formulas, the rank-one diagram,
commutator table, footnotes and bibliography were visually checked.

Validation (2026-10-04): `make -C translation/SGA3/ExposeXXIII` succeeds,
producing 31 main-text pages (35 PDF pages with front matter); no overfull or
underfull box warnings. The structural check
`python3 translation/SGA3/check_coverage.py --expose XXIII --source-dir source/SGA3 --require-pdf`
passes, as does `git diff --check` for this directory. All 56 numbered statement
labels are present. These checks do not replace independent sentence-level or
mathematical proofreading.

Chunk boundaries follow starting-page sentence ownership. Lemma 3.1.1 and its
list run from en-02 to en-03; item (ii)'s last sentence on p. 15 belongs to en-02.
The sentence at the start of 3.4.2 ending “as in (ii)” on p. 21 belongs to en-03.
The last sentence of 3.5.3 and note 10 finish on p. 26 and belong to en-04.
Editorial note 13 is marked inside the starred original note at 5.4; its text
follows that note, and the ordinary counter continues at 14.

Apparent mathematical, indexing and reference slips are retained as printed,
with `% typo?:` comments. No mathematical correction was applied:

| Source location | Printed text retained |
| --- | --- |
| 1.7 | Target `Z'_{d(Delta'_1)}` in the morphism, and unprimed `Z_{Delta'_1}` in the root-datum display. |
| 1.8.2 | `f(w_alpha)` rather than `f_N(w_alpha)`; free generators indexed by R. |
| Proof of 2.1.2 | Reference to “2.1.5 (ii)”, although 2.1.5 has no numbered parts. |
| Proof of 2.1.4 | `A_{alpha_0 beta_0}` attributed to the notation of 1.7. |
| 2.3 (6) | `w_alpha` also in the beta alternative. |
| Proof of 2.3.3 | “Fewer than k−1”; the transition uses `alpha_j` instead of `alpha_{j+1}`. |
| 2.3.4 and proof | `f_T` evaluated on normalizer elements n and n'. |
| Proofs of 2.3.5 and 2.4 | `n-bar(t)` and `p_alpha`, respectively. |
| 2.6 | Reference “Exp. XII, 5.5.2”; the argument writes x in `U_alpha` when applying `f_beta`, and later uses `U_alpha` again. |
| 3.3.3–3.3.6 | First transformation attributed to formula (2); capital X opposite lowercase x in 3.3.4; pairing value +2 in 3.3.6 whereas 3.3.2 prints −2. |
| 3.4.4 (8), 3.4.5 (9), 3.4.9 | Last factor `p_{3alpha+beta}`; third factor `p_alpha(-1)`; final Weyl-word line follows `s_alpha(t_beta)` by `t_beta`. |
| 3.4.10 and 3.5.3 | Reference to condition (v) of 2.4; generators indexed by R. |
| 4.1.5, 4.1.8, 4.1.9 | Missing primes in the definition of `X'_{alpha'+beta'}`; concluding reference 4.1.7; displayed root-datum arrow direction and references to 2.5 for gluing. |
| 6.1–6.3 | `X_{-alpha}=±X_alpha` without the inverse; first factor `w_{alpha_i}(X_{alpha_1})`; reference to part (i) for Chevalley systems. |
| Proof of 6.6 | System indexed by R+ and said to be a Chevalley system of the Lie algebra. |

The English retains the bibliography's dates and titles exactly as printed.
