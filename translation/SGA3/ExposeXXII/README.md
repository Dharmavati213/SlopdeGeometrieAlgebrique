# SGA 3, XXII

Reductive groups: splittings, subgroups, quotient groups.

Author of the exposé: M. Demazure.

French source (local only): `source/SGA3/Exp22-13oct24.pdf` (68 pages),
the Gille–Polo recomposition.

| | |
| --- | --- |
| Status | Complete translator-checked draft; all 68 source pages translated. Independent sentence-level review and scholarly proofreading remain outstanding. |
| Chunks | en-01.tex (pp. 1--6), en-02.tex (pp. 7--12), en-03.tex (pp. 13--18), en-04.tex (pp. 19--24), en-05.tex (pp. 25--30), en-06.tex (pp. 31--36), en-07.tex (pp. 37--42), en-08.tex (pp. 43--48), en-09.tex (pp. 49--54), en-10.tex (pp. 55--60), en-11.tex (pp. 61--66), en-12.tex (pp. 67--68) |

Typographical corrections made in the English are marked in the body
with `% typo:`. Build: `make -C translation/SGA3/ExposeXXII`.

Verification (2026-10-04): all source pages rendered and read; `make` succeeds
(58 PDF pages), and `check_coverage.py --expose XXII --source-dir source/SGA3
--require-pdf` passes. Selected English diagram, long-formula, footnote and
bibliography pages visually inspected; no clipped content or overfull horizontal
boxes. One 1.34 pt vertical box warning occurs on English p. 31; its contents
and footnotes are fully visible. Notes 0–65 are retained, with repeated marks
for notes 5, 25, 58 and 64 and one note text for each. Five bibliography items.

Clear typographical corrections: the missing closing parenthesis in
5.10.3(d); the omitted “ce” in “D’après ce qui précède” in the proof of
5.9.3; and “mutiplicatif” in editorial note 63.

Potential source slips retained as printed (`% typo?:` in the bodies):

| Place | Printed source retained |
| --- | --- |
| 1.17 | “Each coroot α ∈ R”. |
| 4.1.3 | Reference to 1.19. |
| Proof of 4.1.9 | “in a neighborhood of S”. |
| 4.1.12 | X ∈ Γ(X, g^α). |
| 4.2.4 | W_G(T′) in the diagram's upper-right corner. |
| 4.3.1(ii) | (G′, T′, N, R) called a splitting of G. |
| 5.4.9 | q defined using α + iβ, while the formula uses β + iα. |
| Proof of 5.5.7 | x_i, …, x_{i−1} in Q_i's arguments; Y_i in an exponential; N−i−1 factors. |
| Proof of 5.6.1 | The g^{α_m} component uses ᾱ_m(X). |
| End of proof of 5.6.9 | U asserted to be a subsheaf of H^u. |
| 5.7.5 | Disjoint union formula has no representative n_w. |
| Proof of 5.9.5 | h(α) used for α ∈ R although h has domain M′; B_{S_i} = U_{i,0}. |
| Proof of 5.11.5 | H ∈ 𝓗_0(S′) although the introduced functor is 𝓗_c. |
| Proof of 6.1.2 | rad(T). |
| 6.3.1 | Reference “Exp. IVB 9.2”. |
| 6.3.3 | Bijection with subtori of corad(H). |
| 6.3.4 | T ∩ H called a maximal torus of G. |
