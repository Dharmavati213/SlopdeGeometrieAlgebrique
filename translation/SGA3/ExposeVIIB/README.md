# SGA 3, VIIB

Infinitesimal study of group schemes. Formal groups.

Author of the exposé: P. Gabriel.

French source (local only): `source/SGA3/Exp7B-13oct24.pdf` (99 pages),
the Gille–Polo recomposition.

| | |
| --- | --- |
| Status | Complete English draft: all fifteen fragments translated; independent scholarly proofreading remains outstanding. |
| Chunks | en-01.tex (pp. 1--8), en-02.tex (pp. 9--14), en-03.tex (pp. 15--20), en-04.tex (pp. 21--26), en-05.tex (pp. 27--32), en-06.tex (pp. 33--38), en-07.tex (pp. 39--44), en-08.tex (pp. 45--50), en-09.tex (pp. 51--56), en-10.tex (pp. 57--62), en-11.tex (pp. 63--70), en-12.tex (pp. 71--76), en-13.tex (pp. 77--82), en-14.tex (pp. 83--90), en-15.tex (pp. 91--99) |

Typographical corrections made in the English are marked in the body
with `% typo:`. Build: `make -C translation/SGA3/ExposeVIIB`.

## Progress and checks (2026-10-05)

All fifteen fragments translate every sentence, proof, formula, diagram and
footnote of source PDF pp. 1–99, including all 34 bibliography items. Every
source page was rendered and read. The translation retains editor notes 0–170
(171 note bodies), with repeated markers 12, 92, 138 and 159 printing one text
each. There are 79 distinct labels and no open environments.

The cumulative `make` succeeds, producing an 80-page PDF (76 body pages).
There are no unresolved citations or horizontal box warnings. Four small
vertical warnings (1.45 pt, 2.19 pt, 3.31 pt and 1.59 pt) show no clipping
on inspection after the shared parenthesized-note formatting update.
English physical pages 51–79 were rendered and inspected for the final five
fragments; the earlier portion's representative diagrams, formulas and note
pages were inspected by its worker. Long formulas are split without changing
the mathematics; the snake connecting arrow and labels on leftward parallel
arrows were repaired through layout changes. The accented category superscript
is typeset with `\text{ét}`. The coordinator reflowed 0.2.2's initial Hom formula
to remove a small overflow introduced by the parenthesized note markers.
Independent sentence-level review and scholarly
proofreading remain outstanding.

The full source-heading and PDF coverage gate passes 15/15:
`python3 translation/SGA3/check_coverage.py --expose VIIB --source-dir source/SGA3 --require-pdf`.
The directory whitespace check passes. Structural coverage does not replace
sentence-level or mathematical review.

### Fragment boundaries

en-10 finishes the opening sentence of source p. 63 defining the identity
section; en-11 starts “We shall say that the formal monoid M is infinitesimal
if …”. Cartier's proof spans en-11/en-12, with en-11 completing its final
sentence through “residue field k0” on p. 71. en-12 finishes the formula's
following clause on p. 77; en-13 starts “Formula (*) allows …”. The statement
of Proposition 5.1 spans en-13/en-14: condition (ii) belongs to en-14. en-14
finishes the diagram's following clause on p. 91 through the maps into
omega-infinity; en-15 starts “One therefore sees that a sufficient condition …”.

Earlier boundaries: en-02 finishes the sentence on p. 15 before Definition
0.4.2; en-04 finishes the sentence and notes 56–57 on p. 27 before the flatness
lemma; en-05 includes “is injective” from p. 33, and its proof of 1.3.6.A is
closed in en-06; en-09 finishes the sentence and exact sequence on p. 57,
then en-10 starts “In what follows …”.

## Source slips retained

The following printed mathematical or notation slips were kept, with
`% typo?:` comments. Source page numbers here are PDF page numbers.

| Page | Place | Printed text retained |
| --- | --- | --- |
| 5 | Proof of 0.2.B | Says the quotient topology is “finer”, while the argument proves the converse comparison. |
| 16 | 0.5.A | Projection has source `M tensor ell` in the construction for `M tensor N`. |
| 24–25 | 1.2.5 | Uses `V_k^f(C)` and `V_k^{f,0}(C)` instead of the previously introduced functors of E, and calls the kernel “open” without specifying the origin topology. |
| 25 | Definition in 1.2.6 | Omits the condition that the image s be a closed point. |
| 26 | Proof of 1.3 | Final assertion `A = K` omits the possible zero algebra. |
| 33 | 1.3.6.B | Both terms inside the intersection are indexed i, including `E_0 = 0`; the subsequent proof uses complementary indices. |
| 38 | 1.6.A(ii), (iii) | Switches from `u_0` to `x_0`, x and u; says “lifting of Phi” where phi was given. |
| 41 | Proof of 1.6.E | Calls local components, and then all étale profinite algebras, “topologically free over k”, rather than the general projective condition. |
| 41–42 | 1.6.F | Chooses an arbitrary lifting u, then a monic polynomial of degree n annihilating u; uses k instead of the local component `k_s`. |
| 44 | 2.1 | Asserts that all continuous linear maps form a group under convolution, with inverse obtained from the antipode. |
| 45 | 2.2.1 | Prints `(Alf/k)^0 = Vaf/k`. |
| 46 | Corollary 2.2.1 | Prints `G(H) = Spf* H(G)`; the following affine group-scheme category omits flatness. |
| 51 | End of 2.3.2 | Uses phi rather than theta in maps from G; the first arrow of the beta diagram is labeled `id_H circle sigma_23 circle id_H`. |
| 52 | 2.4.A | Prints `theta circle sigma' : N -> G/Q`. |
| 53–54 | 2.4.A–B | Ordinary tensor symbols, the stated antipode identity, missing target for phi, x in place of x-prime in alpha, and a multiplication formula without the coproduct summation are retained. |
| 55 | 2.5 | Claims Gamma acts on each `X(ell)` even when ell need not be normal. |
| 58 | 2.5.2.A | Defines the “infinitesimal” alpha group using `x^p - x`. |
| 59 | Proof of 2.5.3.B | Identifies the affine algebra after base change with `D(T_K)` itself. |
| 60–61 | 2.6(c), 2.6.1 | Switches dagger to star for dual basis elements; uses `tensor_A C` where the preceding construction is over k. |
| 63 | 2.7 | The antipode identity for every u uses c_n and x; the asserted right-inverse identity repeats the left-inverse composition. |
| 65–66 | 2.9, 2.9.1 | Says the irreducible component corresponds to C_0 rather than S_0, and cancels the epimorphism pi to show its section respects multiplication. |
| 72–74 | 3.3.3, 4.1.1 | Calls the endomorphism functor a formal group; identifies the twisted structure morphism with fr(S) composed with eta. |
| 78–79 | 4.3.2 | Prints k[x] rather than C[x], Prim for the group-like elements, expansions without factorial denominators, and a^3 in the argument also when p=2. |
| 80 | 4.4.2 | Calls G, rather than A, the projective limit of the affine algebras. |
| 83–86 | 5.1, 5.1.1–5.1.3 | Uses pi tensor id_A with the indicated opposite target; local-ideal and infinitesimal-monoid assertions add no flatness hypotheses; describes the associated graded as a formal completion. |
| 85–88 | 5.1.2, 5.1.4 | Middle bottom diagram indices i,n−1; a_n′ tensor a_n′ in the multiplication map; A_i′ in the supplement for degree n. |
| 89–91 | 5.2 notation, 5.2.1, 5.2.1.B | Ideal notation has r in omega_r; the invariance condition uses 1 tensor x; the splitting argument puts e_(n+1), rather than x, in F_j. |
| 93, 95 | 5.2.3–5.2.5 | Identifies J with the closed ideal in B although it was defined inside B^p; uses delta(I_n); gives n ≤ r in the stationarity sentence. |
| 97 | 5.5.1–5.5.2 | Calls the local ring itself a formal power series algebra; omits hats on H and G in affine-algebra notation; cites Corollary 1.4. |

Obvious typographical repairs only: “une morphisme” (p. 34), duplicated
“polynôme” (p. 38), “contruction” in note 73 (p. 41), the missing closing
parenthesis in beta's definition (p. 53), duplicated “est” (p. 72), the repeated
G in 4.4.2 (p. 80), “cet numéro” in note 164 (p. 95), and the doubled period
in J. C. Moore's initials (p. 98). They are marked `% typo:` in the body.
