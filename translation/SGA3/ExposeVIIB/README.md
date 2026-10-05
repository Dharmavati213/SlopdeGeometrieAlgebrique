# SGA 3, Exposé VIIB — Infinitesimal study of group schemes. Formal groups

By P. Gabriel. English translation of the Gille–Polo recomposition,
`Exp7B-13oct24.pdf` (99 pages; not in this repository).
Complete draft; not yet independently reviewed against the French.

| File | Source pages |
| --- | --- |
| [`SGA3-VIIB.tex`](SGA3-VIIB.tex) | Standalone wrapper |
| [`en-01.tex`](en-01.tex) | 1–8 |
| [`en-02.tex`](en-02.tex) | 9–14 |
| [`en-03.tex`](en-03.tex) | 15–20 |
| [`en-04.tex`](en-04.tex) | 21–26 |
| [`en-05.tex`](en-05.tex) | 27–32 |
| [`en-06.tex`](en-06.tex) | 33–38 |
| [`en-07.tex`](en-07.tex) | 39–44 |
| [`en-08.tex`](en-08.tex) | 45–50 |
| [`en-09.tex`](en-09.tex) | 51–56 |
| [`en-10.tex`](en-10.tex) | 57–62 |
| [`en-11.tex`](en-11.tex) | 63–70 |
| [`en-12.tex`](en-12.tex) | 71–76 |
| [`en-13.tex`](en-13.tex) | 77–82 |
| [`en-14.tex`](en-14.tex) | 83–90 |
| [`en-15.tex`](en-15.tex) | 91–99 |
| [`SGA3-VIIB.pdf`](SGA3-VIIB.pdf) | Compiled PDF |

Build: `make -C translation/SGA3/ExposeVIIB`.

## Typographical corrections

Corrected in the English and marked `% typo:` in the source: “une morphisme”
(p. 34); the duplicated “polynôme” (p. 38); “contruction” in note 73 (p. 41);
the missing closing parenthesis in the definition of beta (p. 53); the
duplicated “est” (p. 72); the repeated G in 4.4.2 (p. 80); “cet numéro” in
note 164 (p. 95); the doubled period in J. C. Moore’s initials (p. 98).

## Source points retained as printed

Marked `% typo?:` in the source. These may be slips in the French; the translation keeps them.
Page numbers are PDF page numbers.

| Place | As printed |
| --- | --- |
| p. 5, proof of 0.2.B | Says the quotient topology is “finer”, while the argument proves the converse comparison. |
| p. 16, 0.5.A | Projection has source `M tensor ell` in the construction for `M tensor N`. |
| pp. 24–25, 1.2.5 | Uses `V_k^f(C)` and `V_k^{f,0}(C)` instead of the previously introduced functors of E, and calls the kernel “open” without specifying the origin topology. |
| p. 25, definition in 1.2.6 | Omits the condition that the image s be a closed point. |
| p. 26, proof of 1.3 | Final assertion `A = K` omits the possible zero algebra. |
| p. 33, 1.3.6.B | Both terms inside the intersection are indexed i, including `E_0 = 0`; the subsequent proof uses complementary indices. |
| p. 38, 1.6.A(ii), (iii) | Switches from `u_0` to `x_0`, x and u; says “lifting of Phi” where phi was given. |
| p. 41, proof of 1.6.E | Calls local components, and then all étale profinite algebras, “topologically free over k”, rather than the general projective condition. |
| pp. 41–42, 1.6.F | Chooses an arbitrary lifting u, then a monic polynomial of degree n annihilating u; uses k instead of the local component `k_s`. |
| p. 44, 2.1 | Asserts that all continuous linear maps form a group under convolution, with inverse obtained from the antipode. |
| p. 45, 2.2.1 | Prints `(Alf/k)^0 = Vaf/k`. |
| p. 46, corollary 2.2.1 | Prints `G(H) = Spf* H(G)`; the following affine group-scheme category omits flatness. |
| p. 51, end of 2.3.2 | Uses phi rather than theta in maps from G; the first arrow of the beta diagram is labeled `id_H circle sigma_23 circle id_H`. |
| p. 52, 2.4.A | Prints `theta circle sigma' : N -> G/Q`. |
| pp. 53–54, 2.4.A–B | Ordinary tensor symbols, the stated antipode identity, missing target for phi, x in place of x-prime in alpha, and a multiplication formula without the coproduct summation. |
| p. 55, 2.5 | Claims Gamma acts on each `X(ell)` even when ell need not be normal. |
| p. 58, 2.5.2.A | Defines the “infinitesimal” alpha group using `x^p - x`. |
| p. 59, proof of 2.5.3.B | Identifies the affine algebra after base change with `D(T_K)` itself. |
| pp. 60–61, 2.6(c), 2.6.1 | Switches dagger to star for dual basis elements; uses `tensor_A C` where the preceding construction is over k. |
| p. 63, 2.7 | The antipode identity for every u uses c_n and x; the asserted right-inverse identity repeats the left-inverse composition. |
| pp. 65–66, 2.9, 2.9.1 | Says the irreducible component corresponds to C_0 rather than S_0, and cancels the epimorphism pi to show its section respects multiplication. |
| pp. 72–74, 3.3.3, 4.1.1 | Calls the endomorphism functor a formal group; identifies the twisted structure morphism with fr(S) composed with eta. |
| pp. 78–79, 4.3.2 | Prints k[x] rather than C[x], Prim for the group-like elements, expansions without factorial denominators, and a^3 in the argument also when p=2. |
| p. 80, 4.4.2 | Calls G, rather than A, the projective limit of the affine algebras. |
| pp. 83–86, 5.1, 5.1.1–5.1.3 | Uses pi tensor id_A with the indicated opposite target; local-ideal and infinitesimal-monoid assertions add no flatness hypotheses; describes the associated graded as a formal completion. |
| pp. 85–88, 5.1.2, 5.1.4 | Middle bottom diagram indices i,n−1; a_n′ tensor a_n′ in the multiplication map; A_i′ in the supplement for degree n. |
| pp. 89–91, 5.2 notation, 5.2.1, 5.2.1.B | Ideal notation has r in omega_r; the invariance condition uses 1 tensor x; the splitting argument puts e_(n+1), rather than x, in F_j. |
| pp. 93, 95, 5.2.3–5.2.5 | Identifies J with the closed ideal in B although it was defined inside B^p; uses delta(I_n); gives n ≤ r in the stationarity sentence. |
| p. 97, 5.5.1–5.5.2 | Calls the local ring itself a formal power series algebra; omits hats on H and G in affine-algebra notation; cites Corollary 1.4. |

Also as in the source: the editorial-note markers 12, 92, 138 and 159 are
each repeated, with one note text printed for each.
