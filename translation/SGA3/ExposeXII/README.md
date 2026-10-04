# SGA 3, XII

Maximal tori, the Weyl group, Cartan subgroups, the reductive center of smooth affine group schemes.

Author of the exposé: A. Grothendieck.

French source (local only): `source/SGA3/Expo12.pdf` (48 pages),
the Gille–Polo recomposition.

| | |
| --- | --- |
| Status | Complete English draft; independent sentence review and scholarly proofreading outstanding. |
| Chunks | en-01.tex (pp. 1--6), en-02.tex (pp. 7--12), en-03.tex (pp. 13--18), en-04.tex (pp. 19--24), en-05.tex (pp. 25--30), en-06.tex (pp. 31--36), en-07.tex (pp. 37--42), en-08.tex (pp. 43--48) |
| Verification | All source pages rendered and visually inspected; complete build succeeds (42 English PDF pages); all English pages inspected for layout; structural coverage passes. |

Every sentence, proof, formula, diagram, bibliography item and footnote is
translated, including the January 2008 supplement on fixed points. All 82 printed
numbered statements have labels. The version note (0), three original starred notes,
editor notes 1--13 and six bibliography items are retained. Proofs cross fragment
boundaries in en-05/en-06 and en-07/en-08; do not close them early.

Clear typographical slips are corrected and marked with `% typo:` in the bodies:
`te que`, `une applications`, `par nécessairement`, duplicated k in 8.3,
`la groupe additif`, a missing parenthesis, a stray opening quotation mark,
`un faisceaux`, `pour le sous le groupe`, missing connecting words in the fixed-point
supplement, and `tranformations`.

Apparent mathematical or reference slips are retained and marked with `% typo?:`,
notably:

- 1.3: capital S in T_{bar S}; 1.9: bar k although k already denotes an algebraic closure.
- 2.2 proof: G instead of W; 2.3 statement: T not specified maximal, though used as such.
- 3.2 proof: base S'; 4.1(ii): H over S rather than S'.
- 4.5 proof: T called central in G, and G/T followed by C/T; 4.7 proof: T'_0=T_0/Z_0
  and “Since T is a maximal torus, so is T”; 4.11 proof: reductive rank zero.
- 5.1 proof: reference IX 3.7; 5.5: base S in a statement over k; its proof concludes
  with G/C instead of G/N; 5.6: U called a sub-prescheme of G instead of M.
- 6.2 proof: base S in Hom; 6.6 proof: u^{-1}(C) instead of u^{-1}(C').
- 7.1(d): both functors named T; its proof: “a maximal torus G_{S'}”, unprimed C,T
  after a base change, and s' instead of s''; 7.4 proof: C instead of C^0;
  7.5: equals sign in morphism notation; 7.8 note: capital S in G_{bar S};
  7.9 proof: relation (g/c)^T missing =0; 7.12 proof: references 7.10 and 7.11;
  7.13: C' called a subgroup of G instead of G'.
- 8.8(b): no centrality hypothesis on u in its final assertion.
- 9.4 proof: H^1 instead of H^0 in the affine-action formula, and unspecified L;
  9.5: “Wevers” differs from bibliography “Wewers”; 9.7 proof: missing prime on
  c(epsilon_0), reversed fiber-product base and the printed differential modules;
  9.11 proof: L as the first term of the complex.

Printed bibliography reference abbreviations in the prose are preserved, including
[F], [I], [G-R], [R], [T-Y], [W], which differ from some bibliography labels.
There are no overfull horizontal boxes; two small vertical warnings remain
(1.64pt and 1.38pt), with no visible clipping.

Build: `make -C translation/SGA3/ExposeXII`.
Coverage: `python3 translation/SGA3/check_coverage.py --expose XII --source-dir source/SGA3 --require-pdf`.
