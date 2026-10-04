# SGA 3, XXVI

Parabolic subgroups of reductive groups. Author: M. Demazure.

French source (local only): `source/SGA3/Exp26-13oct24.pdf` (53 pages),
the Gille–Polo recomposition of 13 October 2024.

| | |
| --- | --- |
| Status | Complete English draft. Independent sentence-level review and scholarly proofreading remain outstanding. |
| Chunks | en-01.tex (pp. 1–6), en-02.tex (pp. 7–12), en-03.tex (pp. 13–20), en-04.tex (pp. 21–26), en-05.tex (pp. 27–32), en-06.tex (pp. 33–38), en-07.tex (pp. 39–44), en-08.tex (pp. 45–50), en-09.tex (pp. 51–53) |
| Verification | All 53 source pages rendered and inspected; all nine fragments translated; make and source/PDF structural coverage checks pass; English diagrams, matrix argument, long formulas, notes and bibliography inspected. |

All nine fragments are populated, with 148 unique labels and all extracted
source statement headings retained. Editorial notes 0–39 have 40 bodies;
repeated markers 4 and 23 each share one text, and the original starred note
at 6.12.1 contains the marker for editorial note 31. Five bibliography
entries are retained. The source contains no table in this exposé.

Build: `make -C translation/SGA3/ExposeXXVI` produces 46 physical PDF
pages / 42 body pages. The structural gate
`python3 translation/SGA3/check_coverage.py --expose XXVI --source-dir source/SGA3 --require-pdf`
passes 9/9. No unresolved citations or horizontal overfull boxes remain.
One 1.38 pt vertical warning on body page 34 has no clipping in the rendered
page. Structural checks do not certify translation fidelity.

Boundary ownership: en-05 completes its last sentence on p. 33 through
`f(Q_1)=f(Q_2)`; en-06 starts “If S is the spectrum ...”. Corollary 5.7
opens at the end of en-06 and its separately numbered assertions continue
in en-07. En-07 ends with the statement of Corollary 6.17; en-08 begins its
proof. En-08 ends Counterexamples 7.11, and en-09 starts 7.12. All final
cross-fragment environments are closed.

Obvious typographical corrections are marked `% typo:`: agreement in the
introduction (“exposés”), a missing closing parenthesis in 3.10(i), “Le
démonstration” in the proof of 3.20, “l'assertions” in 4.5.1, and a missing
comma in `(P',Q')` in 4.5.2(iii), and a missing closing parenthesis in
`Aut(det(Lie(U)))` in the proof of 6.7.

Mathematical/reference anomalies are retained and marked `% typo?:`:

- 1.19(i)'s second map starts with unprimed P.
- The explanation of 1.21 says G possesses a Levi subgroup L.
- 2.1.1 defines R_i for i>0, then also uses i=0.
- The proof of 4.1.1 prints B' inside int(n) in the intersection formula,
  and later says “smooth over S” in the field case.
- 4.2.1(vii) and 4.4.1(v) have an unindexed R; the former proof prints a
  double arrow for the product morphism. The end of the 4.2.1 proof calls
  the intersection of the barred Borel subgroups a maximal torus of G.
- The proof of 4.2.4 uses Lie(P) plus Lie(G) as the source of u.
- 4.3.2 cites Exp. XXII 3.16.2(iv) and later 4.2.1 for an open immersion;
  it repeats rad^u(P) in the two intersections used to prove (v).
- The proof of 4.4.6 assigns P'=P^- intersection Q and
  Q'=P intersection Q^-, while the statement asks P' subset P and Q' subset Q.
- The proof of 4.5.1 switches from P_1,P_2 to P,Q; the printed hook on
  the q arrow in the diagram of 4.5.3 is retained.

Underlined functors, root-space superscripts, barred geometric points and
barred quotient tori were checked from the PDF. The truncated cube in
Figure 3.15.1 retains every morphism and property label; its labels were
positioned to avoid intersecting arrows. Long product expressions and
the diagram in 4.5.3 were split for layout without changing the mathematics.

- 5.1.8 prints a finite K-scheme D, then D/k, and the formula
  B'^{u}(k)=B_0^{u}(D).
- 5.1.10 uses an inclusion sign for a single matrix lying in the big cell.
- 5.5(iii) pairs (P,P') and (Q,Q') in its hypothesis, and its proof keeps
  the printed P_1/P'_1 and Q_1/Q'_1 opposition claims.
- 6.8's proof uses the derived group of G, while P' is parabolic in L'.
- 7.1.1 has Q as the denominator in its final normalizer quotient.
- 7.4.1's characterization of s_alpha does not exclude the identity.
- 7.10(3) defines U as rad^u(P)(S), then writes U(S).

The remaining source pages were read with particular attention to conjugation
bars in the finite-field matrix argument, the underlined canonical relative
root datum, geometric-point bars, and the coproduct glyphs for Lie algebras.
Long inline isomorphisms and equations were displayed or split for layout
without altering the mathematics. Independent scholarly review remains.
