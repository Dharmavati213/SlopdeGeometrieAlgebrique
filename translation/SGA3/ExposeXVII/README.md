# SGA 3, XVII

Unipotent algebraic groups. Extensions between unipotent groups and groups of multiplicative type.

Author of the exposé: M. Raynaud.

French source (local only): `source/SGA3/Expo17.pdf` (50 pages),
the Gille–Polo recomposition.

| | |
| --- | --- |
| Status | Complete English draft. Independent sentence-level review and scholarly proofreading remain outstanding. |
| Chunks | en-01.tex (pp. 1--5), en-02.tex (pp. 6--10), en-03.tex (pp. 11--16), en-04.tex (pp. 17--24), en-05.tex (pp. 25--30), en-06.tex (pp. 31--36), en-07.tex (pp. 37--46), en-08.tex (pp. 47--50) |

All 50 source PDF pages were rendered and inspected (p. 50 is blank),
and all eight fragments contain the assigned sentences, proofs, formulas,
diagrams, notes and inline bibliographic text. There is no formal bibliography
section. All English body pages were rendered and inspected across the
three translator allocations, with a final check of the first page, long
formulas, appendices and diagrams. The complete make succeeds: 42 physical
PDF pages / 38 body pages.

The source/PDF structural gate
`python3 translation/SGA3/check_coverage.py --expose XVII --source-dir source/SGA3 --require-pdf`
passes 8/8. All 112 labels are unique; an additional source-heading audit
including Appendix A/B/C finds no omissions. There are no overfull boxes,
clipped formulas or unresolved references. Two harmless underfull vertical
boxes remain. The shared style disables footnote links, preventing duplicate note
destinations from original starred/version notes; contents, section and
citation links remain active. No duplicate destinations remain. Structural checks do not certify sentence-level or mathematical fidelity.

Editorial notes 1–13 have one body each; version note 0 and three original
starred notes are retained. Original notes preserve the editor-note counter.

The original stars occur at the author line and in the proofs of 4.2.1
and 4.6.1. The source's unfinished editorial queries (“reference to VIIA?”, “check
this reference”, “give another reference here ...”) are translated verbatim.

Sentence boundaries: en-01 finishes its last Cartier-duality sentence on
p. 6, through the isomorphism G → D(D(G)); en-02 starts “In particular,
one obtains”. En-02 ends the proof of 3.9(ii); en-03 starts the proof of
3.9(iii). En-03 finishes the Engel sentence on p. 17 through “a suitable
basis of V”; en-04 starts “Since G is of height 1 ...”. En-04 completes
its last p. 24 sentence on p. 25 through “(EGA IV 8 and 1.9.1)”; en-05
starts “There is therefore an extension K of k and a point u in R(K)”.
En-05 finishes its first c) sentence on p. 31 through “dimension dim U −
dim Z”; en-06 starts “In view of point a)”. En-06 completes the unique
lifting U'_1 sentence on p. 37, and en-07 starts “Proceeding as in the
proof of 6.2.4 ...”. En-07 ends Appendix C.1; en-08 starts C.2. All
environments are closed in the completed text.

Clear typography repairs are marked with `% typo:`: “un-k-groupe” in
3.9 ter, the missing “de” before “caractéristique” in 1.5, “corps de classeq” in Serre's book title at the end of 3.9(ii),
and the missing adjective in “le plus entier” in the starred note of the
4.2.1 proof (rendered “the least integer”). The formula in that note is
retained as printed.

Mathematical/reference anomalies are retained:

- Lemma 3.3 prints G in its density assertion.
- The proof of 3.8 cites 3.2 i) ⇒ v).
- The proof of 3.9(i) switches from Lie G to Lie G'' after its reduction.
- The original starred note in the proof of 4.2.1 prints F^h = id_G.
- The proof of 4.1.2 and continuation of 4.1.1 cite “4.1” rather than
  4.1.1; the EGA V reference is retained with the editorial query.
- Section 4.5 and parts (ii)/(v) of 4.6.1 do not print n > 1. Section
  4.5 also identifies a group of points with a group scheme.
- In the proof of 5.3.1, the torsion subgroups of H^0 are called dense in H.

The PDF was authoritative for barred algebraic closures, primes on H',
the underlined invariant functor in 3.1, the barred Lie subspace in 3.9(i),
the iterated powers in 4.1.5, and the left-subscript Frobenius-kernel
notation `{}_{F^n}G` (F is roman at subscript size, n is its superscript).
Formula lines were split for layout only.

Build: `make -C translation/SGA3/ExposeXVII`. Independent scholarly review
remains outstanding.

The tail translator records the following retained source anomalies:
7.3.2 prints x^(ell^n) = 0 in multiplicative notation; Appendix A.2 prints
(f,i) in the pushout construction; A.3 omits the second component gg' in
its product formula; C.5's proof heading prints “Proposition 5.1”, without
C. The missing closing parenthesis in the reference to X 4.8(b) in 7.1.1
was supplied and marked as typography. Appendices have no separate
bibliography; inline titles and bibliographic text are retained.

The middle translator retains these additional mathematical/reference slips:
the p. 27 proof heading says “5.5.1 ii) a)” before Proposition 5.6.1; the
p. 29 smoothness argument cites 5.6.1 and uses Ad(u)X although X' is the
lifting; Lemma 5.7.3 introduces U but repeatedly writes G; on p. 31 C'
becomes C; p. 32 prints (H/H)^0(k); p. 33 keeps x^p+x, t^2 and the printed
root-of-unity hypothesis; p. 34 defines G' then uses G'' in the torus-functor
discussion, and Spec[U,T,T^{-1}] lacks a coefficient field.

Further obvious typography repairs are marked: “de base H est de groupe”
was rendered with “and”; a parenthetical closing delimiter on p. 31 was
supplied; editorial note 10's “(1970.” became “(1970).”. The H(k) versus
H(overline k) distinctions on p. 33 were checked at high resolution.
