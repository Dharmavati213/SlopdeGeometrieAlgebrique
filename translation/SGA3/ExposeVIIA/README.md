# SGA 3, VIIA

Infinitesimal study of group schemes.

Author of the exposé: P. Gabriel.

French source (local only): `source/SGA3/Exp7A-13oct24.pdf` (60 pages),
the Gille–Polo recomposition.

| | |
| --- | --- |
| Status | Complete English draft; independent scholarly proofreading remains outstanding. |
| Chunks | en-01.tex (pp. 1--6), en-02.tex (pp. 7--12), en-03.tex (pp. 13--18), en-04.tex (pp. 19--24), en-05.tex (pp. 25--30), en-06.tex (pp. 31--36), en-07.tex (pp. 37--42), en-08.tex (pp. 43--48), en-09.tex (pp. 49--54), en-10.tex (pp. 55--60) |

Typographical corrections made in the English are marked in the body
with `% typo:`. Build: `make -C translation/SGA3/ExposeVIIA`.

All ten fragments were translated against the source PDF, including every
sentence, proof, formula, diagram, original/editorial footnote and all six
bibliography entries. All 60 source pages were rendered and inspected.
The source's ordinary editorial notes 1–87, its three original starred
notes, and the repeated note-80 marker are retained. Note 38 has its marker
inside an original starred footnote and its text once, outside that footnote.

Validation (2026-10-04): the complete `make` succeeds (52 physical PDF pages);
`python3 translation/SGA3/check_coverage.py --expose VIIA --source-dir
source/SGA3 --require-pdf` passes 10/10; 38 labels, no duplicate labels,
87 editorial-note bodies, six bibliography items, and `git diff --check`
passes. Representative English pages covering the contents, graph
interpretation, coalgebra diagrams, Frobenius, symmetric powers, Lie
algebras, classification, final proof and bibliography were rendered and
inspected. Horizontal overflow and overlapping Frobenius arrow labels
were fixed by changing layout only. One 2.43 pt vertical box warning and
inherited hyperref footnote-anchor warnings remain; the inspected text
and notes are fully visible. These checks are separate from independent
sentence-level and mathematical review.

Page-boundary assignments: en-01 ends at the colon introducing the
unnumbered lemma which starts on p. 7. Remarks 2.4.1 and 3.2.2.2 continue
in the next fragment without a repeated heading. En-05 completes its
last sentence from p. 30 on p. 31, through the image of `a tensor ...
tensor a`; en-06 starts “Similarly, j(A) ...”. En-09 includes the first
diagram and the definition of H on p. 55, finishing the sentence begun
on p. 54; en-10 starts “Now H is the spectrum ...”. No environment is
left open at a fragment boundary.

Clear textual slips corrected (and commented in the bodies): redundant
“de” before the element in 3.2.3; singular “la categories” in the proof
of 8.1.3; the omitted verb in “Comme G → S affine” in 8.5.2; and “Groups
schemes” in the Tate–Oort bibliography title.

Potential mathematical or notational slips retained as printed:

| Location | Printed text retained |
| --- | --- |
| 1.2.0–1.2.1 | `sigma: O_Z[t]` has no target; `s` is used after defining the zero section as tau. |
| 1.2.3; note 11 | `E=(v,d)` rather than `(v,e)`; note 11 changes f to g. |
| 2.3; 2.5 | `Dif_{X/S}`; the middle arrow is labelled `G times x` although its domain is `I_S times G`. |
| 3.1.2.1; 3.2.3 | Roman A in the final spectrum; `(1-vd)` without the prime on d. |
| 4.1; 4.2; 6.3 | Right-hand `Hom_S(T,X)`; `Spec(O_X/I)`; the symmetric group is repeatedly called “of order p”. |
| 4.3.3 | `V^p(A)` rather than `V^p(G)`. |
| 5.3; 5.3.3 | Unnamed A in the universal-property proposition; missing alpha subscripts on z and x in three displayed monomials. |
| 5.4; 5.5.3 | Canonical maps i rather than j; L-star at the start of sequence (*) and L in the dual (**). |
| 6.4.2–6.4.3 | Reference to 6.1 for i; O_S in the differential-operator formulas. |
| 7.1–7.2.1 | `Spec U_p(L)` without the dual star; final action uses G rather than G_p. |
| 7.2.3 | Theta is said to vanish on J/J-squared; the exact sequence and formula (2) use [L,L] without a symbolic-p-power term. |
| 7.4.3; note 79 | omega with subscript G/A; i for an inclusion labelled tau in the sequence. |
| 8.4 | Global étaleness is asserted without assuming commutativity; `I'=I intersection A` without a prime on A; B is said to have height. |
| Proof of 8.5 | The iterated diagonal is first indexed by s and later by s-minus-1; `m_U^p` and tensor signs occur in the displayed “product”. |

The PDF is the authority. These observations do not silently alter any
formula, hypothesis, number or argument.
