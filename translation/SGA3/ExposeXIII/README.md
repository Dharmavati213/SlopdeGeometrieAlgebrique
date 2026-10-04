# SGA 3, XIII

Regular elements of algebraic groups and of Lie algebras.

Author of the exposé: A. Grothendieck.

French source (local only): `source/SGA3/Expo13.pdf` (30 pages),
the Gille–Polo recomposition.

| | |
| --- | --- |
| Status | Complete draft; all source pages translated and visually checked. Independent sentence review and scholarly proofreading remain. |
| Chunks | en-01.tex (pp. 1--6), en-02.tex (pp. 7--12), en-03.tex (pp. 13--18), en-04.tex (pp. 19--24), en-05.tex (pp. 25--30) |

Typographical corrections made in the English are marked in the body
with `% typo:`. Build: `make -C translation/SGA3/ExposeXIII`.

All five fragments are populated. The source has 30 PDF pages (the last is
blank); all were rendered and inspected. The complete English PDF builds to
26 pages (22 body pages plus front matter); all rendered English pages were
inspected, with no clipping and no overfull boxes.

`python3 translation/SGA3/check_coverage.py --expose XIII --source-dir source/SGA3 --require-pdf`
passes. All 42 printed statement headings are labelled, all six sections and
editor notes 1–11 are retained, as is the version note 0. There is no
bibliography in this exposé. Cross-fragment proofs in en-01/en-02 and
en-02/en-03 are closed in the assembled text.

Source slips retained as printed (marked `% typo?:` in the bodies):

| PDF page | Location | Printed text retained |
| --- | --- | --- |
| 1 | Initial sheaf identification | Unintroduced `M` in `G,V,M`. |
| 3 | Formula (1) | Last bound ends in `m_a` without a rank operator. |
| 3 | Proof of 1.1 | `X_n`, rightward `j'_a` in the diagram, and local-ring subscripts `a`/`b`; (iii bis) uses `M`. |
| 5 | Proof of 2.1 | `h ⊃ n` and `h ⊂ g^T` after `c=g^T`, and again `h ⊃ n`. |
| 6 | Proof of 2.1 | `T(K)` although the base field is `k`. |
| 7 | Proof of 2.2 | `ψ=φ∘q` is written with the reversed composition. |
| 8 | Proof of 2.1 | `int(v)·C' → u` and the conclusion `C=H`. |
| 9 | Proof of 2.3 | The proof concludes `C ⊂ G` rather than the statement's `C ⊂ H`. |
| 11 | Formula (†) | Left-hand side ends in `c_0` and omits intermediate terms; prose uses `G(K)`. |
| 12 | Proof of 2.8 | “Regular in C” while proving regularity in G. |
| 15 | Proof of 3.1 | Exponent `n-r-1` uses `r` where surrounding notation uses `ρ`. |
| 18 | Proof of 4.1 | Capital `Ad(a)` instead of `ad(a)`. |
| 21 | Proof of 4.7 | `d'=u(d_A)` is said to contain `a_A`; the action is written `ad(b)_d`. |
| 22 | Section 5 setup | `X` names both the quotient and `G×W(h)`. |
| 26 | Proof of 5.5 | `H=M_a^0` although H was not assumed connected. |
| 27 | Proof of 6.1 | `N=M` rather than `N=M_a`. |

Obvious typography corrected with `% typo:` comments: missing closing
parenthesis in the SL(2) example (p. 13), “ou peut”/“expoée” in the proof
of 2.6 (p. 10), “on vu” (p. 11), “on ouvert”/missing “on” (p. 14), and
the unmatched opening parenthesis after the rank operator (p. 19).
