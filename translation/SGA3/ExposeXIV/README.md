# SGA 3, XIV

Regular elements, continued. Application to algebraic groups.

Author of the exposé: A. Grothendieck, with an appendix by J.-P. Serre.

French source (local only): `source/SGA3/Expo14.pdf` (36 pages),
the Gille–Polo recomposition.

| | |
| --- | --- |
| Status | Complete draft; all source pages translated and visually checked. Independent sentence review and scholarly proofreading remain. |
| Chunks | en-01.tex (pp. 1--6), en-02.tex (pp. 7--12), en-03.tex (pp. 13--18), en-04.tex (pp. 19--24), en-05.tex (pp. 25--30), en-06.tex (pp. 31--36) |

Typographical corrections made in the English are marked in the body
with `% typo:`. Build: `make -C translation/SGA3/ExposeXIV`.

All six fragments are populated, including Serre's appendix. All 36 source
PDF pages were rendered and inspected (p. 36 is blank). The complete English
PDF builds to 30 pages (26 body pages plus front matter); all rendered
English pages were inspected, with no clipping or horizontal overfull boxes.
There is one 3.11pt vertical warning, on body p. 9, with no clipping.

`python3 translation/SGA3/check_coverage.py --expose XIV --source-dir source/SGA3 --require-pdf`
passes. There are 79 statement labels, including the appendix's unnumbered
theorem and lemmas 1–5. All seven sections, editor notes 1–9, four starred
original notes, the appendix's original notes 1–2, and version note 0 are
retained. Editor note 8's entire Bruhat-decomposition proof is included.
The appendix restarts the original note counter independently of editorial
note 9. All four Dynkin diagrams and their automorphism arrows are retained.
There is no bibliography. Cross-fragment statements/proofs are closed.

Source slips retained as printed (marked `% typo?:` in the bodies):

| PDF page | Location | Printed text retained |
| --- | --- | --- |
| 2 | Proof of 1.1 | `C' ↦ C=u⁻¹(C)` and reference 1.3 for existence of a subgroup of type (C). |
| 2 | 1.4 and proof | `S` also names the torus; its centralizer is said to be smooth over `k`. |
| 4 | Following 2.2 | The symmetric algebra is written `Sym(d)` without the dual. |
| 8–10 | Scheme of Cartan subalgebras | Several occurrences use fraktur `d` instead of the functor's script `D`. |
| 10 | Proof of 2.16(c) | `d` rather than `d'` in condition 2; V “contains a”; condition `1°)` rather than `(i)`. |
| 11 | 3.1 | `Γ(s',h_S)` in the transporter condition; proof uses the same `d` for two Cartan subalgebras. |
| 12 | Proof of 3.2(b) | Transports `k₀` into `g₀`, and `k` into `g`; next paragraph's transporter uses `d`. |
| 13 | 3.5 and 3.6 proof | “Cartan subalgebras of G”; “its own normalizer in d”. |
| 14 | Proof of 3.9 | Union of connected components of the fibers has no identity-component qualifier. |
| 15 | 3.12(a) | `g_g` instead of a fiber indexed by s. |
| 16 | 3.17(b) | A “group subprescheme H of S”. |
| 17 | Proof of 3.18 | `Hom(T,G)` with no multiplicative subscript. |
| 19 | Proof of 4.4 | The reduction refers only to the connected normalizer. |
| 21 | 4.10 | Reference to nonexistent 4.7 (editor note 5 explicitly notes its absence). |
| 22 | Proof of 4.12 | `V` names the unipotent group; its Lie algebra `v` supplies the composition series used for the representation. |
| 23 | Proof of 5.2(c) | “Cartan subalgebra of d”. |
| 24 | 5.4 | H is not assumed smooth, despite the stated equivalence and proof's use of XIII 5.5. |
| 25 | 5.6 | Parenthetical equivalence does not repeat the condition H ⊂ D. |
| 26 | Proof of 6.1 | `C'` lacks the x subscript; reference to 7.1 rather than 6.1. |
| 27 | Proof of 6.3 | Composition-series subscript `0 ≤ 1 ≤ n`. |
| 34 | Appendix proof | `ψ(c(θ_i'))` uses a primed index in the displayed comparison. |

Obvious typography corrected with `% typo:` comments: “un en un seul”
(p. 3); punctuation after “corps” (p. 3); duplicated “de” in 2.11(a)
and “section et” (p. 6); “sous-akgèbres” (p. 12); “il n'existe par”
(p. 16); “extension transcendante pur” (p. 26); and “de Lie de de T”
in the appendix (p. 33). No mathematical corrections were made.
