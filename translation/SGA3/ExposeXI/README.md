# SGA 3, XI

Representability criteria. Applications to subgroups of multiplicative type of affine group schemes.

Author of the exposé: A. Grothendieck.

French source (local only): `source/SGA3/Expo11.pdf` (34 pages),
the Gille–Polo recomposition.

| | |
| --- | --- |
| Status | Complete English draft; independent sentence review and scholarly proofreading outstanding. |
| Chunks | en-01.tex (pp. 1--6), en-02.tex (pp. 7--12), en-03.tex (pp. 13--18), en-04.tex (pp. 19--24), en-05.tex (pp. 25--30), en-06.tex (pp. 31--34) |
| Verification | All source pages rendered and visually inspected; complete build succeeds (30 English PDF pages); rendered English layout inspected; structural coverage passes. |

All sentences, proofs, formulas, diagrams and footnotes are translated. The version
note (0), six original starred notes and editor notes 1--7 are retained; the repeated
marker for editor note 2 prints its text once. Source-page sentence boundaries are
respected, including statements and sentences completed on the following page.

Typographical corrections made in the English are marked with `% typo:`:
the missing closing parenthesis in the proof of 5.10 and `S et noethérien` in the
proof of 6.8--6.9. Apparent mathematical or reference slips are retained and marked
with `% typo?:`, notably:

- 1.4: `O_{X,s}`; 1.7: “k'' is the spectrum of a field”; 1.9 discussion: “F over X”;
  1.10: “subscheme S' of S” passing through x.
- 2.2 proof: reference VIII 3.6.
- 3.1(ii): S' → S; its proof: “for every s in S” and Spec(O_{S,s}) → U.
- 3.5 proof: base-change attribution and alternation between bold X and Y.
- 3.7--3.8 proof: T_i → F → T, “factors through F”, and reference (x) to a formula (*).
- 3.12: G_{T_S}; 3.13: “an open subset of F”; its proof: Hom_S(H,G)^I.
- 4.1 proof: T_u; 4.5 proof: I/J notation; condition d'): switch from quotient
  dimension to invariant dimension and locally free module over S.
- 5.8: G is called an S-prescheme without specifying a group structure.
- 6.1: H rather than H_s in condition b), denominator S on the right of (x), and T_n
  called a closed sub-prescheme of T; 6.2: K called a subgroup of H.
- 6.8--6.9 proof: Y_i called of finite presentation over S rather than X.

Build: `make -C translation/SGA3/ExposeXI`.
Coverage: `python3 translation/SGA3/check_coverage.py --expose XI --source-dir source/SGA3 --require-pdf`.
