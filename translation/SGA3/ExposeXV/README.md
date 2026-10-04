# SGA 3, XV

Complements on the subtori of a group prescheme. Application to smooth groups.

Author of the exposé: M. Raynaud.

French source (local only): `source/SGA3/Expo15.pdf` (68 pages),
the Gille–Polo recomposition.

| | |
| --- | --- |
| Status | Complete compiled draft; independent scholarly proofreading remains outstanding. |
| Chunks | en-01.tex (pp. 1--6), en-02.tex (pp. 7--12), en-03.tex (pp. 13--17), en-04.tex (pp. 18--22), en-05.tex (pp. 23--28), en-06.tex (pp. 29--38), en-07.tex (pp. 39--44), en-08.tex (pp. 45--50), en-09.tex (pp. 51--55), en-10.tex (pp. 56--60), en-11.tex (pp. 61--66), en-12.tex (pp. 67--68) |

Typographical corrections made in the English are marked in the body
with `% typo:`. Build: `make -C translation/SGA3/ExposeXV`.

Translated every sentence beginning on all 68 source PDF pages, including
continuations beyond chunk ranges, against rendered source pages. The build
has 56 physical PDF pages (52 body pages), 89 labels, editor notes 1–10, the
version note 0, and three original starred notes. Source pages and the English
pages for the final five chunks were rendered and inspected; earlier QA is
recorded in the handoff log. The final rebuild has no overfull boxes or
clipping. The Frobenius kernels retain the source's left-subscript notation
`{}_{F^n}(H)`, distinguished from the relative morphism `F^n`.

`check_coverage.py --expose XV --source-dir source/SGA3 --require-pdf` passes:
12/12 populated fragments, and all extracted source statement headings have
their labels. `git diff --check` passes. The structural check does not certify
sentence-level or mathematical fidelity.

Clear textual slips corrected: `respectivment`, `un point S`,
`si est seulement si`, the missing `pas` in “ne soit le radical”,
`présentation fine`, and the missing closing parenthesis before the second
definition of the functor in the proof of 5.3. Each has a body comment.

Mathematical or uncertain source slips retained as printed:

- 1.1 prints `H ×_{S_0} S`; 1.2 bis says `u` in the lifting assertion.
- 2.5 asserts the finite diagonalizable subgroups are completely split;
  2.5 bis has `(H ×_s Z)_s`; 2.1(c) renames the obstruction section `f`;
  the proof of 2.10 says the finite subgroup is flat over `S`.
- 3.6 has the two printed product expressions and their subscripts;
  the following reduction has `G_j = G_j ×_{S_i} S_j`; the proof of 3.7
  reverses the direction of `u` in one sentence.
- The proof of 3.1 gives `r^n` as the point count, cites `IX 5 bis`,
  switches `S_1` to `S^1`, and says `u_S` in the group-law check.
- The proof of 4.1 switches `M(n)` to `M_n`; 4.6 says smooth over `S`.
- The proof of 5.2 says `O_S` for a sheaf on `S'`; the proof of 5.3 says
  membership in `F^n` rather than `L^n`; 5.4 switches to `σ_s` and `O_{S'}`;
  the end of 5.2 prints projective limits for increasing unions.
- The proof of 6.2(i) gives `r^q` as the point count; (iii) uses unindexed
  `H` and says `C_η` is a Cartan subgroup of `H_η`; (ii) says `H` is maximal;
  the proof of 6.3 says `H_i` is smooth over `S` and “Corollary Exp. 6.3”.
- The proof of 6.6(c) calls `H_s=N_s` a parabolic subgroup of `G`;
  the finite-type reduction writes `N|_U` after defining `N'`; 6.10 says `G_k`.
- The proof of 7.1(iii) cites `XI 3.6 bis`; (vi) writes `u(CT_G)`;
  the proof of 7.3 concludes a lifting step from `d) => b)`.
- The proof of 8.1 switches between `S_n` and `S'_n` and uses `S'_0`;
  8.4 defines `L'` then uses `L`; the proof of 8.5 gives `T` as a target
  of the desired homomorphism to `G`.
- The proof of 8.9 prints `product_{K/S'} H_{S'}/K`; 8.11 cites 8.10;
  the proof of 8.15 switches from `S''_1` to `S'_1`; the final implication
  of 8.18 uses local constancy of the reductive and abelian ranks.

Additional clear textual slip corrected: `n'étant par nécessairement` to
`n'étant pas nécessairement`, with a body comment. The final starred note
retains the original forthcoming-thesis reference and its N.D.E. addition.
