# English translations

Unofficial English TeX of SGA 1, SGA 2 and SGA 3, with Grothendieck's numbering.
Conventions: [`CONVENTIONS.md`](CONVENTIONS.md).
License: [`LICENSE`](LICENSE) (MIT; SGA 1 Exposé III is CC BY-SA 4.0).
The French sources are not in the repository and must not be added; see
[`../COPYRIGHT.md`](../COPYRIGHT.md).

Every directory below has a `Makefile`; `make -C <dir>` runs `latexmk -pdf`.
From the repository root, `make tex` builds everything. The build needs a
fairly complete TeX Live (`amsart`, `amsbook`, `xy`, `mathtools`, …).

## SGA 1

Source: SMF recomposition, [arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2).
All of SGA 1 is translated. The front matter and Exposés IV, V, VIII–XIII
share the macros in [`SGA1/sga1-en.sty`](SGA1/sga1-en.sty); I, II, III
and VI have their own wrappers.

| Part | Directory | Coverage | Build |
| --- | --- | --- | --- |
| Preface, Introduction, Foreword | [`SGA1/Introduction/`](SGA1/Introduction/) | Full draft, second-reader check | `make -C SGA1/Introduction` |
| I — Étale morphisms | [`SGA1/ExposeI/`](SGA1/ExposeI/) | Full draft, reviewed | `make -C SGA1/ExposeI` |
| II — Smooth morphisms: generalities, differential properties | [`SGA1/ExposeII/`](SGA1/ExposeII/) | Full draft, reviewed | `make -C SGA1/ExposeII` |
| III — Smooth morphisms: extension properties | [`SGA1/ExposeIII/`](SGA1/ExposeIII/) | Full draft, reviewed | `make -C SGA1/ExposeIII` |
| IV — Flat morphisms | [`SGA1/ExposeIV/`](SGA1/ExposeIV/) | Full draft, second-reader check | `make -C SGA1/ExposeIV` |
| V — The fundamental group: generalities | [`SGA1/ExposeV/`](SGA1/ExposeV/) | Full draft, second-reader check | `make -C SGA1/ExposeV` |
| VI — Fibered categories and descent | [`SGA1/ExposeVI/`](SGA1/ExposeVI/) | Full draft, reviewed | `make -C SGA1/ExposeVI` |
| VII | — | Does not exist | |
| VIII — Faithfully flat descent | [`SGA1/ExposeVIII/`](SGA1/ExposeVIII/) | Full draft, second-reader check | `make -C SGA1/ExposeVIII` |
| IX — Descent of étale morphisms. Application to the fundamental group | [`SGA1/ExposeIX/`](SGA1/ExposeIX/) | Full draft, second-reader check | `make -C SGA1/ExposeIX` |
| X — Theory of specialization of the fundamental group | [`SGA1/ExposeX/`](SGA1/ExposeX/) | Full draft, second-reader check | `make -C SGA1/ExposeX` |
| XI — Examples and complements | [`SGA1/ExposeXI/`](SGA1/ExposeXI/) | Full draft, second-reader check | `make -C SGA1/ExposeXI` |
| XII — Algebraic geometry and analytic geometry (M. Raynaud) | [`SGA1/ExposeXII/`](SGA1/ExposeXII/) | Full draft, second-reader check | `make -C SGA1/ExposeXII` |
| XIII — Cohomological properness of sheaves of sets and of sheaves of non-commutative groups (M. Raynaud) | [`SGA1/ExposeXIII/`](SGA1/ExposeXIII/) | Full draft, second-reader check | `make -C SGA1/ExposeXIII` |

"Reviewed": an earlier English version was compared sentence by sentence
with the corrected French and corrected (2026-09-24). The other exposés were
translated chunk by chunk, and a second reader checked each chunk against
the French. Each exposé's README lists the apparent misprints of the French
that the translation keeps.

## SGA 2

Source: SMF recomposition, [arXiv:math/0511279](https://arxiv.org/abs/math/0511279).
Shared macros: [`SGA2/sga2-en.sty`](SGA2/sga2-en.sty). Every exposé is a
draft: none has yet been checked against the French by a second reader.

| Exposé | Directory | Coverage | Build |
| --- | --- | --- | --- |
| Introduction | [`SGA2/Introduction/`](SGA2/Introduction/) | Draft | `make -C SGA2/Introduction` |
| I — Global and local cohomological invariants | [`SGA2/ExposeI/`](SGA2/ExposeI/) | Draft | `make -C SGA2/ExposeI` |
| II — Quasi-coherent sheaves on preschemes | [`SGA2/ExposeII/`](SGA2/ExposeII/) | Draft | `make -C SGA2/ExposeII` |
| III — Cohomological invariants and depth | [`SGA2/ExposeIII/`](SGA2/ExposeIII/) | Draft | `make -C SGA2/ExposeIII` |
| IV — Dualizing modules and functors | [`SGA2/ExposeIV/`](SGA2/ExposeIV/) | Draft | `make -C SGA2/ExposeIV` |
| V — Local duality and structure of $H^i(M)$ | [`SGA2/ExposeV/`](SGA2/ExposeV/) | Draft | `make -C SGA2/ExposeV` |
| VI — $\mathrm{Ext}_Z$ and $\underline{\mathrm{Ext}}_Z$ | [`SGA2/ExposeVI/`](SGA2/ExposeVI/) | Draft | `make -C SGA2/ExposeVI` |
| VII — Vanishing and coherence of $\underline{\mathrm{Ext}}^i_Y$ | [`SGA2/ExposeVII/`](SGA2/ExposeVII/) | Draft | `make -C SGA2/ExposeVII` |
| VIII — The finiteness theorem | [`SGA2/ExposeVIII/`](SGA2/ExposeVIII/) | Draft | `make -C SGA2/ExposeVIII` |
| IX — Algebraic geometry and formal geometry | [`SGA2/ExposeIX/`](SGA2/ExposeIX/) | Draft | `make -C SGA2/ExposeIX` |
| X — Application to the fundamental group | [`SGA2/ExposeX/`](SGA2/ExposeX/) | Draft | `make -C SGA2/ExposeX` |
| XI — Application to the Picard group | [`SGA2/ExposeXI/`](SGA2/ExposeXI/) | Draft | `make -C SGA2/ExposeXI` |
| XII — Applications to projective algebraic schemes | [`SGA2/ExposeXII/`](SGA2/ExposeXII/) | Draft | `make -C SGA2/ExposeXII` |
| XIII — Problems and conjectures | [`SGA2/ExposeXIII/`](SGA2/ExposeXIII/) | Draft | `make -C SGA2/ExposeXIII` |
| XIV — Depth and Lefschetz theorems in étale cohomology | [`SGA2/ExposeXIV/`](SGA2/ExposeXIV/) | Draft | `make -C SGA2/ExposeXIV` |

## SGA 3

Source: the Gille–Polo recomposition of *Schémas en groupes*
(<https://webusers.imj-prg.fr/~patrick.polo/SGA3/>). The foreword, the
introduction and Exposés I–XXVI are translated, and `make -C SGA3 book` builds
them into one volume. Not yet checked against the French by a second reader.
See [`SGA3/README.md`](SGA3/README.md) and
[`SGA3/CONVENTIONS.md`](SGA3/CONVENTIONS.md).
