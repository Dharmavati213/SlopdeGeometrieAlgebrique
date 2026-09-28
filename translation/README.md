# English translations

Unofficial English TeX of SGA, following Grothendieck’s numbering.
Conventions: [`CONVENTIONS.md`](CONVENTIONS.md).
License: [`LICENSE`](LICENSE) (MIT; SGA 1 Exposé III is CC BY-SA 4.0).

Do not add the French source to the repository. See [`../COPYRIGHT.md`](../COPYRIGHT.md).

## SGA 1

Source: SMF recomposition, [arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2).
All of SGA 1 is translated. The front matter and Exposés IV, V, VIII–XIII
share the macros in [`SGA1/sga1-en.sty`](SGA1/sga1-en.sty); I, II, III
and VI keep their own wrappers.

| Part | Directory | Coverage | Build |
| --- | --- | --- | --- |
| Preface, Introduction, Foreword | [`SGA1/Introduction/`](SGA1/Introduction/) | Full draft | `make -C SGA1/Introduction` |
| I — Étale morphisms | [`SGA1/ExposeI/`](SGA1/ExposeI/) | Full draft, reviewed | `make -C SGA1/ExposeI` |
| II — Smooth morphisms: generalities, differential properties | [`SGA1/ExposeII/`](SGA1/ExposeII/) | Full draft, reviewed | `make -C SGA1/ExposeII` |
| III — Smooth morphisms: extension properties | [`SGA1/ExposeIII/`](SGA1/ExposeIII/) | Full draft, reviewed | `make -C SGA1/ExposeIII` |
| IV — Flat morphisms | [`SGA1/ExposeIV/`](SGA1/ExposeIV/) | Full draft | `make -C SGA1/ExposeIV` |
| V — The fundamental group: generalities | [`SGA1/ExposeV/`](SGA1/ExposeV/) | Full draft | `make -C SGA1/ExposeV` |
| VI — Fibered categories and descent | [`SGA1/ExposeVI/`](SGA1/ExposeVI/) | Full draft, reviewed | `make -C SGA1/ExposeVI` |
| VII | — | Does not exist | |
| VIII — Faithfully flat descent | [`SGA1/ExposeVIII/`](SGA1/ExposeVIII/) | Full draft | `make -C SGA1/ExposeVIII` |
| IX — Descent of étale morphisms. Application to the fundamental group | [`SGA1/ExposeIX/`](SGA1/ExposeIX/) | Full draft | `make -C SGA1/ExposeIX` |
| X — Theory of specialization of the fundamental group | [`SGA1/ExposeX/`](SGA1/ExposeX/) | Full draft | `make -C SGA1/ExposeX` |
| XI — Examples and complements | [`SGA1/ExposeXI/`](SGA1/ExposeXI/) | Full draft | `make -C SGA1/ExposeXI` |
| XII — Algebraic geometry and analytic geometry (M. Raynaud) | [`SGA1/ExposeXII/`](SGA1/ExposeXII/) | Full draft | `make -C SGA1/ExposeXII` |
| XIII — Cohomological properness of sheaves of sets and of sheaves of non-commutative groups (M. Raynaud) | [`SGA1/ExposeXIII/`](SGA1/ExposeXIII/) | Full draft | `make -C SGA1/ExposeXIII` |

"Reviewed": the earlier English was compared sentence by sentence with
the corrected French and corrected (2026-09-24). The new exposés were
translated chunk by chunk, and each chunk was re-checked against the
French by a second pass. Each exposé's README lists the apparent
misprints of the French source that the translation retains.

```bash
make -C SGA1/ExposeIV           # latexmk -pdf → SGA1-IV.pdf
make -C SGA1/ExposeIII clean
```

## SGA 2

Source: SMF recomposition, [arXiv:math/0511279](https://arxiv.org/abs/math/0511279).
Checklist: [`docs/status.md`](../docs/status.md) (the original GitHub checklist, issue #9, is closed).
Shared macros: [`SGA2/sga2-en.sty`](SGA2/sga2-en.sty).

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

```bash
make -C SGA2/Introduction      # latexmk -pdf → SGA2-Intro.pdf
make -C SGA2/ExposeI           # latexmk -pdf → SGA2-I.pdf
# … likewise ExposeII–ExposeXIV
```

From the repository root, `make tex` builds all translated exposés.

Needs a reasonably complete TeX Live (`amsart`, `amsbook`, `xy`, `mathtools`, …).

New exposés go in `SGA<n>/Expose<Roman>/` with a `Makefile` like the existing ones.
