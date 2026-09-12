# English translations

Unofficial English TeX of SGA, following Grothendieck’s numbering.
Conventions: [`CONVENTIONS.md`](CONVENTIONS.md).
License: [`LICENSE`](LICENSE) (CC BY-SA 4.0).

Do not add the French source to the repository. See [`../COPYRIGHT.md`](../COPYRIGHT.md).

## SGA 1

| Exposé | Directory | Coverage | Build |
| --- | --- | --- | --- |
| I — Étale morphisms | [`SGA1/ExposeI/`](SGA1/ExposeI/) | Full exposé draft | `make -C SGA1/ExposeI` |
| II — Smooth morphisms: generalities, differential properties | [`SGA1/ExposeII/`](SGA1/ExposeII/) | Full exposé draft | `make -C SGA1/ExposeII` |
| VI — Fibered categories and descent | [`SGA1/ExposeVI/`](SGA1/ExposeVI/) | Full exposé draft | `make -C SGA1/ExposeVI` |

```bash
make -C SGA1/ExposeI           # latexmk -pdf → SGA1-I.pdf
make -C SGA1/ExposeII          # latexmk -pdf → SGA1-II.pdf
make -C SGA1/ExposeVI          # latexmk -pdf → SGA1-VI.pdf
make -C SGA1/ExposeVI clean
```

## SGA 2

Source: SMF recomposition, [arXiv:math/0511279](https://arxiv.org/abs/math/0511279).
Checklist: [`docs/status.md`](../docs/status.md) and GitHub issue #9.
Shared macros: [`SGA2/sga2-en.sty`](SGA2/sga2-en.sty). Label coverage:
`python3 translation/SGA2/check_coverage.py`.

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

From the repository root, `make tex` builds the translated exposés.

Needs a reasonably complete TeX Live (`amsart`, `amsbook`, `xy`, `mathtools`, …).

New exposés go in `SGA<n>/Expose<Roman>/` with a `Makefile` like Exposé I or VI.
