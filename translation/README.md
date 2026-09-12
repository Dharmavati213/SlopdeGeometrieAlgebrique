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
| III — Smooth morphisms: extension properties | [`SGA1/ExposeIII/`](SGA1/ExposeIII/) | Full exposé draft | `make -C SGA1/ExposeIII` |
| VI — Fibered categories and descent | [`SGA1/ExposeVI/`](SGA1/ExposeVI/) | Full exposé draft | `make -C SGA1/ExposeVI` |

```bash
make -C SGA1/ExposeI           # latexmk -pdf → SGA1-I.pdf
make -C SGA1/ExposeII          # latexmk -pdf → SGA1-II.pdf
make -C SGA1/ExposeIII         # latexmk -pdf → SGA1-III.pdf
make -C SGA1/ExposeVI          # latexmk -pdf → SGA1-VI.pdf
make -C SGA1/ExposeIII clean
```

From the repository root, `make tex` builds all translated exposés.

Needs a reasonably complete TeX Live (`amsart`, `amsbook`, `xy`, `mathtools`, …).

New exposés go in `SGA<n>/Expose<Roman>/` with a `Makefile` like Exposé I or VI.
