# English translations

Unofficial English TeX of SGA, following Grothendieck’s numbering.
Conventions: [`CONVENTIONS.md`](CONVENTIONS.md).
License: [`LICENSE`](LICENSE) (CC BY-SA 4.0).

Do not add the French source to the repository. See [`../COPYRIGHT.md`](../COPYRIGHT.md).

## SGA 1

| Exposé | Directory | Coverage | Build |
| --- | --- | --- | --- |
| I — Étale morphisms | [`SGA1/ExposeI/`](SGA1/ExposeI/) | Full exposé draft | `make -C SGA1/ExposeI` |
| VI — Fibered categories and descent | [`SGA1/ExposeVI/`](SGA1/ExposeVI/) | Full exposé draft | `make -C SGA1/ExposeVI` |

```bash
make -C SGA1/ExposeI           # latexmk -pdf → SGA1-I.pdf
make -C SGA1/ExposeVI          # latexmk -pdf → SGA1-VI.pdf
make -C SGA1/ExposeVI clean
```

From the repository root, `make tex` builds both exposés.

Needs a reasonably complete TeX Live (`amsart`, `amsbook`, `xy`, `mathtools`, …).

New exposés go in `SGA<n>/Expose<Roman>/` with a `Makefile` like Exposé VI.
