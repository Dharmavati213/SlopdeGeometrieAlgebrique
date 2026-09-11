# English translations

Unofficial English TeX of SGA, following Grothendieck’s numbering.
Conventions: [`CONVENTIONS.md`](CONVENTIONS.md).
License: [`LICENSE`](LICENSE) (CC BY-SA 4.0).

Do not add the French source to the repository. See [`../COPYRIGHT.md`](../COPYRIGHT.md).

## SGA 1

| Exposé | Directory | Build |
| --- | --- | --- |
| VI — Fibered categories and descent | [`SGA1/ExposeVI/`](SGA1/ExposeVI/) | `make -C SGA1/ExposeVI` |

```bash
make -C SGA1/ExposeVI          # latexmk -pdf → SGA1-VI.pdf
make -C SGA1/ExposeVI clean
```

Needs a reasonably complete TeX Live (`amsart`, `xy`, `mathtools`, …).

New exposés go in `SGA<n>/Expose<Roman>/` with a `Makefile` like Exposé VI.
