# SGA, English + Lean

Unofficial English translations of Grothendieck’s *Séminaire de Géométrie
Algébrique du Bois Marie* (SGA), together with a Lean 4 formalization
on [mathlib](https://github.com/leanprover-community/mathlib4).

This is a working tree, not a finished edition. One exposé is translated;
the Lean side is a compiling scaffold.

## Layout

```
translation/     English TeX + PDF
lean/            Lean 4 library (Lake + mathlib)
docs/            status and formalization notes
```

| Work | State |
| --- | --- |
| SGA 1, Exposé VI — English | translated |
| SGA 1, Exposé VI — Lean | scaffold (mathlib already has the language) |
| Other exposés of SGA 1–7 | not started |

Tick-list: [`docs/status.md`](docs/status.md).
How to add an exposé or a lemma: [`.github/CONTRIBUTING.md`](.github/CONTRIBUTING.md).
Sources and licenses: [`COPYRIGHT.md`](COPYRIGHT.md).

## Build

Needs [elan](https://github.com/leanprover/elan) and a TeX Live with `latexmk`.

```bash
make            # Lean + PDF
make lean       # lake build in lean/
make tex        # PDF of SGA 1 VI
```

First Lean build, from `lean/`:

```bash
cd lean
lake exe cache get    # download mathlib oleans; do this first
lake build
```

Open `lean/` in VS Code (Lean 4 extension) or Neovim (`lean.nvim`).
The root module is `SGA.SGA1.ExposeVI`.

## License

- Lean code, docs, and repo tooling: [Apache-2.0](LICENSE)
- English translation: [CC BY-SA 4.0](translation/LICENSE)

This is not an official edition of SGA. The French original is not in
this repository.
