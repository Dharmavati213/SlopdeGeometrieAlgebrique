# SGA, English + Lean

Unofficial English translations of Grothendieck’s *Séminaire de Géométrie
Algébrique du Bois Marie* (SGA), together with a Lean 4 formalization
built on [mathlib](https://github.com/leanprover-community/mathlib4).

This repository is a **working tree**, not a finished edition. One exposé
is translated; the Lean side is a compiling scaffold you can fill in.

## Status

| Work | State |
| --- | --- |
| SGA 1, Exposé VI — *Fibered categories and descent* (English) | translated |
| SGA 1, Exposé VI — Lean | scaffold only (mathlib already has the language) |
| Other exposés of SGA 1–7 | not started |

Details: [`STATUS.md`](STATUS.md). How to add an exposé or a lemma:
[`CONTRIBUTING.md`](CONTRIBUTING.md). License and sources:
[`COPYRIGHT.md`](COPYRIGHT.md).

## Layout

```
translation/SGA1/ExposeVI/   English TeX + PDF of SGA 1 VI
translation/CONVENTIONS.md   terminology and numbering rules
SGA/                         Lean 4 library (Lake + mathlib)
docs/                        roadmap and formalization notes
```

## Translation

The current text is SGA 1, Exposé VI, from the SMF recomposition
[arXiv:math/0206203](https://arxiv.org/abs/math/0206203). Statement
numbering is Grothendieck’s.

- TeX: [`translation/SGA1/ExposeVI/SGA1-Expose-VI-fibered-categories-EN.tex`](translation/SGA1/ExposeVI/SGA1-Expose-VI-fibered-categories-EN.tex)
- PDF: [`translation/SGA1/ExposeVI/SGA1-Expose-VI-fibered-categories-EN.pdf`](translation/SGA1/ExposeVI/SGA1-Expose-VI-fibered-categories-EN.pdf)

```bash
cd translation/SGA1/ExposeVI
make
```

The French original is **not** in this repo. See [`COPYRIGHT.md`](COPYRIGHT.md).

## Lean

Requires [elan](https://github.com/leanprover/elan). The toolchain is
pinned in `lean-toolchain` (same Lean as mathlib `v4.34.0-rc2`).

```bash
lake update
lake exe cache get    # download mathlib oleans; do this first
lake build
```

Open the folder in VS Code (Lean 4 extension) or Neovim (`lean.nvim`).
The root module is `SGA.SGA1.ExposeVI`.

## License

- Lean code, docs, and repo tooling: [Apache-2.0](LICENSE)
- English translation: [CC BY-SA 4.0](translation/LICENSE)

This is not an official edition of SGA.
