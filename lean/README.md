# Lean 4 library

Lake project on mathlib. Toolchain: [`lean-toolchain`](lean-toolchain)
(same Lean as mathlib `v4.34.0-rc2`).

```bash
lake exe cache get    # first time: download mathlib oleans
lake build
```

Root modules: `SGA.SGA1.ExposeI`, `SGA.SGA1.ExposeVI`, `SGA.SGA2.ExposeI`,
and `SGA.SGA2.ExposeII`. Lemmas live in the matching exposé directories and
are imported from the barrel modules. SGA 2 currently has partial Exposé I
foundations and the module arguments for II.(7.5), II.9, and the principal
case of II.11; see the formalization notes for precise coverage and gaps.

See [`../docs/formalization.md`](../docs/formalization.md).
