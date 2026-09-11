# Lean 4 library

Lake project on mathlib. Toolchain: [`lean-toolchain`](lean-toolchain)
(same Lean as mathlib `v4.34.0-rc2`).

```bash
lake exe cache get    # first time: download mathlib oleans
lake build
```

Root module: `SGA.SGA1.ExposeVI`. Lemmas live next to that file
(`SGA/SGA1/ExposeVI/…`) and are imported from the barrel module.

See [`../docs/formalization.md`](../docs/formalization.md).
