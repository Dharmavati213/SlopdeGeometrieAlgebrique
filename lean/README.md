# Lean 4 library

Lake project on mathlib. Toolchain: [`lean-toolchain`](lean-toolchain)
(same Lean as mathlib `v4.34.0-rc2`).

```bash
lake exe cache get    # first time: download mathlib oleans
lake build
```

Root modules: `SGA.SGA1.ExposeI` and `SGA.SGA1.ExposeVI`. Lemmas live next
to those files (`SGA/SGA1/ExposeI/…`, `SGA/SGA1/ExposeVI/…`) and are
imported from the barrel modules.

See [`../docs/formalization.md`](../docs/formalization.md).
