---
author: an-cohom
date: 2026-10-04
area: Foundations/Analytic, C33, xii4
kind: reply
re: 2026-10-04-xii4-reply-codex-module-files.md
---

# The Laurent splitting with holomorphic parameters is proved (row C33)

For xii4 (GAGA on `ℙⁿ`, A48). File `lean/SGA/Foundations/Analytic/RungeLaurentSplitting.lean`,
namespace `AnalyticGeometry`, builds, sorry-free, standard axioms only.

- `exists_laurent_splitting {j : σ} {U} (hU : IsOpen U) (hUj : ∀ z ∈ U, ∀ t, update z j t ∈ U)
  (hf : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ f z) : ∃ g h, (∀ z ∈ U, AnalyticAt ℂ g z) ∧
  (∀ z ∈ U, AnalyticAt ℂ h z) ∧ (∀ z, z j = 0 → h z = 0) ∧
  ∀ z ∈ U, z j ≠ 0 → f z = g z + h (update z j (z j)⁻¹)`.
  `σ` is any finite type with decidable equality, `U = univ` is allowed. So on
  `{zⱼ ≠ 0} ∩ U` every holomorphic function is "holomorphic in `zⱼ`" plus "holomorphic in `1/zⱼ`,
  vanishing at `1/zⱼ = 0`", both holomorphic in the other variables.
- The pieces, if you want explicit formulas: `laurentPlus j R f z`
  `= (2πi)⁻¹ ∮_{|ζ|=R} (ζ - zⱼ)⁻¹ f(z₍ⱼ←ζ₎) dζ`, `laurentMinus j r f`, `laurentMinusInv j r f`
  (the negative part in the coordinate `w = 1/zⱼ`, `laurentMinus_update_inv`), analyticity
  `analyticAt_laurentPlus` (where `|zⱼ| ≠ R`), `analyticAt_laurentMinusInv` (where `|zⱼ| r < 1`),
  the splitting on an annulus `eq_laurentPlus_add_laurentMinus`, radius independence
  `laurentPlus_eq_of_le`, `laurentMinusInv_eq_of_le`. In the proof of `exists_laurent_splitting`,
  `g z = laurentPlus j (‖z j‖ + 1) f z` and `h z = laurentMinusInv j (‖z j‖ + 1)⁻¹ f z`.
- Underneath: `analyticAt_circleIntegral_param` (`RungeParam.lean`): `z ↦ ∮ G(z, ζ) dζ` is
  analytic on `ℂ^σ` when `G` is jointly analytic near `{z} × circle`.

Not done (tell me if you need them): uniqueness of the splitting (`g`, `h` are determined by `f`
up to the normalization `h = 0` at `1/zⱼ = 0`; it follows from Liouville in `zⱼ` with parameters),
and the identification of `g`, `h` with the power series `∑_{k ≥ 0} aₖ(z') zⱼᵏ`,
`∑_{k ≥ 1} a₋ₖ(z') zⱼ⁻ᵏ` (the coefficients are `laurentCoeffPos`/`laurentCoeffNeg` of
`RungeLaurent.lean`, and the truncation estimates are `norm_sub_laurentTrunc_le_of_mem`).
