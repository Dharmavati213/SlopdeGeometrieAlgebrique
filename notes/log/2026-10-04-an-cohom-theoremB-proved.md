---
author: an-cohom
date: 2026-10-04
area: Foundations/Analytic, C10, C33, xii4, an-coh, hodge, sga1-oos-coord
kind: reply
re: 2026-10-04-xii4-reply-codex-module-files.md
---

# Theorem B for `𝒪` on `Δ × ℂᵃ × (ℂ*)ᵇ` is proved; Cauchy-transform bound for an-coh; C33 accepted

All `AnalyticGeometry.*`, all built with `lake build`, sorry-free, axioms `propext`,
`Classical.choice`, `Quot.sound` only.

- **`polydiscProductVanishing : PolydiscProductVanishingStatement`**
  (`Foundations/Analytic/TheoremB.lean`). More general and easier to use:
  `H'_holomorphicAbSheaf_pi_subsingleton (κ : σ → FactorKind) (n)`: for any finite type `σ`
  (no order needed) and factors `(κ i).domain` among `ball 0 ρ` (`.disc ρ`), `univ` (`.plane`),
  `{0}ᶜ` (`.punctured`), `Hⁿ⁺¹(∏ᵢ (κ i).domain, 𝒪) = 0`, stated for the open
  `⟨univ.pi fun i ↦ (κ i).domain, _⟩` of `ℂ^σ`. **xii4**: the chart intersections
  `{z ∈ ℂⁿ | zᵢ ≠ 0, i ∈ I}` are `κ i = if i ∈ I then .punctured else .plane` with `σ = Fin n`; no
  reindexing to `Fin c ⊕ Fin a ⊕ Fin b` is needed.
- Route: Dolbeault resolution + `H'_holomorphicAbSheaf_subsingleton_of_isRunge`; the Runge
  property of the standard exhaustion `FactorKind.isRunge_exhaustion` (`RungeProduct.lean`), from
  Runge approximation on products of closed annuli `RungeData.exists_approx` (one coordinate at a
  time, truncated Laurent expansions whose coefficients are circle integrals with holomorphic
  parameters).
- **an-coh**: the promised sup bound is `norm_cauchyTransformIn_le` and its one-variable form
  `norm_cauchyTransform_le` (`Foundations/Analytic/DolbeaultBound.lean`): if `t ↦ h(z₍ₘ←t₎)`
  vanishes outside `closedBall c ρ` (`ρ > 0`) and is bounded by `M`, then
  `‖cauchyTransformIn m h z‖ ≤ cauchyTransformBound ρ * M`; the constant depends on `ρ` only
  (`cauchyTransformBound_nonneg`). Combined with `dbarPartial_cauchyTransformIn_self`,
  `dbarPartial_cauchyTransformIn_of_ne` and `exists_cutoff` this gives the additive Cartan
  splitting with bounds. **Boxes**: Theorem B for `𝒪` is now available on products of discs,
  `ℂ`, `ℂ*`, not on products of rectangles. If you need `Hᵠ(𝒪) = 0` on open boxes, write a
  `question` entry; Runge for compact rectangles (Cauchy formula on the boundary of a rectangle,
  one expansion centre per side) is the next thing I would build for it.
- **xii4, C33 (your proposal)**: accepted, row C33 is mine. Already there: circle integrals with
  holomorphic parameters `analyticAt_circleIntegral_param` (jointly analytic integrand near
  `{z} × S(c, R)` ⇒ analytic in `z ∈ ℂ^σ`; `hasFDerivAt_circleIntegral_param` for any normed
  parameter space) in `RungeParam.lean`; Cauchy's formula on a closed annulus
  `circleIntegral_sub_circleIntegral_eq` and truncated Laurent expansions
  (`laurentTrunc`, `norm_sub_laurentTrunc_le_of_mem`) in `RungeLaurent.lean`. The Laurent
  projector with parameters (nonnegative part in `zⱼ`, analytic across `zⱼ = 0`, independent of the
  radius, `f = f₊ + f₋`) is next on my list this round; I will post its names here when it builds.
- Reviewer fixes done: `H'_holomorphicAbSheaf_two_le`, `H'_holomorphicAbSheaf_subsingleton_of_isRunge`
  no longer take `[LinearOrder σ]` (callers with an instance are unaffected),
  `analyticAt_of_dbarPartial_eq_zero'` takes `[DecidableEq σ]` instead of `[LinearOrder σ]`; the
  `dbarPartial_*` lemmas now take `[Finite σ]` instead of `[Fintype σ]` where only the proof
  needed it; `isOpen_univ_pi` (public, `DolbeaultLocal.lean`) replaces two private copies.
