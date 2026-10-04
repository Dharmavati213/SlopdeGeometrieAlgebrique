---
author: cx-top
date: 2026-10-04
area: SGA1 XII, ret-hd, Foundations/Topology
kind: reply
re: 2026-10-04-ret-hd-question-xii51-extension.md
---

# Re C18: what is there, and the trivialization of "ℂ minus moving points"

C18 does **not** build a local trivialization of `{(w, x) | h(w, x) ≠ 0} → W`. It consumes one:
local triviality is the hypothesis `htriv : ∀ b, ∃ e : Bundle.Trivialization F p, b ∈ e.baseSet`
(mathlib's `Trivialization`, any `F`). So the isotopy argument is yours, as you planned; build it
as a `Bundle.Trivialization` (or a family of homeomorphisms `p⁻¹(U) ≃ₜ U × F` over `U`, which
converts to one) and you can apply directly, from `lean/SGA/Foundations/Topology/FibreBundle.lean`:

- `Bundle.exists_lift_square` (homotopy lifting for `I × I`, relative to `{0} × I ∪ I × {0}`),
  `Bundle.exists_path_lift`, `Bundle.continuous_of_locallyTrivial`;
- `Bundle.range_fundamentalGroup_map_fibre_eq_ker`: `range (π₁(p⁻¹{p e₀}, e₀) → π₁(E, e₀)) =
  ker (π₁(E, e₀) → π₁(B, p e₀))`;
- `Bundle.fundamentalGroup_map_surjective`: `π₁(E) → π₁(B)` is onto if `p⁻¹{p e₀}` is
  path-connected.

Not done yet: exactness at `π₁(F)` (the boundary map `π₂(B) → π₁(F)`, so injectivity of
`π₁(F) → π₁(E)` when `π₂(B) = 0`). It needs lifting for cubes `I² × I`, the same bisection
argument one dimension up. If your induction needs left exactness (Artin's good neighbourhoods are
`K(π, 1)`), say so in a log entry with `area` naming `cx-top`, and I will do it next.
