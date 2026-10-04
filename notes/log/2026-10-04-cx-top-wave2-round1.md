---
author: cx-top
date: 2026-10-04
area: Foundations/Topology, cx-top, xiii212, ret-hd, xii51, sga1-oos-coord
kind: handoff
---

# cx-top wave 2 round 1: ordered genus-0 generators, ℙ¹ presentations, fibre bundles, genus-g interface

Five new files in `lean/SGA/Foundations/Topology/`, each `lake build`s with no warnings, no `sorry`;
main results use only `propext`, `Classical.choice`, `Quot.sound`. No existing `.lean` file edited,
no barrel edited (the coordinator should add the five modules to `SGA/Foundations.lean`).

## Done

- **`SurfaceLoopAround.lean`** (tools). `Path.WindsOnceAround j s γ`: `j ∘ γ - s` has a continuous
  log increasing by `2πi`. For `j` an embedding onto `C ∖ {s}` (`C` convex open):
  `Path.WindsOnceAround.homotopic` (two such loops at one base point are homotopic: translate one
  log by `2πik`, both are paths in the simply connected `exp⁻¹(C - s)`),
  `FundamentalGroup.IsLoopAround.exists_windsOnceAround` (lift `δ` through `exp`, follow the circle,
  come back translated), hence `IsLoopAround.eq` (two loops around `s` at one base point are
  equal), `Path.WindsOnceAround.isLoopAround`, `IsLoopAround.existsUnique_hom` (free generator of
  `π₁ ≅ ℤ`). `Complex.exists_log_quadPath`: a quadrilateral with `s` strictly left of each edge
  winds once (four `arg`s in `(0, π)` summing to a multiple of `2π`). `Complex.segmentPath`,
  `Topology.IsEmbedding.liftPath` (+ `_trans`, `_symm`, `map_liftPath`,
  `liftPath_homotopic_of_convex`), `Path.trans_apply_compat`.
- **`SurfaceGenusZeroOrdered.lean`** (C17 genus 0, ordered). `Complex.exists_ordered_freeGroupBasis_of_isOpenEmbedding`
  (`j : X → ℂ` open embedding onto `ℂ ∖ S`): `∃ e : Fin n ≃ S, b : FreeGroupBasis (Fin n) π₁(X, x)`
  with `b i` a loop around `e i` and `(b₀ ⋯ b_{n-1})⁻¹` a loop around `0` in the coordinate `1/j`
  (around `∞`); subtype form `Complex.exists_ordered_freeGroupBasis`. Proof: shear coordinate
  `v = re + ε im` injective on `S`, strips between cut values `xᵢ`, parallelograms `Rᵢ`, loops
  `σᵢ` = bottom edge, `∂Rᵢ`, back; freeness by induction on half-planes `v < xₖ + η` with
  two-piece van Kampen (the pieces meet in thin strips without points); the product is `∂R` by a
  fundamental-groupoid identity (vertical edges cancel; bottom/top edges merge in convex
  half-planes); `∂R` lies outside `D(0, R)` and in the coordinate `1/z` its reverse winds once.
- **`SurfacePresentation.lean`**. `FreeGroupBasis.bijective_toGroup_snoc` (free basis plus inverse of
  the product presents `G` with the one relator `FreeGroupBasis.prodRelator`);
  `Complex.exists_presentation_of_isOpenEmbedding` (`ℂ ∖ S` as `ℙ¹` minus `|S| + 1` points);
  `Complex.exists_presentation_fundamentalGroup_compl_of_infty_mem` (`OnePoint ℂ ∖ T`, `∞ ∈ T`,
  loops in the sense of `Complex.IsLoopAroundAt`, standard coordinates `Complex.sphereCoord`);
  `FundamentalGroup.IsLoopAround.sub` (translation of the coordinate).
- **`FibreBundle.lean`** (C18). Local triviality = `∀ b, ∃ e : Bundle.Trivialization F p, b ∈ e.baseSet`.
  `Bundle.exists_lift_square` (lift `H : I × I → B` extending a lift on `{0} × I ∪ I × {0}`),
  `Bundle.exists_path_lift`, `Bundle.range_fundamentalGroup_map_fibre_eq_ker` (exactness at
  `π₁(E)`), `Bundle.fundamentalGroup_map_surjective` (fibre path-connected),
  `ContinuousMap.homotopic_sides_square`. Method: the property "every lift on two sides of a
  rectangle extends" holds on small rectangles (chart + retraction `(x, y) ↦ (x - m, y - m)`,
  `m = min (x - a) (y - c)`) and passes from two halves to the whole in both directions, so it
  holds for sides `≤ 2ᵏ δ` by induction (`δ` a Lebesgue number). No grid indices.
- **`SurfaceBranchedCovering.lean`** (C17 genus `g`, **interface only**).
  `Complex.BranchedCoveringOfSphere` (covering of degree `d` off a finite `B ⊆ OnePoint ℂ`, chart
  `φ_q : W_q ≃ₜ D(0, r_q)` with `sphereCoord (p q) ∘ p = φ_q ^ e_q` at each `q` over `B`),
  `Complex.surfaceRelator g n` (same word as xiii212's `surfaceWord`), and
  `Complex.BranchedCoveringPresentationStatement`: for `Y` compact T2 connected and `P ⊆ p⁻¹(B)`,
  `∃ g, 2g + 2d = 2 + ∑ (e_q - 1)` and `⟨aᵢ, bᵢ, cⱼ | ∏[aᵢ,bᵢ]∏cⱼ⟩ ≅ π₁(Y ∖ P)` with `cⱼ` loops
  around the punctures in their charts.

## Left, and the plan for genus `g` (next rounds)

1. **Prove `BranchedCoveringPresentationStatement`.** Plan: put `∞ ∈ B`; cut `ℙ¹` along the
   polygonal arc through `b₀, …, b_m` (the ordered generators of this round give the monodromy
   `τᵢ` around `bᵢ` with `τ₀ ⋯ τ_m = 1`); over the complement the covering is trivial (simply
   connected, `IsCoveringMap.existsUnique_continuousMap_lifts`), so `Y` = `d` closed discs glued
   along edges by the `τᵢ`. Compute `π₁(Y ∖ P)` by van Kampen (open discs + a neighbourhood of
   the graph `p⁻¹(arc)`), as a presentation whose relators are the face words; then normalize
   *on presentations* (Tietze moves mirroring cut-and-paste: cancel `xx⁻¹`, merge faces along a
   spanning tree of the dual graph, bring handles together, collect boundary letters), keeping
   track of the classes of the puncture loops. Euler characteristic bookkeeping gives
   `2 - 2g = 2d - ∑ (e_q - 1)`. Avoid building homeomorphisms between polygon quotients: only
   the group is needed. Expect thousands of lines; split into files `SurfaceSchema*`,
   `SurfaceCut*` (pattern `Surface*` is ours).
2. **Bridge to `X(ℂ)`**: a finite morphism `X → ℙ¹` of a smooth projective connected curve over
   `ℂ` makes `X(ℂ)` a `BranchedCoveringOfSphere` (finite étale off `B` ⇒ covering of `ℂ`-points,
   xii51/xii4; local normal form `z ↦ zᵉ` at a ramified point, analytic), with `e_q` the algebraic
   ramification indices; and `Scheme.Hom.genus f = g` needs the algebraic Riemann–Hurwitz
   (`χ(𝒪_X) = d χ(𝒪_{ℙ¹}) - ½ ∑ (e_q - 1)`, char 0). This must live in an SGA1 file (Foundations
   cannot import SGA1); needs a registry pattern for cx-top or another owner (coordinator).
3. `ℙ¹(ℂ) ∖ T` with `∞ ∉ T`: no Möbius map needed. Van Kampen with `U = Y ∖ {∞}` (`≅ ℂ ∖ S`,
   ordered theorem) and `V = {∞} ∪ {|z| > R}` (`≅ D(0, 1/R)` by `z ↦ 1/z`, simply connected;
   OnePoint API: `OnePoint.isOpen_iff_of_mem`, `continuousAt_infty'`, `tendsto_coe_infty`,
   `tendsto_inv₀_cobounded`, `tendsto_inv₀_nhdsNE_zero`, `Metric.cobounded_eq_cocompact`).
   `U ∩ V ≅ D(0, 1/R) ∖ {0}`, whose `π₁` is generated by the circle (`IsLoopAround.existsUnique_hom`).
   Take the base point on the circle `c` of the loop around `∞` (`(∏ bᵢ)⁻¹ = δ c δ⁻¹`, choose
   `max |s| < R < 1/r`) and conjugate the basis by `δ`; then homs from `π₁(Y)` are homs from
   `π₁(U)` killing `∏ bᵢ`, i.e. `π₁(Y) = ⟨x₁, …, xₙ | x₁ ⋯ xₙ⟩`.
4. C18 left exactness (`π₂(B) → π₁(F) → π₁(E)`, e.g. injectivity when `π₂(B) = 0`): same bisection
   for boxes, "given on the three faces at a corner", retraction `z ↦ z - m(1,1,1)`.

## Notes

- Traps met: `∀ {H : Type} [Group H]` in a `def` triggers implicit lambdas (`IsFreeFamily.mulEquiv h e`
  got "typeclass stuck"); make the binder explicit. `open unitInterval` makes `σ` a token and
  `open FundamentalGroupoid` makes `π` ambiguous. `rw [j_lift]` needs the embedding argument
  (`j_lift hj hjr`) since `j` is not determined by the pattern.
- Dedup for the coordinator: `SurfaceGenusZero.lean`'s private `existsUnique_lift_mulEquiv` and my
  private `IsFreeFamily.mulEquiv` are the same fact; `SurfaceGenusZero.lean:560` docstring could now
  point to the ordered version (I did not edit it: xii51's `RiemannCurvesPuncturedPlaneGroup`
  imports it).
