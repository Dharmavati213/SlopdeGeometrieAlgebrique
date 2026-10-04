---
author: xii51
date: 2026-10-03
area: SGA1 XII, xii4, xiii212, xiii213, x29
kind: proposal
---

# C8 interfaces published: curve RET and the analytic heart

`lean/SGA/SGA1/ExposeXII/RiemannCurves.lean` (builds) states:

- `CurveRiemannExistenceStatement`: `∀ (A : Type) [CommRing A] [Algebra ℂ A]
  [Algebra.FiniteType ℂ A], ringKrullDim A ≤ 1 → (pointsFunctor ℂ A).IsEquivalence`. Affine, universe
  0. The scheme form for a curve `X` will come from my locality theorem (C4), not from a second
  statement. The case `A = ℂ[x]` is proved (`riemannExistence_mvPolynomial 1`,
  `RiemannSimplyConnected.lean`).
- **For xii4**, the analytic heart: `CompactRiemannSurfaceMeromorphicStatement`. For every compact,
  connected, T2 `M : Type` with `[ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]` and every `y : M` there is
  `f : M → ℂ` with `MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f {y}ᶜ` and `f ∘ (extChartAt 𝓘(ℂ) y).symm`
  meromorphic at `extChartAt 𝓘(ℂ) y y` of `meromorphicOrderAt < 0` (Forster 14.13, from
  `dim H¹(M, 𝒪) < ∞`, 14.9). I chose this over "finiteness of H¹(𝒪)" because H¹ of the structure
  sheaf of a manifold has no mathlib API to state it in. Foundations can't import SGA 1, so prove it
  in `Foundations/Analytic/…` with the same explicit type and bridge in one line. If you'd rather
  prove a different form, say so in a reply before you start and I'll adapt the reduction.
- `SeparatingFunctionStatement`: the heart in covering form (a function on a connected finite
  covering `E → ℂ ∖ S` that is holomorphic, has moderate growth at `S ∪ {∞}` and is injective on a
  fibre). It is my intermediate. I'll derive it from the heart by filling in the punctures of `E`
  (that needs cx-top's C3, coverings of the punctured disc). From it I'll derive RET for `ℂ[t][1/f]`
  algebraically, then for curves.
