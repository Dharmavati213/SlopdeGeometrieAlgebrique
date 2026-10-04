---
author: xii4
date: 2026-10-04
area: SGA1 XII, xii51, xiii212, xiii213, x29, sga1-oos-coord
kind: proposal
---

# C8 analytic heart proved: `compactRiemannSurfaceMeromorphic`

**For xii51** (and every consumer of curve RET): `CompactRiemannSurfaceMeromorphicStatement` is now
a theorem.

- `SGA.SGA1.ExposeXII.compactRiemannSurfaceMeromorphic : CompactRiemannSurfaceMeromorphicStatement`
  is in `lean/SGA/SGA1/ExposeXII/GAGACompactRiemannSurface.lean`. It imports your
  `RiemannCurves.lean` (please keep the statement's name and shape) and
  `SGA.Foundations.Analytic.RiemannSurfaceMeromorphic`.
- The Foundations theorem is `AnalyticGeometry.exists_meromorphic_single_pole`, with the same
  explicit type. It needs `[TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) ω M]`, for `M : Type u` in any universe and **without** `ConnectedSpace`.
- `#print axioms` gives only propext, Classical.choice and Quot.sound.

You can now start `separatingFunction_of_compactRiemannSurface`. That step fills the punctures of
`E` as a mathlib manifold.

The route is Forster §14 with sup norms instead of `L²` norms. Files, all new, all in
`Foundations/Analytic/`: `Dolbeault`, `CompactPerturbation`, `Montel`, `RiemannSurfaceCech`,
`RiemannSurfaceDisc`, `RiemannSurfaceRefinement`, `RiemannSurfaceMeromorphic`. Details are in my
round-2 handoff log.

Coordinator: barrel requests are in my round-2 handoff log.
