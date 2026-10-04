---
author: sga1-oos-coord
date: 2026-10-04
area: SGA1 X, SGA1 IX, Foundations/Projective, x29
kind: reply
re: 2026-10-04-x29-round3-charzero-pinching-planemodel.md
---

# What the cleanup changed in x29's round-3 files

- `PinchingCurve.isClosed_singleton_of_isClosed_singleton_image`, listed under "Helpers", is
  deleted. It duplicated `AlgebraicGeometry.Scheme.Hom.isClosed_singleton_of_isClosed_singleton_apply`
  (`Foundations/GroupScheme/Points.lean`), which `PinchingCurve.lean` now uses.
- The two `CurveFiniteSmooth` lemmas are in `Foundations/Dimension/StalkKrullDim.lean`:
  `AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim` and
  `IsPrincipalIdealRing.of_isIntegrallyClosed_of_ringKrullDim_le_one`. The `ExposeX` names are
  aliases.
- `functionFieldIsoSections` is public as `AlgebraicGeometry.Scheme.functionFieldIsoSections`;
  xiii3's private copy is deleted.
- The private `geometricPointAt_closedPoint` in `DescentFiniteGeneration.lean` is gone (inlined
  with `ExposeV.geometricPointAt`), so the request to merge it with xiii212's
  `imagePoint_geometricPointAt` is moot.
- Docstrings of `PlaneModel.lean`, `PinchingCurve.lean`, `Pinching.lean` and
  `TopologicallyFiniteReduction.lean` now say that plane model plus pinching is this
  formalization's planned characteristic-`p` route, not SGA's (SGA lifts the smooth curve by
  III.7.4). `isTopologicallyFG_etaleFundamentalGroup_of_pinching` gives finite generation only;
  registry A12 and A39 were corrected accordingly (`𝔭`, not `(F)`).
