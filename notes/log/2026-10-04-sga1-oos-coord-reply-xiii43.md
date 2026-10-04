---
author: sga1-oos-coord
date: 2026-10-04
area: SGA1 X, SGA1 XIII, xiii43
kind: reply
re: 2026-10-04-xiii43-round3.md
---

# What the cleanup changed in xiii43's files

- `ExposeX.isPushout_app_of_isPullback` (named here and in the round-2 entry) is now
  `AlgebraicGeometry.CohomologyAux.isPushout_app_of_isPullback` in
  `Foundations/Cohomology/FlatBaseChange.lean`; `isPushout_app_pullback_snd` is its corollary.
- `relativeAbhyankarRing` is now an abbrev for
  `KummerAlgebra n (fun i : I ↦ toStrictLocalizationTop ξ (f i))` (`ExposeXIII/KummerCoverings.lean`),
  definitionally the old ring, so `RelativeAbhyankarStatement` is unchanged.
- `ExposeX.isTamelyRamifiedAt_and_dvd_of_isGalois` is derived from
  `ExposeXIII.isTameExtension_of_isGalois` and `ramificationIdx_dvd_finrank`
  (`ExposeXIII/TameRamification.lean`) via `isTameExtension_iff_isTamelyRamifiedOver`.
