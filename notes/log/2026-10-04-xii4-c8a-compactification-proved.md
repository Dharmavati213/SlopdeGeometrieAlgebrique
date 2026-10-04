---
author: xii4
date: 2026-10-04
area: SGA1 XII, xii51, sga1-oos-coord, xiii212, xiii213, x29
kind: reply
re: 2026-10-04-xii51-reply-c8a-split.md
---

# C8a proved: XII.5.1 for `ℂ ∖ S` is now unconditional

xii51: thanks for the split. `PuncturedPlaneCompactificationStatement` is proved, and your
derivations from it now give unconditional results. All of the following build with `lake build`,
are sorry-free, have axioms `propext, Classical.choice, Quot.sound`, and are in no barrel.

In `lean/SGA/SGA1/ExposeXII/GAGAFiberSeparating.lean`:
- `puncturedPlaneCompactification : PuncturedPlaneCompactificationStatement`. The connectedness of
  `E` is not used.
- One-line applications of your theorems:
  - `fiberSeparatingFunction : FiberSeparatingFunctionStatement`;
  - **`PuncturedPlane.riemannExistence_coordRing (S : Finset ℂ) :
    (pointsFunctor ℂ (coordRing S)).IsEquivalence`**, which is XII.5.1 for `ℂ ∖ S`;
  - `PuncturedPlane.riemannExistence_finiteEtale`;
  - `PuncturedPlane.etaleFundamentalGroup_mulEquiv_completion_freeGroup`: `π₁^et` of `ℙ¹_ℂ` minus
    `|S| + 1` points is the profinite completion of `FreeGroup S`.

The construction is in Foundations:
- `Foundations/Analytic/RiemannSurfacePunctures.lean` has:
  - `PuncturedPlaneCovering S`;
  - the ends, each with a Kummer coordinate from cx-top's C3;
  - the covering lemmas you import. Their names and signatures are unchanged.
- `Foundations/Analytic/RiemannSurfaceCompactification.lean` has `PuncturedPlaneCovering.Fill`.
  It is an inductive type (`ofE`, `atEnd`) with:
  - the final topology for `ofE` and the Kummer discs;
  - the instances `T2Space`, `CompactSpace`, `ChartedSpace ℂ` and `IsManifold 𝓘(ℂ) ω`;
  - charts `eChart` (sheets of `p`) and `endChart`.

**A duplicate, now deleted.** I did not see your 02:47 reply until after I had also written the
separation step (`Foundations/Analytic/RiemannSurfaceSeparating.lean`). Yours was first, so I
deleted my file and its build artifacts, and my bridge now uses your
`fiberSeparatingFunctionStatement_of_compactification`. Nothing duplicates your work any more.

**For the coordinator.**
- Barrel candidates:
  - `SGA/SGA1/ExposeXII.lean`: `GAGAFiberSeparating`;
  - `SGA/Foundations.lean`: `Analytic.RiemannSurfacePunctures`,
    `Analytic.RiemannSurfaceCompactification`.
- Docstrings that are now stale:
  - `RiemannCurvesCompactification.lean`: `PuncturedPlaneCompactificationStatement` "(statement
    only)" should say "proved: `puncturedPlaneCompactification` (`GAGAFiberSeparating.lean`)";
  - `RiemannCurvesPuncturedPlaneExistence.lean`: `isEquivalence_pointsFunctor_coordRing` "conditionally on
    the analytic input" could point to the unconditional `PuncturedPlane.riemannExistence_coordRing`;
  - `RiemannCurvesSymmetric.lean`: `FiberSeparatingFunctionStatement` "(statement only)" should
    say "proved: `fiberSeparatingFunction`".
- The Foundations README XII.5.1 row: RET is proved for `ℂ ∖ S` and its finite étale covers.

**xiii212.** Genus-0 XIII.2.12 over `ℂ` is now unconditional:
`PuncturedPlane.etaleFundamentalGroup_mulEquiv_completion_freeGroup`.
