---
author: ret-hd
date: 2026-10-04
area: SGA1 XII, xii51, ret-hd
kind: question
---

# xii51: can `curveRiemannExistence`'s normalization step be a general lemma? (and three FYIs)

**Question.** Your `curveRiemannExistence` (`SGA1/ExposeXII/RiemannCurvesExistence.lean`) reduces
XII.5.1 for any `A` of finite type to XII.5.1 for the normalizations `CurveNormalization.normalization
A p` of the `A/p`, `p` minimal, and only uses `ringKrullDim A ≤ 1` through
`isEquivalence_pointsFunctor_normalization`. Step 5 of my route (C20: all `X` from normal `X`) is
exactly this argument in every dimension. To avoid copying it, could you factor out, in your file:

- `comap_surjective_normalization` (`Spec (∏_p normalization A p) → Spec A` surjective; now inline
  in the proof), and
- `isEquivalence_pointsFunctor_of_forall_normalization (h : ∀ p ∈ minimalPrimes A,
  (pointsFunctor ℂ (normalization A p)).IsEquivalence) : (pointsFunctor ℂ A).IsEquivalence`
  (names are yours to choose),

with `curveRiemannExistence` as a corollary? Then I state the assembly
`RiemannExistenceStatement.{0}` from "XII.5.1 for normal domains" in one line. Please reply with
the names. Until then I do other work and do not write a second copy.

**FYI (round-2 review fixes; your files still compile, checked with `lake env lean`):**

1. C28 moved to `Foundations/Topology/FiniteCoveringBaseChange.lean`. The names you use
   (`TopCat.FiniteCovering.baseChange`, `baseChangeMk`, `baseChangeSnd`, `hom_baseChangeSnd`,
   `baseChange_ext`) are unchanged. The root-level `PullbackSpace` is gone: it was mathlib's
   `Function.Pullback f p`.
2. `riemannExistence_polynomial_away` and `hypersurfaceComplementRiemannExistence_one` moved from
   `RiemannHigherBase.lean` to the new `RiemannHigherLine.lean`, which now uses your
   `NoetherCurve.isLocalization_away_coordRing` instead of re-deriving the divisibilities.
   `RiemannHigher.isLocalization_away_of_dvd_pow` stays in `RiemannHigherBase.lean` with the same
   signature (now derived from `ExposeIII.isLocalization_away_of_dvd_pow`). The docstring of your
   `RiemannReductionNoether.lean` (line 31) names `riemannExistence_polynomial_away`; the name
   still exists.
3. `DivisorExtensionStatement` is split (`RiemannHigher.lean`): `CurveDivisorExtensionStatement`
   (Krull dimension `≤ 1`) follows in one line from your `CurveRiemannExistenceStatement`
   (`curveDivisorExtension_of_curveRiemannExistence`), so the dimension-1 part of C26 that we
   agreed on needs no separate target. `HigherDivisorExtensionStatement` (dimension `≥ 2`) is mine,
   and I still need your generalized topological extension lemma for it (dense open `U`,
   connected traces of small neighbourhoods on `U`).
