---
author: xii51
date: 2026-10-03
area: SGA1 XII, sga1-oos-coord, x29, xii4, xiii212, cx-top
kind: handoff
---

# XII.5.1 round 1: Ψ fully faithful, π̂₁ ↠ π₁, RET for 𝔸ⁿ and 𝔾_m, C8 statements

All seven new files build (`lake build SGA.SGA1.ExposeXII.<File>`), sorry-free, axioms clean, no
`maxHeartbeats`. None is in a barrel yet (coordinator). All under `lean/SGA/SGA1/ExposeXII/`:

- `FundamentalGroupQuotient.lean`: the easy half of XII.5.2 (row C7):
  `surjective_autWhiskerLeft_schemePointsFunctor` (connected `X`, `X(ℂ)` LPC and SLSC; LPC always
  holds by xii52's `SchemePoints.locallyPathConnectedSpace`), `…_of_smooth`, affine
  `surjective_autWhiskerLeft_pointsFunctor[_of_smooth]` (`A : Type`), and
  `TopCat.FiniteCovering.isConnected_iff_connectedSpace`. x29 imports this file, so don't rename.
- `RiemannFull.lean`: step 1) of XII.5.1 for every `X`: `instance : (schemePointsFunctor ℂ X).Full`,
  via `SchemePoints.exists_hom_map_eq`. This is SGA's general form: for `Y' → S` finite étale and
  any `Y₁ → S`, continuous maps `Y₁(ℂ) → Y'(ℂ)` over `S(ℂ)` come from `S`-morphisms. Also
  `SchemePoints.exists_isClopen_preimage_pt_eq` (a clopen subset of `Z(ℂ)` is `W(ℂ)` for a clopen `W`)
  and `SchemePoints.isIso_of_bijective_map` (étale, qc, qs, bijective on `ℂ`-points ⇒ iso).
- `RiemannLocalAffine.lean`: the affine form vs the scheme form. `pointsFunctorIsoSpec` (via my
  own `specCoveringFunctor`, isomorphic to `ExposeV.specFunctor`, and
  `TopCat.FiniteCovering.mapHomeomorph`), the affine `Full` instance,
  `isEquivalence_pointsFunctor_iff`, `riemannExistence_of_schemeRiemannExistence` (scheme ⇒ affine,
  `.{0}`).
- `RiemannReduction.lean`: `isEquivalence_schemePointsFunctor_iff_injective` (RET ⇔ π̂₁ ↠ π₁ is
  injective, V.6.10) and `isEquivalence_{scheme,}pointsFunctor_of_forall_isConnected` (RET from its
  connected case, `Ψ` being exact).
- `RiemannSimplyConnected.lean`: RET when `X(ℂ)` is simply connected (scheme and affine),
  `riemannExistence_mvPolynomial` (𝔸ⁿ), `subsingleton_aut_etaleFiber_mvPolynomial` (π₁(𝔸ⁿ_ℂ) = 1)
  and `subsingleton_etaleFundamentalGroup_of_simplyConnectedSpace`.
- `RiemannKummer.lean`: **RET for 𝔾_m**, `riemannExistence_laurentPolynomial`. cx-top's
  `Complex.exists_homeomorph_powRestrict` (C3) shows that every connected cover is Kummer, and the
  Kummer algebras are xiii212's `ExposeXI.KummerAlgebra` with `etale_kummer`. **For xiii212:** I no
  longer need A14 for the Kummer case of RET.
- `RiemannCurves.lean` (C8 interface, published): `CurveRiemannExistenceStatement`,
  `CompactRiemannSurfaceMeromorphicStatement` (xii4 accepted it as their target) and
  `SeparatingFunctionStatement`.

**What was hard.** Plumbing, not mathematics (details in `strategy.md`, "Lean and mathlib
technique"):

- kernel deterministic timeouts from a homeomorphism defined with `subst` on an `Over` instance;
- `((specFunctor R).obj S).left` being `Spec S` only after heavy unfolding;
- instances for `R : CommRingCat` not firing at `CommRingCat.of A`;
- two `Over` instances on `Spec S` (`specOver` vs `overOfCovering`).

The mathematics went as SGA and the critic said. The critic's fullness shortcut via V.6.9 worked
first, then the general graph-clopen proof superseded it, so I deleted the special cases.

**Not done / next (round 2), in order:**
1. C4 locality, `SchemeRiemannExistenceStatement` from RET on affine opens. Plan: glue with
   mathlib's `Scheme.Cover.RelativeGluingData` over `X.directedAffineCover`
   (`Mathlib/AlgebraicGeometry/RelativeGluing.lean`, `Cover/Directed.lean`). Pieces: (a) Ψ commutes
   with restriction to an open `U` (`Set.restrictPreimage` coverings, `pullbackHomeomorph`); (b)
   transition maps and the pullback squares from `exists_hom_map_eq` and faithfulness; (c) the glued
   `Y` is finite étale (local on the target); (d) `Ψ(Y) ≅ E` by gluing maps on the open cover of
   `X(ℂ)`; (e) RET for affine schemes `U` from `RiemannExistenceStatement.{0}`, by invariance of Ψ
   under `U ≅ Spec Γ(U)` and `isEquivalence_pointsFunctor_iff`.
2. The algebraic half of the curve case: `SeparatingFunctionStatement → RET for ℂ[t][1/f]` (critic's
   C7: symmetric functions with `exists_polynomial_of_differentiableOn`, discriminant, a bijective
   map of coverings is an iso), then C6 extension across points with a *per-object* hypothesis
   (cx-top's `Complex.not_forall_pow_eq_of_continuous`), then C9 curves (Noether normalization).
3. The universe transport `RiemannExistenceStatement.{u}` from `.{0}` (critic's fix). It is only
   needed once RET is proved.
4. Bridge `separatingFunction_of_compactRiemannSurface` (fill in the punctures of `E` as a
   mathlib manifold), once xii4's heart is near.

**For the coordinator.** These `TopCat.FiniteCovering` lemmas use only Foundations and mathlib and
should move to `Foundations/Topology/` (cx-top asked too): `exists_monodromy_eq`,
`isConnected_of_pathConnectedSpace`, `isConnected_of_connectedSpace`,
`connectedSpace_of_isConnected`, `isConnected_iff_connectedSpace` (FundamentalGroupQuotient),
`subsingleton_aut_fiber` (RiemannSimplyConnected), `mapHomeomorph*` (RiemannLocalAffine).
`AffineAnalytification.ΓSpecAlgEquiv` (`ReducedComparison.lean`) is the special case
`R = PresentedAlgebra g` of my `SchemePoints.ΓSpecAlgEquiv`.
