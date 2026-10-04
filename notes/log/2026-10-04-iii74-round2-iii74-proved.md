---
author: iii74
date: 2026-10-04
area: SGA1 III, Foundations/Projective, x29, xiii212, sga1-oos-coord
kind: handoff
---

# iii74 round 2: SGA 1 III.7.4 is proved

`SGA.SGA1.ExposeIII.smoothProperCurveLiftStatement : SmoothProperCurveLiftStatement` (statement
unchanged, `lean/SGA/SGA1/ExposeIII/Schemes.lean`; proof in
`lean/SGA/SGA1/ExposeIII/CurveLiftCurve.lean`). `#print axioms` gives propext, Classical.choice
and Quot.sound only. No sorry, admit, axiom, native_decide, implemented_by or maxHeartbeats. Every
touched module builds with `lake build`. A clash check passes: one scratch file imports the
`ExposeIII` barrel, every built `Foundations/Projective` and `Foundations/Formal` module and
`CurveLiftCurve`.

This round had two agents. The first fixed the reviewer's points (docstrings, long lines, `erw`)
and wrote `CurveLiftSmooth.lean` and `CurveLiftAssembly.lean`. I wrote the rest. The coordinator's
wrap-up note (`2026-10-04-sga1-oos-coord-wave2-wrap-up.md`) arrived just after III.7.4 closed, so I
stopped there.

## What is new this round

- `SGA1/ExposeIII/CurveLiftSmooth.lean` (first agent): `CurveLift.smoothOfRelativeDimension_of_isPullback`.
  It says: let `f : Y ⟶ Spec R` be flat, universally closed and locally of finite presentation
  over a local `R`, and let its closed fibre be smooth of relative dimension `n`. Then `f` is
  smooth of relative dimension `n`. Uses Stacks 00TF at the closed fibre, then specialization,
  then the fibre dimension.
- `SGA1/ExposeIII/CurveLiftAssembly.lean` (first agent): `CurveLift.exists_lift_of_base` gives
  III.7.4 for curves that come with level-0 data `Base` whose chart maps are finite and flat.
  Also `CurveLift.flat_projToSpec` and `CurveLift.isProper_projToSpec` (for `ℙ(σ; R)`).
- `Foundations/Projective/CurveProjectiveChart.lean`: the standard charts of `ℙ¹_R`.
  - `ProjectiveSpace.lineCoord₀` (`= x₁/x₀`, a `Proj.fracSection`), `lineCoord_mul`,
    `basicOpen_lineCoord₀`;
  - `bijective_eval₂Hom_lineCoord₀`: `R[t] ≅ Γ(D₊(x₀))`;
  - for `g : Y ⟶ ℙ¹_R` finite (resp. flat and affine), `R[t] → Γ(g⁻¹D₊(x₀))`, `t ↦ g^*(x₁/x₀)`,
    is finite (resp. flat): `finite_eval₂Hom_app_lineCoord₀`, `flat_eval₂Hom_app_lineCoord₀`.
  - Each of these has a `₁` version.
- `SGA1/ExposeIII/CurveLiftBase.lean`:
  - `CurveLift.baseOfHom`: the level-0 data of a finite `g : X₀ ⟶ ℙ¹_κ`, with charts `g⁻¹D₊(xᵢ)`
    and coordinates `τᵈ, σᵈ`. The exponent `d` comes from `CurveLift.exists_pow_H1` (Čech `H¹`
    of `g^*𝒪(2d)` vanishes, via `AmpleLift.exists_forall_eq_add_pow_mul`).
  - `chartHom_baseOfHom_zero/one`: the chart maps are finite and flat. This uses
    `CurveLift.finite_expand` and `flat_expand`: `t ↦ tᵈ` is finite and flat on `k[t]`.
  - `CurveLift.exists_lift_of_finite_flat`: III.7.4 for any smooth `X₀` of relative dimension `n`
    that has a finite flat `X₀ ⟶ ℙ¹_κ`.
  - `smoothProperCurveLiftStatement_of_smoothProperCurveFiniteFlatStatement`.
  - Algebra helpers: `flat_of_injective_of_isDedekindDomain` and
    `exists_finset_span_pow_mul_eq_top`.
- `SGA1/ExposeIII/CurveLiftCurve.lean`:
  - `AlgebraicGeometry.smoothProperCurveFiniteFlatStatement`: a smooth proper curve over a field
    (not necessarily connected) has a finite flat `X ⟶ ℙ¹_k` over `k`. The statement is in
    `Foundations/Projective/CurveProjective.lean`. The proof is in an SGA 1 file because it uses
    SGA 1 II/X/XIII lemmas, and Foundations cannot import SGA 1.
  - `CurveLift.exists_finite_flat_of_isIntegral` handles the integral case:
    1. `exists_transcendental`: an element `τ ∈ K(X)` transcendental over `k`; otherwise the
       sections over an affine open would form a field, of dimension 0.
    2. `(1 : τ) : Spec K(X) ⟶ ℙ¹` via `genericChartData`, extended by x29's
       `ExposeX.CurvePlaneModel.exists_hom_of_valuationRing`. The stalks are valuation rings:
       regular of dimension ≤ 1 (`valuationRing_stalk`).
    3. The generic point maps to a non-closed point (`not_isClosed_genericChartData_toProj`).
       So the fibres are finite (`finite_preimage_singleton_of_not_isClosed`), and the morphism
       is finite by `IsFinite.of_isProper_of_locallyQuasiFinite`.
    4. Flatness on each chart: `Γ(D₊(xᵢ)) → Γ(g⁻¹D₊(xᵢ))` is injective into a domain, and
       `k[t]` is a PID.
  - `CurveLift.exists_finite_flat` glues the integral case over `ExposeX.componentOpens` with
    `Scheme.Cover.glueMorphisms`.
  - `SGA.SGA1.ExposeIII.smoothProperCurveLiftStatement`.

## What was hard, what was easy

- The ℙ¹ side was cheap once I used `Proj.fracSection`: the product and basic-open lemmas
  already exist in `Projective/TwistingSheaf.lean`.
- `algebraize` on an endomorphism `R →+* R` clashes with `Algebra.id`. Fix: go through
  `Polynomial k →+* MvPolynomial σ k`. See `strategy.md`.
- Proving that the generic point maps to a non-closed point went by points through
  `TwoChartData.ι_toProj_zero` and `Proj.awayι`. The image is the prime `⊥` of
  `k[x₀,x₁]_(x₀) ≅ k[t]`, which is not maximal.
- I did not need the full `RationalMap` API. `exists_hom_of_valuationRing` was enough.

## Dependencies on other streams' files (read-only imports)

- `SGA1/ExposeX/CurveFinitePlaneModel.lean` (x29, uncommitted wave-2 file):
  `CurvePlaneModel.exists_hom_of_valuationRing`. **x29: please keep this name and signature.**
- Committed wave-1 or earlier files:
  - `ExposeX/ConstantFamily.lean`: `componentOpens`, `locallyConnectedSpace_of_isLocallyNoetherian`;
  - `ExposeX/NormalCompleteLocalBase.lean`: `isIntegral_and_isNormalScheme_of_smooth`;
  - `ExposeXIII/DesingularizationCurvesStrong.lean`: `isClosed_singleton_of_ne_genericPoint`;
  - `ExposeXI/RationalVarieties.lean`: `fromSpecStalk_comp_eq_SpecMap`;
  - `ExposeII/Field.lean`;
  - `Foundations/Desingularization.lean`.

## For consumers (x29, xiii212)

`SGA.SGA1.ExposeIII.smoothProperCurveLiftStatement` is available. Import
`SGA.SGA1.ExposeIII.CurveLiftCurve`. It lifts every smooth proper curve over the residue field of
a complete noetherian local ring, for example from `k` to `W(k)`, to a smooth proper curve.

## Left (rest of row A43, not needed for III.7.4)

- Coherent Grothendieck existence on `ℙⁿ`, the projective case of `GrothendieckExistenceStatement`.
  See `hard-parts.md` §1 for why it is hard.
- EGA III 5.4.5 with an ample line bundle; III.5.9; III.7.1–III.7.3.
- Optional cleanups:
  - rename `AmpleLift.Two` / `TwoChartData` to a neutral namespace. Consumers exist only in my
    files, so this needs aliases for safety;
  - make `exists_smooth_lift_of_sup_eq_top` (`TwoChartLift.lean`) a corollary of my
    `exists_smooth_lift_of_sup_eq_top_preimage` (coordinator file);
  - derive the finite étale existence results from the finite flat ones in
    `FormalAlgebraization.lean`.

## Coordinator requests

- Barrels:
  - add to `SGA/Foundations.lean`:
    - `SGA.Foundations.Cohomology.FormalAlgebraization`
    - `SGA.Foundations.Formal.AmpleLift`
    - `SGA.Foundations.Formal.AmpleLiftProj`
    - `SGA.Foundations.Projective.CurveProjective`
    - `SGA.Foundations.Projective.CurveProjectiveChart`
  - add to `SGA/SGA1/ExposeIII.lean`: `CurveLiftCharts`, `CurveLiftStage`, `CurveLiftSystem`,
    `CurveLiftFinite`, `CurveLiftFlat`, `CurveLiftSmooth`, `CurveLiftAssembly`,
    `CurveLiftBase` and `CurveLiftCurve`. Note: `CurveLiftCurve` imports Exposé X, XI and XIII
    modules. No module imports the `ExposeIII` barrel, so this creates no cycle.
- `lean/SGA/SGA1/ExposeIII/Schemes.lean` is not my file. The docstring of
  `SmoothProperCurveLiftStatement` still lists what is "missing". Replace that list with "proved
  as `smoothProperCurveLiftStatement` (`CurveLiftCurve.lean`), by a route through a finite flat
  morphism to `ℙ¹`".
- Update the III.7.4 row in `Foundations/README.md` and `docs/` to proved.
