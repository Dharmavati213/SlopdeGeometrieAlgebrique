---
author: x29
date: 2026-10-04
area: SGA1 X, SGA1 IX, Foundations/Projective, sga1-oos-coord, xiii3, xiii212
kind: handoff
---

# X.2.9 round 3: X.2.9 in characteristic 0 (`#k ≤ 𝔠`), pinching for curves, plane-model infrastructure

Every module listed below builds with `lake build`, one at a time. None contains sorry, and
`#print axioms` shows only propext, Classical.choice and Quot.sound. I edited only my own
untracked files; none of them is imported by another stream's file. Nothing went into a barrel.
This was the last round of stream x29 in this wave.

## Done

- **Reviewer fixes from round 2**:
  - `Pinching.lean`:
    - the module title, `pinchFunctor` and the main theorem now say "IX.5.4, consequence";
    - the main theorem's docstring lists SGA's hypotheses next to the replacement hypotheses;
    - `eq_of_comp_eq_id` cites mathlib's `ext_of_apply_closedPoint_eq`;
    - the general helpers are private or documented.
  - `DescentFiniteGeneration.lean`:
    - the family form states its deviation from SGA;
    - the module doc points to Pinching for IX.5.4.
  - "(universe 0)" added in `TopologicallyFiniteReduction.lean` and in hard-parts.md.
  - Registry: A30 now says "of no larger dimension"; A12 says "consequence".
- **X.2.9 and X.2.12 in characteristic 0 for `#k ≤ 𝔠`, every proper connected `X`, universe 0,
  unconditional.** File `SGA1/ExposeX/TopologicallyFiniteCharZero.lean`, rewritten:
  - `isTopologicallyFG_etaleFundamentalGroup_complex`;
  - `isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum`;
  - `finite_principalH1_complex`, `finite_principalH1_of_mk_le_continuum`.
  - These come from xii52's `ExposeXII.semilocallySimplyConnectedStatement`.
  - The round-2 theorems `…_of_isNormalScheme_of_mk_le_continuum` and `…_of_hyperplane` are
    deleted: they were special cases. Nothing referenced them.
- **Pinching checked for curves (row A12).**
  - `SGA1/ExposeIX/PinchingCurve.lean`:
    `ExposeIX.isTopologicallyFG_etaleFundamentalGroup_of_isFinite_of_isIso_morphismRestrict`.
    Hypotheses: `k = k̄`, `D` of finite type over `k`, `g : C ⟶ D` finite and surjective, `C`
    connected, `g` an isomorphism over an open `U` whose complement is a finite set of closed
    points. Conclusion: π₁(D) t.f.g. ⇒ π₁(C) t.f.g.
  - Helpers in the same file:
    - `PinchingCurve.mem_range_diagonal_of_mono`: over the locus where `g` is a monomorphism,
      `C ×_D C` is the diagonal;
    - `PinchingCurve.isClosed_singleton_of_isClosed_singleton_image`.
  - `SGA1/ExposeIX/PinchingCurveNormalization.lean`:
    `isTopologicallyFG_etaleFundamentalGroup_normalization_of_isTopologicallyFG`, the same for the
    normalization of an integral curve. It uses xiii3's `exists_isAffineOpen_isIntegrallyClosed`,
    `isIso_fromNormalization_restrict` and `ExposeXIII.isClosed_singleton_of_ne_genericPoint`.
- **X.1.8 in both directions**: `isTopologicallyFG_etaleFundamentalGroup_pullback_iff` in
  `SGA1/ExposeX/TopologicallyFiniteBaseChange.lean`. The map π₁(X_K) → π₁(X) is a continuous
  bijection of compact Hausdorff groups. This is what descends the curve case to a countable field.
- **Plane-model infrastructure (rows A29 and A39, both new or started).**
  - `Foundations/Projective/PlaneModelField.lean`, `Field.exists_planeModel_of_trdeg_eq_one`.
    For `k` perfect and `K` finitely generated of trdeg 1: `K = k(x, y)` with `x`
    transcendental, and `ker(k[s][t] → K) = (f)` with `f = minpoly_{k[s]} y` monic irreducible.
  - `Foundations/Projective/GradedQuotient.lean`, the grading of `A ⧸ I` (not in mathlib):
    instance `HomogeneousIdeal.gradedAlgebra`, plus `coe_decompose_mk` and
    `quotientGradedRingHom`.
  - `Foundations/Projective/PlaneModel.lean`:
    - `AlgebraicGeometry.planeCurve k x y = Proj (k[X₀,X₁,X₂] ⧸ 𝔭)`, where `𝔭 = PlaneCurve.ideal`
      is the homogeneous kernel of `Xᵢ ↦ (1, x, y)ᵢ T`. This avoids homogenization and any
      irreducibility argument: `𝔭` is prime because it is a kernel.
    - Proper structure map `PlaneCurve.toSpec` (`isProper_toSpec`).
    - Injective chart `chartHom : Γ(D₊(X₀)) → K` with image `k[x, y]` (`range_chartAlgHom`).
    - Generic point `genericPt` (`isGenericPoint_genericPt`), so `IrreducibleSpace`; it lies in
      `D₊(X₀)`.
    - `K`-point `kPoint` over `k` (`kPoint_toSpec`) mapping to the generic point
      (`kPoint_apply`).

## What was hard

- **`obtain ⟨P, hP, rfl⟩ := ha` breaks later rewrites** when `ha` is a membership in
  `quotientGrading` (`Submodule.map`). After destructuring, `Away.mk … a ha` carries a proof whose
  type is the unfolded `∃`, and `rw` reports "motive is not type correct". Fix: copy first,
  `have ha' : ∃ P ∈ _, _ = a := ha; obtain ⟨P, hP, hPa⟩ := ha'`. State API lemmas with an
  equation `hPa : mk P = a` rather than with `a := mk P`.
- **`DirectSum.toAlgebra` has no `_of` simp lemma.** Unfolding it leaves the `hone`/`hmul` proofs
  as metavariables. Fix: name the component maps and their two proofs (private `auxMap`,
  `auxMap_one`, `auxMap_mul`), then use `toSemiring_of (A := fun i ↦ ↥(𝒜 i))` with them.
- **`rintro _ (rfl | rfl)` on `z ∈ {x, y}`** substitutes away the variable `x` itself. Use
  `rintro z (hz | hz)` and rewrite.
- **`Proj.toSpecBase` is `toSpecZero ≫ Spec.map _`.** `infer_instance` does not find `IsProper`
  for the composite, and `cancel_right_of_respectsIso` does not rewrite through a non-reducible
  `def planeCurve`. Fix: make `planeCurve` an `abbrev`, then
  `rw [MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)]`.
- **`ProjectiveSpectrum.le_iff_mem_closure` takes `𝒜` explicitly.** For points of `Proj`, give it
  explicitly, and give `bot_le (a := p.asHomogeneousIdeal)`.

## Next (in order of value)

1. **The finite birational morphism `C ⟶ planeCurve k x y`.** `C` is normal, integral and proper
   over `k = k̄` of dimension 1; `x, y` come from `Field.exists_planeModel_of_trdeg_eq_one` for
   `K(C)`, with the `functionFieldMap` algebra. Suggested file:
   `SGA1/ExposeX/CurveFinitePlaneModel.lean` (pattern `CurveFinite*`). Steps:
   - (a) `trdeg k K(C) = 1` from `topologicalKrullDim C = 1`: use
     `IsAffineOpen.topologicalKrullDimAt_eq_ringKrullDim_stalk_add_trdeg` at the generic point,
     then `topologicalKrullDimAt_eq_of_isIntegral`.
   - (b) the morphism `g`: `Scheme.RationalMap.ofFunctionField` applied to `kPoint`, then
     `ExposeX.mem_domain_of_valuationRing` at every point. The stalks are valuation rings by
     `isPrincipalIdealRing_of_isIntegrallyClosed_of_ringKrullDim_le_one` (normal and
     dimension ≤ 1); `RationalMap.toPartialMap` then has domain `⊤`.
   - (c) `g` maps the generic point to `genericPt` (`kPoint_apply`), hence is surjective (closed
     image).
   - (d) `g` is finite: proper plus finite fibres; the fibres are proper closed subsets of `C`.
   - (e) `g` is an iso over `U = D(h) ⊆ D₊(X₀)`:
     - `h ≠ 0` lies in the conductor of `k[x, y]`, by xiii3's
       `exists_ne_zero_forall_isIntegral_mul_mem` and Noether A30;
     - on `g⁻¹ U`, `Γ` is finite over `k[x, y]_h`, sits inside `K`, and `k[x, y]_h` is
       integrally closed;
     - this needs the compatibility `chartHom = (Γ(D₊X₀) → K(D) → K(C))`.
   - (f) `Uᶜ` is finite and consists of closed points (xiii3's `isClosed_singleton_of_ne_genericPoint`
     and `NoetherianSpace.finite_of_isClosed_of_forall_isClosed_singleton`).
   - Then `isTopologicallyFG_etaleFundamentalGroup_of_isFinite_of_isIso_morphismRestrict` gives:
     **curve case ⇐ plane curves**.
2. **Char 0, `#k > 𝔠`, curve case.** Descend `planeCurve k x y` to a countable algebraically
   closed `k₀` containing the coefficients of generators of `𝔭`, using `ProjBaseChange`. Then
   apply `…_pullback_iff` and the `#k ≤ 𝔠` theorem.
3. **Char `p`.**
   - `𝔭 = (F)`: a height-one homogeneous prime of a UFD is principal.
   - Lift `F` to `W(k₀)`. Check flatness, geometrically reduced fibres, geometrically connected
     fibres, and the closed immersion into `ℙ(Fin 3; Spec W)`.
   - Then apply `exists_continuous_surjective_specialization_of_isClosedImmersion`.
4. **hH (X.2.10)** in every characteristic: the Bertini field lemma, then the generic hyperplane.
   No usable proof was found yet. The critic's "major" objection still applies: hH in existence
   form is what the generic-hyperplane route proves.

## For the coordinator (sga1-oos-coord)

- **Barrel entries.**
  - `SGA/SGA1/ExposeIX.lean`: `Pinching`, `PinchingCurve`, `PinchingCurveNormalization`,
    `DescentFiniteGeneration`.
  - `SGA/SGA1/ExposeX.lean`: `TopologicallyFinite`, `TopologicallyFiniteComplex`,
    `TopologicallyFiniteReduction`, `TopologicallyFiniteCharZero`,
    `TopologicallyFiniteBaseChange`, `CurveFiniteSmooth`.
  - `SGA/Foundations.lean`: `Pro.TopologicallyFG`, `Fields.ComplexEmbedding`,
    `CommAlg.NoetherFiniteness`, `NormalizationFinite`, `Projective.GradedQuotient`,
    `Projective.PlaneModelField`, `Projective.PlaneModel`.
- **Docs.** In `Foundations/README.md`, `docs/formalization.md:40` and the
  `ExposeX/Semicontinuity.lean` module doc (lines 20-22, 46-47; barrel `SGA1/ExposeX.lean`
  line 37):
  - X.2.9 and X.2.12 are proved in characteristic 0 for `#k ≤ 𝔠`, universe 0, for every proper
    `X`;
  - they do not need XII.5.1;
  - what is left is characteristic `p`, `#k > 𝔠`, universes and X.2.10.
- **Stale docstring.** The module doc of `ExposeIX/FundamentalGroupDescent.lean` (line 34) says
  IX.5.4 is not formalized. Its consequence now is (`ExposeIX/Pinching.lean`).
- **Moves.**
  - `CurveFiniteSmooth.lean`'s `isPrincipalIdealRing_of_isIntegrallyClosed_of_ringKrullDim_le_one`
    and `ringKrullDim_stalk_le_topologicalKrullDim` are general facts. Move them to Foundations;
    xiii3 imports them.
  - Make `functionFieldIsoSections` in `Foundations/NormalizationFinite.lean` public, so xiii3 can
    drop its private copy. I did not edit the file because xiii3's `Desingularization` imports it.
  - My private `geometricPointAt_closedPoint` in `DescentFiniteGeneration.lean` duplicates
    xiii212's `ExposeXIII.imagePoint_geometricPointAt`. Move that lemma next to
    `ExposeV.geometricPointAt` and use it in both places.
