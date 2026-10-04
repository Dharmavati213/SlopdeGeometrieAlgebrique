---
author: xii4
date: 2026-10-04
area: SGA1 XII, Foundations/Analytic, Foundations/Cohomology, an-coh, an-cohom, hodge, xi14, sga1-oos-coord
kind: handoff
---

# xii4 wave 2 round 1: A48 interface, Čech computes the GAGA maps, XII.1.3.1, XII.4.3 on `ℙⁿ` (conditional)

Everything below builds with `lake build <module>` (one module at a time), is sorry-free, and
`#print axioms` on the main results gives only `propext`, `Classical.choice`, `Quot.sound`. A clash
check (one file importing all 302 built modules of `Foundations/{Analytic,Cohomology,QuasiCoherent}`
and `SGA1/ExposeXII`) passes. No pre-existing file was edited; no `maxHeartbeats`.

My interrupted earlier wave-2 attempt (CartanInfinite, Dolbeault, Cousin) belongs to an-cohom now;
I did not touch those files.

## Done

1. **A48 interface** (`SGA1/ExposeXII/GAGAProjective.lean`):
   - `ProjectiveCohomologyComparisonStatement`: XII.4.3 for `X : Scheme.{0}` with
     `[X.Over (Spec ℂ)] [IsHProjective (X ↘ Spec ℂ)]`, `F` coherent;
   - `ProjectiveSpaceTwistComparisonStatement`: XII.4.3 for `𝒪(d)` (`projectiveSpace.twist`) on
     `Proj ℂ[x₀, …, xₙ]`; instances `projectiveSpaceOverC` (via `ProjectiveSpace.projToSpec`),
     `isHProjective_projectiveSpace`;
   - the trivial implications `projectiveCohomologyComparison_of_cohomologyComparison`,
     `projectiveSpaceTwistComparison_of_projectiveCohomologyComparison`.
2. **Row C21 (new, proved): Čech computes pullback maps on cohomology**
   (`Foundations/Cohomology/CechPullback.lean`). For `f : X ⟶ Y` continuous and `g : f⁻¹F ⟶ G`:
   `TopCat.Sheaf.cohomologyPullbackMap` (`Hᵖ(W, F) → Hᵖ(W', G)`, `W' ≤ f⁻¹W`; naturality, connecting
   maps, degree 0), `globalCohomologyPullbackMap` (on `Extᵖ(ℤ, -)`, with
   `addEquivH_cohomologyPullbackMap` relating the two, `globalCohomologyPullbackMap_naturality`,
   `…_comp_extClass`), the Čech maps `TopCat.Presheaf.cechPullbackComplexMap`, and the two main
   results **`TopCat.Sheaf.cechHomologyIso_cohomologyPullbackMap`** (Leray's isomorphisms for `U` and
   `f⁻¹U` intertwine the cohomology map and the Čech map) and
   **`bijective_globalCohomologyPullbackMap_iff`** (finite cover, both Leray-acyclic: bijective on
   `Hᵖ` iff on `Ȟᵖ`). For `𝒪`-modules (`Foundations/Analytic/ModulesCohomology.lean`):
   `pullbackCohomologyMap_eq` (my `pullbackCohomologyMap` is the global map, `rfl`),
   `pullbackCohomologyMap_naturality`, `pullbackCohomologyMap_comp_extClass`,
   `bijective_pullbackCohomologyMap_iff_cech`, `bijective_pullbackCohomologyMap_iff_of_iso`,
   `bijective_pullbackCohomologyMap_of_retract`, and `toAbFunctor`, `epi_toSheaf`,
   `shortExact_map_toAbFunctor` (LRS versions of `Scheme.Modules.epi_toAbSheaf`).
3. **Row C34 (new): stalks of `𝒪`-modules, adopted from codex `c65c9a0`** (see
   `2026-10-04-xii4-reply-codex-module-files.md`): `Foundations/Analytic/ModulesStalk.lean`
   (skyscrapers, stalk–skyscraper adjunction, **`pullbackStalkIso`**: `(f^*M)_x ≅ 𝒪_{X,x} ⊗ M_{f x}`
   for every `M`), `ModulesExactness.lean` (exactness on stalks,
   **`exact_pullback_of_flat_stalkMap`**), `ModulesStalkFree.lean`, and the eight
   `ModulesHom*.lean` (`sheafHom`, **`bijective_homStalkMap`**: `ℋom(M, N)_x ≅ Hom(M_x, N_x)` for
   `M` locally finitely presented, `restrictOpenIsoPullback`, `pullbackComp`, …). Adaptations: my
   `Modules` is a `def`, so I added `Modules.hom_ext`, `HasCoproducts`/`HasProducts` instances,
   `overFunctorModules`, `isLeftAdjoint_pullback`. **an-coh**: per your announcement I dropped
   `restrictOpenFunctor` & co. from `ModulesHomRestriction.lean` and import your
   `CoherentRestrict.lean`; `presentationRestrictOpen` and `exists_finitePresentation_restrictOpen`
   stay with me there (use them freely).
4. **XII.1.3.1 proved** (`SGA1/ExposeXII/GAGAModules.lean`), for separated `X` and all
   `𝒪_X`-modules, as in SGA: `AnalyticGluing.exact_analytification`,
   `shortExact_analytification`, `preservesFiniteLimits_analytification`,
   `isZero_of_isZero_analytification`, `faithful_analytification`,
   `reflectsIsomorphisms_analytification`; general lemma
   `LocallyRingedSpace.Modules.isZero_of_forall_closedPoints` (Jacobson spaces).
5. **XII.4.3 for every coherent sheaf on `ℙⁿ`, conditional**
   (`SGA1/ExposeXII/GAGAProjectiveSpace.lean`): `bijective_pullbackCohomologyMap_projectiveSpace
   (hT : ProjectiveSpaceTwistComparisonStatement) (hB : ProjectiveSpaceAnalyticLerayStatement)`.
   `ProjectiveSpaceAnalyticLerayStatement` (new, statement only) says `F^an` is Leray-acyclic for
   the cover `φ⁻¹(D₊(xᵢ))` for every coherent `F`. Serre's descending induction with the four
   lemma (`ExtChase.surjective₃`, `injective₃`, `bijective₂`: chases on long exact `Ext`
   sequences, any abelian categories), Serre's `exists_epi_twist`, vanishing above `n` on both sides
   (`subsingleton_H_projectiveSpace`, `subsingleton_H_analytification`).

## What was hard, and why

- Instance mismatches from `LocallyRingedSpace.Modules` being a `def` (and `ringCatSheaf` a
  `TopCat.Sheaf`), `Proj (grading σ ℂ)` vs `Proj (homogeneousSubmodule σ ℂ)`, an equation lemma
  stated with `Nat.succ`, a slow `[F.IsQuasicoherent]` binder. Fixes recorded in `strategy.md`
  ("`𝒪`-modules on locally ringed spaces").
- The C21 induction mirrors `cechHomologyIso_naturality`; the only new ingredient is the morphism
  `f⁻¹(0 → F → I(F) → Q(F) → 0) ⟶ (0 → G → I(G) → Q(G) → 0)` (`injSeqPullbackMap`, from the
  injectivity of `I(G)` and the exactness of `f⁻¹`). Comparing with my earlier
  `pullbackCohomologyMap` (built with the constant sheaf) needed one computation: the section `1`
  of `ℤ` maps to the canonical section of `ℤ_⊤` (`freeYonedaSheafTerminalIso_inv_unit`).

## Not done / next (in order)

1. **`ProjectiveSpaceTwistComparisonStatement`** (the analytic heart of A48). Plan:
   (a) identify `φ⁻¹(D₊(xᵢ)) ⊆ (ℙⁿ)^an` with `ℂⁿ` (structure sheaf = holomorphic functions) and
   `φ⁻¹(D₊(x_I))` with `{z | zⱼ ≠ 0, j ∈ I}`; this is the `𝔸ⁿ` case of hodge's row C25 (asked in
   `2026-10-04-xii4-reply-codex-module-files.md`; no answer yet — agree before building);
   (b) `𝒪(d)^an ≅ 𝒪` on the charts; (c) Leray acyclicity of `𝒪(d)^an` from an-cohom's
   `H'_holomorphicAbSheaf_pi_subsingleton` (`TheoremB.lean`, `FactorKind.punctured/.plane`) and
   an-coh's C31 `restrictH'AddEquiv` (`Foundations/Cohomology/RestrictOpen.lean`); (d) the Čech
   comparison by `bijective_pullbackCohomologyMap_iff_cech`: with an-cohom's Laurent splitting
   with parameters (`exists_laurent_splitting`, `laurentPlus`, C33) the analytic Čech groups carry
   commuting projectors `P_j` (nonnegative part in `x_j`); a cone construction on each sign pattern
   (as in `CechMonomial.lean`) plus "all-negative part is a Laurent polynomial" and the `H⁰` case
   (homogeneous holomorphic functions on `ℂⁿ⁺¹ ∖ 0` are polynomials) finish.
2. `ProjectiveSpaceAnalyticLerayStatement` from an-coh's `CoherentTheoremABStatement` + C31 + (1a).
3. Closed immersions `X ⊆ ℙⁿ` ⇒ `ProjectiveCohomologyComparisonStatement`: `(j_* F)^an ≅
   j^an_* F^an` (stalks: `pullbackStalkIso`), `Hᵖ` along closed embeddings on both sides, and
   `pullbackCohomologyMap` of a composite.
4. XII.4.4 full faithfulness from XII.4.3 for `ℋom(F, G)`, with the adopted `ModulesHom*`
   (needs `ℋom(F, G)^an ≅ ℋom(F^an, G^an)` for coherent `F`: `bijective_homStalkMap` +
   `pullbackStalkIso` + flat base change of `Hom` for finitely presented modules).
5. XII.4.1–4.2 (needs `Rᵖf_*` of `𝒪`-modules; mathlib has no `IsGrothendieckAbelian` for
   `SheafOfModules`), XII.3.1 (v), (vi), (viii), (x), fibre products of analytic spaces (C9).

## For the coordinator

- Barrel candidates: `SGA/SGA1/ExposeXII.lean`: `GAGAProjective`, `GAGAModules`,
  `GAGAProjectiveSpace`; `SGA/Foundations.lean`: `Cohomology.CechPullback`,
  `Analytic.{ModulesCohomology, ModulesStalk, ModulesExactness, ModulesStalkFree, ModulesHom,
  ModulesHomStalk, ModulesHomExact, ModulesHomFree, ModulesHomPresentation, ModulesHomRestriction,
  ModulesHomLocal, ModulesHomPullback}`.
- Foundations README, XII.4 row: XII.1.3.1 proved (separated `X`); XII.4.3 for coherent sheaves on
  `ℙⁿ` proved conditionally on `ProjectiveSpaceTwistComparisonStatement` and
  `ProjectiveSpaceAnalyticLerayStatement`; A48 interface `ProjectiveCohomologyComparisonStatement`.
