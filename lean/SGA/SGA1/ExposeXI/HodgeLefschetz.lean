/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.SerreUnirationalProjective
import SGA.SGA1.ExposeXI.HodgeLefschetzAlgebra
import SGA.SGA1.ExposeX.NormalCompleteLocalBase
import SGA.Foundations.Cohomology.BaseChangeSections
import SGA.Foundations.Fields.ComplexEmbedding
import SGA.Foundations.Fields.GeometricallyConnected
import SGA.Foundations.Projective.QuasiProjective

/-!
# The Lefschetz principle for XI.1.4

SGA 1 XI.1.4 (Serre) concerns an arbitrary algebraically closed field `k` of characteristic `0`;
its transcendental input, Hodge symmetry, is a statement over `ℂ`
(`HodgeSymmetryZeroComplexStatement`). This file passes from `ℂ` to `k` (registry row A47). We do
not transport Hodge numbers; we transport simple connectivity, which needs less:

* `isSimplyConnected_of_isSimplyConnected_pullback`: for `k` algebraically closed and any field
  extension `k → K`, a connected `k`-scheme `X` is simply connected if `X_K = X ×_k K` is. A
  connected finite étale covering `Y ⟶ X` gives the connected (`k = k̄`,
  `connectedSpace_pullback_of_isAlgClosed_of_connectedSpace`) finite étale covering `Y_K ⟶ X_K`,
  which is an isomorphism; isomorphisms descend along the faithfully flat quasi-compact
  `X_K ⟶ X` (mathlib's fpqc descent).
* `isIntegral_pullback_of_smooth`: a connected smooth `k`-scheme stays integral after base change
  to any field `K ⊇ k` (`k = k̄`): `X_K` is connected and smooth over `K`, hence regular, hence
  integral.
* `isUnirational_functionField_pullback`: unirationality of the function field ascends from `X` to
  `X_K` (`X` integral and locally of finite type over `k`, `X_K` integral): on a nonempty
  affine open `U = Spec A`, `X_K` has the affine open `Spec (K ⊗_k A)`
  (`CohomologyAux.isPushout_baseChange`), and `isUnirational_of_isPushout` applies to the fraction
  fields.
* **`isSimplyConnected_of_hodgeSymmetryZeroComplex_of_mk_le_continuum`**: XI.1.4 in SGA's form
  (projective `X`) over an algebraically closed field `k` of characteristic `0` with `#k ≤ 𝔠`,
  in universe `0`, given `HodgeSymmetryZeroComplexStatement`. Embed `k ↪ ℂ`
  (`Complex.nonempty_ringHom_of_mk_le_continuum`); `X_ℂ` is smooth, proper, quasi-projective,
  integral and unirational, hence simply connected
  (`isSimplyConnected_of_hodgeSymmetryZeroComplex`),
  hence so is `X`.

Fields with `#k > 𝔠` are treated in `HodgeLefschetzDescent.lean` and `HodgeLefschetzSpread.lean`
(descend `X` to a countable algebraically closed subfield, then X.1.8). Universes above `0` are not
treated: `HodgeSymmetryZeroComplexStatement` is about `Scheme.{0}`.

## References

* [SGA 1, X.1.8, XI.1.4]
* [EGA IV₂, 2.7.1] (fpqc descent of properties of morphisms, isomorphisms among them)
* [EGA IV₂, 4.5] (connected schemes over an algebraically closed field are geometrically
  connected)
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace SGA.SGA1.ExposeXI

section BaseChange

variable {k K : Type u} [Field k] [IsAlgClosed k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- **Simple connectivity descends along a base field extension** (`k` algebraically closed):
if `X` is a connected `k`-scheme and `X ×_k K` is simply connected for some field `K ⊇ k`, then `X`
is simply connected. A connected finite étale covering `Y ⟶ X` base changes to a connected
(`Y ×_X X_K = Y ×_k K`, geometric connectedness over `k = k̄`) finite étale covering of `X_K`,
which is an isomorphism; isomorphisms descend along the faithfully flat quasi-compact projection
`X_K ⟶ X`. -/
theorem isSimplyConnected_of_isSimplyConnected_pullback [ConnectedSpace X]
    (h : IsSimplyConnected (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    IsSimplyConnected X := by
  set ρ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  refine ⟨inferInstance, fun Y π _ _ hY ↦ ?_⟩
  set p := pullback.fst f ρ
  have : ConnectedSpace ↥(pullback (π ≫ f) ρ) :=
    connectedSpace_pullback_of_isAlgClosed_of_connectedSpace (π ≫ f) ρ
  let e := pullbackRightPullbackFstIso f ρ π
  have : ConnectedSpace ↥(pullback π p) :=
    e.inv.surjective.connectedSpace e.inv.continuous
  have hiso : IsIso (pullback.snd π p) := h.2 (pullback.snd π p) this
  have hp : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) p :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms _)
    (IsPullback.of_hasPullback π p).flip hp hiso

/-- A connected smooth scheme over an algebraically closed field `k` stays integral after base
change to any field `K ⊇ k`: `X ×_k K` is connected (`k = k̄`) and smooth over `K`, hence regular,
hence integral (`ExposeX.isIntegral_and_isNormalScheme_of_smooth`). -/
theorem isIntegral_pullback_of_smooth [ConnectedSpace X] [Smooth f] :
    IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have := connectedSpace_pullback_of_isAlgClosed_of_connectedSpace f
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  exact (ExposeX.isIntegral_and_isNormalScheme_of_smooth K
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).1

end BaseChange

section FunctionField

/-- The structure map `k → K(Y)` of an irreducible `k`-scheme `Y` factors through the sections over
any nonempty open `W`. -/
theorem germToFunctionField_comp_appLE {k : Type u} [Field k] {Y : Scheme.{u}}
    [IrreducibleSpace Y] (g : Y ⟶ Spec (.of k)) (W : Y.Opens) [Nonempty W] :
    (Y.germToFunctionField W).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ W le_top).hom =
      functionFieldMap g := by
  rw [functionFieldMap, ← CommRingCat.hom_comp]
  congr 1
  simp only [Scheme.germToFunctionField, Category.assoc, Scheme.Hom.appLE,
    TopCat.Presheaf.germ_res]
  rfl

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- **Unirationality ascends along a base field extension**: if `X` is an integral scheme locally
of finite type over a field `k` with unirational function field, `K ⊇ k` is a field and `X ×_k K`
is integral (automatic for `X` smooth and `k` algebraically closed,
`isIntegral_pullback_of_smooth`), then the function field of `X ×_k K` is unirational over `K`.
On a nonempty affine open `U` of `X`, the inverse image of `U` in `X ×_k K` is affine with ring
`K ⊗_k Γ(X, U)` (`CohomologyAux.isPushout_baseChange`), and `isUnirational_of_isPushout`
applies. -/
theorem isUnirational_functionField_pullback
    [IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))]
    (h : letI := (functionFieldMap f).toAlgebra; IsUnirational k X.functionField) :
    letI := (functionFieldMap
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).toAlgebra
    IsUnirational K (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).functionField := by
  set ρ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  set p := pullback.fst f ρ
  set fK := pullback.snd f ρ
  -- a nonempty affine open `U ⊆ X` and its inverse image `V ⊆ X_K`
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  set V := p ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage p
  have : Nonempty V := by
    obtain ⟨y, hy⟩ := p.surjective x
    exact ⟨⟨y, by rw [Scheme.Hom.mem_preimage, hy]; exact hxU⟩⟩
  -- the pushout square of rings
  have H := CohomologyAux.isPushout_baseChange (IsPullback.of_hasPullback f ρ) hU
  let a₁ := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom
  let a₃ := (p.appLE U V le_rfl).hom
  let a₄ := ((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appLE ⊤ V le_top).hom
  let _ : Algebra k Γ(X, U) := a₁.toAlgebra
  let _ : Algebra Γ(X, U) Γ(pullback f ρ, V) := a₃.toAlgebra
  let _ : Algebra K Γ(pullback f ρ, V) := a₄.toAlgebra
  let _ : Algebra k Γ(pullback f ρ, V) := (a₃.comp a₁).toAlgebra
  have : IsScalarTower k Γ(X, U) Γ(pullback f ρ, V) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k K Γ(pullback f ρ, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom H.w)
  have : Algebra.IsPushout k Γ(X, U) K Γ(pullback f ρ, V) :=
    CommRingCat.isPushout_iff_isPushout.mp H
  have : Algebra.IsPushout k K Γ(X, U) Γ(pullback f ρ, V) := Algebra.IsPushout.symm this
  -- the fraction fields
  let _ : Algebra k X.functionField := (functionFieldMap f).toAlgebra
  let _ : Algebra K (pullback f ρ).functionField := (functionFieldMap fK).toAlgebra
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsFractionRing Γ(pullback f ρ, V) (pullback f ρ).functionField :=
    functionField_isFractionRing_of_isAffineOpen _ V hV
  have : IsScalarTower k Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq' (germToFunctionField_comp_appLE f U).symm
  have : IsScalarTower K Γ(pullback f ρ, V) (pullback f ρ).functionField :=
    IsScalarTower.of_algebraMap_eq' (germToFunctionField_comp_appLE fK V).symm
  have : Algebra.EssFiniteType k X.functionField := essFiniteType_functionFieldMap f
  exact isUnirational_of_isPushout Γ(X, U) Γ(pullback f ρ, V) h

end FunctionField

section Complex

/-- **XI.1.4 (Serre) for projective `X` over a field `k` with `#k ≤ 𝔠`**, in universe `0`,
conditional on Hodge symmetry over `ℂ` (`HodgeSymmetryZeroComplexStatement`, not proved yet): a
smooth projective (proper and quasi-projective) integral scheme `X` over an algebraically closed
field `k` of characteristic `0` and cardinality at most that of `ℂ`, with unirational function
field, is simply connected. Embed `k ↪ ℂ`; `X_ℂ` is smooth, proper, quasi-projective, integral
(`isIntegral_pullback_of_smooth`) and unirational (`isUnirational_functionField_pullback`), hence
simply connected (`isSimplyConnected_of_hodgeSymmetryZeroComplex`), and simple connectivity
descends to `X` (`isSimplyConnected_of_isSimplyConnected_pullback`). -/
theorem isSimplyConnected_of_hodgeSymmetryZeroComplex_of_mk_le_continuum
    (hC : HodgeSymmetryZeroComplexStatement) {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (hk : Cardinal.mk k ≤ Cardinal.continuum) {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsQuasiProjective f] [Smooth f]
    (h : letI := (functionFieldMap f).toAlgebra; IsUnirational k X.functionField) :
    IsSimplyConnected X := by
  obtain ⟨σ⟩ := Complex.nonempty_ringHom_of_mk_le_continuum k hk
  let _ : Algebra k ℂ := σ.toAlgebra
  have : IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k ℂ)))) :=
    isIntegral_pullback_of_smooth f
  have : IsQuasiProjective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k ℂ)))) :=
    IsQuasiProjective.of_isPullback (IsPullback.of_hasPullback f _)
  exact isSimplyConnected_of_isSimplyConnected_pullback f
    (isSimplyConnected_of_hodgeSymmetryZeroComplex hC _
      (isUnirational_functionField_pullback f h))

end Complex

end SGA.SGA1.ExposeXI
