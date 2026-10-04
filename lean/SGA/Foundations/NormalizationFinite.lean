/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.NoetherFiniteness
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import SGA.Foundations.Dimension.Scheme

/-!
# The normalization of an integral scheme of finite type over a perfect field

For an integral scheme `X`, the normalization `X' ⟶ X` is mathlib's relative normalization
(`Scheme.Hom.normalization`) of `X` in `Spec K(X) ⟶ X` (`X.fromSpecStalk (genericPoint X)`):
over an affine open `U`, it is `Spec` of the integral closure of `Γ(X, U)` in `K(X)`. We prove:

* `isIntegrallyClosed_stalk_normalization_fromSpecStalk_genericPoint`: `X'` is normal (its local
  rings are integrally closed domains; `X'` is integral by mathlib);
* `surjective_fromNormalization_fromSpecStalk_genericPoint`: `X' ⟶ X` is surjective;
* `isFinite_fromNormalization_fromSpecStalk_genericPoint`: if `X` is locally of finite type over a
  perfect field, `X' ⟶ X` is finite (E. Noether's finiteness theorem,
  `Algebra.FiniteType.finite_integralClosure`);
* `Scheme.Hom.topologicalKrullDim_le_of_locallyQuasiFinite`: a locally quasi-finite morphism (for
  instance a finite one) does not raise the dimension;
* `exists_isFinite_surjective_isIntegrallyClosed_stalk`: the resulting existence statement, a
  finite surjective morphism from a normal integral scheme of no larger dimension.

We also record that an integral scheme locally of finite type over a field has the same dimension
at all its points (`topologicalKrullDimAt_eq_of_isIntegral`, from
`Algebra.FiniteType.topologicalKrullDimAt_eq_ringKrullDim`), hence that its nonempty open
subsets have its dimension (`topologicalKrullDim_opens_eq_of_isIntegral`) and that a modification
(an isomorphism over a nonempty open, like the cover in Chow's lemma) does not change it
(`topologicalKrullDim_eq_of_isIso_morphismRestrict`).

## References

* [A. Grothendieck, *EGA* II, 6.3][EGA2]; [*EGA* IV₂, 7.8.3][EGA4]
* [Stacks Project, Morphisms of schemes, Section "Normalization"]
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X]

/-- `Spec K(X) ⟶ X`, the generic point of the integral scheme `X`. -/
local notation "η" => X.fromSpecStalk (genericPoint X)

/-- The generic point of an integral scheme lies in every nonempty open subset. -/
lemma Scheme.preimage_fromSpecStalk_genericPoint (U : X.Opens) [Nonempty U] :
    η ⁻¹ᵁ U = ⊤ := by
  refine top_le_iff.mp fun z _ ↦ ?_
  have hz : z = IsLocalRing.closedPoint _ :=
    Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
  change η z ∈ U
  rw [hz, Scheme.fromSpecStalk_closedPoint]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

set_option backward.isDefEq.respectTransparency false in
/-- For a nonempty open `U` of an integral scheme `X`, the sections of `Spec K(X)` over the
preimage of `U` are `K(X)`, compatibly with the restriction maps from `Γ(X, U)`
(`Scheme.germToFunctionField_comp_functionFieldIsoSections`). -/
noncomputable def Scheme.functionFieldIsoSections (U : X.Opens) [Nonempty U] :
    X.functionField ≅ Γ(Spec X.functionField, η ⁻¹ᵁ U) :=
  (Scheme.ΓSpecIso _).symm ≪≫
    (Spec X.functionField).presheaf.mapIso
      (eqToIso (Scheme.preimage_fromSpecStalk_genericPoint U)).op

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `Scheme.functionFieldIsoSections` is compatible with the maps from
`Γ(X, U)`. -/
lemma Scheme.germToFunctionField_comp_functionFieldIsoSections (U : X.Opens) [Nonempty U] :
    X.germToFunctionField U ≫ (Scheme.functionFieldIsoSections U).hom =
      (η).app U := by
  rw [Scheme.fromSpecStalk_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `Γ(X, U)`-algebra isomorphism `Γ(Spec K(X), U) ≃ K(X)` for a nonempty open `U` of an
integral scheme. -/
private noncomputable def functionFieldAlgEquiv (U : X.Opens) [Nonempty U] :
    letI := ((η).app U).hom.toAlgebra
    Γ(Spec X.functionField, η ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      X.functionField :=
  letI := ((η).app U).hom.toAlgebra
  AlgEquiv.ofRingEquiv (f := (Scheme.functionFieldIsoSections U).commRingCatIsoToRingEquiv.symm)
    fun a ↦ by
      change (Scheme.functionFieldIsoSections U).inv ((η).app U a) = _
      rw [← Scheme.germToFunctionField_comp_functionFieldIsoSections, CommRingCat.comp_apply,
        ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
      rfl

/-- The sections of the normalization of an integral scheme over a nonempty open `U` (the
integral closure of `Γ(X, U)` in `K(X)`) form an integrally closed domain. -/
private lemma isDomain_and_isIntegrallyClosed_integralClosure (U : X.Opens) [Nonempty U] :
    letI := ((η).app U).hom.toAlgebra
    IsDomain (integralClosure Γ(X, U)
        Γ(Spec X.functionField, η ⁻¹ᵁ U)) ∧
      IsIntegrallyClosed (integralClosure Γ(X, U)
        Γ(Spec X.functionField, η ⁻¹ᵁ U)) := by
  let := ((η).app U).hom.toAlgebra
  let e := (functionFieldAlgEquiv U).mapIntegralClosure
  have : IsIntegrallyClosed (integralClosure Γ(X, U) X.functionField) :=
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn
      (R := integralClosure Γ(X, U) X.functionField) (S := X.functionField)
  exact ⟨e.injective.isDomain e, IsIntegrallyClosed.of_equiv e.symm.toRingEquiv⟩

/-- E. Noether's finiteness theorem on a nonempty affine open `U` of an integral scheme `X`
locally of finite type over a perfect field: the integral closure of `Γ(X, U)` in `K(X)` is a
finite `Γ(X, U)`-module. -/
private lemma finite_integralClosure_of_isAffineOpen {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] :
    letI := ((η).app U).hom.toAlgebra
    Module.Finite Γ(X, U) (integralClosure Γ(X, U)
      Γ(Spec X.functionField, η ⁻¹ᵁ U)) := by
  let := ((η).app U).hom.toAlgebra
  let ψ : CommRingCat.of k ⟶ Γ(X, U) := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top
  have hft : ψ.hom.FiniteType :=
    (RingHom.finiteType_respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (.of k)).inv _).mpr
      (f.finiteType_appLE (isAffineOpen_top _) hU le_top)
  let := ψ.hom.toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := hft
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have := Algebra.FiniteType.finite_integralClosure k Γ(X, U) X.functionField X.functionField
  exact Module.Finite.equiv (functionFieldAlgEquiv U).symm.mapIntegralClosure.toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- **Finiteness of the normalization** (E. Noether, EGA IV 7.8.3): the
normalization `X' ⟶ X` of an integral scheme `X` locally of finite type over a perfect field
(mathlib's relative normalization of `Spec K(X) ⟶ X`) is finite. -/
theorem isFinite_fromNormalization_fromSpecStalk_genericPoint {k : Type u} [Field k]
    [PerfectField k] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    IsFinite (η).fromNormalization := by
  set g := η
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _ (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (g.fromNormalization ⁻¹ᵁ U).ι
    (g.normalizationOpenCover.f U)
      (by simpa using congr($(g.fromNormalization_preimage U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _ U.2.isoSpec.hom]
  have : (g.normalizationDiagramMap.app (.op U)).hom.Finite := by
    let := (g.app U).hom.toAlgebra
    change (algebraMap Γ(X, U) (integralClosure Γ(X, U) Γ(_, g ⁻¹ᵁ U))).Finite
    rw [RingHom.finite_algebraMap]
    by_cases hU : (U : Set X).Nonempty
    · have : Nonempty U.1 := hU.to_subtype
      exact finite_integralClosure_of_isAffineOpen f U.2
    · have hU' : g ⁻¹ᵁ U.1 = ⊥ := by
        rw [Set.not_nonempty_iff_eq_empty] at hU
        have : U.1 = ⊥ := TopologicalSpace.Opens.ext hU
        rw [this, Scheme.Hom.preimage_bot]
      have : Subsingleton Γ(Spec X.functionField, g ⁻¹ᵁ U.1) := by
        rw [hU']; infer_instance
      infer_instance
  convert! (IsFinite.SpecMap_iff _).mpr this
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, Scheme.Hom.ι_fromNormalization]

/-- The normalization of an integral scheme (mathlib's relative normalization of
`Spec K(X) ⟶ X`) is normal: its local rings are integrally closed (domains, as it is integral). -/
theorem isIntegrallyClosed_stalk_normalization_fromSpecStalk_genericPoint
    (x : (η).normalization) :
    IsIntegrallyClosed ((η).normalization.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((η).fromNormalization x)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have hV : IsAffineOpen ((η).fromNormalization ⁻¹ᵁ U) := hU.preimage _
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_integralClosure U
  let φ := ((η).normalizationObjIso hU).commRingCatIsoToRingEquiv
  have : IsDomain Γ((η).normalization, (η).fromNormalization ⁻¹ᵁ U) := φ.injective.isDomain φ
  have : IsIntegrallyClosed Γ((η).normalization, (η).fromNormalization ⁻¹ᵁ U) :=
    IsIntegrallyClosed.of_equiv φ.symm
  let : Algebra Γ((η).normalization, (η).fromNormalization ⁻¹ᵁ U)
      ((η).normalization.presheaf.stalk x) :=
    (η).normalization.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime ((η).normalization.presheaf.stalk x)
      (hV.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxU⟩
  exact isIntegrallyClosed_of_isLocalization _ _
    (Ideal.primeCompl_le_nonZeroDivisors (hV.primeIdealOf ⟨x, hxU⟩).asIdeal)

/-- The normalization of an integral scheme is surjective onto it: it is closed (integral), and
its image contains the generic point. -/
instance surjective_fromNormalization_fromSpecStalk_genericPoint :
    Surjective (η).fromNormalization := by
  refine ⟨fun x ↦ ?_⟩
  have hc : IsClosed (Set.range (η).fromNormalization) :=
    (η).fromNormalization.isClosedMap.isClosed_range
  have hg : genericPoint X ∈ Set.range (η).fromNormalization :=
    ⟨(η).toNormalization (IsLocalRing.closedPoint _), by
      change ((η).toNormalization ≫
        (η).fromNormalization)
          (IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X))) = _
      rw [Scheme.Hom.toNormalization_fromNormalization, Scheme.fromSpecStalk_closedPoint]⟩
  have hx : x ∈ closure {genericPoint X} := by
    rw [(genericPoint_spec X).def]; trivial
  exact hc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hg) hx

/-- A locally quasi-finite morphism does not raise the dimension: its fibres are discrete, so it
maps chains of specializations to chains of specializations of the same length. -/
theorem Scheme.Hom.topologicalKrullDim_le_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] : topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim, topologicalKrullDim, Order.krullDim_eq_of_orderIso
    irreducibleSetEquivPoints, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
  refine Order.krullDim_le_of_strictMono f fun a b hab ↦ ?_
  have hle : f a ≤ f b := (le_iff_specializes.mp hab.le).map f.continuous
  refine lt_of_le_not_ge hle fun hge ↦ hab.ne ?_
  have heq : f a = f b :=
    ((le_iff_specializes.mp hge).antisymm (le_iff_specializes.mp hle)).eq
  have := (f.isDiscrete_preimage_singleton (f a)).to_subtype
  have hsp : (⟨b, heq.symm⟩ : f ⁻¹' {f a}) ⤳ ⟨a, rfl⟩ :=
    (subtype_specializes_iff _ _).mpr (le_iff_specializes.mp hab.le)
  exact (congrArg Subtype.val (specializes_iff_eq.mp hsp)).symm


section Dimension

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]

include f in
/-- On a nonempty affine open `U` of an integral scheme locally of finite type over a field, the
dimension of `X` at every point of `U` is `dim Γ(X, U)`. -/
private lemma topologicalKrullDimAt_eq_ringKrullDim_of_isAffineOpen {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    topologicalKrullDimAt X x = ringKrullDim Γ(X, U) := by
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  let ψ : CommRingCat.of k ⟶ Γ(X, U) := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top
  have hft : ψ.hom.FiniteType :=
    (RingHom.finiteType_respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (.of k)).inv _).mpr
      (f.finiteType_appLE (isAffineOpen_top _) hU le_top)
  let := ψ.hom.toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := hft
  rw [hU.topologicalKrullDimAt_eq hx, Algebra.FiniteType.topologicalKrullDimAt_eq_ringKrullDim k]

include f in
/-- An integral scheme locally of finite type over a field has the same dimension at all its
points. -/
theorem topologicalKrullDimAt_eq_of_isIntegral (x y : X) :
    topologicalKrullDimAt X x = topologicalKrullDimAt X y := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  obtain ⟨z, hzU, hzV⟩ := nonempty_preirreducible_inter U.2 V.2 ⟨x, hxU⟩ ⟨y, hyV⟩
  rw [topologicalKrullDimAt_eq_ringKrullDim_of_isAffineOpen f hU hxU,
    ← topologicalKrullDimAt_eq_ringKrullDim_of_isAffineOpen f hU hzU,
    topologicalKrullDimAt_eq_ringKrullDim_of_isAffineOpen f hV hzV,
    topologicalKrullDimAt_eq_ringKrullDim_of_isAffineOpen f hV hyV]

include f in
/-- A nonempty open subset of an integral scheme locally of finite type over a field has the
dimension of the scheme. -/
theorem topologicalKrullDim_opens_eq_of_isIntegral (U : X.Opens) (hU : (U : Set X).Nonempty) :
    topologicalKrullDim U = topologicalKrullDim X := by
  refine le_antisymm (topologicalKrullDim_subspace_le _ _) ?_
  obtain ⟨z, hz⟩ := hU
  rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt (X := X)]
  refine iSup_le fun x ↦ ?_
  rw [topologicalKrullDimAt_eq_of_isIntegral f x z,
    ← U.isOpen.topologicalKrullDimAt_eq ⟨z, hz⟩]
  exact topologicalKrullDimAt_le_topologicalKrullDim _

include f in
/-- A morphism `π : X' ⟶ X` of integral schemes locally of finite type over a field which is an
isomorphism over a nonempty open subset of `X` (a modification, e.g. the cover in Chow's lemma)
does not change the dimension. -/
theorem topologicalKrullDim_eq_of_isIso_morphismRestrict {X' : Scheme.{u}} [IsIntegral X']
    (f' : X' ⟶ Spec (.of k)) [LocallyOfFiniteType f'] (π : X' ⟶ X) {U : X.Opens}
    (hU : (U : Set X).Nonempty) [IsIso (π ∣_ U)] :
    topologicalKrullDim X' = topologicalKrullDim X := by
  have hne : ((π ⁻¹ᵁ U : X'.Opens) : Set X').Nonempty := by
    obtain ⟨u, hu⟩ := hU
    obtain ⟨v, hv⟩ := (π ∣_ U).homeomorph.surjective ⟨u, hu⟩
    exact ⟨v.1, v.2⟩
  rw [← topologicalKrullDim_opens_eq_of_isIntegral f' _ hne,
    ← topologicalKrullDim_opens_eq_of_isIntegral f U hU]
  exact IsHomeomorph.topologicalKrullDim_eq _ (π ∣_ U).homeomorph.isHomeomorph

end Dimension

/-- **Normalization of an integral scheme of finite type over a perfect field**: there is a
finite surjective morphism `ν : X' ⟶ X` from an integral scheme `X'` whose local rings are
integrally closed, with `dim X' ≤ dim X` (the normalization of `X` in `K(X)`). -/
theorem exists_isFinite_surjective_isIntegrallyClosed_stalk {k : Type u} [Field k]
    [PerfectField k] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    ∃ (X' : Scheme.{u}) (ν : X' ⟶ X), IsFinite ν ∧ Surjective ν ∧ IsIntegral X' ∧
      (∀ x : X', IsIntegrallyClosed (X'.presheaf.stalk x)) ∧
        topologicalKrullDim X' ≤ topologicalKrullDim X :=
  have := isFinite_fromNormalization_fromSpecStalk_genericPoint f
  ⟨_, (η).fromNormalization, this, inferInstance, inferInstance,
    isIntegrallyClosed_stalk_normalization_fromSpecStalk_genericPoint,
    Scheme.Hom.topologicalKrullDim_le_of_locallyQuasiFinite
      (η).fromNormalization⟩

end AlgebraicGeometry
