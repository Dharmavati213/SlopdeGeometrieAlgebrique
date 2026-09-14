/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.MatlisCategories
import SGA.SGA2.ExposeIV.LocalCompletionEquivalence
import SGA.SGA2.ExposeIV.CompletionSubmodules

/-!
# Completion equivalence on the actual category `CA`

Original scalar extension and restriction preserve local Artinianness and
finite generation of the actual socle. Their restricted adjunction gives
an equivalence of the original `CA` categories. The unit is `x ↦ 1 ⊗ x`
and the counit is the existing completed scalar action.

No noetherianity of the completed ring is assumed. Restriction preserves
finite socles by the actual completed-submodule stability theorem applied
to the socle itself. The two socles have exactly the same underlying set.
-/

noncomputable section

universe u

open CategoryTheory Limits ModuleCat TensorProduct

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The actual restriction of a linear equivalence to the original socles. -/
def localSocleLinearEquiv {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    [Module R X] [Module R Y] (e : X ≃ₗ[R] Y) :
    localSocle (R := R) X ≃ₗ[R] localSocle (R := R) Y :=
  (LinearEquiv.ofEq _ _ (localSocle_comap_linearEquiv e).symm).trans
    (e.ofSubmodule' (localSocle (R := R) Y))

@[simp]
theorem localSocleLinearEquiv_apply {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    [Module R X] [Module R Y] (e : X ≃ₗ[R] Y) (x : localSocle (R := R) X) :
    ((localSocleLinearEquiv e x : localSocle (R := R) Y) : Y) = e x := rfl

/-- The identity-on-modules inclusion of `CA` in locally Artinian modules. -/
def matlisArtinianToLocallyArtinian (R : Type u) [CommRing R] [IsLocalRing R] :
    MatlisArtinianModuleCat R ⥤ LocallyArtinianModuleCat R :=
  (locallyArtinianModuleProperty R).lift (matlisArtinianModuleProperty R).ι
    (fun X ↦ X.property.1)

variable [IsNoetherianRing R]

/-- Restriction identifies the actual socle conditions element by element. -/
theorem mem_localSocle_completion_restrict_iff
    (X : ModuleCat.{u} (AdicCompletion (IsLocalRing.maximalIdeal R) R)) (x : X) :
    (show (restrictScalars
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj X from x) ∈
      localSocle (R := R)
        ((restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj X) ↔
      x ∈ localSocle (R := AdicCompletion (IsLocalRing.maximalIdeal R) R) X := by
  rw [mem_localSocle, mem_localSocle]
  change (∀ r ∈ IsLocalRing.maximalIdeal R,
    algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r • x = 0) ↔
      ∀ a ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R), a • x = 0
  constructor
  · intro hx
    have hAnn : (IsLocalRing.maximalIdeal R).map
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) ≤
          Ideal.torsionOf (AdicCompletion (IsLocalRing.maximalIdeal R) R) X x := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      exact hx r hr
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact fun a ha ↦ hAnn ha
  · intro hx r hr
    apply hx (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r)
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ hr

/-- The canonical identity-on-elements linear equivalence between the
restricted completed socle and the original-ring socle. -/
def completionSocleRestrictionEquiv
    (X : ModuleCat.{u} (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
    (restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj
        (ModuleCat.of (AdicCompletion (IsLocalRing.maximalIdeal R) R)
          (localSocle (R := AdicCompletion (IsLocalRing.maximalIdeal R) R) X)) ≃ₗ[R]
      localSocle (R := R)
        ((restrictScalars
          (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj X) where
  toFun x := ⟨x.val, (mem_localSocle_completion_restrict_iff X x.val).mpr x.property⟩
  invFun x := ⟨x.val, (mem_localSocle_completion_restrict_iff X x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem completionSocleRestrictionEquiv_apply
    (X : ModuleCat.{u} (AdicCompletion (IsLocalRing.maximalIdeal R) R))
    (x : (restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj
      (ModuleCat.of (AdicCompletion (IsLocalRing.maximalIdeal R) R)
        (localSocle (R := AdicCompletion (IsLocalRing.maximalIdeal R) R) X))) :
    (completionSocleRestrictionEquiv X x).val = x.val := rfl

/-- Finite generation of the actual socle is invariant under completion
restriction, for every completed-ring module, not only supported modules. -/
theorem completion_localSocle_finite_iff
    (X : ModuleCat.{u} (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
    Module.Finite (AdicCompletion (IsLocalRing.maximalIdeal R) R)
        (localSocle (R := AdicCompletion (IsLocalRing.maximalIdeal R) R) X) ↔
      Module.Finite R (localSocle (R := R)
        ((restrictScalars
          (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj X)) := by
  let m := IsLocalRing.maximalIdeal R
  let A := AdicCompletion m R
  let f := algebraMap R A
  let S := ModuleCat.of A (localSocle (R := A) X)
  let e := completionSocleRestrictionEquiv X
  constructor
  · intro hS
    have : Module.Finite A S := hS
    have hSupp : supportedModuleProperty (m.map f) S := by
      rw [supportedModuleProperty, Module.support_eq_zeroLocus]
      apply PrimeSpectrum.zeroLocus_anti_mono
      intro r hr
      apply Module.mem_annihilator.mpr
      intro x
      apply Subtype.ext
      apply (mem_localSocle X x.val).mp x.property r
      rwa [AdicCompletion.maximalIdeal_eq_map]
    have := completion_restrictScalars_finite m S hSupp
    exact Module.Finite.of_surjective e.toLinearMap e.surjective
  · intro hS
    have : Module.Finite R ((restrictScalars f).obj S) :=
      Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
    let g : ((restrictScalars f).obj S) →ₛₗ[f] S :=
      { toFun := id
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    exact Module.Finite.of_surjective g Function.surjective_id

/-- Actual restriction preserves precisely the original `CA` property. -/
theorem matlisArtinian_completion_restrict
    (X : ModuleCat.{u} (AdicCompletion (IsLocalRing.maximalIdeal R) R))
    (hX : matlisArtinianModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R) X) :
    matlisArtinianModuleProperty R
      ((restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj X) :=
  ⟨((localArtinianCompletionEquivalence (R := R)).inverse.obj ⟨X, hX.1⟩).property,
    (completion_localSocle_finite_iff X).mp hX.2⟩

/-- Actual tensor extension preserves the original `CA` property. The
finite-socle comparison is induced by the genuine tensor unit. -/
theorem matlisArtinian_completion_extend (X : ModuleCat.{u} R)
    (hX : matlisArtinianModuleProperty R X) :
    matlisArtinianModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      ((extendScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj X) := by
  let m := IsLocalRing.maximalIdeal R
  let f := algebraMap R (AdicCompletion m R)
  have hSupp := (moduleLocallyArtinian_iff_support_maximalIdeal X).mp hX.1
  have := completion_unit_isIso m X hSupp
  let e : X ≃ₗ[R] (restrictScalars f).obj ((extendScalars f).obj X) :=
    (asIso ((extendRestrictScalarsAdj f).unit.app X)).toLinearEquiv
  have := hX.2
  have hSocle : Module.Finite R (localSocle (R := R)
      ((restrictScalars f).obj ((extendScalars f).obj X))) :=
    Module.Finite.of_surjective (localSocleLinearEquiv e).toLinearMap
      (localSocleLinearEquiv e).surjective
  exact ⟨((localArtinianCompletionEquivalence (R := R)).functor.obj ⟨X, hX.1⟩).property,
    (completion_localSocle_finite_iff ((extendScalars f).obj X)).mpr hSocle⟩

/-- The original tensor-extension functor, restricted to `CA`. -/
def matlisArtinianCompletionExtension : MatlisArtinianModuleCat R ⥤
    MatlisArtinianModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  (matlisArtinianModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R)).lift
    ((matlisArtinianModuleProperty R).ι ⋙
      extendScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))
    (fun X ↦ matlisArtinian_completion_extend X.obj X.property)

/-- The original scalar-restriction functor, restricted to `CA`. -/
def matlisArtinianCompletionRestriction :
    MatlisArtinianModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R) ⥤
      MatlisArtinianModuleCat R :=
  (matlisArtinianModuleProperty R).lift
    ((matlisArtinianModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R)).ι ⋙
      restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))
    (fun X ↦ matlisArtinian_completion_restrict X.obj X.property)

/-- The adjunction is inherited from the original tensor/restriction adjunction. -/
def matlisArtinianCompletionAdjunction :
    matlisArtinianCompletionExtension (R := R) ⊣ matlisArtinianCompletionRestriction (R := R) :=
  (extendRestrictScalarsAdj
    (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).restrictFullyFaithful
    (matlisArtinianModuleProperty R).fullyFaithfulι
    (matlisArtinianModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R)).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

@[simp]
theorem matlisArtinianCompletionAdjunction_unit_hom (X : MatlisArtinianModuleCat R) :
    ((matlisArtinianCompletionAdjunction (R := R)).unit.app X).hom =
      (extendRestrictScalarsAdj
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).unit.app X.obj := by
  change (matlisArtinianModuleProperty R).ι.map
    ((matlisArtinianCompletionAdjunction (R := R)).unit.app X) = _
  simp only [matlisArtinianCompletionAdjunction, Adjunction.map_restrictFullyFaithful_unit_app,
    Iso.refl_hom, NatTrans.id_app]
  rfl

@[simp]
theorem matlisArtinianCompletionAdjunction_counit_hom
    (X : MatlisArtinianModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
    ((matlisArtinianCompletionAdjunction (R := R)).counit.app X).hom =
      (extendRestrictScalarsAdj
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).counit.app X.obj := by
  change (matlisArtinianModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R)).ι.map
    ((matlisArtinianCompletionAdjunction (R := R)).counit.app X) = _
  simp only [matlisArtinianCompletionAdjunction, Adjunction.map_restrictFullyFaithful_counit_app,
    Iso.refl_inv, NatTrans.id_app]
  change 𝟙 _ ≫ (extendScalars _).map (𝟙 _) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

/-- Completion gives an equivalence of the actual `CA` categories, without
assuming that the completed ring is noetherian. -/
def matlisArtinianCompletionEquivalence : MatlisArtinianModuleCat R ≌
    MatlisArtinianModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  let adj := matlisArtinianCompletionAdjunction (R := R)
  haveI (X : MatlisArtinianModuleCat R) : IsIso (adj.unit.app X) := by
    apply (ObjectProperty.isIso_hom_iff _).mp
    change IsIso (((matlisArtinianCompletionAdjunction (R := R)).unit.app X).hom)
    rw [matlisArtinianCompletionAdjunction_unit_hom]
    exact completion_unit_isIso _ X.obj X.supported
  haveI (X : MatlisArtinianModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
      IsIso (adj.counit.app X) := by
    apply (ObjectProperty.isIso_hom_iff _).mp
    change IsIso (((matlisArtinianCompletionAdjunction (R := R)).counit.app X).hom)
    rw [matlisArtinianCompletionAdjunction_counit_hom]
    exact completion_counit_isIso _ X.obj
      ((completion_locallyArtinian_iff_supported X.obj).mp X.property.1)
  exact adj.toEquivalence

/-- On underlying modules and morphisms the forward functor is literal tensor extension. -/
theorem matlisArtinianCompletionEquivalence_functor_forget :
    (matlisArtinianCompletionEquivalence (R := R)).functor ⋙
        (matlisArtinianModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R)).ι =
      (matlisArtinianModuleProperty R).ι ⋙
        extendScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) := rfl

/-- On underlying modules and morphisms the inverse is literal restriction. -/
theorem matlisArtinianCompletionEquivalence_inverse_forget :
    (matlisArtinianCompletionEquivalence (R := R)).inverse ⋙ (matlisArtinianModuleProperty R).ι =
      (matlisArtinianModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R)).ι ⋙
        restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) := rfl

/-- The equivalence commutes with the existing locally Artinian completion functor. -/
theorem matlisArtinianCompletionEquivalence_functor_locallyArtinian :
    (matlisArtinianCompletionEquivalence (R := R)).functor ⋙
        matlisArtinianToLocallyArtinian (AdicCompletion (IsLocalRing.maximalIdeal R) R) =
      matlisArtinianToLocallyArtinian R ⋙
        (localArtinianCompletionEquivalence (R := R)).functor := rfl

/-- Its inverse commutes with existing locally Artinian scalar restriction. -/
theorem matlisArtinianCompletionEquivalence_inverse_locallyArtinian :
    (matlisArtinianCompletionEquivalence (R := R)).inverse ⋙ matlisArtinianToLocallyArtinian R =
      matlisArtinianToLocallyArtinian (AdicCompletion (IsLocalRing.maximalIdeal R) R) ⋙
        (localArtinianCompletionEquivalence (R := R)).inverse := rfl

@[simp]
theorem matlisArtinianCompletionEquivalence_unit_apply
    (X : MatlisArtinianModuleCat R) (x : X.obj) :
    ((matlisArtinianCompletionEquivalence (R := R)).unitIso.hom.app X).hom x =
      (1 : AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗ₜ[R] x := by
  change ((matlisArtinianCompletionAdjunction (R := R)).unit.app X).hom x = _
  rw [matlisArtinianCompletionAdjunction_unit_hom]
  rfl

@[simp]
theorem matlisArtinianCompletionEquivalence_counit_tmul
    (X : MatlisArtinianModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R))
    (a : AdicCompletion (IsLocalRing.maximalIdeal R) R) (x : X.obj) :
    ((matlisArtinianCompletionEquivalence (R := R)).counitIso.hom.app X).hom
      (a ⊗ₜ[R] (show (restrictScalars
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj X.obj from x)) =
        a • x := by
  change ((matlisArtinianCompletionAdjunction (R := R)).counit.app X).hom _ = _
  rw [matlisArtinianCompletionAdjunction_counit_hom]
  rfl

end SGA.SGA2.ExposeIV
