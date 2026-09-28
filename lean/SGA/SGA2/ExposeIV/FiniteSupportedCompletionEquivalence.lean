/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.CompletionSubmodules
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Completion equivalence on actual finite supported modules

The functors retain the original tensor product and restriction of scalars.
Their adjunction is restricted from the original scalar-change adjunction;
thus its unit and counit are the original tensor-unit and multiplication
maps. Finite generation after restriction is proved, not assumed, and no
noetherianity hypothesis on the completed ring is added.
-/

noncomputable section

universe u

open CategoryTheory Limits ModuleCat TensorProduct

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Inclusion of the actual finite supported category into all supported modules. -/
def supportedFiniteToSupported (J : Ideal R) : SupportedFGModuleCat J ⥤ SupportedModuleCat J where
  obj M := ⟨M.obj.obj, M.property⟩
  map f := ObjectProperty.homMk f.hom.hom

/-- All original module maps remain available in the finite supported inclusion. -/
def supportedFiniteToSupportedFullyFaithful (J : Ideal R) :
    (supportedFiniteToSupported J).FullyFaithful where
  preimage f := ObjectProperty.homMk (ObjectProperty.homMk f.hom)
  map_preimage _ := rfl
  preimage_map _ := rfl

instance (J : Ideal R) : (supportedFiniteToSupported J).Full :=
  (supportedFiniteToSupportedFullyFaithful J).full

instance (J : Ideal R) : (supportedFiniteToSupported J).Faithful :=
  (supportedFiniteToSupportedFullyFaithful J).faithful

instance (J : Ideal R) : (supportedFiniteToSupported J).Additive where
  map_add := rfl

instance (J : Ideal R) : (supportedFiniteToSupported J).Linear R where
  map_smul _ _ := rfl

/-- The inclusion in all modules is likewise genuinely fully faithful. -/
def supportedFiniteToModuleFullyFaithful (J : Ideal R) :
    (supportedFiniteToModule J).FullyFaithful where
  preimage f := ObjectProperty.homMk (ObjectProperty.homMk f)
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- Actual scalar extension of a finite module is finite over the target ring. -/
theorem extendScalars_finite (f : R →+* S) (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.Finite S ((extendScalars f).obj M) := by
  let := f.toAlgebra
  exact Module.Finite.base_change (R := R) (A := S) (M := M)

/-- Finite supported scalar extension with the original tensor product and maps. -/
def supportedFiniteExtendScalars (f : R →+* S) (J : Ideal R) (hJ : J.FG) :
    SupportedFGModuleCat J ⥤ SupportedFGModuleCat (J.map f) where
  obj M := by
    have := extendScalars_finite f M.obj.obj
    exact ⟨FGModuleCat.of S ((extendScalars f).obj M.obj.obj),
      supported_extendScalars f J hJ M.obj.obj M.property⟩
  map g := ObjectProperty.homMk (ObjectProperty.homMk ((extendScalars f).map g.hom.hom))
  map_id M := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (extendScalars f).map_id _
  map_comp g h := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (extendScalars f).map_comp _ _

instance (f : R →+* S) (J : Ideal R) (hJ : J.FG) :
    (supportedFiniteExtendScalars f J hJ).Additive where
  map_add := by
    intro X Y g h
    have : PreservesColimits (extendScalars f) :=
      (extendRestrictScalarsAdj f).leftAdjoint_preservesColimits
    have : (extendScalars f).Additive :=
      rightExactFunctor_le_additiveFunctor (ModuleCat R) (ModuleCat S)
        (extendScalars f) (by rw [rightExactFunctor_iff]; infer_instance)
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (extendScalars f).map_add

/-- The finite extension is the literal restriction of full supported extension. -/
theorem supportedFiniteExtendScalars_forget (f : R →+* S) (J : Ideal R) (hJ : J.FG) :
    supportedFiniteExtendScalars f J hJ ⋙ supportedFiniteToSupported (J.map f) =
      supportedFiniteToSupported J ⋙ supportedExtendScalars f J hJ := rfl

variable [IsNoetherianRing R] (J : Ideal R)

/-- The forward finite completion functor is actual tensor scalar extension. -/
abbrev finiteSupportedCompletionExtension :
    SupportedFGModuleCat J ⥤
      SupportedFGModuleCat (J.map (algebraMap R (AdicCompletion J R))) :=
  supportedFiniteExtendScalars (algebraMap R (AdicCompletion J R)) J J.fg_of_isNoetherianRing

/-- The inverse functor is actual restriction; finiteness follows from the
proved stability of every original submodule under the completed action. -/
def finiteSupportedCompletionRestriction :
    SupportedFGModuleCat (J.map (algebraMap R (AdicCompletion J R))) ⥤
      SupportedFGModuleCat J where
  obj M := by
    have := completion_restrictScalars_finite J M.obj.obj M.property
    exact ⟨FGModuleCat.of R
      ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M.obj.obj),
      (supported_restrictScalars_iff _ J J.fg_of_isNoetherianRing M.obj.obj).mpr M.property⟩
  map g := ObjectProperty.homMk (ObjectProperty.homMk
    ((restrictScalars (algebraMap R (AdicCompletion J R))).map g.hom.hom))

instance : (finiteSupportedCompletionRestriction J).Additive where
  map_add := rfl

/-- Comparison with the actual full supported restriction functor. -/
theorem finiteSupportedCompletionRestriction_forget :
    finiteSupportedCompletionRestriction J ⋙ supportedFiniteToSupported J =
      supportedFiniteToSupported (J.map (algebraMap R (AdicCompletion J R))) ⋙
        (supportedCompletionEquivalence J).inverse := rfl

/-- Restrict the original tensor/restriction adjunction along the actual
fully faithful inclusions of finite supported modules. -/
def finiteSupportedCompletionAdjunction :
    finiteSupportedCompletionExtension J ⊣ finiteSupportedCompletionRestriction J :=
  (extendRestrictScalarsAdj (algebraMap R (AdicCompletion J R))).restrictFullyFaithful
    (supportedFiniteToModuleFullyFaithful J)
    (supportedFiniteToModuleFullyFaithful (J.map (algebraMap R (AdicCompletion J R))))
    (Iso.refl _) (Iso.refl _)

/-- The finite adjunction retains the original scalar-extension unit. -/
@[simp] theorem finiteSupportedCompletionAdjunction_unit_hom (M : SupportedFGModuleCat J) :
    ((finiteSupportedCompletionAdjunction J).unit.app M).hom.hom =
      (extendRestrictScalarsAdj (algebraMap R (AdicCompletion J R))).unit.app M.obj.obj := by
  change (supportedFiniteToModule J).map
    ((finiteSupportedCompletionAdjunction J).unit.app M) = _
  simp only [finiteSupportedCompletionAdjunction, Adjunction.map_restrictFullyFaithful_unit_app,
    Iso.refl_hom, NatTrans.id_app]
  rfl

/-- The finite adjunction retains the original multiplication counit. -/
@[simp] theorem finiteSupportedCompletionAdjunction_counit_hom
    (M : SupportedFGModuleCat (J.map (algebraMap R (AdicCompletion J R)))) :
    ((finiteSupportedCompletionAdjunction J).counit.app M).hom.hom =
      (extendRestrictScalarsAdj (algebraMap R (AdicCompletion J R))).counit.app M.obj.obj := by
  change (supportedFiniteToModule (J.map (algebraMap R (AdicCompletion J R)))).map
    ((finiteSupportedCompletionAdjunction J).counit.app M) = _
  simp only [finiteSupportedCompletionAdjunction, Adjunction.map_restrictFullyFaithful_counit_app,
    Iso.refl_inv, NatTrans.id_app]
  change 𝟙 _ ≫ (extendScalars _).map (𝟙 _) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

/-- The genuine completion equivalence on the original finite supported categories. -/
def finiteSupportedCompletionEquivalence :
    SupportedFGModuleCat J ≌
      SupportedFGModuleCat (J.map (algebraMap R (AdicCompletion J R))) := by
  let adj := finiteSupportedCompletionAdjunction J
  haveI (M : SupportedFGModuleCat J) : IsIso (adj.unit.app M) := by
    apply (ObjectProperty.isIso_hom_iff _).mp
    apply (ObjectProperty.isIso_hom_iff _).mp
    change IsIso (((finiteSupportedCompletionAdjunction J).unit.app M).hom.hom)
    rw [finiteSupportedCompletionAdjunction_unit_hom]
    exact completion_unit_isIso J M.obj.obj M.property
  haveI (M : SupportedFGModuleCat (J.map (algebraMap R (AdicCompletion J R)))) :
      IsIso (adj.counit.app M) := by
    apply (ObjectProperty.isIso_hom_iff _).mp
    apply (ObjectProperty.isIso_hom_iff _).mp
    change IsIso (((finiteSupportedCompletionAdjunction J).counit.app M).hom.hom)
    rw [finiteSupportedCompletionAdjunction_counit_hom]
    exact completion_counit_isIso J M.obj.obj M.property
  exact adj.toEquivalence

@[simp] theorem finiteSupportedCompletionEquivalence_functor :
    (finiteSupportedCompletionEquivalence J).functor = finiteSupportedCompletionExtension J := rfl

@[simp] theorem finiteSupportedCompletionEquivalence_inverse :
    (finiteSupportedCompletionEquivalence J).inverse = finiteSupportedCompletionRestriction J := rfl

/-- The finite equivalence commutes with full supported completion on actual maps. -/
theorem finiteSupportedCompletionEquivalence_functor_forget :
    (finiteSupportedCompletionEquivalence J).functor ⋙
        supportedFiniteToSupported (J.map (algebraMap R (AdicCompletion J R))) =
      supportedFiniteToSupported J ⋙ (supportedCompletionEquivalence J).functor := rfl

/-- The original unit agrees with the unit of the full supported equivalence. -/
theorem finiteSupportedCompletionEquivalence_unit_forget (M : SupportedFGModuleCat J) :
    (supportedFiniteToSupported J).map
        ((finiteSupportedCompletionEquivalence J).unitIso.hom.app M) =
      (supportedCompletionEquivalence J).unitIso.hom.app
        ((supportedFiniteToSupported J).obj M) := by
  apply ObjectProperty.hom_ext
  change ((finiteSupportedCompletionAdjunction J).unit.app M).hom.hom =
    ((supportedExtendRestrictScalarsAdj _ J _).unit.app
      ((supportedFiniteToSupported J).obj M)).hom
  rw [finiteSupportedCompletionAdjunction_unit_hom, supportedExtendRestrictScalarsAdj_unit_hom]
  rfl

/-- The multiplication counit agrees with that of the full supported equivalence. -/
theorem finiteSupportedCompletionEquivalence_counit_forget
    (M : SupportedFGModuleCat (J.map (algebraMap R (AdicCompletion J R)))) :
    (supportedFiniteToSupported (J.map (algebraMap R (AdicCompletion J R)))).map
        ((finiteSupportedCompletionEquivalence J).counitIso.hom.app M) =
      (supportedCompletionEquivalence J).counitIso.hom.app
        ((supportedFiniteToSupported (J.map (algebraMap R (AdicCompletion J R)))).obj M) := by
  apply ObjectProperty.hom_ext
  change ((finiteSupportedCompletionAdjunction J).counit.app M).hom.hom =
    ((supportedExtendRestrictScalarsAdj _ J _).counit.app
      ((supportedFiniteToSupported (J.map (algebraMap R (AdicCompletion J R)))).obj M)).hom
  rw [finiteSupportedCompletionAdjunction_counit_hom, supportedExtendRestrictScalarsAdj_counit_hom]
  rfl

/-- Its original unit sends `x` to `1 ⊗ x`. -/
@[simp] theorem finiteSupportedCompletionEquivalence_unit_apply
    (M : SupportedFGModuleCat J) (x : M.obj) :
    ((finiteSupportedCompletionEquivalence J).unitIso.hom.app M).hom.hom x =
      (1 : AdicCompletion J R) ⊗ₜ[R] x := by
  change ((finiteSupportedCompletionAdjunction J).unit.app M).hom.hom x = _
  rw [finiteSupportedCompletionAdjunction_unit_hom]
  rfl

/-- Its original counit sends `a ⊗ x` to the existing completed scalar action. -/
@[simp] theorem finiteSupportedCompletionEquivalence_counit_tmul
    (M : SupportedFGModuleCat (J.map (algebraMap R (AdicCompletion J R))))
    (a : AdicCompletion J R) (x : M.obj) :
    ((finiteSupportedCompletionEquivalence J).counitIso.hom.app M).hom.hom
      (a ⊗ₜ[R] (show (restrictScalars (algebraMap R (AdicCompletion J R))).obj M.obj.obj from x)) =
        a • x := by
  change ((finiteSupportedCompletionAdjunction J).counit.app M).hom.hom _ = _
  rw [finiteSupportedCompletionAdjunction_counit_hom]
  rfl

end SGA.SGA2.ExposeIV
