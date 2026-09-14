/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.CompleteModuleScalarChange

/-!
# Actual completion equivalence on the literal category `DA`

The forward functor is module-adic completion, not tensoring an arbitrary
module with the completed ring. The inverse is original scalar restriction.
The unit is the original completion map; the counit is its inverse for an
already complete completed-ring module, proved linear for its existing
action. The triangle law is verified on these very maps.
-/

noncomputable section
universe u
open CategoryTheory ModuleCat

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The original module-adic completion functor, with its actual completed
scalar action and the original maps on compatible quotient sequences. -/
def moduleAdicCompletionFunctor (J : Ideal R) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} (AdicCompletion J R) where
  obj M := ModuleCat.of (AdicCompletion J R) (AdicCompletion J M)
  map f := ModuleCat.ofHom (AdicCompletion.map J f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    exact AdicCompletion.map_id J M
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact (AdicCompletion.map_comp J f.hom g.hom).symm

instance (J : Ideal R) : (moduleAdicCompletionFunctor J).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    exact (AdicCompletion.map J).map_add f.hom g.hom

variable [IsLocalRing R] [IsNoetherianRing R]

/-- Restrict actual module completion to the original `DA` objects. -/
def matlisCompleteCompletionFunctor : MatlisCompleteModuleCat R ⥤
    MatlisCompleteModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  (matlisCompleteModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R)).lift
    ((matlisCompleteModuleProperty R).ι ⋙ moduleAdicCompletionFunctor (IsLocalRing.maximalIdeal R))
    (fun M ↦ matlisComplete_completion_obj M.obj M.property)

/-- The inverse functor retains the existing completed action and simply
restricts it along the original completion ring map. -/
def matlisCompleteCompletionRestriction :
    MatlisCompleteModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R) ⥤
      MatlisCompleteModuleCat R :=
  (matlisCompleteModuleProperty R).lift
    ((matlisCompleteModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R)).ι ⋙
      restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))
    (fun M ↦ matlisComplete_completion_restrict M.obj M.property)

/-- The original completion equivalence on the underlying module of a `DA` object. -/
def matlisCompleteCompletionUnitComponent (M : MatlisCompleteModuleCat R) :
    M ≅ ((matlisCompleteCompletionFunctor (R := R)) ⋙
      matlisCompleteCompletionRestriction (R := R)).obj M := by
  have : IsAdicComplete (IsLocalRing.maximalIdeal R) M.obj := M.property.2
  exact ObjectProperty.isoMk _
    (AdicCompletion.ofLinearEquiv (IsLocalRing.maximalIdeal R) M.obj).toModuleIso

@[simp]
theorem matlisCompleteCompletionUnitComponent_apply
    (M : MatlisCompleteModuleCat R) (x : M.obj) :
    (matlisCompleteCompletionUnitComponent M).hom.hom x =
      AdicCompletion.of (IsLocalRing.maximalIdeal R) M.obj x := rfl

/-- Naturality of the actual original completion maps. -/
def matlisCompleteCompletionUnitIso : 𝟭 (MatlisCompleteModuleCat R) ≅
    matlisCompleteCompletionFunctor (R := R) ⋙ matlisCompleteCompletionRestriction (R := R) :=
  NatIso.ofComponents matlisCompleteCompletionUnitComponent (by
    intro M N f
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

section Counit

variable (M : MatlisCompleteModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R))

local instance : Module R M.obj := Module.compHom M.obj
  (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
local instance : IsScalarTower R (AdicCompletion (IsLocalRing.maximalIdeal R) R) M.obj :=
  IsScalarTower.of_compHom R (AdicCompletion (IsLocalRing.maximalIdeal R) R) M.obj
local instance : IsAdicComplete (IsLocalRing.maximalIdeal R) M.obj :=
  (matlisComplete_completion_restrict M.obj M.property).2

/-- The counit is the inverse of the original completion map, with genuine
linearity for the pre-existing completed scalar action. -/
def matlisCompleteCompletionCounitComponent :
    ((matlisCompleteCompletionRestriction (R := R)) ⋙
      matlisCompleteCompletionFunctor (R := R)).obj M ≅ M :=
  ObjectProperty.isoMk _
    (completionOfLinearEquiv (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing M.obj).symm.toModuleIso

@[simp]
theorem matlisCompleteCompletionCounitComponent_apply_of (x : M.obj) :
    (matlisCompleteCompletionCounitComponent M).hom.hom
      (AdicCompletion.of (IsLocalRing.maximalIdeal R)
        ((restrictScalars (algebraMap R
          (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj M.obj) x) = x :=
  (completionOfLinearEquiv (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing M.obj).symm_apply_apply x

@[simp]
theorem matlisCompleteCompletionCounitComponent_inv_apply (x : M.obj) :
    (matlisCompleteCompletionCounitComponent M).inv.hom x =
      AdicCompletion.of (IsLocalRing.maximalIdeal R)
        ((restrictScalars (algebraMap R
          (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj M.obj) x := rfl

end Counit

/-- The inverse completion maps are natural for all original completed-linear maps. -/
def matlisCompleteCompletionCounitIso :
    matlisCompleteCompletionRestriction (R := R) ⋙ matlisCompleteCompletionFunctor (R := R) ≅
      𝟭 (MatlisCompleteModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :=
  NatIso.ofComponents matlisCompleteCompletionCounitComponent (by
    intro M N f
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let m := IsLocalRing.maximalIdeal R
    let ρ := algebraMap R (AdicCompletion m R)
    have : IsAdicComplete m ((restrictScalars ρ).obj M.obj) :=
      (matlisComplete_completion_restrict M.obj M.property).2
    obtain ⟨y, rfl⟩ := AdicCompletion.of_surjective m ((restrictScalars ρ).obj M.obj) x
    change (matlisCompleteCompletionCounitComponent N).hom.hom
      (AdicCompletion.map m ((restrictScalars ρ).map f.hom).hom
        (AdicCompletion.of m ((restrictScalars ρ).obj M.obj) y)) =
      f.hom ((matlisCompleteCompletionCounitComponent M).hom.hom
        (AdicCompletion.of m ((restrictScalars ρ).obj M.obj) y))
    rw [AdicCompletion.map_of, matlisCompleteCompletionCounitComponent_apply_of,
      matlisCompleteCompletionCounitComponent_apply_of]
    rfl)

/-- **IV.5.1, `DA` completion transport.** The literal complete-module
categories are equivalent by actual module completion and scalar restriction. -/
def matlisCompleteCompletionEquivalence : MatlisCompleteModuleCat R ≌
    MatlisCompleteModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R) where
  functor := matlisCompleteCompletionFunctor
  inverse := matlisCompleteCompletionRestriction
  unitIso := matlisCompleteCompletionUnitIso
  counitIso := matlisCompleteCompletionCounitIso
  functor_unitIso_comp M := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have : IsAdicComplete (IsLocalRing.maximalIdeal R) M.obj := M.property.2
    obtain ⟨y, rfl⟩ := AdicCompletion.of_surjective (IsLocalRing.maximalIdeal R) M.obj x
    change (matlisCompleteCompletionCounitComponent
      ((matlisCompleteCompletionFunctor (R := R)).obj M)).hom.hom
        (AdicCompletion.map (IsLocalRing.maximalIdeal R)
          (matlisCompleteCompletionUnitComponent M).hom.hom.hom
            (AdicCompletion.of (IsLocalRing.maximalIdeal R) M.obj y)) = _
    rw [AdicCompletion.map_of]
    exact matlisCompleteCompletionCounitComponent_apply_of
      ((matlisCompleteCompletionFunctor (R := R)).obj M)
      (AdicCompletion.of (IsLocalRing.maximalIdeal R) M.obj y)

/-- Forgetting properties leaves actual module-adic completion, not tensor extension. -/
theorem matlisCompleteCompletionEquivalence_functor_forget :
    (matlisCompleteCompletionEquivalence (R := R)).functor ⋙
        (matlisCompleteModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R)).ι =
      (matlisCompleteModuleProperty R).ι ⋙
        moduleAdicCompletionFunctor (IsLocalRing.maximalIdeal R) := rfl

/-- Forgetting properties leaves the original scalar restriction functor. -/
theorem matlisCompleteCompletionEquivalence_inverse_forget :
    (matlisCompleteCompletionEquivalence (R := R)).inverse ⋙
        (matlisCompleteModuleProperty R).ι =
      (matlisCompleteModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R)).ι ⋙
        restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) := rfl

@[simp]
theorem matlisCompleteCompletionEquivalence_unit_apply
    (M : MatlisCompleteModuleCat R) (x : M.obj) :
    ((matlisCompleteCompletionEquivalence (R := R)).unitIso.hom.app M).hom x =
      AdicCompletion.of (IsLocalRing.maximalIdeal R) M.obj x := rfl

@[simp]
theorem matlisCompleteCompletionEquivalence_counit_apply_of
    (M : MatlisCompleteModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R)) (x : M.obj) :
    ((matlisCompleteCompletionEquivalence (R := R)).counitIso.hom.app M).hom
      (AdicCompletion.of (IsLocalRing.maximalIdeal R)
        ((restrictScalars (algebraMap R
          (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj M.obj) x) = x :=
  matlisCompleteCompletionCounitComponent_apply_of M x

/-- The source's equivalent finite-completed-module formulation follows
from the literal `DA` equivalence and the proved complete-base identification. -/
def matlisCompleteFiniteCompletionEquivalence :
    MatlisCompleteModuleCat R ≌ FGModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  (matlisCompleteCompletionEquivalence (R := R)).trans
    (matlisCompleteFiniteEquivalence (R := AdicCompletion (IsLocalRing.maximalIdeal R) R))

end SGA.SGA2.ExposeIV
