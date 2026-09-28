/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedCompletionEquivalence
import SGA.SGA2.ExposeIV.LocalArtinianFiniteIdeal

/-!
# IV.4.5: equivalence of the actual locally Artinian module categories

Locally Artinian means literally that every finitely generated submodule is
Artinian. Original extension and restriction of scalars give quasi-inverse
equivalences for this property. The completed ring is not assumed noetherian
as an additional hypothesis: finite generation of its actual maximal ideal
suffices for the support characterization used here.
-/

noncomputable section
universe u
open CategoryTheory ModuleCat

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

/-- The literal locally Artinian property on actual module objects. -/
def locallyArtinianModuleProperty (R : Type u) [CommRing R] :
    ObjectProperty (ModuleCat.{u} R) := fun M => ModuleLocallyArtinian (R := R) M

/-- The source's category of all locally Artinian modules. -/
abbrev LocallyArtinianModuleCat (R : Type u) [CommRing R] :=
  (locallyArtinianModuleProperty R).FullSubcategory

variable {R : Type u} [CommRing R]

/-- The identity-on-modules identification when the literal local Artinian
property is characterized by support on a specified closed subset. -/
def locallyArtinianSupportEquivalence (J : Ideal R)
    (h : ∀ M : ModuleCat.{u} R, ModuleLocallyArtinian (R := R) M ↔
      supportedModuleProperty J M) :
    LocallyArtinianModuleCat R ≌ SupportedModuleCat J where
  functor := (supportedModuleProperty J).lift (locallyArtinianModuleProperty R).ι
    (fun M => (h M.obj).mp M.property)
  inverse := (locallyArtinianModuleProperty R).lift (supportedModuleProperty J).ι
    (fun M => (h M.obj).mpr M.property)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable [IsNoetherianRing R] [IsLocalRing R]

/-- The completed-ring locally Artinian property equals actual support on
the mapped maximal ideal, derived without extra noetherianity assumptions. -/
theorem completion_locallyArtinian_iff_supported
    (M : ModuleCat.{u} (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
    ModuleLocallyArtinian (R := AdicCompletion (IsLocalRing.maximalIdeal R) R) M ↔
      supportedModuleProperty ((IsLocalRing.maximalIdeal R).map
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))) M := by
  have hm : (IsLocalRing.maximalIdeal
      (AdicCompletion (IsLocalRing.maximalIdeal R) R)).FG := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing.map _
  rw [supportedModuleProperty, ← AdicCompletion.maximalIdeal_eq_map]
  exact moduleLocallyArtinian_iff_support_maximalIdeal_of_fg hm M

/-- **SGA 2, IV.4.5, categorical conclusion.** Actual scalar extension and
restriction identify the two actual categories of locally Artinian modules. -/
def localArtinianCompletionEquivalence :
    LocallyArtinianModuleCat R ≌
      LocallyArtinianModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  (locallyArtinianSupportEquivalence (IsLocalRing.maximalIdeal R)
      (fun M => moduleLocallyArtinian_iff_support_maximalIdeal M)).trans
    ((supportedCompletionEquivalence (IsLocalRing.maximalIdeal R)).trans
      (locallyArtinianSupportEquivalence _
        (completion_locallyArtinian_iff_supported (R := R))).symm)

/-- Forgetting the recorded property leaves precisely original tensor extension. -/
theorem localArtinianCompletionEquivalence_functor_forget :
    (localArtinianCompletionEquivalence (R := R)).functor ⋙
        (locallyArtinianModuleProperty
          (AdicCompletion (IsLocalRing.maximalIdeal R) R)).ι =
      (locallyArtinianModuleProperty R).ι ⋙
        extendScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) := rfl

/-- Forgetting the recorded property leaves precisely original restriction. -/
theorem localArtinianCompletionEquivalence_inverse_forget :
    (localArtinianCompletionEquivalence (R := R)).inverse ⋙
        (locallyArtinianModuleProperty R).ι =
      (locallyArtinianModuleProperty
        (AdicCompletion (IsLocalRing.maximalIdeal R) R)).ι ⋙
        restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) := rfl

end SGA.SGA2.ExposeIV
