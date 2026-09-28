/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.CompletionHomDuality
import SGA.SGA2.ExposeIV.FiniteSupportedCompletionEquivalence
import SGA.SGA2.ExposeIV.SupportedDualityTransport

/-! # IV.4.6: transfer of actual supported Hom duality through completion

The original finite-Hom and canonical-evaluation conditions are equivalent
under actual scalar restriction. Tensor extension gives the inverse transfer
using its original unit. In the local case this proves IV.4.6 for the named
supported dualizing modules; no noetherianity of the completion is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite ModuleCat

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R)

/-- Finiteness of all original supported Hom values transfers in both
directions along actual completion restriction. -/
theorem completion_finiteSupportedHomValues_iff
    (H : ModuleCat.{u} (AdicCompletion J R))
    (hH : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) H) :
    FiniteSupportedHomValues (J.map (algebraMap R (AdicCompletion J R))) H ↔
      FiniteSupportedHomValues J ((restrictScalars (algebraMap R (AdicCompletion J R))).obj H) := by
  let f := algebraMap R (AdicCompletion J R)
  constructor
  · intro hfin M hM hsM
    let := hM
    let N := (extendScalars f).obj M
    have : Module.Finite (AdicCompletion J R) N := extendScalars_finite f M
    have hsN := supported_extendScalars f J J.fg_of_isNoetherianRing M hsM
    have hd : Module.Finite R ((moduleHomDual ((restrictScalars f).obj H)).obj
        (op ((extendScalars f ⋙ restrictScalars f).obj M))) :=
      (completion_moduleHomDual_finite_iff J H N hH hsN).mp (hfin N inferInstance hsN)
    let := hd
    let := completion_unit_isIso J M hsM
    let e := (moduleHomDual ((restrictScalars f).obj H)).mapIso
      (asIso ((extendRestrictScalarsAdj f).unit.app M)).op
    exact Module.Finite.of_surjective e.hom.hom e.toLinearEquiv.surjective
  · intro hfin M hM hsM
    let := hM
    have := completion_restrictScalars_finite J M hsM
    exact (completion_moduleHomDual_finite_iff J H M hH hsM).mpr
      (hfin ((restrictScalars f).obj M) inferInstance
        ((supported_restrictScalars_iff f J J.fg_of_isNoetherianRing M).mpr hsM))

/-- All original canonical bidual evaluations transfer in both directions.
For arbitrary base-ring tests, the input comparison is the actual tensor unit. -/
theorem completion_supportedModuleBiduality_iff
    (H : ModuleCat.{u} (AdicCompletion J R))
    (hH : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) H) :
    SupportedModuleBiduality (J.map (algebraMap R (AdicCompletion J R))) H ↔
      SupportedModuleBiduality J ((restrictScalars (algebraMap R (AdicCompletion J R))).obj H) := by
  let f := algebraMap R (AdicCompletion J R)
  constructor
  · intro hbid M hM hsM
    let := hM
    let N := (extendScalars f).obj M
    have : Module.Finite (AdicCompletion J R) N := extendScalars_finite f M
    have hsN := supported_extendScalars f J J.fg_of_isNoetherianRing M hsM
    have : IsIso (moduleBidualEvaluation ((restrictScalars f).obj H)
        ((extendScalars f ⋙ restrictScalars f).obj M)) :=
      (completion_moduleBidualEvaluation_isIso_iff J H N hH hsN).mp (hbid N inferInstance hsN)
    let := completion_unit_isIso J M hsM
    exact moduleBidualEvaluation_isIso_of_testIso ((restrictScalars f).obj H)
      (asIso ((extendRestrictScalarsAdj f).unit.app M)).symm
  · intro hbid M hM hsM
    let := hM
    have := completion_restrictScalars_finite J M hsM
    exact (completion_moduleBidualEvaluation_isIso_iff J H M hH hsM).mpr
      (hbid ((restrictScalars f).obj M) inferInstance
        ((supported_restrictScalars_iff f J J.fg_of_isNoetherianRing M).mpr hsM))

variable [IsLocalRing R]

/-- **IV.4.6, restriction:** the original supported dualizing-module property
over the completed local ring is equivalent to that over the original ring.
The Hom modules and canonical bidual maps are the actual ones on both sides. -/
theorem completion_supportedDualizingModule_iff
    (H : ModuleCat.{u} (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
    SupportedDualizingModule H ↔
      SupportedDualizingModule
        ((restrictScalars
          (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj H) := by
  simp only [SupportedDualizingModule, AdicCompletion.maximalIdeal_eq_map]
  let J := IsLocalRing.maximalIdeal R
  let f := algebraMap R (AdicCompletion J R)
  constructor
  · rintro ⟨hs, hf, hb⟩
    exact ⟨(supported_restrictScalars_iff f J J.fg_of_isNoetherianRing H).mpr hs,
      (completion_finiteSupportedHomValues_iff J H hs).mp hf,
      (completion_supportedModuleBiduality_iff J H hs).mp hb⟩
  · rintro ⟨hs, hf, hb⟩
    have hH := (supported_restrictScalars_iff f J J.fg_of_isNoetherianRing H).mp hs
    exact ⟨hH, (completion_finiteSupportedHomValues_iff J H hH).mpr hf,
      (completion_supportedModuleBiduality_iff J H hH).mpr hb⟩

/-- **IV.4.6, tensor extension:** tensoring the original supported dualizing
module with the completed ring again gives a supported dualizing module. -/
theorem SupportedDualizingModule.completion {H : ModuleCat.{u} R}
    (hH : SupportedDualizingModule H) :
    SupportedDualizingModule
      ((extendScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj H) := by
  let J := IsLocalRing.maximalIdeal R
  let f := algebraMap R (AdicCompletion J R)
  apply (completion_supportedDualizingModule_iff ((extendScalars f).obj H)).mpr
  let := completion_unit_isIso J H hH.1
  exact SupportedDualizingModule.of_iso (asIso ((extendRestrictScalarsAdj f).unit.app H)) hH

/-- For any supported module, tensor extension preserves and reflects the
original dualizing property, via the literal tensor unit rather than module completion. -/
theorem completion_tensor_supportedDualizingModule_iff (H : ModuleCat.{u} R)
    (hH : supportedModuleProperty (IsLocalRing.maximalIdeal R) H) :
    SupportedDualizingModule
        ((extendScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj H) ↔
      SupportedDualizingModule H := by
  let J := IsLocalRing.maximalIdeal R
  let f := algebraMap R (AdicCompletion J R)
  constructor
  · intro h
    have hr := (completion_supportedDualizingModule_iff ((extendScalars f).obj H)).mp h
    let := completion_unit_isIso J H hH
    exact SupportedDualizingModule.of_iso (asIso ((extendRestrictScalarsAdj f).unit.app H)).symm hr
  · exact SupportedDualizingModule.completion

/-- The isomorphism of original modules in IV.4.6 is the actual tensor unit. -/
def SupportedDualizingModule.completionUnitIso {H : ModuleCat.{u} R}
    (hH : SupportedDualizingModule H) :
    H ≅ (restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj
      ((extendScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj H) := by
  letI := completion_unit_isIso (IsLocalRing.maximalIdeal R) H hH.1
  exact asIso ((extendRestrictScalarsAdj
    (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).unit.app H)

/-- **IV.4.6, underlying groups:** the original module and its tensor
extension have canonically isomorphic additive groups. -/
def SupportedDualizingModule.completionAddEquiv {H : ModuleCat.{u} R}
    (hH : SupportedDualizingModule H) :
    H ≃+ ((extendScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj H) :=
  hH.completionUnitIso.toLinearEquiv.toAddEquiv

/-- The underlying-group comparison is literally `x ↦ 1 ⊗ x`, not the
map to the adic completion of the coefficient module. -/
@[simp]
theorem SupportedDualizingModule.completionAddEquiv_apply {H : ModuleCat.{u} R}
    (hH : SupportedDualizingModule H) (x : H) :
    hH.completionAddEquiv x =
      (1 : AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗ₜ[R] x := rfl

end SGA.SGA2.ExposeIV
