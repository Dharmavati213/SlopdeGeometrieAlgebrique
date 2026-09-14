/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedScalarChange
import SGA.SGA2.ExposeIV.AdicTensorSupported
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Supported-module equivalence under actual adic scalar extension

Extension and restriction of scalars along the original completion map are
inverse equivalences on arbitrary supported modules. The unit is the actual
map `x ↦ 1 ⊗ x`, and the counit is the actual multiplication map. The hypotheses
include neither finite generation of the modules nor noetherianity of the
completed ring as an additional assumption.
-/

noncomputable section
universe u
open CategoryTheory ModuleCat

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R)

/-- The genuine scalar-extension unit on any supported module is invertible. -/
theorem completion_unit_isIso (M : ModuleCat.{u} R)
    (hM : supportedModuleProperty J M) :
    IsIso ((extendRestrictScalarsAdj (algebraMap R (AdicCompletion J R))).unit.app M) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact adicTensorUnit_bijective_of_support J M hM

/-- The original multiplication counit is invertible on supported modules
over the completed ring. This follows from the original triangle identity. -/
theorem completion_counit_isIso (M : ModuleCat.{u} (AdicCompletion J R))
    (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M) :
    IsIso ((extendRestrictScalarsAdj (algebraMap R (AdicCompletion J R))).counit.app M) := by
  let f := algebraMap R (AdicCompletion J R)
  have hR : supportedModuleProperty J ((restrictScalars f).obj M) :=
    (supported_restrictScalars_iff f J J.fg_of_isNoetherianRing M).mpr hM
  let := completion_unit_isIso J ((restrictScalars f).obj M) hR
  have : IsIso ((restrictScalars f).map ((extendRestrictScalarsAdj f).counit.app M)) :=
    isIso_of_hom_comp_eq_id _ ((extendRestrictScalarsAdj f).right_triangle_components M)
  exact isIso_of_reflects_iso _ (restrictScalars f)

/-- Actual extension and restriction of scalars along `R → Â`. -/
def supportedCompletionEquivalence :
    SupportedModuleCat J ≌
      SupportedModuleCat (J.map (algebraMap R (AdicCompletion J R))) := by
  let adj := supportedExtendRestrictScalarsAdj
    (algebraMap R (AdicCompletion J R)) J J.fg_of_isNoetherianRing
  haveI (M : SupportedModuleCat J) : IsIso (adj.unit.app M) := by
    apply (ObjectProperty.isIso_hom_iff _).mp
    change IsIso (((supportedExtendRestrictScalarsAdj _ _ _).unit.app M).hom)
    rw [supportedExtendRestrictScalarsAdj_unit_hom]
    exact completion_unit_isIso J M.obj M.property
  haveI (M : SupportedModuleCat (J.map (algebraMap R (AdicCompletion J R)))) :
      IsIso (adj.counit.app M) := by
    apply (ObjectProperty.isIso_hom_iff _).mp
    change IsIso (((supportedExtendRestrictScalarsAdj _ _ _).counit.app M).hom)
    rw [supportedExtendRestrictScalarsAdj_counit_hom]
    exact completion_counit_isIso J M.obj M.property
  exact adj.toEquivalence

/-- The equivalence uses the original tensor scalar-extension functor. -/
@[simp] theorem supportedCompletionEquivalence_functor :
    (supportedCompletionEquivalence J).functor =
      supportedExtendScalars (algebraMap R (AdicCompletion J R)) J
        J.fg_of_isNoetherianRing := rfl

/-- Its inverse is genuine restriction of scalars, preserving underlying groups. -/
@[simp] theorem supportedCompletionEquivalence_inverse :
    (supportedCompletionEquivalence J).inverse =
      supportedRestrictScalars (algebraMap R (AdicCompletion J R)) J
        J.fg_of_isNoetherianRing := rfl

/-- The original tensor map is the unit of the categorical equivalence. -/
@[simp] theorem supportedCompletionEquivalence_unit_apply
    (M : SupportedModuleCat J) (x : M.obj) :
    ((supportedCompletionEquivalence J).unitIso.hom.app M).hom x =
      (1 : AdicCompletion J R) ⊗ₜ[R] x := by
  change ((supportedExtendRestrictScalarsAdj _ _ _).unit.app M).hom x = _
  rw [supportedExtendRestrictScalarsAdj_unit_hom]
  rfl

end SGA.SGA2.ExposeIV
