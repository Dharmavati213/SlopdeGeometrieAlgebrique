/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleOpenRestrictionInjectives
import SGA.SGA2.ExposeVI.SchemeInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Exact open restriction of module sheaves

The actual restriction to the open slice site is additive and exact and
preserves injective objects. These properties allow local module Ext to
be computed by restricting a global injective resolution.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (U : Opens X)

/-- Restriction to the actual sheaf of rings on the open slice site. -/
def moduleOpenRestriction : SheafOfModules.{u} R ⥤ SheafOfModules.{u} (R.over U) :=
  SheafOfModules.overFunctor R U

instance moduleOpenRestriction_additive : (moduleOpenRestriction R U).Additive where
  map_add := rfl

instance moduleOpenRestriction_isLeftAdjoint : (moduleOpenRestriction R U).IsLeftAdjoint := by
  dsimp [moduleOpenRestriction, SheafOfModules.overFunctor]
  infer_instance

instance moduleOpenRestriction_isRightAdjoint : (moduleOpenRestriction R U).IsRightAdjoint := by
  dsimp [moduleOpenRestriction, SheafOfModules.overFunctor]
  infer_instance

instance moduleOpenRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (moduleOpenRestriction R U) := inferInstance

instance moduleOpenRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (moduleOpenRestriction R U) := inferInstance

/-- Actual open restriction preserves exact sequences. -/
instance moduleOpenRestriction_preservesHomology :
    (moduleOpenRestriction R U).PreservesHomology := inferInstance

/-- Actual open restriction preserves injective module sheaves. -/
instance moduleOpenRestriction_preservesInjectiveObjects :
    (moduleOpenRestriction R U).PreservesInjectiveObjects where
  injective_obj {N} hN := by
    let := hN
    exact moduleOpenRestriction_injective U R N

end SGA.SGA2.ExposeVI
