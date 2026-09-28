/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.RingedModuleInjectiveFlasque
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Exactness of forgetting the module structure of a sheaf

The underlying additive-sheaf functor preserves colimits: after precomposition
with module sheafification, it is additive sheafification composed with the
pointwise forgetful functor. Together with preservation of finite limits this
gives exactness, with no flatness hypothesis on the structure sheaf.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- Forgetting to additive sheaves preserves small colimits on any ringed space. -/
instance moduleToSheaf_preservesColimits :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R) := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).preservesColimitsOfSize_iff
    (SheafOfModules.toSheaf R)).mpr
  exact preservesColimits_of_natIso
    (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm

/-- A short exact sequence of module sheaves is short exact as additive sheaves. -/
theorem moduleToSheaf_map_shortExact {S : ShortComplex (SheafOfModules.{u} R)}
    (hS : S.ShortExact) : (S.map (SheafOfModules.toSheaf R)).ShortExact :=
  hS.map_of_exact (SheafOfModules.toSheaf R)

/-- Exactness of forgetting scalars also preserves the homology of complexes. -/
instance moduleToSheaf_preservesHomology :
    (SheafOfModules.toSheaf.{u} R).PreservesHomology :=
  ((Functor.exact_tfae (SheafOfModules.toSheaf.{u} R)).out 1 3).mp
    (fun _ hS ↦ moduleToSheaf_map_shortExact R hS)

end SGA.SGA2.ExposeV
