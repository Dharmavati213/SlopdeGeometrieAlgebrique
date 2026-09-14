/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.SupportedSectionExactness
import SGA.SGA2.ExposeI.DerivedFunctors
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Right-derived supported sections

This file constructs the original right-derived functors of actual
supported sections. Left exactness and the degree-zero comparison are
proved from the section maps. Comparison with the independently defined
`H_Z = Ext(ℤ_{Z,X}, -)` is a separate assertion.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeI

section Comparison

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasInjectiveResolutions C]

/-- A proved natural isomorphism of additive coefficient functors induces
natural isomorphisms of their actual right-derived functors. -/
def rightDerivedFunctorIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := e.hom.rightDerived n
  inv := e.inv.rightDerived n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

end Comparison

variable {X : TopCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Supported sections preserve finite limits in the coefficient sheaf. -/
instance gammaZSectionsFunctor_preservesFiniteLimits (Z : Closeds X) (U : Opens X) :
    PreservesFiniteLimits (gammaZSectionsFunctor Z U) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr
  intro S hS
  have : Mono S.f := hS.mono_f
  constructor
  · rw [ShortComplex.ab_exact_iff_function_exact]
    exact exact_gammaZSectionsMap_of_shortExact hS Z U
  · exact (AddCommGrpCat.mono_iff_injective _).mpr
      (injective_gammaZSectionsMap_of_mono S.f Z U)

/-- The original right-derived supported-section functors, computed using
injective resolutions in the category of abelian sheaves. -/
def derivedGammaZSections (Z : Closeds X) (U : Opens X) (n : ℕ) :
    Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  (gammaZSectionsFunctor Z U).rightDerived n

/-- Degree zero of the derived functor is naturally actual supported sections. -/
def derivedGammaZSectionsZeroIso (Z : Closeds X) (U : Opens X) :
    derivedGammaZSections Z U 0 ≅ gammaZSectionsFunctor Z U :=
  (gammaZSectionsFunctor Z U).rightDerivedZeroIsoSelf

/-- Higher right-derived supported sections vanish on injective sheaves. -/
theorem derivedGammaZSections_isZero_of_injective (Z : Closeds X) (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] (n : ℕ) :
    IsZero ((derivedGammaZSections Z U (n + 1)).obj F) :=
  (gammaZSectionsFunctor Z U).isZero_rightDerived_obj_injective_succ n F

end SGA.SGA2.ExposeI
