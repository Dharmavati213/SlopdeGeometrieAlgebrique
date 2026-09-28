/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.CofiniteFunctorEvaluation
import SGA.SGA2.ExposeIV.CofiniteStageRepresentation

/-!
# Nonlocal representation by the actual cofinite-ideal colimit

The original canonical evaluation into `Hom_R(-, colim_I T(R/I))` is an
isomorphism precisely when the original additive functor on finite-length
modules is left exact. The actual stage evaluation is invertible by IV.1.1
over the cofinite quotient ring. Original injective stage inclusions and
finite-source factorization prove global bijectivity.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable (T : (FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- Original evaluation is injective for a left-exact functor. -/
theorem cofiniteFunctorEvaluation_injective [PreservesFiniteLimits T]
    (M : FiniteLengthModuleCat R) : Function.Injective (cofiniteFunctorEvaluation T M) := by
  let I := cofiniteAnnihilator M.obj M.property
  have hI : I.val ≤ Module.annihilator R M.obj := le_rfl
  intro t s h
  apply (cofiniteStageEvaluation_bijective T M I hI).injective
  apply (cancel_mono (cofiniteFunctorColimitι T I)).mp
  rw [cofiniteFunctorEvaluation_eq_stage T M I hI] at h
  exact h

/-- Every actual map into the colimit comes from the original functor
value: factor through one stage and evaluate over a common cofinite ideal. -/
theorem cofiniteFunctorEvaluation_surjective [PreservesFiniteLimits T]
    (M : FiniteLengthModuleCat R) : Function.Surjective (cofiniteFunctorEvaluation T M) := by
  intro f
  let I := cofiniteAnnihilator M.obj M.property
  obtain ⟨J, g, hg⟩ := cofiniteFunctorColimit_exists_factor T M.obj f
  have hK : (I ⊔ J).val ≤ Module.annihilator R M.obj := inf_le_left
  obtain ⟨t, ht⟩ := (cofiniteStageEvaluation_bijective T M (I ⊔ J) hK).surjective
    (g ≫ cofiniteFunctorTransition T le_sup_right)
  refine ⟨t, ?_⟩
  rw [cofiniteFunctorEvaluation_eq_stage T M (I ⊔ J) hK]
  change cofiniteStageEvaluation T M (I ⊔ J) hK t ≫ cofiniteFunctorColimitι T (I ⊔ J) = f
  rw [ht, Category.assoc, cofiniteFunctorColimitι_transition, hg]

instance [PreservesFiniteLimits T] (M : (FiniteLengthModuleCat R)ᵒᵖ) :
    IsIso ((cofiniteFunctorEvaluationNatTrans T).app M) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨cofiniteFunctorEvaluation_injective T M.unop,
      cofiniteFunctorEvaluation_surjective T M.unop⟩

instance [PreservesFiniteLimits T] : IsIso (cofiniteFunctorEvaluationNatTrans T) :=
  NatIso.isIso_of_isIso_app _

/-- The module-valued representation retains the original canonical actions. -/
def cofiniteFunctorRepresentationIso [PreservesFiniteLimits T] :
    additiveFunctorModuleLift (R := R) T ≅
      finiteLengthModuleHomFunctor (cofiniteFunctorColimit T) :=
  asIso (cofiniteFunctorEvaluationNatTrans T)

/-- The original canonical evaluation represents the additive functor
exactly when that functor is left exact. -/
theorem additiveCofiniteFunctorEvaluation_isIso_iff :
    IsIso (additiveCofiniteFunctorEvaluationNatTrans T) ↔ PreservesFiniteLimits T := by
  constructor
  · intro h
    have := comp_preservesFiniteLimits
      (finiteLengthModuleHomFunctor (cofiniteFunctorColimit T))
      (forget₂ (ModuleCat R) AddCommGrpCat)
    exact preservesFiniteLimits_of_natIso
      (asIso (additiveCofiniteFunctorEvaluationNatTrans T)).symm
  · intro h
    unfold additiveCofiniteFunctorEvaluationNatTrans
    infer_instance

/-- **IV.4.2, nonlocal representation:** every original additive left-exact
functor on finite-length modules is represented by its actual cofinite-ideal
colimit through original canonical evaluation. -/
def additiveCofiniteFunctorRepresentationIso [PreservesFiniteLimits T] :
    T ≅ finiteLengthModuleHomFunctor (cofiniteFunctorColimit T) ⋙
      forget₂ (ModuleCat R) AddCommGrpCat := by
  letI := (additiveCofiniteFunctorEvaluation_isIso_iff T).mpr inferInstance
  exact asIso (additiveCofiniteFunctorEvaluationNatTrans T)

end SGA.SGA2.ExposeIV
