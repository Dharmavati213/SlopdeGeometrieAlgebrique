/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorEvaluation
import SGA.SGA2.ExposeIV.SupportedStageRepresentation

/-!
# SGA 2, IV.1.3: representation of supported left-exact functors

The canonical map to Hom into the actual colimit `colim T(R/Jⁿ)` is an
isomorphism precisely when the original additive functor is left exact.
Stagewise representation, compatibility, monicity of colimit inclusions,
and factorization of finite-module maps are proved in the imported files.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- Left exactness makes the original canonical colimit evaluation injective. -/
theorem supportedFunctorEvaluation_injective [PreservesFiniteLimits T]
    (M : SupportedFGModuleCat J) : Function.Injective (supportedFunctorEvaluation J T M) := by
  obtain ⟨n, hn⟩ := supportedFinite_exists_pow_annihilator J M
  intro t s h
  apply (supportedStageEvaluation_bijective J T M n hn).injective
  apply (cancel_mono (supportedFunctorColimitι J T n)).mp
  rw [supportedFunctorEvaluation_eq_stage J T M n hn] at h
  exact h

/-- Every map into the actual colimit is represented by an element of the
original functor value: factor through a stage and apply IV.1.1 there. -/
theorem supportedFunctorEvaluation_surjective [PreservesFiniteLimits T]
    (M : SupportedFGModuleCat J) : Function.Surjective (supportedFunctorEvaluation J T M) := by
  intro f
  obtain ⟨n, hn⟩ := supportedFinite_exists_pow_annihilator J M
  obtain ⟨m, g, hg⟩ := supportedFunctorColimit_exists_factor J T M.obj.obj f
  have hk : J ^ max n m ≤ Module.annihilator R M.obj :=
    (Ideal.pow_le_pow_right (le_max_left n m)).trans hn
  obtain ⟨t, ht⟩ := (supportedStageEvaluation_bijective J T M (max n m) hk).surjective
    (g ≫ supportedFunctorTransition J T (le_max_right n m))
  refine ⟨t, ?_⟩
  rw [supportedFunctorEvaluation_eq_stage J T M (max n m) hk]
  change supportedStageEvaluation J T M (max n m) hk t ≫
    supportedFunctorColimitι J T (max n m) = f
  rw [ht, Category.assoc, supportedFunctorColimitι_transition, hg]

instance [PreservesFiniteLimits T] (M : (SupportedFGModuleCat J)ᵒᵖ) :
    IsIso ((supportedFunctorEvaluationNatTrans J T).app M) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨supportedFunctorEvaluation_injective J T M.unop,
      supportedFunctorEvaluation_surjective J T M.unop⟩

instance [PreservesFiniteLimits T] : IsIso (supportedFunctorEvaluationNatTrans J T) :=
  NatIso.isIso_of_isIso_app _

/-- The canonical module-valued representation uses the actual colimit. -/
def supportedFunctorRepresentationIso [PreservesFiniteLimits T] :
    additiveFunctorModuleLift (R := R) T ≅
      supportedModuleHomFunctor J (supportedFunctorColimit J T) :=
  asIso (supportedFunctorEvaluationNatTrans J T)

/-- **IV.1.3:** the original canonical evaluation into `colim T(R/Jⁿ)` is
an isomorphism if and only if the original additive functor is left exact. -/
theorem additiveSupportedFunctorEvaluation_isIso_iff :
    IsIso (additiveSupportedFunctorEvaluationNatTrans J T) ↔ PreservesFiniteLimits T := by
  constructor
  · intro h
    have := comp_preservesFiniteLimits
      (supportedModuleHomFunctor J (supportedFunctorColimit J T))
      (forget₂ (ModuleCat R) AddCommGrpCat)
    exact preservesFiniteLimits_of_natIso
      (asIso (additiveSupportedFunctorEvaluationNatTrans J T)).symm
  · intro h
    unfold additiveSupportedFunctorEvaluationNatTrans
    infer_instance

/-- The specified canonical representation of the original abelian-group-valued
functor. Its target is the actual supported colimit, with no finiteness
condition on that representing module. -/
def additiveSupportedFunctorRepresentationIso [PreservesFiniteLimits T] :
    T ≅ supportedModuleHomFunctor J (supportedFunctorColimit J T) ⋙
      forget₂ (ModuleCat R) AddCommGrpCat := by
  letI := (additiveSupportedFunctorEvaluation_isIso_iff J T).mpr inferInstance
  exact asIso (additiveSupportedFunctorEvaluationNatTrans J T)

end SGA.SGA2.ExposeIV
