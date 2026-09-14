/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorColimit
import SGA.SGA2.ExposeIV.SupportedStageEvaluation
import SGA.SGA2.ExposeIV.FiniteModuleRepresentation

/-!
# The canonical supported-functor evaluation into the actual colimit

This constructs IV.1.3's original map `φ_T`, before imposing left exactness.
Choosing a power annihilating a finite module gives its stage evaluation;
transition compatibility proves that the resulting colimit-valued map is
independent of this choice and natural in the original finite module.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The actual linear Hom functor on finite supported modules. -/
def supportedModuleHomFunctor (J : Ideal R) (H : ModuleCat.{u} R) :
    (SupportedFGModuleCat J)ᵒᵖ ⥤ ModuleCat.{u} R :=
  (supportedFiniteInclusion J).op ⋙ finiteModuleHomFunctor H

instance (J : Ideal R) (H : ModuleCat.{u} R) : (supportedModuleHomFunctor J H).Additive := by
  unfold supportedModuleHomFunctor
  infer_instance

instance (J : Ideal R) (H : ModuleCat.{u} R) :
    PreservesFiniteLimits (supportedModuleHomFunctor J H) := by
  have := preservesFiniteLimits_op (supportedFiniteInclusion J)
  unfold supportedModuleHomFunctor
  exact comp_preservesFiniteLimits _ _

variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- Evaluation through one annihilating stage, followed by its actual
colimit structural map. -/
def supportedColimitStageEvaluation (M : SupportedFGModuleCat J) (n : ℕ)
    (hn : J ^ n ≤ Module.annihilator R M.obj) :
    (additiveFunctorModuleLift (R := R) T).obj (op M) →ₗ[R]
      (M.obj.obj ⟶ supportedFunctorColimit J T) where
  toFun t := supportedStageEvaluation J T M n hn t ≫ supportedFunctorColimitι J T n
  map_add' t s := by rw [_root_.map_add, Preadditive.add_comp]
  map_smul' r t := by rw [_root_.map_smul, Linear.smul_comp]; rfl

@[simp] theorem supportedColimitStageEvaluation_apply (M : SupportedFGModuleCat J) (n : ℕ)
    (hn : J ^ n ≤ Module.annihilator R M.obj)
    (t : (additiveFunctorModuleLift (R := R) T).obj (op M)) (x : M.obj) :
    supportedColimitStageEvaluation J T M n hn t x =
      supportedFunctorColimitι J T n (supportedStageEvaluation J T M n hn t x) := rfl

/-- Passing to a larger annihilating power gives the same colimit-valued map. -/
theorem supportedColimitStageEvaluation_eq_of_le (M : SupportedFGModuleCat J) {n m : ℕ}
    (hn : J ^ n ≤ Module.annihilator R M.obj)
    (hm : J ^ m ≤ Module.annihilator R M.obj) (h : n ≤ m) :
    supportedColimitStageEvaluation J T M n hn = supportedColimitStageEvaluation J T M m hm := by
  ext t x
  change (supportedStageEvaluation J T M n hn t ≫ supportedFunctorColimitι J T n) x =
    (supportedStageEvaluation J T M m hm t ≫ supportedFunctorColimitι J T m) x
  rw [← supportedFunctorColimitι_transition J T h, ← Category.assoc,
    supportedStageEvaluation_transition_hom J T M hn hm h]

/-- The map does not depend on the annihilating power. -/
theorem supportedColimitStageEvaluation_independent (M : SupportedFGModuleCat J) (n m : ℕ)
    (hn : J ^ n ≤ Module.annihilator R M.obj)
    (hm : J ^ m ≤ Module.annihilator R M.obj) :
    supportedColimitStageEvaluation J T M n hn = supportedColimitStageEvaluation J T M m hm := by
  have hk : J ^ max n m ≤ Module.annihilator R M.obj :=
    (Ideal.pow_le_pow_right (le_max_left n m)).trans hn
  exact (supportedColimitStageEvaluation_eq_of_le J T M hn hk (le_max_left n m)).trans
    (supportedColimitStageEvaluation_eq_of_le J T M hm hk (le_max_right n m)).symm

/-- The canonical map to Hom into the actual colimit. The apparent choice
of an annihilating power is eliminated by `supportedFunctorEvaluation_eq_stage`. -/
def supportedFunctorEvaluation (M : SupportedFGModuleCat J) :
    (additiveFunctorModuleLift (R := R) T).obj (op M) →ₗ[R]
      (M.obj.obj ⟶ supportedFunctorColimit J T) :=
  supportedColimitStageEvaluation J T M
    (supportedFinite_exists_pow_annihilator J M).choose
    (supportedFinite_exists_pow_annihilator J M).choose_spec

/-- Any annihilating power computes the original canonical evaluation. -/
theorem supportedFunctorEvaluation_eq_stage (M : SupportedFGModuleCat J) (n : ℕ)
    (hn : J ^ n ≤ Module.annihilator R M.obj) :
    supportedFunctorEvaluation J T M = supportedColimitStageEvaluation J T M n hn :=
  supportedColimitStageEvaluation_independent J T M _ n _ hn

/-- Naturality in every morphism of actual finite supported modules. -/
theorem supportedFunctorEvaluation_naturality {M N : SupportedFGModuleCat J}
    (f : M ⟶ N) (t : (additiveFunctorModuleLift (R := R) T).obj (op N)) (x : M.obj) :
    supportedFunctorEvaluation J T M (T.map f.op t) x =
      supportedFunctorEvaluation J T N t (f.hom.hom x) := by
  obtain ⟨n, hn⟩ := supportedFinite_exists_pow_annihilator J M
  obtain ⟨m, hm⟩ := supportedFinite_exists_pow_annihilator J N
  have hM : J ^ max n m ≤ Module.annihilator R M.obj :=
    (Ideal.pow_le_pow_right (le_max_left n m)).trans hn
  have hN : J ^ max n m ≤ Module.annihilator R N.obj :=
    (Ideal.pow_le_pow_right (le_max_right n m)).trans hm
  rw [supportedFunctorEvaluation_eq_stage J T M _ hM,
    supportedFunctorEvaluation_eq_stage J T N _ hN,
    supportedColimitStageEvaluation_apply, supportedColimitStageEvaluation_apply,
    supportedStageEvaluation_naturality J T _ hM hN f]

/-- The original canonical evaluation as a natural transformation of
module-valued functors. -/
def supportedFunctorEvaluationNatTrans :
    additiveFunctorModuleLift (R := R) T ⟶
      supportedModuleHomFunctor J (supportedFunctorColimit J T) where
  app M := ModuleCat.ofHom (X := (additiveFunctorModuleLift (R := R) T).obj M)
    (Y := (supportedModuleHomFunctor J (supportedFunctorColimit J T)).obj M)
    (supportedFunctorEvaluation J T M.unop)
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact supportedFunctorEvaluation_naturality J T f.unop t x

/-- **IV.1.3, construction:** the natural map from the original additive
abelian-group-valued functor to Hom into `colim T(R/Jⁿ)`. -/
def additiveSupportedFunctorEvaluationNatTrans :
    T ⟶ supportedModuleHomFunctor J (supportedFunctorColimit J T) ⋙
      forget₂ (ModuleCat R) AddCommGrpCat :=
  (additiveFunctorModuleLiftForgetIso (R := R) T).inv ≫
    whiskerRight (supportedFunctorEvaluationNatTrans J T) (forget₂ (ModuleCat R) AddCommGrpCat)

end SGA.SGA2.ExposeIV
