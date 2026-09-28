/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.CofiniteFunctorColimit
import SGA.SGA2.ExposeIV.CofiniteStageEvaluation

/-!
# Canonical evaluation into the original cofinite-ideal colimit

Every finite-length module has a canonical cofinite annihilator. Evaluation
through that quotient and its original colimit map is independent of any
annihilating cofinite ideal. Intersections prove naturality in the original
finite-length module, without imposing left exactness or representability.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Actual linear Hom on the original finite-length category. -/
def finiteLengthModuleHomFunctor (H : ModuleCat.{u} R) :
    (FiniteLengthModuleCat R)ᵒᵖ ⥤ ModuleCat.{u} R :=
  (finiteLengthInclusion R).op ⋙ moduleHomDual H

instance (H : ModuleCat.{u} R) : (finiteLengthModuleHomFunctor H).Additive := by
  unfold finiteLengthModuleHomFunctor
  infer_instance

instance (H : ModuleCat.{u} R) : (finiteLengthModuleHomFunctor H).Linear R where
  map_smul f r := by
    apply ModuleCat.hom_ext
    ext g
    apply ModuleCat.hom_ext
    ext x
    exact g.hom.map_smul r (f.unop.hom x)

instance (H : ModuleCat.{u} R) : PreservesFiniteLimits (finiteLengthModuleHomFunctor H) := by
  have := preservesFiniteLimits_op (finiteLengthInclusion R)
  unfold finiteLengthModuleHomFunctor
  exact comp_preservesFiniteLimits _ _

variable (T : (FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- Original stage evaluation followed by its actual colimit map. -/
def cofiniteColimitStageEvaluation (M : FiniteLengthModuleCat R) (I : CofiniteIdealIndex R)
    (hI : I.val ≤ Module.annihilator R M.obj) :
    finiteLengthFunctorValue T M →ₗ[R] (M.obj ⟶ cofiniteFunctorColimit T) where
  toFun t := cofiniteStageEvaluation T M I hI t ≫ cofiniteFunctorColimitι T I
  map_add' t s := by rw [_root_.map_add, Preadditive.add_comp]
  map_smul' r t := by rw [_root_.map_smul, Linear.smul_comp]; rfl

@[simp]
theorem cofiniteColimitStageEvaluation_apply (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hI : I.val ≤ Module.annihilator R M.obj)
    (t : finiteLengthFunctorValue T M) (x : M.obj) :
    cofiniteColimitStageEvaluation T M I hI t x =
      cofiniteFunctorColimitι T I (cofiniteStageEvaluation T M I hI t x) := rfl

/-- Shrinking the annihilating cofinite ideal leaves evaluation unchanged. -/
theorem cofiniteColimitStageEvaluation_eq_of_le (M : FiniteLengthModuleCat R)
    {I J : CofiniteIdealIndex R} (hI : I.val ≤ Module.annihilator R M.obj)
    (hJ : J.val ≤ Module.annihilator R M.obj) (h : I ≤ J) :
    cofiniteColimitStageEvaluation T M I hI = cofiniteColimitStageEvaluation T M J hJ := by
  ext t x
  change (cofiniteStageEvaluation T M I hI t ≫ cofiniteFunctorColimitι T I) x =
    (cofiniteStageEvaluation T M J hJ t ≫ cofiniteFunctorColimitι T J) x
  rw [← cofiniteFunctorColimitι_transition T h, ← Category.assoc,
    cofiniteStageEvaluation_transition_hom T M hI hJ h]

/-- The actual map is independent of the annihilating cofinite ideal. -/
theorem cofiniteColimitStageEvaluation_independent (M : FiniteLengthModuleCat R)
    (I J : CofiniteIdealIndex R) (hI : I.val ≤ Module.annihilator R M.obj)
    (hJ : J.val ≤ Module.annihilator R M.obj) :
    cofiniteColimitStageEvaluation T M I hI = cofiniteColimitStageEvaluation T M J hJ := by
  have hK : (I ⊔ J).val ≤ Module.annihilator R M.obj :=
    (show (I ⊔ J).val ≤ I.val from inf_le_left).trans hI
  exact (cofiniteColimitStageEvaluation_eq_of_le T M hI hK le_sup_left).trans
    (cofiniteColimitStageEvaluation_eq_of_le T M hJ hK le_sup_right).symm

/-- Canonical evaluation uses the actual annihilator quotient, not a chosen
presentation or an independently specified representing module. -/
def cofiniteFunctorEvaluation (M : FiniteLengthModuleCat R) :
    finiteLengthFunctorValue T M →ₗ[R] (M.obj ⟶ cofiniteFunctorColimit T) :=
  cofiniteColimitStageEvaluation T M (cofiniteAnnihilator M.obj M.property) le_rfl

/-- Any cofinite ideal annihilating the original source computes this map. -/
theorem cofiniteFunctorEvaluation_eq_stage (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hI : I.val ≤ Module.annihilator R M.obj) :
    cofiniteFunctorEvaluation T M = cofiniteColimitStageEvaluation T M I hI :=
  cofiniteColimitStageEvaluation_independent T M _ I _ hI

/-- Naturality holds for every original linear map of finite-length modules. -/
theorem cofiniteFunctorEvaluation_naturality {M N : FiniteLengthModuleCat R}
    (f : M ⟶ N) (t : finiteLengthFunctorValue T N) (x : M.obj) :
    cofiniteFunctorEvaluation T M (T.map f.op t) x =
      cofiniteFunctorEvaluation T N t (f.hom x) := by
  let I := cofiniteAnnihilator M.obj M.property
  let J := cofiniteAnnihilator N.obj N.property
  have hM : (I ⊔ J).val ≤ Module.annihilator R M.obj := inf_le_left
  have hN : (I ⊔ J).val ≤ Module.annihilator R N.obj := inf_le_right
  rw [cofiniteFunctorEvaluation_eq_stage T M _ hM,
    cofiniteFunctorEvaluation_eq_stage T N _ hN,
    cofiniteColimitStageEvaluation_apply, cofiniteColimitStageEvaluation_apply,
    cofiniteStageEvaluation_naturality T _ hM hN f]

/-- The original canonical evaluation with its canonical scalar actions. -/
def cofiniteFunctorEvaluationNatTrans :
    additiveFunctorModuleLift (R := R) T ⟶
      finiteLengthModuleHomFunctor (cofiniteFunctorColimit T) where
  app M := ModuleCat.ofHom (X := (additiveFunctorModuleLift (R := R) T).obj M)
    (Y := (finiteLengthModuleHomFunctor (cofiniteFunctorColimit T)).obj M)
    (cofiniteFunctorEvaluation T M.unop)
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact cofiniteFunctorEvaluation_naturality T f.unop t x

/-- Original abelian-group-valued evaluation into Hom to the actual colimit. -/
def additiveCofiniteFunctorEvaluationNatTrans :
    T ⟶ finiteLengthModuleHomFunctor (cofiniteFunctorColimit T) ⋙
      forget₂ (ModuleCat R) AddCommGrpCat :=
  (additiveFunctorModuleLiftForgetIso (R := R) T).inv ≫
    whiskerRight (cofiniteFunctorEvaluationNatTrans T) (forget₂ (ModuleCat R) AddCommGrpCat)

end SGA.SGA2.ExposeIV
