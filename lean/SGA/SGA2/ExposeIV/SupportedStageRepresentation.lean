/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedStageEvaluation
import SGA.SGA2.ExposeIV.FiniteModuleRepresentation

/-!
# Representation at each actual quotient stage

The canonical stage evaluation is bijective for a left-exact functor. We
apply IV.1.1 over the quotient ring and compare its actual canonical map with
the evaluation already defined in `SupportedStageEvaluation`.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A specified annihilating power gives the original module an actual
quotient-ring module structure on the same abelian group. -/
def supportedModuleOverQuotient (J : Ideal R) (M : SupportedFGModuleCat J) (n : ℕ)
    (hM : J ^ n ≤ Module.annihilator R M.obj) : FGModuleCat.{u} (R ⧸ J ^ n) := by
  have h : Module.IsTorsionBySet R M.obj ((J ^ n : Ideal R) : Set R) :=
    (Module.isTorsionBySet_iff_subset_annihilator R M.obj).mpr hM
  letI := h.module
  letI := Module.Finite.of_surjective h.semilinearMap Function.surjective_id
  exact FGModuleCat.of (R ⧸ J ^ n) M.obj

/-- Restriction of this quotient action recovers the original supported
module by the identity on its underlying group. -/
def supportedModuleOverQuotientIso (J : Ideal R) (M : SupportedFGModuleCat J) (n : ℕ)
    (hM : J ^ n ≤ Module.annihilator R M.obj) :
    (supportedQuotientStage J n).obj (supportedModuleOverQuotient J M n hM) ≅ M :=
  (supportedFiniteModuleProperty J).isoMk ((ModuleCat.isFG R).isoMk
    (LinearEquiv.toModuleIso (X₁ :=
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (J ^ n))).obj
        (supportedModuleOverQuotient J M n hM).obj) (X₂ := M.obj.obj)
      { toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }))

/-- Scalar multiplication from `R` agrees with the quotient-stage homothety. -/
theorem supportedQuotientStage_map_mk_smul_id (J : Ideal R) (n : ℕ)
    (N : FGModuleCat.{u} (R ⧸ J ^ n)) (r : R) :
    (supportedQuotientStage J n).map (Ideal.Quotient.mk (J ^ n) r • 𝟙 N) =
      r • 𝟙 ((supportedQuotientStage J n).obj N) := by
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  ext x
  rfl

/-- The quotient-stage point map is the original quotient point map after
the already-proved cyclic-stage isomorphism. -/
theorem supportedQuotientPoint_stage (J : Ideal R) (n : ℕ)
    (N : FGModuleCat.{u} (R ⧸ J ^ n)) (x : N) :
    (supportedRingQuotientStageIso J n).inv ≫
      (supportedQuotientStage J n).map (finiteModulePoint N x) =
    supportedQuotientPoint J ((supportedQuotientStage J n).obj N) n
      (quotientFiniteRestriction_annihilator (J ^ n) N) x := by
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  ext q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- The actual restriction of the original functor to the quotient stage. -/
def quotientStageFunctor (n : ℕ) : (FGModuleCat.{u} (R ⧸ J ^ n))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (supportedQuotientStage J n).op ⋙ T

instance (n : ℕ) : (quotientStageFunctor J T n).Additive := by
  unfold quotientStageFunctor
  infer_instance

instance [PreservesFiniteLimits T] (n : ℕ) :
    PreservesFiniteLimits (quotientStageFunctor J T n) := by
  have := preservesFiniteLimits_op (supportedQuotientStage J n)
  unfold quotientStageFunctor
  exact comp_preservesFiniteLimits _ _

/-- The quotient-stage functor with its canonical quotient-ring scalar action. -/
abbrev quotientStageModuleFunctor (n : ℕ) :=
  additiveFunctorModuleLift (R := R ⧸ J ^ n) (quotientStageFunctor J T n)

/-- The canonical quotient action and original canonical `R`-action agree
after genuine restriction of scalars, by equality of homotheties. -/
def quotientStageCanonicalModuleIso (n : ℕ) (N : FGModuleCat.{u} (R ⧸ J ^ n)) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (J ^ n))).obj
      ((quotientStageModuleFunctor J T n).obj (op N)) ≅
    (additiveFunctorModuleLift (R := R) T).obj (op ((supportedQuotientStage J n).obj N)) :=
  LinearEquiv.toModuleIso (X₁ :=
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (J ^ n))).obj
        ((quotientStageModuleFunctor J T n).obj (op N)))
    (X₂ := (additiveFunctorModuleLift (R := R) T).obj
      (op ((supportedQuotientStage J n).obj N)))
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        change T.map (((supportedQuotientStage J n).map
          (Ideal.Quotient.mk (J ^ n) r • 𝟙 N)).op) x =
          T.map (r • 𝟙 (op ((supportedQuotientStage J n).obj N))) x
        rw [supportedQuotientStage_map_mk_smul_id]
        rfl }

/-- The value on the quotient-stage ring identifies with the original `Hₙ`. -/
def quotientStageRingValueIso (n : ℕ) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (J ^ n))).obj
      ((quotientStageModuleFunctor J T n).obj (op (FGModuleCat.of (R ⧸ J ^ n) (R ⧸ J ^ n)))) ≅
      supportedFunctorStage J T n :=
  quotientStageCanonicalModuleIso J T n (FGModuleCat.of (R ⧸ J ^ n) (R ⧸ J ^ n)) ≪≫
    (additiveFunctorModuleLift (R := R) T).mapIso (supportedRingQuotientStageIso J n).symm.op

/-- Actual quotient-linear maps identify with the `R`-linear maps used by
canonical supported evaluation. -/
def quotientStageHomEquiv (n : ℕ) (N : FGModuleCat.{u} (R ⧸ J ^ n)) :
    (N.obj ⟶ (quotientStageModuleFunctor J T n).obj
      (op (FGModuleCat.of (R ⧸ J ^ n) (R ⧸ J ^ n)))) ≃
      (((supportedQuotientStage J n).obj N).obj.obj ⟶ supportedFunctorStage J T n) :=
  (fullyFaithfulQuotientRestriction (J ^ n)).homEquiv.trans
    (Iso.homCongr (Iso.refl _) (quotientStageRingValueIso J T n))

/-- The transported IV.1.1 evaluation is the actual supported stage map. -/
theorem quotientStageHomEquiv_evaluation (n : ℕ) (N : FGModuleCat.{u} (R ⧸ J ^ n))
    (t : (quotientStageModuleFunctor J T n).obj (op N)) :
    quotientStageHomEquiv J T n N (finiteModuleEvaluation (quotientStageModuleFunctor J T n) N t) =
      supportedStageEvaluation J T ((supportedQuotientStage J n).obj N) n
        (quotientFiniteRestriction_annihilator (J ^ n) N) t := by
  apply ModuleCat.hom_ext
  ext x
  change (T.map (((supportedQuotientStage J n).map (finiteModulePoint N x)).op) ≫
    T.map (supportedRingQuotientStageIso J n).inv.op) t = _
  rw [← T.map_comp, ← op_comp, supportedQuotientPoint_stage]
  rfl

/-- IV.1.1 over the quotient ring proves bijectivity of the already-defined
canonical evaluation on every quotient-stage object. -/
theorem supportedStageEvaluation_stage_bijective [PreservesFiniteLimits T] (n : ℕ)
    (N : FGModuleCat.{u} (R ⧸ J ^ n)) :
    Function.Bijective (supportedStageEvaluation J T ((supportedQuotientStage J n).obj N) n
      (quotientFiniteRestriction_annihilator (J ^ n) N)) := by
  have h := (quotientStageHomEquiv J T n N).bijective.comp
    (show Function.Bijective (finiteModuleEvaluation (quotientStageModuleFunctor J T n) N) from
      ⟨finiteModuleEvaluation_injective _ _, finiteModuleEvaluation_surjective _ _⟩)
  simpa only [Function.comp_def, quotientStageHomEquiv_evaluation] using h

/-- Canonical evaluation is bijective for any original supported module and
any specified annihilating power, not only for objects presented in a stage. -/
theorem supportedStageEvaluation_bijective [PreservesFiniteLimits T]
    (M : SupportedFGModuleCat J) (n : ℕ) (hM : J ^ n ≤ Module.annihilator R M.obj) :
    Function.Bijective (supportedStageEvaluation J T M n hM) := by
  let N := supportedModuleOverQuotient J M n hM
  let e := supportedModuleOverQuotientIso J M n hM
  let hN : J ^ n ≤ Module.annihilator R ((supportedQuotientStage J n).obj N).obj :=
    quotientFiniteRestriction_annihilator (J ^ n) N
  have heval := supportedStageEvaluation_stage_bijective J T n N
  have he := ConcreteCategory.bijective_of_isIso (T.map e.hom.op)
  constructor
  · intro t s h
    apply he.injective
    apply heval.injective
    apply ModuleCat.hom_ext
    ext x
    exact (supportedStageEvaluation_naturality J T
      (M := (supportedQuotientStage J n).obj N) (N := M) n hN hM e.hom t x).trans
      ((congrArg (fun g ↦ g (e.hom.hom.hom x)) h).trans
        (supportedStageEvaluation_naturality J T
          (M := (supportedQuotientStage J n).obj N) (N := M) n hN hM e.hom s x).symm)
  · intro f
    let eR := (supportedFiniteToModule J).mapIso e
    obtain ⟨s, hs⟩ := heval.surjective (eR.hom ≫ f)
    obtain ⟨t, ht⟩ := he.surjective s
    refine ⟨t, ?_⟩
    apply (cancel_epi eR.hom).mp
    apply ModuleCat.hom_ext
    ext x
    calc
      _ = supportedStageEvaluation J T ((supportedQuotientStage J n).obj N) n hN
          (T.map e.hom.op t) x :=
        (supportedStageEvaluation_naturality J T n hN hM e.hom t x).symm
      _ = supportedStageEvaluation J T ((supportedQuotientStage J n).obj N) n hN s x := by
        rw [ht]
      _ = _ := congrArg (fun g ↦ g x) hs

/-- The isomorphism is constructed from the original canonical stage map. -/
def supportedStageEvaluationEquiv [PreservesFiniteLimits T]
    (M : SupportedFGModuleCat J) (n : ℕ) (hM : J ^ n ≤ Module.annihilator R M.obj) :
    (additiveFunctorModuleLift (R := R) T).obj (op M) ≃ₗ[R]
      (M.obj.obj ⟶ supportedFunctorStage J T n) :=
  LinearEquiv.ofBijective (supportedStageEvaluation J T M n hM)
    (supportedStageEvaluation_bijective J T M n hM)

@[simp] theorem supportedStageEvaluationEquiv_apply [PreservesFiniteLimits T]
    (M : SupportedFGModuleCat J) (n : ℕ) (hM : J ^ n ≤ Module.annihilator R M.obj)
    (t : (additiveFunctorModuleLift (R := R) T).obj (op M)) :
    supportedStageEvaluationEquiv J T M n hM t = supportedStageEvaluation J T M n hM t := rfl

instance [PreservesFiniteLimits T] (M : SupportedFGModuleCat J) (n : ℕ)
    (hM : J ^ n ≤ Module.annihilator R M.obj) :
    IsIso (ModuleCat.ofHom (supportedStageEvaluation J T M n hM)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (supportedStageEvaluation_bijective J T M n hM)

end SGA.SGA2.ExposeIV
