/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.CofiniteStageEvaluation
import SGA.SGA2.ExposeIV.CofiniteQuotientStages
import SGA.SGA2.ExposeIV.FiniteModuleRepresentation

/-!
# Representation by the original evaluation at cofinite quotient stages

Apply IV.1.1 to the genuine restriction of the original functor to finite
modules over `R/I`. The canonical quotient scalar action is compared with
the original canonical `R`-action by equality of the actual homotheties.
The resulting evaluation is precisely `cofiniteStageEvaluation`, not a
replacement representing map. Its bijectivity therefore holds at every
cofinite annihilating ideal for every original finite-length module.

Only left exactness of the original additive functor is assumed. The base
ring can be any commutative ring: each cofinite quotient is noetherian by
its already-proved finite length.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Restriction identifies the original and quotient-stage homotheties. -/
theorem cofiniteQuotientRestriction_map_mk_smul_id (I : CofiniteIdealIndex R)
    (N : FGModuleCat.{u} (R ⧸ I.val)) (r : R) :
    (cofiniteQuotientRestriction I).map (Ideal.Quotient.mk I.val r • 𝟙 N) =
      r • 𝟙 ((cofiniteQuotientRestriction I).obj N) := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- The quotient-linear point map becomes the original cofinite point map. -/
theorem cofiniteQuotientPoint_stage (I : CofiniteIdealIndex R)
    (N : FGModuleCat.{u} (R ⧸ I.val)) (x : N) :
    (cofiniteQuotientRestriction_ringIso I).inv ≫
      (cofiniteQuotientRestriction I).map (finiteModulePoint N x) =
      cofiniteQuotientPoint ((cofiniteQuotientRestriction I).obj N) I
        (cofiniteQuotientRestriction_annihilator I N) x := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

variable (T : (FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- The actual original functor restricted to finite quotient-ring modules. -/
def cofiniteQuotientStageFunctor (I : CofiniteIdealIndex R) :
    (FGModuleCat.{u} (R ⧸ I.val))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (cofiniteQuotientRestriction I).op ⋙ T

instance (I : CofiniteIdealIndex R) : (cofiniteQuotientStageFunctor T I).Additive := by
  unfold cofiniteQuotientStageFunctor
  infer_instance

instance [PreservesFiniteLimits T] (I : CofiniteIdealIndex R) :
    PreservesFiniteLimits (cofiniteQuotientStageFunctor T I) := by
  have := preservesFiniteLimits_op (cofiniteQuotientRestriction I)
  unfold cofiniteQuotientStageFunctor
  exact comp_preservesFiniteLimits _ _

/-- The stage functor with its canonical quotient-ring scalar action. -/
abbrev cofiniteQuotientStageModuleFunctor (I : CofiniteIdealIndex R) :=
  additiveFunctorModuleLift (R := R ⧸ I.val) (cofiniteQuotientStageFunctor T I)

/-- The quotient-induced and original canonical scalar actions agree by
restriction, via the identity on the actual original functor values. -/
def cofiniteQuotientStageCanonicalModuleIso (I : CofiniteIdealIndex R)
    (N : FGModuleCat.{u} (R ⧸ I.val)) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I.val)).obj
      ((cofiniteQuotientStageModuleFunctor T I).obj (op N)) ≅
      finiteLengthFunctorValue T ((cofiniteQuotientRestriction I).obj N) :=
  LinearEquiv.toModuleIso (X₁ :=
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I.val)).obj
        ((cofiniteQuotientStageModuleFunctor T I).obj (op N)))
    (X₂ := finiteLengthFunctorValue T ((cofiniteQuotientRestriction I).obj N))
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change T.map (((cofiniteQuotientRestriction I).map
          (Ideal.Quotient.mk I.val r • 𝟙 N)).op) x =
          T.map (r • 𝟙 (op ((cofiniteQuotientRestriction I).obj N))) x
        rw [cofiniteQuotientRestriction_map_mk_smul_id]
        rfl }

@[simp]
theorem cofiniteQuotientStageCanonicalModuleIso_hom_apply (I : CofiniteIdealIndex R)
    (N : FGModuleCat.{u} (R ⧸ I.val))
    (x : (cofiniteQuotientStageModuleFunctor T I).obj (op N)) :
    (cofiniteQuotientStageCanonicalModuleIso T I N).hom x = x := rfl

/-- The original value on the stage ring is the actual coefficient `T(R/I)`. -/
def cofiniteQuotientStageRingValueIso (I : CofiniteIdealIndex R) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I.val)).obj
      ((cofiniteQuotientStageModuleFunctor T I).obj
        (op (FGModuleCat.of (R ⧸ I.val) (R ⧸ I.val)))) ≅ cofiniteFunctorStage T I :=
  cofiniteQuotientStageCanonicalModuleIso T I (FGModuleCat.of (R ⧸ I.val) (R ⧸ I.val)) ≪≫
    (additiveFunctorModuleLift (R := R) T).mapIso
      (cofiniteQuotientRestriction_ringIso I).symm.op

/-- Genuine quotient-linear maps identify with the original `R`-linear maps
used by cofinite-stage evaluation. -/
def cofiniteQuotientStageHomEquiv (I : CofiniteIdealIndex R)
    (N : FGModuleCat.{u} (R ⧸ I.val)) :
    (N.obj ⟶ (cofiniteQuotientStageModuleFunctor T I).obj
      (op (FGModuleCat.of (R ⧸ I.val) (R ⧸ I.val)))) ≃
      (((cofiniteQuotientRestriction I).obj N).obj ⟶ cofiniteFunctorStage T I) :=
  (fullyFaithfulQuotientRestriction I.val).homEquiv.trans
    (Iso.homCongr (Iso.refl _) (cofiniteQuotientStageRingValueIso T I))

/-- The transported IV.1.1 map is exactly the original canonical evaluation. -/
theorem cofiniteQuotientStageHomEquiv_evaluation (I : CofiniteIdealIndex R)
    (N : FGModuleCat.{u} (R ⧸ I.val))
    (t : (cofiniteQuotientStageModuleFunctor T I).obj (op N)) :
    cofiniteQuotientStageHomEquiv T I N
        (finiteModuleEvaluation (cofiniteQuotientStageModuleFunctor T I) N t) =
      cofiniteStageEvaluation T ((cofiniteQuotientRestriction I).obj N) I
        (cofiniteQuotientRestriction_annihilator I N) t := by
  apply ModuleCat.hom_ext
  ext x
  change (T.map (((cofiniteQuotientRestriction I).map (finiteModulePoint N x)).op) ≫
    T.map (cofiniteQuotientRestriction_ringIso I).inv.op) t = _
  rw [← T.map_comp, ← op_comp, cofiniteQuotientPoint_stage]
  rfl

/-- IV.1.1 proves bijectivity on every actual quotient-stage object. -/
theorem cofiniteStageEvaluation_stage_bijective [PreservesFiniteLimits T]
    (I : CofiniteIdealIndex R) (N : FGModuleCat.{u} (R ⧸ I.val)) :
    Function.Bijective (cofiniteStageEvaluation T ((cofiniteQuotientRestriction I).obj N) I
      (cofiniteQuotientRestriction_annihilator I N)) := by
  have h := (cofiniteQuotientStageHomEquiv T I N).bijective.comp
    (show Function.Bijective
        (finiteModuleEvaluation (cofiniteQuotientStageModuleFunctor T I) N) from
      ⟨finiteModuleEvaluation_injective _ _, finiteModuleEvaluation_surjective _ _⟩)
  simpa only [Function.comp_def, cofiniteQuotientStageHomEquiv_evaluation] using h

/-- The actual canonical evaluation is bijective for every original
finite-length module at every cofinite annihilating ideal. -/
theorem cofiniteStageEvaluation_bijective [PreservesFiniteLimits T]
    (M : FiniteLengthModuleCat R) (I : CofiniteIdealIndex R)
    (hM : I.val ≤ Module.annihilator R M.obj) :
    Function.Bijective (cofiniteStageEvaluation T M I hM) := by
  let N := finiteLengthModuleQuotientStage M I hM
  let e := finiteLengthModuleQuotientStageIso M I hM
  let hN : I.val ≤ Module.annihilator R ((cofiniteQuotientRestriction I).obj N).obj :=
    cofiniteQuotientRestriction_annihilator I N
  have heval := cofiniteStageEvaluation_stage_bijective T I N
  have he := ConcreteCategory.bijective_of_isIso (T.map e.hom.op)
  constructor
  · intro t s h
    apply he.injective
    apply heval.injective
    apply ModuleCat.hom_ext
    ext x
    exact (cofiniteStageEvaluation_naturality T
      (M := (cofiniteQuotientRestriction I).obj N) (N := M) I hN hM e.hom t x).trans
      ((congrArg (fun g => g (e.hom.hom x)) h).trans
        (cofiniteStageEvaluation_naturality T
          (M := (cofiniteQuotientRestriction I).obj N) (N := M) I hN hM e.hom s x).symm)
  · intro f
    let eR := (finiteLengthInclusion R).mapIso e
    obtain ⟨s, hs⟩ := heval.surjective (eR.hom ≫ f)
    obtain ⟨t, ht⟩ := he.surjective s
    refine ⟨t, ?_⟩
    apply (cancel_epi eR.hom).mp
    apply ModuleCat.hom_ext
    ext x
    calc
      _ = cofiniteStageEvaluation T ((cofiniteQuotientRestriction I).obj N) I hN
          (T.map e.hom.op t) x :=
        (cofiniteStageEvaluation_naturality T I hN hM e.hom t x).symm
      _ = cofiniteStageEvaluation T ((cofiniteQuotientRestriction I).obj N) I hN s x := by
        rw [ht]
      _ = _ := congrArg (fun g => g x) hs

/-- The linear equivalence is built from the original canonical evaluation. -/
def cofiniteStageEvaluationEquiv [PreservesFiniteLimits T]
    (M : FiniteLengthModuleCat R) (I : CofiniteIdealIndex R)
    (hM : I.val ≤ Module.annihilator R M.obj) :
    finiteLengthFunctorValue T M ≃ₗ[R] (M.obj ⟶ cofiniteFunctorStage T I) :=
  LinearEquiv.ofBijective (cofiniteStageEvaluation T M I hM)
    (cofiniteStageEvaluation_bijective T M I hM)

@[simp]
theorem cofiniteStageEvaluationEquiv_apply [PreservesFiniteLimits T]
    (M : FiniteLengthModuleCat R) (I : CofiniteIdealIndex R)
    (hM : I.val ≤ Module.annihilator R M.obj) (t : finiteLengthFunctorValue T M) :
    cofiniteStageEvaluationEquiv T M I hM t = cofiniteStageEvaluation T M I hM t := rfl

instance [PreservesFiniteLimits T] (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hM : I.val ≤ Module.annihilator R M.obj) :
    IsIso (ModuleCat.ofHom (cofiniteStageEvaluation T M I hM)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (cofiniteStageEvaluation_bijective T M I hM)

end SGA.SGA2.ExposeIV
