/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorDiagram

/-!
# Canonical evaluation at an annihilating quotient stage

For an actual supported module killed by `Jⁿ`, evaluation uses the actual maps
`R/Jⁿ → M`, sending `1` to `x`. Its naturality and transition compatibility
follow from equality of these maps, independently of any representation theorem.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The genuine quotient-linear point map `1 ↦ x`. -/
def supportedQuotientPoint (J : Ideal R) (M : SupportedFGModuleCat J) (n : ℕ)
    (hM : J ^ n ≤ Module.annihilator R M.obj) (x : M.obj) :
    supportedRingQuotient J n ⟶ M :=
  ObjectProperty.homMk (FGModuleCat.ofHom
    ((J ^ n).liftQ (LinearMap.toSpanSingleton R M.obj x)
      (fun _ hr ↦ Module.mem_annihilator.mp (hM hr) x)))

@[simp] theorem supportedQuotientPoint_apply (J : Ideal R) (M : SupportedFGModuleCat J)
    (n : ℕ) (hM : J ^ n ≤ Module.annihilator R M.obj) (x : M.obj) (r : R) :
    (supportedQuotientPoint J M n hM x).hom.hom.hom (Ideal.Quotient.mk (J ^ n) r) =
      r • x := rfl

@[simp] theorem supportedQuotientPoint_add (J : Ideal R) (M : SupportedFGModuleCat J)
    (n : ℕ) (hM : J ^ n ≤ Module.annihilator R M.obj) (x y : M.obj) :
    supportedQuotientPoint J M n hM (x + y) =
      supportedQuotientPoint J M n hM x + supportedQuotientPoint J M n hM y := by
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  ext q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact smul_add r x y

@[simp] theorem supportedQuotientPoint_smul (J : Ideal R) (M : SupportedFGModuleCat J)
    (n : ℕ) (hM : J ^ n ≤ Module.annihilator R M.obj) (r : R) (x : M.obj) :
    supportedQuotientPoint J M n hM (r • x) = r • supportedQuotientPoint J M n hM x := by
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  ext q
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact smul_comm s r x

/-- Naturality of the original point maps. -/
theorem supportedQuotientPoint_comp (J : Ideal R) {M N : SupportedFGModuleCat J}
    (n : ℕ) (hM : J ^ n ≤ Module.annihilator R M.obj)
    (hN : J ^ n ≤ Module.annihilator R N.obj) (f : M ⟶ N) (x : M.obj) :
    supportedQuotientPoint J M n hM x ≫ f =
      supportedQuotientPoint J N n hN (f.hom.hom x) := by
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  ext q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact f.hom.hom.hom.map_smul r x

/-- The point map for a larger power factors through the original quotient
transition, with no chosen stage identification. -/
theorem supportedQuotientPoint_transition (J : Ideal R) (M : SupportedFGModuleCat J)
    {n m : ℕ} (hn : J ^ n ≤ Module.annihilator R M.obj)
    (hm : J ^ m ≤ Module.annihilator R M.obj) (h : n ≤ m) (x : M.obj) :
    supportedRingQuotientMap J h ≫ supportedQuotientPoint J M n hn x =
      supportedQuotientPoint J M m hm x := by
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  ext q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- Canonical stage evaluation, linear for the functor's canonical scalar
action. Its target consists of the original `R`-linear maps. -/
def supportedStageEvaluation (M : SupportedFGModuleCat J) (n : ℕ)
    (hM : J ^ n ≤ Module.annihilator R M.obj) :
    (additiveFunctorModuleLift (R := R) T).obj (op M) →ₗ[R]
      (M.obj.obj ⟶ supportedFunctorStage J T n) where
  toFun t := ModuleCat.ofHom (X := M.obj.obj) (Y := supportedFunctorStage J T n)
    { toFun x := (additiveFunctorModuleLift (R := R) T).map
        (supportedQuotientPoint J M n hM x).op t
      map_add' x y := by simp
      map_smul' r x := by simp }
  map_add' t s := by
    apply ModuleCat.hom_ext
    ext x
    exact ((additiveFunctorModuleLift (R := R) T).map
      (supportedQuotientPoint J M n hM x).op).hom.map_add t s
  map_smul' r t := by
    apply ModuleCat.hom_ext
    ext x
    exact ((additiveFunctorModuleLift (R := R) T).map
      (supportedQuotientPoint J M n hM x).op).hom.map_smul r t

@[simp] theorem supportedStageEvaluation_apply (M : SupportedFGModuleCat J) (n : ℕ)
    (hM : J ^ n ≤ Module.annihilator R M.obj)
    (t : (additiveFunctorModuleLift (R := R) T).obj (op M)) (x : M.obj) :
    supportedStageEvaluation J T M n hM t x = T.map (supportedQuotientPoint J M n hM x).op t :=
  rfl

/-- Stage evaluation is natural in the actual coefficient module. -/
theorem supportedStageEvaluation_naturality {M N : SupportedFGModuleCat J}
    (n : ℕ) (hM : J ^ n ≤ Module.annihilator R M.obj)
    (hN : J ^ n ≤ Module.annihilator R N.obj) (f : M ⟶ N)
    (t : (additiveFunctorModuleLift (R := R) T).obj (op N)) (x : M.obj) :
    supportedStageEvaluation J T M n hM (T.map f.op t) x =
      supportedStageEvaluation J T N n hN t (f.hom.hom x) := by
  change (T.map f.op ≫ T.map (supportedQuotientPoint J M n hM x).op) t = _
  rw [← T.map_comp, ← op_comp, supportedQuotientPoint_comp J n hM hN f]
  rfl

/-- Evaluation commutes with the original transitions `Hₙ → Hₘ`. -/
theorem supportedStageEvaluation_transition (M : SupportedFGModuleCat J) {n m : ℕ}
    (hn : J ^ n ≤ Module.annihilator R M.obj)
    (hm : J ^ m ≤ Module.annihilator R M.obj) (h : n ≤ m)
    (t : (additiveFunctorModuleLift (R := R) T).obj (op M)) (x : M.obj) :
    supportedFunctorTransition J T h (supportedStageEvaluation J T M n hn t x) =
      supportedStageEvaluation J T M m hm t x := by
  change (T.map (supportedQuotientPoint J M n hn x).op ≫
    T.map (supportedRingQuotientMap J h).op) t = _
  rw [← T.map_comp, ← op_comp, supportedQuotientPoint_transition J M hn hm h]
  rfl

/-- The same compatibility as equality of actual module morphisms. -/
theorem supportedStageEvaluation_transition_hom (M : SupportedFGModuleCat J) {n m : ℕ}
    (hn : J ^ n ≤ Module.annihilator R M.obj)
    (hm : J ^ m ≤ Module.annihilator R M.obj) (h : n ≤ m)
    (t : (additiveFunctorModuleLift (R := R) T).obj (op M)) :
    supportedStageEvaluation J T M n hn t ≫ supportedFunctorTransition J T h =
      supportedStageEvaluation J T M m hm t := by
  apply ModuleCat.hom_ext
  ext x
  exact supportedStageEvaluation_transition J T M hn hm h t x

end SGA.SGA2.ExposeIV
