/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.CofiniteFunctorDiagram

/-!
# Original evaluation at a cofinite annihilating quotient

For a finite-length module killed by a cofinite ideal `I`, the point maps
`R/I → M`, sending `1` to `x`, induce the actual evaluation
`T(M) → Hom_R(M,T(R/I))`.  This map is linear for the canonical source-induced
scalar actions.  Its naturality and compatibility with the original quotient
transitions follow directly from equality of the original point maps.

Neither left exactness nor a representation theorem is assumed.  The ring
is an arbitrary commutative ring.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false

/-- The original point map from the actual quotient, sending `1` to `x`. -/
def cofiniteQuotientPoint (M : FiniteLengthModuleCat R) (I : CofiniteIdealIndex R)
    (hM : I.val ≤ Module.annihilator R M.obj) (x : M.obj) :
    cofiniteRingQuotient I ⟶ M :=
  ObjectProperty.homMk (ModuleCat.ofHom
    (I.val.liftQ (LinearMap.toSpanSingleton R M.obj x)
      (fun _ hr => Module.mem_annihilator.mp (hM hr) x)))

@[simp]
theorem cofiniteQuotientPoint_apply (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hM : I.val ≤ Module.annihilator R M.obj)
    (x : M.obj) (r : R) :
    (cofiniteQuotientPoint M I hM x).hom (Ideal.Quotient.mk I.val r) = r • x := rfl

@[simp]
theorem cofiniteQuotientPoint_one (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hM : I.val ≤ Module.annihilator R M.obj) (x : M.obj) :
    (cofiniteQuotientPoint M I hM x).hom (1 : R ⧸ I.val) = x := by
  change (1 : R) • x = x
  exact one_smul R x

@[simp]
theorem cofiniteQuotientPoint_add (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hM : I.val ≤ Module.annihilator R M.obj) (x y : M.obj) :
    cofiniteQuotientPoint M I hM (x + y) =
      cofiniteQuotientPoint M I hM x + cofiniteQuotientPoint M I hM y := by
  apply ObjectProperty.hom_ext
  ext q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact smul_add r x y

@[simp]
theorem cofiniteQuotientPoint_smul (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hM : I.val ≤ Module.annihilator R M.obj)
    (r : R) (x : M.obj) :
    cofiniteQuotientPoint M I hM (r • x) = r • cofiniteQuotientPoint M I hM x := by
  apply ObjectProperty.hom_ext
  ext q
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact smul_comm s r x

/-- The actual point maps are natural in the original finite-length module. -/
theorem cofiniteQuotientPoint_comp {M N : FiniteLengthModuleCat R}
    (I : CofiniteIdealIndex R) (hM : I.val ≤ Module.annihilator R M.obj)
    (hN : I.val ≤ Module.annihilator R N.obj) (f : M ⟶ N) (x : M.obj) :
    cofiniteQuotientPoint M I hM x ≫ f =
      cofiniteQuotientPoint N I hN (f.hom x) := by
  apply ObjectProperty.hom_ext
  ext q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact f.hom.hom.map_smul r x

/-- A smaller annihilating ideal gives the same point map after the original
quotient transition. -/
theorem cofiniteQuotientPoint_transition (M : FiniteLengthModuleCat R)
    {I J : CofiniteIdealIndex R} (hI : I.val ≤ Module.annihilator R M.obj)
    (hJ : J.val ≤ Module.annihilator R M.obj) (h : I ≤ J) (x : M.obj) :
    cofiniteRingQuotientMap h ≫ cofiniteQuotientPoint M I hI x =
      cofiniteQuotientPoint M J hJ x := by
  apply ObjectProperty.hom_ext
  ext q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

/-- At the quotient itself, the point `1` gives its actual identity map. -/
theorem cofiniteQuotientPoint_self_one (I : CofiniteIdealIndex R)
    (hI : I.val ≤ Module.annihilator R (cofiniteRingQuotient I).obj) :
    cofiniteQuotientPoint (cofiniteRingQuotient I) I hI (1 : R ⧸ I.val) =
      𝟙 (cofiniteRingQuotient I) := by
  apply ObjectProperty.hom_ext
  ext q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  change r • (1 : R ⧸ I.val) = Ideal.Quotient.mk I.val r
  simp [Algebra.smul_def]

variable (T : (FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- Canonical cofinite-stage evaluation, linear in the original functor value
and taking values in actual linear maps out of the original module. -/
def cofiniteStageEvaluation (M : FiniteLengthModuleCat R) (I : CofiniteIdealIndex R)
    (hM : I.val ≤ Module.annihilator R M.obj) :
    finiteLengthFunctorValue T M →ₗ[R] (M.obj ⟶ cofiniteFunctorStage T I) where
  toFun t := ModuleCat.ofHom (X := M.obj) (Y := cofiniteFunctorStage T I)
    { toFun x := (additiveFunctorModuleLift (R := R) T).map
        (cofiniteQuotientPoint M I hM x).op t
      map_add' x y := by simp
      map_smul' r x := by simp }
  map_add' t s := by
    apply ModuleCat.hom_ext
    ext x
    exact ((additiveFunctorModuleLift (R := R) T).map
      (cofiniteQuotientPoint M I hM x).op).hom.map_add t s
  map_smul' r t := by
    apply ModuleCat.hom_ext
    ext x
    exact ((additiveFunctorModuleLift (R := R) T).map
      (cofiniteQuotientPoint M I hM x).op).hom.map_smul r t

@[simp]
theorem cofiniteStageEvaluation_apply (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hM : I.val ≤ Module.annihilator R M.obj)
    (t : finiteLengthFunctorValue T M) (x : M.obj) :
    cofiniteStageEvaluation T M I hM t x = T.map (cofiniteQuotientPoint M I hM x).op t := rfl

/-- Evaluation is natural under original finite-length module maps. -/
theorem cofiniteStageEvaluation_naturality {M N : FiniteLengthModuleCat R}
    (I : CofiniteIdealIndex R) (hM : I.val ≤ Module.annihilator R M.obj)
    (hN : I.val ≤ Module.annihilator R N.obj) (f : M ⟶ N)
    (t : finiteLengthFunctorValue T N) (x : M.obj) :
    cofiniteStageEvaluation T M I hM (T.map f.op t) x =
      cofiniteStageEvaluation T N I hN t (f.hom x) := by
  change (T.map f.op ≫ T.map (cofiniteQuotientPoint M I hM x).op) t = _
  rw [← T.map_comp, ← op_comp, cofiniteQuotientPoint_comp I hM hN f]
  rfl

/-- The same source naturality as an equality of actual module maps. -/
theorem cofiniteStageEvaluation_naturality_hom {M N : FiniteLengthModuleCat R}
    (I : CofiniteIdealIndex R) (hM : I.val ≤ Module.annihilator R M.obj)
    (hN : I.val ≤ Module.annihilator R N.obj) (f : M ⟶ N)
    (t : finiteLengthFunctorValue T N) :
    cofiniteStageEvaluation T M I hM (T.map f.op t) =
      f.hom ≫ cofiniteStageEvaluation T N I hN t := by
  apply ModuleCat.hom_ext
  ext x
  exact cofiniteStageEvaluation_naturality T I hM hN f t x

/-- Evaluation commutes with the actual quotient-induced stage transitions. -/
theorem cofiniteStageEvaluation_transition (M : FiniteLengthModuleCat R)
    {I J : CofiniteIdealIndex R} (hI : I.val ≤ Module.annihilator R M.obj)
    (hJ : J.val ≤ Module.annihilator R M.obj) (h : I ≤ J)
    (t : finiteLengthFunctorValue T M) (x : M.obj) :
    cofiniteFunctorTransition T h (cofiniteStageEvaluation T M I hI t x) =
      cofiniteStageEvaluation T M J hJ t x := by
  change (T.map (cofiniteQuotientPoint M I hI x).op ≫
    T.map (cofiniteRingQuotientMap h).op) t = _
  rw [← T.map_comp, ← op_comp, cofiniteQuotientPoint_transition M hI hJ h]
  rfl

/-- Transition compatibility as equality of actual module morphisms. -/
theorem cofiniteStageEvaluation_transition_hom (M : FiniteLengthModuleCat R)
    {I J : CofiniteIdealIndex R} (hI : I.val ≤ Module.annihilator R M.obj)
    (hJ : J.val ≤ Module.annihilator R M.obj) (h : I ≤ J)
    (t : finiteLengthFunctorValue T M) :
    cofiniteStageEvaluation T M I hI t ≫ cofiniteFunctorTransition T h =
      cofiniteStageEvaluation T M J hJ t := by
  apply ModuleCat.hom_ext
  ext x
  exact cofiniteStageEvaluation_transition T M hI hJ h t x

/-- On `T(R/I)`, evaluation at the actual point `1` recovers the original element. -/
@[simp]
theorem cofiniteStageEvaluation_self_apply_one (I : CofiniteIdealIndex R)
    (hI : I.val ≤ Module.annihilator R (cofiniteRingQuotient I).obj)
    (t : cofiniteFunctorStage T I) :
    cofiniteStageEvaluation T (cofiniteRingQuotient I) I hI t (1 : R ⧸ I.val) = t := by
  rw [cofiniteStageEvaluation_apply, cofiniteQuotientPoint_self_one]
  simp

end SGA.SGA2.ExposeIV
