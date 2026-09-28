/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.HomComplexConnectingCocycle
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! # V.1: computing the Ext boundary with the original lifted cocycle -/

noncomputable section
universe w v u
open CategoryTheory Limits Preadditive HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X : C} (P : ProjectiveResolution X)

section Derived
variable [HasDerivedCategory C]

/-- The canonical projective-resolution class comparison retains the actual
resolution augmentation, with the single-object identities simplified. -/
theorem projectiveExtCocycle_hom {Y : C} {n : ℕ}
    (z : Cocycle P.cochainComplex ((singleFunctor C 0).obj Y) (n : ℤ)) :
    (P.extEquivCohomologyClass.symm (CohomologyClass.mk z)).hom =
      inv (DerivedCategory.Q.map P.π') ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q := by
  rw [ProjectiveResolution.extEquivCohomologyClass_symm_mk_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

omit [HasExt C] in
/-- The original Ext connecting morphism is the triangle of the original
single-object short exact sequence, with no additional change of objects. -/
theorem singleδ_eq_triangleOfSESδ (S : ShortComplex C) (hS : S.ShortExact) :
    hS.singleδ = DerivedCategory.triangleOfSESδ
      (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) := by
  dsimp [ShortComplex.ShortExact.singleδ, SingleFunctors.evaluation]
  rw [DerivedCategory.singleFunctorsPostcompQIso_hom_hom,
    DerivedCategory.singleFunctorsPostcompQIso_inv_hom]
  simp only [NatTrans.id_app, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end Derived

/-- The actual Yoneda connecting class is computed by lifting the original
cocycle, differentiating in the Hom complex, and factoring through the
original monomorphism. -/
theorem projectiveExtCocycle_comp_extClass (S : ShortComplex C) (hS : S.ShortExact)
    {n m : ℕ} (h : n + 1 = m)
    (a : Cocycle P.cochainComplex ((singleFunctor C 0).obj S.X₁) (m : ℤ))
    (b : Cochain P.cochainComplex ((singleFunctor C 0).obj S.X₂) (n : ℤ))
    (c : Cocycle P.cochainComplex ((singleFunctor C 0).obj S.X₃) (n : ℤ))
    (hb : δ (n : ℤ) (m : ℤ) b =
      a.1.comp (Cochain.ofHom ((singleFunctor C 0).map S.f)) (add_zero _))
    (hc : b.comp (Cochain.ofHom ((singleFunctor C 0).map S.g)) (add_zero _) = c.1) :
    (P.extEquivCohomologyClass.symm (CohomologyClass.mk c)).comp hS.extClass h =
      P.extEquivCohomologyClass.symm (CohomologyClass.mk a) := by
  let := HasDerivedCategory.standard C
  have hd := homCocycle_connecting_eq_derived (S.map (singleFunctor C 0))
    (by exact_mod_cast h) a b c hb hc
      (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0))
  apply Abelian.Ext.ext
  rw [Abelian.Ext.comp_hom, projectiveExtCocycle_hom,
    ShortComplex.ShortExact.extClass_hom, singleδ_eq_triangleOfSESδ,
    projectiveExtCocycle_hom]
  convert! congrArg (inv (DerivedCategory.Q.map P.π') ≫ ·) hd using 1
  simp only [ShiftedHom.comp, Category.assoc]
  rfl

omit [HasExt C] in
/-- The representative produced by lifting and differentiating is
automatically a cocycle, using the original monomorphism and square-zero. -/
theorem projectiveLiftBoundary_cocycle (S : ShortComplex C) (hS : S.ShortExact)
    {n m : ℕ} (f₂ : P.complex.X n ⟶ S.X₂) (f₁ : P.complex.X m ⟶ S.X₁)
    (hf : P.complex.d m n ≫ f₂ = f₁ ≫ S.f) : P.complex.d (m + 1) m ≫ f₁ = 0 := by
  have := hS.mono_f
  rw [← cancel_mono S.f, Category.assoc, ← hf, ← Category.assoc]
  simp

/-- On the unchanged, unsigned projective-resolution Hom representatives,
the Yoneda boundary carries the exact degree sign `(-1)^(n+1)`. -/
theorem projectiveExtMk_comp_extClass (S : ShortComplex C) (hS : S.ShortExact)
    {n m : ℕ} (h : n + 1 = m)
    (f₃ : P.complex.X n ⟶ S.X₃) (hf₃ : P.complex.d m n ≫ f₃ = 0)
    (f₂ : P.complex.X n ⟶ S.X₂) (hf₂ : f₂ ≫ S.g = f₃)
    (f₁ : P.complex.X m ⟶ S.X₁) (hf₁ : P.complex.d m n ≫ f₂ = f₁ ≫ S.f) :
    (P.extMk f₃ m h hf₃).comp hS.extClass h =
      (m : ℤ).negOnePow • P.extMk f₁ (m + 1) rfl
        (projectiveLiftBoundary_cocycle P S hS f₂ f₁ hf₁) := by
  let a : Cocycle P.cochainComplex ((singleFunctor C 0).obj S.X₁) (m : ℤ) :=
    Cocycle.toSingleMk ((P.cochainComplexXIso (-m) m rfl).hom ≫ f₁) (by simp)
      (-(m + 1)) (by omega) (by
        rw [P.cochainComplex_d (-(m + 1)) (-m) (m + 1) m (by omega) rfl]
        simp [Category.assoc, projectiveLiftBoundary_cocycle P S hS f₂ f₁ hf₁])
  let b : Cochain P.cochainComplex ((singleFunctor C 0).obj S.X₂) (n : ℤ) :=
    Cochain.toSingleMk ((P.cochainComplexXIso (-n) n rfl).hom ≫ f₂) (by simp)
  let c : Cocycle P.cochainComplex ((singleFunctor C 0).obj S.X₃) (n : ℤ) :=
    Cocycle.toSingleMk ((P.cochainComplexXIso (-n) n rfl).hom ≫ f₃) (by simp)
      (-m) (by omega) (by
        simpa [ProjectiveResolution.cochainComplex_d _ _ _ _ _ rfl rfl] using
          congrArg ((P.cochainComplexXIso (-m) m rfl).hom ≫ ·) hf₃)
  have hb : δ (n : ℤ) (m : ℤ) b =
      ((m : ℤ).negOnePow • a).1.comp (Cochain.ofHom ((singleFunctor C 0).map S.f))
        (add_zero _) := by
    dsimp [a, b]
    rw [Cochain.δ_toSingleMk _ _ (m : ℤ) (-m) (by simp)]
    simp only [Cochain.units_smul_comp, ← Cochain.toSingleMk_postcomp]
    congr 2
    rw [ProjectiveResolution.cochainComplex_d _ _ _ m n rfl rfl]
    simp [Category.assoc, hf₁]
  have hc : b.comp (Cochain.ofHom ((singleFunctor C 0).map S.g)) (add_zero _) = c.1 := by
    dsimp [b, c]
    rw [← Cochain.toSingleMk_postcomp, Category.assoc, hf₂]
  have hd := projectiveExtCocycle_comp_extClass P S hS h
    ((m : ℤ).negOnePow • a) b c hb hc
  change (P.extMk f₃ m h hf₃).comp hS.extClass h =
    P.extAddEquivCohomologyClass.symm
      ((CohomologyClass.mkAddMonoidHom _ _ _) ((m : ℤ).negOnePow • a)) at hd
  rw [hd]
  change P.extAddEquivCohomologyClass.symm
      ((CohomologyClass.mkAddMonoidHom _ _ _) (((m : ℤ).negOnePow : ℤ) • a)) =
    ((m : ℤ).negOnePow : ℤ) • P.extAddEquivCohomologyClass.symm
      ((CohomologyClass.mkAddMonoidHom _ _ _) a)
  rw [map_zsmul, map_zsmul]

omit [HasExt C] in
/-- Actual lifts and factorization representatives always exist; they are
obtained from projectivity and the original short exact sequence. -/
theorem exists_projectiveBoundaryLift (S : ShortComplex C) (hS : S.ShortExact)
    {n m : ℕ} (f₃ : P.complex.X n ⟶ S.X₃) (hf₃ : P.complex.d m n ≫ f₃ = 0) :
    ∃ (f₂ : P.complex.X n ⟶ S.X₂) (f₁ : P.complex.X m ⟶ S.X₁),
      f₂ ≫ S.g = f₃ ∧ P.complex.d m n ≫ f₂ = f₁ ≫ S.f := by
  have := hS.epi_g
  have := hS.mono_f
  let f₂ := Projective.factorThru f₃ S.g
  have hf₂ : f₂ ≫ S.g = f₃ := Projective.factorThru_comp f₃ S.g
  have hz : (P.complex.d m n ≫ f₂) ≫ S.g = 0 := by
    rw [Category.assoc, hf₂, hf₃]
  exact ⟨f₂, hS.exact.lift _ hz, hf₂, (hS.exact.lift_f _ hz).symm⟩

/-- Every Ext class has actual lift-and-differentiate representatives with
the proved signed Yoneda boundary formula, using the specified resolution. -/
theorem exists_projectiveExtBoundaryFormula (S : ShortComplex C) (hS : S.ShortExact)
    (n : ℕ) (x : Abelian.Ext X S.X₃ n) :
    ∃ (f₃ : P.complex.X n ⟶ S.X₃) (hf₃ : P.complex.d (n + 1) n ≫ f₃ = 0)
      (f₂ : P.complex.X n ⟶ S.X₂) (f₁ : P.complex.X (n + 1) ⟶ S.X₁)
      (hf₁ : P.complex.d (n + 1) n ≫ f₂ = f₁ ≫ S.f),
      f₂ ≫ S.g = f₃ ∧ P.extMk f₃ (n + 1) rfl hf₃ = x ∧
        x.comp hS.extClass rfl = (n + 1 : ℤ).negOnePow •
          P.extMk f₁ (n + 1 + 1) rfl (projectiveLiftBoundary_cocycle P S hS f₂ f₁ hf₁) := by
  obtain ⟨f₃, hf₃, hx⟩ := P.extMk_surjective x (n + 1) rfl
  obtain ⟨f₂, f₁, hf₂, hf₁⟩ := exists_projectiveBoundaryLift P S hS f₃ hf₃
  refine ⟨f₃, hf₃, f₂, f₁, hf₁, hf₂, hx, ?_⟩
  rw [← hx]
  exact projectiveExtMk_comp_extClass P S hS rfl f₃ hf₃ f₂ hf₂ f₁ hf₁

end SGA.SGA2.ExposeV
