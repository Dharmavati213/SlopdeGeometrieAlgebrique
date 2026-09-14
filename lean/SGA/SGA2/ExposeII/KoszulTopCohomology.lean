/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.KoszulRegularResolution
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# The concrete top degree of the Hom–Koszul complex

The top term of the original recursively defined Koszul complex is its
coefficient module. Evaluating Hom on this identification computes the image
of the last dual differential and hence the top cohomology.
-/

noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex Opposite

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The actual top term of the scalar cofiber is the preceding top term,
because the unshifted summand in that degree is zero. -/
def koszulTopStepIso (M : ModuleCat.{u} R) (f : R) (fs : List R) :
    (koszulComplex M (f :: fs)).X (fs.length + 1) ≅
      (koszulComplex M fs).X fs.length where
  hom := homotopyCofiber.fstX (f • 𝟙 (koszulComplex M fs)) (fs.length + 1) fs.length rfl
  inv := homotopyCofiber.inlX (f • 𝟙 (koszulComplex M fs)) fs.length (fs.length + 1) rfl
  hom_inv_id := by
    apply homotopyCofiber.ext_from_X (f • 𝟙 (koszulComplex M fs))
      fs.length (fs.length + 1) rfl
    · simp
      rfl
    · exact (koszulComplex_isZero_X M fs (fs.length + 1) (Nat.lt_succ_self _)).eq_of_src _ _
  inv_hom_id := homotopyCofiber.inlX_fstX _ _ _ _

/-- The top Koszul term is canonically its coefficient module, with the
orientation given by the original recursive cofiber inclusions. -/
def koszulTopIso (M : ModuleCat.{u} R) :
    (fs : List R) → (koszulComplex M fs).X fs.length ≅ M
  | [] => singleObjXSelf (ComplexShape.down ℕ) 0 M
  | f :: fs => koszulTopStepIso M f fs ≪≫ koszulTopIso M fs

/-- Top-degree Hom is evaluated on the actual ordered top generator. -/
def koszulTopHomEquiv (fs : List R) (E : ModuleCat.{u} R) :
    ((koszulComplex (ModuleCat.of R R) fs).X fs.length ⟶ E) ≃ₗ[R] E :=
  (Linear.homCongr R (koszulTopIso (ModuleCat.of R R) fs) (Iso.refl E)).trans
    (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R R E))

@[simp]
theorem koszulTopHomEquiv_apply (fs : List R) (E : ModuleCat.{u} R)
    (g : (koszulComplex (ModuleCat.of R R) fs).X fs.length ⟶ E) :
    koszulTopHomEquiv fs E g = g ((koszulTopIso (ModuleCat.of R R) fs).inv 1) := rfl

/-- The incoming top cochain differential, followed by evaluation on the
ordered top generator of the original Koszul complex. -/
def koszulTopBoundary (fs : List R) (E : ModuleCat.{u} R) :
    ((koszulComplex (ModuleCat.of R R) fs).X (fs.length - 1) ⟶ E) →ₗ[R] E :=
  (koszulTopHomEquiv fs E).toLinearMap.comp
    (Linear.leftComp R E ((koszulComplex (ModuleCat.of R R) fs).d fs.length (fs.length - 1)))

@[simp]
theorem koszulTopBoundary_apply (fs : List R) (E : ModuleCat.{u} R)
    (g : (koszulComplex (ModuleCat.of R R) fs).X (fs.length - 1) ⟶ E) :
    koszulTopBoundary fs E g =
      koszulTopHomEquiv fs E ((koszulComplex (ModuleCat.of R R) fs).d
        fs.length (fs.length - 1) ≫ g) := rfl

/-- The top dual boundary on a nonempty tail is the sum of the negative
old dual boundary and scalar multiplication on the unshifted summand. -/
theorem koszulTopBoundary_cons (f : R) (fs : List R) (E : ModuleCat.{u} R)
    (hfs : 0 < fs.length)
    (g : (koszulComplex (ModuleCat.of R R) (f :: fs)).X fs.length ⟶ E) :
    koszulTopBoundary (f :: fs) E g =
      -koszulTopBoundary fs E
        (homotopyCofiber.inlX (f • 𝟙 (koszulComplex (ModuleCat.of R R) fs))
          (fs.length - 1) fs.length (by simpa using Nat.sub_add_cancel hfs) ≫ g) +
      f • koszulTopHomEquiv fs E
        (homotopyCofiber.inrX (f • 𝟙 (koszulComplex (ModuleCat.of R R) fs)) fs.length ≫ g) := by
  let K := koszulComplex (ModuleCat.of R R) fs
  let φ := f • 𝟙 K
  change koszulTopHomEquiv fs E
    (homotopyCofiber.inlX φ fs.length (fs.length + 1) rfl ≫
      (homotopyCofiber φ).d (fs.length + 1) fs.length ≫ g) = _
  erw [homotopyCofiber.inlX_d_assoc φ (fs.length + 1) fs.length (fs.length - 1)
    rfl (by simpa using Nat.sub_add_cancel hfs)]
  simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc,
    φ, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
    Linear.smul_comp, Category.id_comp, map_add, map_neg, map_smul]
  rfl

/-- For a singleton the top dual boundary is just multiplication by its
generator, expressed through the existing top-term evaluation. -/
theorem koszulTopBoundary_singleton (f : R) (E : ModuleCat.{u} R)
    (g : (koszulComplex (ModuleCat.of R R) [f]).X 0 ⟶ E) :
    koszulTopBoundary [f] E g =
      f • koszulTopHomEquiv [] E
        (homotopyCofiber.inrX (f • 𝟙 (koszulComplex (ModuleCat.of R R) [])) 0 ≫ g) := by
  let K := koszulComplex (ModuleCat.of R R) []
  let φ := f • 𝟙 K
  change koszulTopHomEquiv [] E
    (homotopyCofiber.inlX φ 0 1 rfl ≫ (homotopyCofiber φ).d 1 0 ≫ g) = _
  erw [homotopyCofiber.inlX_d'_assoc φ 1 0 rfl (by simp)]
  simp only [φ, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
    Linear.smul_comp, Category.id_comp, map_smul]
  rfl

/-- The image of the last dual differential is precisely the generated
ideal times the coefficient module. This is an actual image calculation,
valid without regularity or noetherian hypotheses. -/
theorem koszulTopBoundary_range (fs : List R) (E : ModuleCat.{u} R) :
    LinearMap.range (koszulTopBoundary fs E) = koszulIdeal fs • (⊤ : Submodule R E) := by
  open scoped Pointwise in
  induction fs with
  | nil =>
    rw [koszulIdeal_nil, Submodule.bot_smul]
    apply LinearMap.range_eq_bot.mpr
    ext g
    change koszulTopHomEquiv [] E
      ((koszulComplex (ModuleCat.of R R) []).d 0 0 ≫ g) = 0
    rw [(koszulComplex (ModuleCat.of R R) []).shape 0 0 (by simp), zero_comp, map_zero]
  | cons f fs ih =>
    let K := koszulComplex (ModuleCat.of R R) fs
    let φ := f • 𝟙 K
    rw [koszulIdeal_cons, Submodule.sup_smul, Submodule.ideal_span_singleton_smul, ← ih]
    have hleft : f • (⊤ : Submodule R E) ≤ LinearMap.range (koszulTopBoundary (f :: fs) E) := by
      intro z hz
      obtain ⟨y, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists z f ⊤).mp hz
      refine ⟨homotopyCofiber.sndX φ fs.length ≫ (koszulTopHomEquiv fs E).symm y, ?_⟩
      by_cases hn : fs = []
      · subst fs
        rw [koszulTopBoundary_singleton]
        dsimp only [φ, K]
        erw [homotopyCofiber.inrX_sndX_assoc]
        exact congrArg (f • ·) ((koszulTopHomEquiv [] E).apply_symm_apply y)
      · rw [koszulTopBoundary_cons f fs E (List.length_pos_iff.mpr hn)]
        dsimp only [φ, K]
        simp only [homotopyCofiber.inlX_sndX_assoc,
          homotopyCofiber.inrX_sndX_assoc, zero_comp, map_zero, neg_zero, zero_add,
          LinearEquiv.apply_symm_apply]
    by_cases hn : fs = []
    · subst fs
      have hbot : LinearMap.range (koszulTopBoundary [] E) = ⊥ := by
        simpa only [koszulIdeal_nil, Submodule.bot_smul] using ih
      rw [hbot, sup_bot_eq]
      apply le_antisymm ?_ hleft
      rintro z ⟨g, rfl⟩
      rw [koszulTopBoundary_singleton]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.mem_top)
    · have hp := List.length_pos_iff.mpr hn
      apply le_antisymm
      · rintro z ⟨g, rfl⟩
        rw [koszulTopBoundary_cons f fs E hp]
        apply Submodule.add_mem _
        · exact Submodule.mem_sup_right ((LinearMap.range (koszulTopBoundary fs E)).neg_mem
            (LinearMap.mem_range_self _ _))
        · exact Submodule.mem_sup_left (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
      · apply sup_le hleft
        rintro z ⟨g, rfl⟩
        refine ⟨-(homotopyCofiber.fstX φ fs.length (fs.length - 1)
          (by simpa using Nat.sub_add_cancel hp) ≫ g), ?_⟩
        rw [koszulTopBoundary_cons f fs E hp]
        dsimp only [φ, K]
        simp only [Preadditive.comp_neg,
          homotopyCofiber.inlX_fstX_assoc, homotopyCofiber.inrX_fstX_assoc,
          zero_comp, map_neg, neg_neg, map_zero, neg_zero, smul_zero, add_zero]

/-- The outgoing top Hom–Koszul differential vanishes because the next
term of the original Koszul chain complex is zero. -/
theorem koszulTopCochain_d_eq_zero (fs : List R) (E : ModuleCat.{u} R) :
    ((koszulComplex (ModuleCat.of R R) fs).linearYonedaObj R E).d
      fs.length (fs.length + 1) = 0 := by
  have hK := koszulComplex_isZero_X (ModuleCat.of R R) fs
    (fs.length + 1) (Nat.lt_succ_self _)
  have hH : IsZero (((koszulComplex (ModuleCat.of R R) fs).linearYonedaObj R E).X
      (fs.length + 1)) :=
    ((linearYoneda R (ModuleCat.{u} R)).obj E).map_isZero hK.op
  exact hH.eq_of_tgt _ 0

/-- Evaluation of the actual top Hom term identifies its quotient by
coboundaries with the quotient of coefficients by the generated ideal. -/
def koszulTopOpcyclesEquivQuotient (fs : List R) (E : ModuleCat.{u} R) :
    (((koszulComplex (ModuleCat.of R R) fs).linearYonedaObj R E).X fs.length ⧸
      LinearMap.range (((koszulComplex (ModuleCat.of R R) fs).linearYonedaObj R E).d
        (fs.length - 1) fs.length).hom) ≃ₗ[R]
      E ⧸ koszulIdeal fs • (⊤ : Submodule R E) :=
  Submodule.Quotient.equiv _ _ (koszulTopHomEquiv fs E) (by
    rw [← LinearMap.range_comp]
    exact koszulTopBoundary_range fs E)

/-- The top cohomology of the original Hom–Koszul complex is the original
coefficient quotient. This holds for arbitrary lists over any commutative
ring, without any regularity assumption. -/
def koszulTopCohomologyIsoQuotient (fs : List R) (E : ModuleCat.{u} R) :
    koszulCohomology fs E fs.length ≅
      ModuleCat.of R (E ⧸ koszulIdeal fs • (⊤ : Submodule R E)) :=
  ((koszulComplex (ModuleCat.of R R) fs).linearYonedaObj R E).homologyIsoSc'
      (fs.length - 1) fs.length (fs.length + 1) (by cases fs.length <;> simp) (by simp) ≪≫
    (((koszulComplex (ModuleCat.of R R) fs).linearYonedaObj R E).sc'
      (fs.length - 1) fs.length (fs.length + 1)).asIsoHomologyι
        (koszulTopCochain_d_eq_zero fs E) ≪≫
    (((koszulComplex (ModuleCat.of R R) fs).linearYonedaObj R E).sc'
      (fs.length - 1) fs.length (fs.length + 1)).moduleCatOpcyclesIso ≪≫
    (koszulTopOpcyclesEquivQuotient fs E).toModuleIso

/-- With ring coefficients, top Hom–Koszul cohomology is literally the
quotient ring, considered as its original `R`-module. -/
def koszulTopCohomologyRingIsoQuotient (fs : List R) :
    koszulCohomology fs (ModuleCat.of R R) fs.length ≅ ModuleCat.of R (R ⧸ koszulIdeal fs) :=
  koszulTopCohomologyIsoQuotient fs (ModuleCat.of R R) ≪≫
    (Submodule.quotEquivOfEq _ (koszulIdeal fs)
      (by simp only [Ideal.smul_eq_mul, Ideal.mul_top])).toModuleIso

end SGA.SGA2.ExposeII
