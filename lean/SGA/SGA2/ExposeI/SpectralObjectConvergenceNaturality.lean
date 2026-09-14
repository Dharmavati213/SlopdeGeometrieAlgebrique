/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.SpectralObjectConvergence
import SGA.SGA2.ExposeI.SpectralSequenceCoefficientMaps

/-! # Coefficient naturality of the actual spectral-object convergence filtration -/

noncomputable section

open CategoryTheory Limits ComposableArrows CategoryTheory.Abelian

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI.SpectralObjectCoefficientMaps

variable {C ι : Type*} [Category C] [Category ι] [Abelian C]
  {S T : SpectralObject C ι} (φ : S ⟶ T)

/-- The coefficient map on the actual cokernel defining opcycles. -/
def opcyclesCoefficientMap {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    S.opcycles f g n ⟶ T.opcycles f g n :=
  cokernel.map _ _ ((φ.hom (n - 1)).app (mk₁ g)) ((φ.hom n).app (mk₁ f))
    (φ.comm (n - 1) n (by lia) f g)

@[reassoc (attr := simp)]
lemma p_opcyclesCoefficientMap {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    S.pOpcycles f g n ≫ opcyclesCoefficientMap φ f g n =
      (φ.hom n).app (mk₁ f) ≫ T.pOpcycles f g n := by
  apply cokernel.π_desc

@[reassoc]
lemma opcyclesCoefficientMap_fromOpcycles {i j k : ι}
    (f : i ⟶ j) (g : j ⟶ k) (fg : i ⟶ k) (hfg : f ≫ g = fg) (n : ℤ) :
    opcyclesCoefficientMap φ f g n ≫ T.fromOpcycles f g fg hfg n =
      S.fromOpcycles f g fg hfg n ≫ (φ.hom n).app (mk₁ fg) := by
  rw [← cancel_epi (S.pOpcycles f g n)]
  simp only [p_opcyclesCoefficientMap_assoc,
    SpectralObject.p_fromOpcycles, SpectralObject.p_fromOpcycles_assoc]
  exact ((φ.hom n).naturality _).symm

@[reassoc]
lemma opcyclesCoefficientMap_toE {i j k l : ι}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    opcyclesCoefficientMap φ f₁₂ f₃ n₁ ≫
        T.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ =
      S.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ ≫
        EMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  rw [← cancel_epi (S.pOpcycles f₁₂ f₃ n₁)]
  simp only [p_opcyclesCoefficientMap_assoc,
    SpectralObject.p_opcyclesToE, SpectralObject.p_opcyclesToE_assoc,
    πE_EMap, toCycles_cyclesMap_assoc]

end SpectralObjectCoefficientMaps

namespace SpectralObjectConvergence

open SpectralObjectCoefficientMaps

variable {C : Type*} [Category C] [Abelian C]
  {S T : SpectralObject C EInt} (φ : S ⟶ T)

/-- The actual coefficient map on the total interval. -/
def totalMap (n : ℤ) : total S n ⟶ total T n :=
  (φ.hom n).app (mk₁ (homOfLE bot_le))

@[simp] lemma totalMap_id (n : ℤ) : totalMap (𝟙 S) n = 𝟙 _ := rfl

@[simp] lemma totalMap_comp {U : SpectralObject C EInt} (ψ : T ⟶ U) (n : ℤ) :
    totalMap (φ ≫ ψ) n = totalMap φ n ≫ totalMap ψ n := rfl

/-- Coefficients act on the concrete image-filtration representatives. -/
def filtrationCoefficientMap (n : ℤ) (q : EInt) :
    filtrationObj S n q ⟶ filtrationObj T n q :=
  opcyclesCoefficientMap φ (homOfLE bot_le) (homOfLE le_top) n

@[reassoc (attr := simp)]
lemma filtrationCoefficientMap_ι (n : ℤ) (q : EInt) :
    filtrationCoefficientMap φ n q ≫ filtrationι T n q =
      filtrationι S n q ≫ totalMap φ n :=
  opcyclesCoefficientMap_fromOpcycles φ _ _ _ _ n

@[reassoc]
lemma filtrationCoefficientMap_map (n : ℤ) (q q' : EInt) (h : q ≤ q') :
    filtrationCoefficientMap φ n q ≫ filtrationMap T n q q' h =
      filtrationMap S n q q' h ≫ filtrationCoefficientMap φ n q' := by
  rw [← cancel_mono (filtrationι T n q')]
  simp

/-- The coefficient map on the actual subobjects, not just their opcycle representatives. -/
def filtrationSubobjectMap (n : ℤ) (q : EInt) :
    (filtration S n q : C) ⟶ (filtration T n q : C) :=
  (Subobject.underlyingIso (filtrationι S n q)).hom ≫
    filtrationCoefficientMap φ n q ≫
      (Subobject.underlyingIso (filtrationι T n q)).inv

@[reassoc (attr := simp)]
lemma filtrationSubobjectMap_arrow (n : ℤ) (q : EInt) :
    filtrationSubobjectMap φ n q ≫ (filtration T n q).arrow =
      (filtration S n q).arrow ≫ totalMap φ n := by
  dsimp only [filtrationSubobjectMap, filtration]
  simp

/-- A filtration map is uniquely determined by the actual total map. -/
lemma filtrationSubobjectMap_eq_of_totalMap_eq {ψ : S ⟶ T} (n : ℤ) (q : EInt)
    (h : totalMap φ n = totalMap ψ n) :
    filtrationSubobjectMap φ n q = filtrationSubobjectMap ψ n q := by
  rw [← cancel_mono (filtration T n q).arrow]
  simp only [filtrationSubobjectMap_arrow, h]

@[simp] lemma filtrationSubobjectMap_id (n : ℤ) (q : EInt) :
    filtrationSubobjectMap (𝟙 S) n q = 𝟙 _ := by
  rw [← cancel_mono (filtration S n q).arrow]
  simp

@[simp] lemma filtrationSubobjectMap_comp {U : SpectralObject C EInt}
    (ψ : T ⟶ U) (n : ℤ) (q : EInt) :
    filtrationSubobjectMap (φ ≫ ψ) n q =
      filtrationSubobjectMap φ n q ≫ filtrationSubobjectMap ψ n q := by
  rw [← cancel_mono (filtration U n q).arrow]
  simp

/-- The actual total map preserves the canonical image filtration. -/
theorem totalMap_preserves_filtration (n : ℤ) (q : EInt) :
    imageSubobject ((filtration S n q).arrow ≫ totalMap φ n) ≤ filtration T n q :=
  imageSubobject_le _ (filtrationSubobjectMap φ n q)
    (filtrationSubobjectMap_arrow φ n q)

@[reassoc]
lemma filtrationSubobjectMap_ofLE (n : ℤ) (q q' : EInt) (h : q ≤ q') :
    filtrationSubobjectMap φ n q ≫
        Subobject.ofLE _ _ (filtration_monotone T n h) =
      Subobject.ofLE _ _ (filtration_monotone S n h) ≫
        filtrationSubobjectMap φ n q' := by
  rw [← cancel_mono (filtration T n q').arrow]
  simp

/-- The map induced on the genuine cokernel of consecutive subobject inclusions. -/
def gradedPieceMap (n q : ℤ) : gradedPiece S n q ⟶ gradedPiece T n q :=
  cokernel.map _ _ (filtrationSubobjectMap φ n q)
    (filtrationSubobjectMap φ n (q + 1 : ℤ))
    (filtrationSubobjectMap_ofLE φ n q (q + 1 : ℤ) (by simp)).symm

@[reassoc (attr := simp)]
lemma cokernel_π_gradedPieceMap (n q : ℤ) :
    cokernel.π _ ≫ gradedPieceMap φ n q =
      filtrationSubobjectMap φ n (q + 1 : ℤ) ≫ cokernel.π _ := by
  apply cokernel.π_desc

/-- The associated-graded coefficient map depends only on the total map. -/
lemma gradedPieceMap_eq_of_totalMap_eq {ψ : S ⟶ T} (n q : ℤ)
    (h : totalMap φ n = totalMap ψ n) : gradedPieceMap φ n q = gradedPieceMap ψ n q := by
  rw [← cancel_epi (cokernel.π (Subobject.ofLE _ _
    (filtration_monotone S n (show (q : EInt) ≤ (q + 1 : ℤ) by simp))))]
  simp only [cokernel_π_gradedPieceMap, filtrationSubobjectMap_eq_of_totalMap_eq φ n _ h]

@[simp] lemma gradedPieceMap_id (n q : ℤ) : gradedPieceMap (𝟙 S) n q = 𝟙 _ := by
  rw [← cancel_epi (cokernel.π (Subobject.ofLE _ _
    (filtration_monotone S n (show (q : EInt) ≤ (q + 1 : ℤ) by simp))))]
  simp [gradedPiece]

@[simp] lemma gradedPieceMap_comp {U : SpectralObject C EInt}
    (ψ : T ⟶ U) (n q : ℤ) :
    gradedPieceMap (φ ≫ ψ) n q = gradedPieceMap φ n q ≫ gradedPieceMap ψ n q := by
  rw [← cancel_epi (cokernel.π (Subobject.ofLE _ _
    (filtration_monotone S n (show (q : EInt) ≤ (q + 1 : ℤ) by simp))))]
  simp

@[reassoc]
lemma gradedPieceMap_eqToIso (n n' q : ℤ) (h : n = n') :
    gradedPieceMap φ n q ≫ eqToHom (congrArg (fun k => gradedPiece T k q) h) =
      eqToHom (congrArg (fun k => gradedPiece S k q) h) ≫ gradedPieceMap φ n' q := by
  subst n'
  simp

/-- The actual induced cokernel map for any two comparable filtration indices. -/
def filtrationQuotientMap (n : ℤ) (a b : EInt) (h : a ≤ b) :
    cokernel (Subobject.ofLE _ _ (filtration_monotone S n h)) ⟶
      cokernel (Subobject.ofLE _ _ (filtration_monotone T n h)) :=
  cokernel.map _ _ (filtrationSubobjectMap φ n a) (filtrationSubobjectMap φ n b)
    (filtrationSubobjectMap_ofLE φ n a b h).symm

/-- Equality transport for genuine quotients of subobjects. -/
def cokernelOfLEIsoOfEq {V : C} (A B A' B' : Subobject V)
    (h : A ≤ B) (h' : A' ≤ B') (hA : A = A') (hB : B = B') :
    cokernel (Subobject.ofLE A B h) ≅ cokernel (Subobject.ofLE A' B' h') := by
  subst A' B'
  exact Iso.refl _

/-- Reindexing equal filtration terms transports their original quotient. -/
def filtrationQuotientIsoOfEq (S : SpectralObject C EInt) (n : ℤ)
    (a b a' b' : EInt) (h : a ≤ b) (h' : a' ≤ b') (ha : a = a') (hb : b = b') :
    cokernel (Subobject.ofLE _ _ (filtration_monotone S n h)) ≅
      cokernel (Subobject.ofLE _ _ (filtration_monotone S n h')) :=
  cokernelOfLEIsoOfEq _ _ _ _ _ _
    (congrArg (filtration S n) ha) (congrArg (filtration S n) hb)

@[reassoc]
lemma filtrationQuotientIsoOfEq_naturality (n : ℤ)
    (a b a' b' : EInt) (h : a ≤ b) (h' : a' ≤ b') (ha : a = a') (hb : b = b') :
    filtrationQuotientMap φ n a b h ≫
        (filtrationQuotientIsoOfEq T n a b a' b' h h' ha hb).hom =
      (filtrationQuotientIsoOfEq S n a b a' b' h h' ha hb).hom ≫
        filtrationQuotientMap φ n a' b' h' := by
  subst a' b'
  simp [filtrationQuotientIsoOfEq, cokernelOfLEIsoOfEq]

/-- Coefficients act on the actual infinite-endpoint page terms. -/
def inftyTermMap (n q : ℤ) : inftyTerm S n q ⟶ inftyTerm T n q :=
  EMap φ _ _ _ _ _ _ _ _

@[reassoc]
lemma filtrationToInfty_naturality (n q : ℤ) :
    filtrationCoefficientMap φ n (q + 1 : ℤ) ≫ filtrationToInfty T n q =
      filtrationToInfty S n q ≫ inftyTermMap φ n q :=
  opcyclesCoefficientMap_toE φ _ _ _ _ _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma cokernel_π_gradedPieceIsoInfty_hom (n q : ℤ) :
    cokernel.π _ ≫ (gradedPieceIsoInfty S n q).hom =
      (Subobject.underlyingIso (filtrationι S n (q + 1 : ℤ))).hom ≫
        filtrationToInfty S n q := by
  dsimp only [gradedPieceIsoInfty, Iso.trans_hom]
  simp only [cokernel.mapIso_hom, cokernel.map, cokernel.π_desc_assoc, Category.assoc]
  congr 1
  exact (cokernelIsCokernel (filtrationSequence S n q).f).comp_coconePointUniqueUpToIso_hom
    (filtrationSequence_exact S n q).gIsCokernel WalkingParallelPair.one

@[reassoc]
lemma gradedPieceIsoInfty_naturality (n q : ℤ) :
    gradedPieceMap φ n q ≫ (gradedPieceIsoInfty T n q).hom =
      (gradedPieceIsoInfty S n q).hom ≫ inftyTermMap φ n q := by
  rw [← cancel_epi (cokernel.π (Subobject.ofLE _ _
    (filtration_monotone S n (show (q : EInt) ≤ (q + 1 : ℤ) by simp))))]
  dsimp only [gradedPieceMap, cokernel.map]
  rw [cokernel.π_desc_assoc, Category.assoc, cokernel_π_gradedPieceIsoInfty_hom,
    cokernel_π_gradedPieceIsoInfty_hom_assoc]
  simp only [filtrationSubobjectMap, Category.assoc, Iso.inv_hom_id_assoc,
    filtrationToInfty_naturality]

omit [Abelian C] in
private lemma iso_comp_symm_naturality
    {A B D A' B' D' : C} (a : A ≅ B) (b : D ≅ B)
    (a' : A' ≅ B') (b' : D' ≅ B') (f : A ⟶ A') (g : B ⟶ B') (h : D ⟶ D')
    (ha : f ≫ a'.hom = a.hom ≫ g) (hb : h ≫ b'.hom = b.hom ≫ g) :
    f ≫ (a' ≪≫ b'.symm).hom = (a ≪≫ b.symm).hom ≫ h := by
  rw [← cancel_mono b'.hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, hb, Iso.inv_hom_id_assoc]
  exact ha

section FirstQuadrant

variable [S.IsFirstQuadrant] [T.IsFirstQuadrant]

/-- The original comparison from finite to infinite endpoints is natural
in every coefficient morphism. -/
@[reassoc]
lemma finiteEndpointsIsoInfty_naturality (n q : ℤ) (a b : EInt)
    (ha : a ≤ (q : EInt)) (hb : (q + 1 : ℤ) ≤ b)
    (ha0 : a ≤ (0 : ℤ)) (hnb : (n - 1 : ℤ) < b) :
    EMap φ (homOfLE ha) (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp))
        (homOfLE hb) (n - 1) n (n + 1) (by lia) rfl ≫
      (finiteEndpointsIsoInfty T n q a b ha hb ha0 hnb).hom =
    (finiteEndpointsIsoInfty S n q a b ha hb ha0 hnb).hom ≫ inftyTermMap φ n q := by
  apply iso_comp_symm_naturality
  · exact EMap_map φ _ _ _ _ _ _ _ _ _ _ _ _
  · exact EMap_map φ _ _ _ _ _ _ _ _ _ _ _ _

unseal SpectralObject.spectralSequence in
/-- The original stable finite-page comparison with the infinite-endpoint
term intertwines the actual spectral-sequence coefficient maps. -/
@[reassoc]
lemma stablePageIsoInfty_naturality (p q r : ℤ) (hr : 2 ≤ r)
    (hqr : q + 2 ≤ r) (hpr : p + 1 ≤ r) :
    ((spectralSequenceMap φ SpectralObject.coreE₂Cohomological).hom r hr).f (p, q) ≫
        (stablePageIsoInfty T p q r hr hqr hpr).hom =
      (stablePageIsoInfty S p q r hr hqr hpr).hom ≫ inftyTermMap φ (p + q) q := by
  dsimp only [stablePageIsoInfty, Iso.trans_hom]
  have h := pageXIso_inv_pageXMap φ SpectralObject.coreE₂Cohomological r hr (p, q)
    (q - r + 2 : ℤ) q (q + 1 : ℤ) (q + r - 1 : ℤ) rfl rfl rfl rfl
    (p + q - 1) (p + q) (p + q + 1) rfl (by lia) rfl
  rw [← cancel_epi (S.spectralSequencePageXIso SpectralObject.coreE₂Cohomological
    r hr (p, q) (q - r + 2 : ℤ) q (q + 1 : ℤ) (q + r - 1 : ℤ)
    rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1) rfl).inv]
  dsimp only [SpectralObject.spectralSequencePageXIso, spectralSequenceMap, pageMap]
  erw [← Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact finiteEndpointsIsoInfty_naturality φ _ _ _ _ _ _ _ _

/-- Coefficients commute with the existing stable-page isomorphism to the
genuine associated graded of the actual total filtration. -/
@[reassoc]
lemma stablePageIsoGraded_naturality (p q r : ℤ) (hr : 2 ≤ r)
    (hqr : q + 2 ≤ r) (hpr : p + 1 ≤ r) :
    ((spectralSequenceMap φ SpectralObject.coreE₂Cohomological).hom r hr).f (p, q) ≫
        (stablePageIsoGraded T p q r hr hqr hpr).hom =
      (stablePageIsoGraded S p q r hr hqr hpr).hom ≫ gradedPieceMap φ (p + q) q :=
  iso_comp_symm_naturality _ _ _ _ _ _ _
    (stablePageIsoInfty_naturality φ p q r hr hqr hpr)
    (gradedPieceIsoInfty_naturality φ (p + q) q)

/-- The original uniform-total-degree stable-page comparison is natural. -/
@[reassoc]
lemma stablePageIsoGradedTotal_naturality (n : ℕ) (q : Fin (n + 1)) (r : ℤ)
    (hr : (n : ℤ) + 2 ≤ r) :
    ((spectralSequenceMap φ SpectralObject.coreE₂Cohomological).hom r (by lia)).f
        ((n : ℤ) - q, q) ≫ (stablePageIsoGradedTotal T n q r hr).hom =
      (stablePageIsoGradedTotal S n q r hr).hom ≫ gradedPieceMap φ n q := by
  dsimp only [stablePageIsoGradedTotal, Iso.trans_hom, eqToIso.hom]
  rw [stablePageIsoGraded_naturality_assoc,
    gradedPieceMap_eqToIso φ _ _ _ (sub_add_cancel (n : ℤ) (q : ℤ))]
  simp only [Category.assoc]

end FirstQuadrant

end SpectralObjectConvergence

end SGA.SGA2.ExposeI
