/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# The canonical total-cohomology filtration of a spectral object

The filtration is the image of `Hⁿ(-∞, q) → Hⁿ(-∞, +∞)`, with
concrete representatives provided by the spectral object's opcycles.
Its genuine associated-graded cokernels identify with the
infinite-endpoint terms. First-quadrant vanishing makes the filtration
finite and exhaustive and identifies these quotients with actual finite
pages, for both integer and natural bidegrees, with explicit bounds.
-/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open CategoryTheory.Abelian

namespace SGA.SGA2.ExposeI.SpectralObjectConvergence

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Abelian C] (X : SpectralObject C EInt)

/-- The actual total cohomology object of a spectral object. -/
def total (n : ℤ) : C := (X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))

/-- Truncated cohomology with lower endpoint `-∞`. -/
def truncated (n : ℤ) (q : EInt) : C :=
  (X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ q)))

/-- The actual natural map from truncated cohomology to total cohomology. -/
def toTotal (n : ℤ) (q : EInt) : truncated X n q ⟶ total X n :=
  (X.H n).map (twoδ₂Toδ₁ (homOfLE bot_le) (homOfLE le_top) (homOfLE bot_le)
    (Subsingleton.elim _ _))

/-- A concrete representative of the image filtration. -/
def filtrationObj (n : ℤ) (q : EInt) : C :=
  X.opcycles (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE le_top) n

/-- Its canonical embedding in the actual total cohomology. -/
def filtrationι (n : ℤ) (q : EInt) : filtrationObj X n q ⟶ total X n :=
  X.fromOpcycles (homOfLE bot_le) (homOfLE le_top) (homOfLE bot_le)
    (Subsingleton.elim _ _) n

instance (n : ℤ) (q : EInt) : Mono (filtrationι X n q) := by
  dsimp [filtrationι]
  infer_instance

/-- The epimorphism from truncated cohomology onto its image. -/
def filtrationπ (n : ℤ) (q : EInt) : truncated X n q ⟶ filtrationObj X n q :=
  X.pOpcycles (homOfLE bot_le) (homOfLE le_top) n

instance (n : ℤ) (q : EInt) : Epi (filtrationπ X n q) := by
  dsimp [filtrationπ]
  infer_instance

@[reassoc (attr := simp)] theorem filtrationπ_ι (n : ℤ) (q : EInt) :
    filtrationπ X n q ≫ filtrationι X n q = toTotal X n q :=
  X.p_fromOpcycles _ _ _ _ _

/-- The canonical subobject filtration of total cohomology. -/
def filtration (n : ℤ) (q : EInt) : Subobject (total X n) :=
  Subobject.mk (filtrationι X n q)

/-- These subobjects really are the images of the actual truncated maps. -/
theorem filtration_eq_imageSubobject (n : ℤ) (q : EInt) :
    filtration X n q = imageSubobject (toTotal X n q) := by
  have := strongEpi_of_epi (filtrationπ X n q)
  apply Subobject.eq_of_comm
    (Subobject.underlyingIso (filtrationι X n q) ≪≫
      image.isoStrongEpiMono (filtrationπ X n q) (filtrationι X n q) (filtrationπ_ι X n q) ≪≫
      (imageSubobjectIso (toTotal X n q)).symm)
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, imageSubobject_arrow',
    image.isoStrongEpiMono_hom_comp_ι, Subobject.underlyingIso_hom_comp_eq_mk]

/-- The transition map between consecutive or more widely separated
image-filtration representatives. -/
def filtrationMap (n : ℤ) (q q' : EInt) (h : q ≤ q') :
    filtrationObj X n q ⟶ filtrationObj X n q' :=
  X.opcyclesMap _ _ _ _
    (homMk₂ (𝟙 ⊥) (homOfLE h) (𝟙 ⊤) (Subsingleton.elim _ _) (Subsingleton.elim _ _)) n

@[reassoc (attr := simp)] theorem filtrationπ_map (n : ℤ) (q q' : EInt) (h : q ≤ q') :
    filtrationπ X n q ≫ filtrationMap X n q q' h =
      (X.H n).map (homMk₁ (𝟙 ⊥) (homOfLE h) (Subsingleton.elim _ _)) ≫
        filtrationπ X n q' := by
  exact X.p_opcyclesMap _ _ _ _ _ _ n

@[reassoc (attr := simp)] theorem filtrationMap_ι (n : ℤ) (q q' : EInt) (h : q ≤ q') :
    filtrationMap X n q q' h ≫ filtrationι X n q' = filtrationι X n q := by
  rw [← cancel_epi (filtrationπ X n q), ← Category.assoc, filtrationπ_map,
    Category.assoc, filtrationπ_ι, filtrationπ_ι]
  dsimp [toTotal]
  rw [← Functor.map_comp]
  congr 1

instance (n : ℤ) (q q' : EInt) (h : q ≤ q') : Mono (filtrationMap X n q q' h) :=
  mono_of_mono_fac (filtrationMap_ι X n q q' h)

/-- The actual image filtration is increasing. -/
theorem filtration_monotone (n : ℤ) : Monotone (filtration X n) :=
  fun q q' h => Subobject.mk_le_mk_of_comm (filtrationMap X n q q' h)
    (filtrationMap_ι X n q q' h)

/-- The lower infinite endpoint of the filtration is zero. -/
theorem filtration_bot (n : ℤ) : filtration X n ⊥ = ⊥ := by
  apply Subobject.mk_eq_bot_iff_zero.mpr
  apply (X.isZero_opcycles _ _ _ ?_).eq_of_src
  exact X.isZero_H_obj_of_isIso _ (by exact inferInstanceAs (IsIso (𝟙 (⊥ : EInt)))) n

/-- The upper infinite endpoint is the whole total cohomology. -/
theorem filtration_top (n : ℤ) : filtration X n ⊤ = ⊤ := by
  have : IsIso (filtrationι X n ⊤) := X.isIso_fromOpcycles _ _ _ _ n
    (X.isZero_H_obj_of_isIso _ (by exact inferInstanceAs (IsIso (𝟙 (⊤ : EInt)))) n)
  exact Subobject.mk_eq_top_of_isIso _

/-- The infinite-endpoint term in total degree `n` and filtration degree `q`. -/
def inftyTerm (n q : ℤ) : C :=
  X.E (homOfLE (bot_le : (⊥ : EInt) ≤ q))
    (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp))
    (homOfLE le_top) (n - 1) n (n + 1)

/-- The canonical projection of a filtration term onto its infinite-page quotient. -/
def filtrationToInfty (n q : ℤ) : filtrationObj X n (q + 1 : ℤ) ⟶ inftyTerm X n q :=
  X.opcyclesToE (homOfLE bot_le)
    (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp)) (homOfLE le_top)
    (homOfLE bot_le) (Subsingleton.elim _ _) (n - 1) n (n + 1)

instance (n q : ℤ) : Epi (filtrationToInfty X n q) := by
  dsimp [filtrationToInfty]
  infer_instance

@[reassoc (attr := simp)] theorem filtrationMap_toInfty (n q : ℤ) :
    filtrationMap X n q (q + 1 : ℤ) (by simp) ≫ filtrationToInfty X n q = 0 := by
  rw [← cancel_epi (filtrationπ X n q), ← Category.assoc, filtrationπ_map,
    Category.assoc, comp_zero]
  have hz := (X.cokernelSequenceOpcyclesE (homOfLE bot_le)
    (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp)) (homOfLE le_top)
    (homOfLE bot_le) (Subsingleton.elim _ _) (n - 1) n (n + 1)).zero
  dsimp only [SpectralObject.cokernelSequenceOpcyclesE] at hz
  convert! hz using 1
  simp only [Category.assoc]
  congr 2

/-- The actual short exact sequence of consecutive filtration representatives
and the infinite-endpoint page term. -/
def filtrationSequence (n q : ℤ) : ShortComplex C :=
  ShortComplex.mk _ _ (filtrationMap_toInfty X n q)

instance (n q : ℤ) : Mono (filtrationSequence X n q).f := by
  dsimp [filtrationSequence]
  infer_instance

instance (n q : ℤ) : Epi (filtrationSequence X n q).g := by
  dsimp [filtrationSequence]
  infer_instance

theorem filtrationSequence_exact (n q : ℤ) : (filtrationSequence X n q).Exact := by
  let S := X.cokernelSequenceOpcyclesE (homOfLE (bot_le : (⊥ : EInt) ≤ q))
    (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp)) (homOfLE le_top)
    (homOfLE bot_le) (Subsingleton.elim _ _) (n - 1) n (n + 1)
  let φ : S ⟶ filtrationSequence X n q :=
    { τ₁ := filtrationπ X n q
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp only [S, SpectralObject.cokernelSequenceOpcyclesE, filtrationSequence]
        rw [Category.comp_id, filtrationπ_map]
        congr 2
      comm₂₃ := by simp [S, filtrationSequence, filtrationToInfty] }
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
  have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp
    (X.cokernelSequenceOpcyclesE_exact _ _ _ _ _ _ _ _)

theorem filtrationSequence_shortExact (n q : ℤ) : (filtrationSequence X n q).ShortExact :=
  ⟨filtrationSequence_exact X n q⟩

/-- The associated graded is the genuine cokernel of the inclusion of
consecutive subobjects of the actual total object. -/
def gradedPiece (n q : ℤ) : C :=
  cokernel (Subobject.ofLE (filtration X n q) (filtration X n (q + 1 : ℤ))
    (filtration_monotone X n (by simp)))

/-- The genuine associated-graded quotient identifies with the spectral
object's infinite-endpoint term, without any convergence assumption. -/
def gradedPieceIsoInfty (n q : ℤ) : gradedPiece X n q ≅ inftyTerm X n q :=
  cokernel.mapIso _ (filtrationMap X n q (q + 1 : ℤ) (by simp))
    (Subobject.underlyingIso (filtrationι X n q))
    (Subobject.underlyingIso (filtrationι X n (q + 1 : ℤ))) (by
      dsimp only [filtration]
      rw [Subobject.ofLE_mk_le_mk_of_comm (filtrationMap X n q (q + 1 : ℤ) (by simp))
        (filtrationMap_ι X n q (q + 1 : ℤ) (by simp))]
      simp) ≪≫
    (cokernelIsCokernel (filtrationSequence X n q).f).coconePointUniqueUpToIso
      (filtrationSequence_exact X n q).gIsCokernel

section FirstQuadrant

variable [X.IsFirstQuadrant]

/-- First-quadrant vanishing makes every nonpositive filtration term zero. -/
theorem filtration_eq_bot (n : ℤ) (q : EInt) (hq : q ≤ (0 : ℤ)) :
    filtration X n q = ⊥ := by
  apply Subobject.mk_eq_bot_iff_zero.mpr
  exact (X.isZero_opcycles _ _ n
    (X.isZero₁_of_isFirstQuadrant ⊥ q bot_le hq n)).eq_of_src _ _

/-- In degree `n`, the filtration is exhaustive as soon as `n < q`. -/
theorem filtration_eq_top (n : ℤ) (q : EInt) (hq : (n : EInt) < q) :
    filtration X n q = ⊤ := by
  have : IsIso (filtrationι X n q) := X.isIso_fromOpcycles _ _ _ _ n
    (X.isZero₂_of_isFirstQuadrant q ⊤ le_top n hq)
  exact Subobject.mk_eq_top_of_isIso _

/-- A genuinely finite filtration of total degree `n ≥ 0`, from term zero
through term `n + 1`. -/
def finiteFiltration (n : ℕ) : Fin (n + 2) →o Subobject (total X n) where
  toFun q := filtration X n (q.1 : ℤ)
  monotone' := fun a b h => filtration_monotone X n (by simpa using h)

@[simp] theorem finiteFiltration_zero (n : ℕ) : finiteFiltration X n 0 = ⊥ :=
  filtration_eq_bot X n 0 le_rfl

@[simp] theorem finiteFiltration_last (n : ℕ) : finiteFiltration X n (Fin.last (n + 1)) = ⊤ := by
  apply filtration_eq_top
  simp only [Fin.val_last, Nat.cast_add, Nat.cast_one, WithBotTop.coe_lt_coe]
  lia

/-- First-quadrant vanishing identifies finite outer endpoints with the
infinite-endpoint term as soon as both endpoints lie beyond the possible
nonzero region. -/
def finiteEndpointsIsoInfty (n q : ℤ) (a b : EInt)
    (ha : a ≤ (q : EInt)) (hb : (q + 1 : ℤ) ≤ b)
    (ha0 : a ≤ (0 : ℤ)) (hnb : (n - 1 : ℤ) < b) :
    X.E (homOfLE ha) (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp))
      (homOfLE hb) (n - 1) n (n + 1) ≅ inftyTerm X n q :=
  X.isoMapFourδ₄Toδ₃' a q (q + 1 : ℤ) b ⊤ ha (by simp) hb le_top
    (n - 1) n (n + 1) (X.isZero₂_of_isFirstQuadrant b ⊤ le_top (n - 1) hnb) ≪≫
    (X.isoMapFourδ₁Toδ₀' ⊥ a q (q + 1 : ℤ) ⊤ bot_le ha (by simp) le_top
      (n - 1) n (n + 1) (X.isZero₁_of_isFirstQuadrant ⊥ a bot_le ha0 (n + 1))).symm

/-- An actual finite page of the integer-indexed spectral sequence is
canonically its infinite-endpoint term beyond the first-quadrant bound. -/
def stablePageIsoInfty (p q r : ℤ) (hr : 2 ≤ r)
    (hqr : q + 2 ≤ r) (hpr : p + 1 ≤ r) :
    (X.E₂SpectralSequence.page r).X (p, q) ≅ inftyTerm X (p + q) q :=
  X.spectralSequencePageXIso SpectralObject.coreE₂Cohomological r hr (p, q)
    (q - r + 2 : ℤ) q (q + 1 : ℤ) (q + r - 1 : ℤ) rfl rfl rfl rfl
    (p + q - 1) (p + q) (p + q + 1) rfl ≪≫
  finiteEndpointsIsoInfty X (p + q) q (q - r + 2 : ℤ) (q + r - 1 : ℤ)
    (by simp; lia) (by simp; lia) (by simp; lia) (by simp; lia)

/-- First-quadrant convergence: sufficiently late actual pages are the
genuine associated-graded quotients of the total-cohomology image filtration. -/
def stablePageIsoGraded (p q r : ℤ) (hr : 2 ≤ r)
    (hqr : q + 2 ≤ r) (hpr : p + 1 ≤ r) :
    (X.E₂SpectralSequence.page r).X (p, q) ≅ gradedPiece X (p + q) q :=
  stablePageIsoInfty X p q r hr hqr hpr ≪≫ (gradedPieceIsoInfty X (p + q) q).symm

/-- The same genuine stable-page comparison for mathlib's naturally
indexed first-quadrant spectral sequence. -/
def stablePageNatIsoInfty (p q : ℕ) (r : ℤ) (hr : 2 ≤ r)
    (hqr : (q : ℤ) + 2 ≤ r) (hpr : (p : ℤ) + 1 ≤ r) :
    (X.E₂SpectralSequenceNat.page r).X (p, q) ≅ inftyTerm X (p + q) q :=
  X.spectralSequencePageXIso SpectralObject.coreE₂CohomologicalNat r hr (p, q)
    ((q : ℤ) - r + 2 : ℤ) (q : ℤ) ((q : ℤ) + 1 : ℤ) ((q : ℤ) + r - 1 : ℤ)
    rfl rfl rfl rfl ((p : ℤ) + q - 1) ((p : ℤ) + q) ((p : ℤ) + q + 1) rfl ≪≫
  finiteEndpointsIsoInfty X ((p : ℤ) + q) q ((q : ℤ) - r + 2 : ℤ) ((q : ℤ) + r - 1 : ℤ)
    (by simp; lia) (by simp; lia) (by simp; lia) (by simp; lia)

/-- The naturally indexed late-page terms are the actual associated
graded of total cohomology. -/
def stablePageNatIsoGraded (p q : ℕ) (r : ℤ) (hr : 2 ≤ r)
    (hqr : (q : ℤ) + 2 ≤ r) (hpr : (p : ℤ) + 1 ≤ r) :
    (X.E₂SpectralSequenceNat.page r).X (p, q) ≅ gradedPiece X (p + q) q :=
  stablePageNatIsoInfty X p q r hr hqr hpr ≪≫ (gradedPieceIsoInfty X (p + q) q).symm

/-- The single bound `r ≥ n + 2` works simultaneously for all associated
graded pieces in nonnegative total degree `n`. -/
def stablePageIsoGradedTotal (n : ℕ) (q : Fin (n + 1)) (r : ℤ)
    (hr : (n : ℤ) + 2 ≤ r) :
    (X.E₂SpectralSequence.page r).X ((n : ℤ) - q, q) ≅ gradedPiece X n q :=
  stablePageIsoGraded X ((n : ℤ) - q) q r (by lia)
    (by have := q.isLt; omega) (by have := q.isLt; omega) ≪≫
      eqToIso (congrArg (fun k : ℤ => gradedPiece X k q) (sub_add_cancel (n : ℤ) (q : ℤ)))

end FirstQuadrant

end SGA.SGA2.ExposeI.SpectralObjectConvergence
