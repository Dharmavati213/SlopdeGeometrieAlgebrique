/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.InjectiveResolutionSequenceRows

/-! # Comparison of arbitrary specified injective resolution sequences

Every map of original short complexes lifts to an augmentation-compatible map
between any two supplied resolution sequences. Comparison and homotopies take
place in the category of whole rows, hence preserve both horizontal arrows.
The actual integer-indexed comparison extends the original recovered maps.
-/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV.InjectiveResolutionSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S T U : ShortComplex C} (R : InjectiveResolutionSequence S)
  (R' : InjectiveResolutionSequence T) (R'' : InjectiveResolutionSequence U)

/-- Simultaneous comparison between arbitrary supplied resolution-sequence models. -/
def rowCompare (φ : S ⟶ T) : R.rowCocomplex ⟶ R'.rowCocomplex :=
  InjectiveResolution.desc φ R'.rowResolution R.rowResolution

@[reassoc (attr := simp)]
theorem rowCompare_augmentation (φ : S ⟶ T) :
    R.rowAugmentation ≫ R.rowCompare R' φ =
      (single₀ (ShortComplex C)).map φ ≫ R'.rowAugmentation :=
  InjectiveResolution.desc_commutes φ R'.rowResolution R.rowResolution

@[reassoc (attr := simp)]
theorem rowCompare_augmentation_zero (φ : S ⟶ T) :
    R.rowι ≫ (R.rowCompare R' φ).f 0 = φ ≫ R'.rowι := by
  simpa only [comp_f, rowAugmentation_f_zero, single₀_map_f_zero]
    using congr_hom (R.rowCompare_augmentation R' φ) 0

/-- Any two simultaneous lifts of the same original map are homotopic as maps of rows. -/
def rowCompareHomotopy (φ : S ⟶ T) (a b : R.rowCocomplex ⟶ R'.rowCocomplex)
    (ha : R.rowAugmentation ≫ a = (single₀ (ShortComplex C)).map φ ≫ R'.rowAugmentation)
    (hb : R.rowAugmentation ≫ b = (single₀ (ShortComplex C)).map φ ≫ R'.rowAugmentation) :
    Homotopy a b :=
  InjectiveResolution.descHomotopy (I := R.rowResolution) (J := R'.rowResolution) φ a b ha hb

/-- Identity coherence for arbitrary specified models. -/
def rowCompareIdHomotopy : Homotopy (R.rowCompare R (𝟙 S)) (𝟙 R.rowCocomplex) :=
  InjectiveResolution.descIdHomotopy S R.rowResolution

/-- Composition coherence for arbitrary specified models. -/
def rowCompareCompHomotopy (φ : S ⟶ T) (ψ : T ⟶ U) :
    Homotopy (R.rowCompare R'' (φ ≫ ψ)) (R.rowCompare R' φ ≫ R'.rowCompare R'' ψ) :=
  InjectiveResolution.descCompHomotopy φ ψ R.rowResolution R'.rowResolution R''.rowResolution

/-- The first column comparison lies over the original first component map. -/
def firstCompareNatHom (φ : S ⟶ T) : InjectiveResolution.Hom R.I₁ R'.I₁ φ.τ₁ where
  hom := (ShortComplex.π₁.mapHomologicalComplex (ComplexShape.up ℕ)).map (R.rowCompare R' φ)
  ι_f_zero_comp_hom_f_zero := by
    simpa only [ShortComplex.comp_τ₁, single₀_map_f_zero]
      using! congrArg ShortComplex.Hom.τ₁ (R.rowCompare_augmentation_zero R' φ)

/-- The middle column comparison lies over the original middle component map. -/
def middleCompareNatHom (φ : S ⟶ T) : InjectiveResolution.Hom R.I₂ R'.I₂ φ.τ₂ where
  hom := (ShortComplex.π₂.mapHomologicalComplex (ComplexShape.up ℕ)).map (R.rowCompare R' φ)
  ι_f_zero_comp_hom_f_zero := by
    simpa only [ShortComplex.comp_τ₂, single₀_map_f_zero]
      using! congrArg ShortComplex.Hom.τ₂ (R.rowCompare_augmentation_zero R' φ)

/-- The last column comparison lies over the original last component map. -/
def lastCompareNatHom (φ : S ⟶ T) : InjectiveResolution.Hom R.I₃ R'.I₃ φ.τ₃ where
  hom := (ShortComplex.π₃.mapHomologicalComplex (ComplexShape.up ℕ)).map (R.rowCompare R' φ)
  ι_f_zero_comp_hom_f_zero := by
    simpa only [ShortComplex.comp_τ₃, single₀_map_f_zero]
      using! congrArg ShortComplex.Hom.τ₃ (R.rowCompare_augmentation_zero R' φ)

/-- Comparison on the original supplied integer-indexed resolution sequences. -/
def compare (φ : S ⟶ T) : R.cochainShortComplex ⟶ R'.cochainShortComplex where
  τ₁ := (R.firstCompareNatHom R' φ).hom'
  τ₂ := (R.middleCompareNatHom R' φ).hom'
  τ₃ := (R.lastCompareNatHom R' φ).hom'
  comm₁₂ := by
    change _ ≫ R'.f = R.f ≫ _
    rw [← R'.firstNatHom_hom', ← R.firstNatHom_hom']
    change (ComplexShape.embeddingUpNat.extendFunctor C).map _ ≫
      (ComplexShape.embeddingUpNat.extendFunctor C).map _ =
      (ComplexShape.embeddingUpNat.extendFunctor C).map _ ≫
        (ComplexShape.embeddingUpNat.extendFunctor C).map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    ext n
    exact ((R.rowCompare R' φ).f n).comm₁₂
  comm₂₃ := by
    change _ ≫ R'.g = R.g ≫ _
    rw [← R'.lastNatHom_hom', ← R.lastNatHom_hom']
    change (ComplexShape.embeddingUpNat.extendFunctor C).map _ ≫
      (ComplexShape.embeddingUpNat.extendFunctor C).map _ =
      (ComplexShape.embeddingUpNat.extendFunctor C).map _ ≫
        (ComplexShape.embeddingUpNat.extendFunctor C).map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    ext n
    exact ((R.rowCompare R' φ).f n).comm₂₃

/-- The actual comparison preserves all original augmentation squares. -/
@[reassoc]
theorem compare_augmentation (φ : S ⟶ T) :
    R.augmentation ≫ R.compare R' φ =
      (singleFunctor C 0).mapShortComplex.map φ ≫ R'.augmentation := by
  apply ShortComplex.Hom.ext
  · exact (R.firstCompareNatHom R' φ).ι'_comp_hom'
  · exact (R.middleCompareNatHom R' φ).ι'_comp_hom'
  · exact (R.lastCompareNatHom R' φ).ι'_comp_hom'

variable (Q Q' : InjectiveResolutionSequence S)

/-- Coherent model change between arbitrary supplied resolution sequences. -/
def change :
    (HomotopyCategory.quotient (ShortComplex C) (ComplexShape.up ℕ)).obj R.rowCocomplex ≅
      (HomotopyCategory.quotient (ShortComplex C) (ComplexShape.up ℕ)).obj Q.rowCocomplex :=
  InjectiveRowResolution.change R.rowResolution Q.rowResolution

@[simp]
theorem change_refl : R.change R = Iso.refl _ :=
  InjectiveRowResolution.change_refl R.rowResolution

@[simp]
theorem change_trans : R.change Q ≪≫ Q.change Q' = R.change Q' :=
  InjectiveRowResolution.change_trans R.rowResolution Q.rowResolution Q'.rowResolution

/-- Model change is natural for maps of the original short complexes. -/
@[reassoc]
theorem change_naturality (Q_T : InjectiveResolutionSequence T) (φ : S ⟶ T) :
    (HomotopyCategory.quotient _ _).map (R.rowCompare R' φ) ≫ (R'.change Q_T).hom =
      (R.change Q).hom ≫ (HomotopyCategory.quotient _ _).map (Q.rowCompare Q_T φ) :=
  InjectiveRowResolution.change_naturality φ
    R.rowResolution Q.rowResolution R'.rowResolution Q_T.rowResolution

end SGA.SGA2.ExposeV.InjectiveResolutionSequence
