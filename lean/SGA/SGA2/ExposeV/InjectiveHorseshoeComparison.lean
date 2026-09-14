/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.InjectiveHorseshoeRowResolution
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-! # Comparison maps on the original horseshoe resolution sequences

Comparison in the category of short complexes projects to the original three
injective resolutions. Extending by zero gives a morphism of the actual
integer-indexed resolution sequences, with strictly commuting augmentation
squares. Identity and composition are coherent up to simultaneous homotopy.
-/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV.InjectiveHorseshoe

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable {S T U : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact) (hU : U.ShortExact)

section Projection

variable (F : ShortComplex C ⥤ C) [F.Additive]

/-- A projected component of the simultaneous comparison map. -/
abbrev compareProjected (φ : S ⟶ T) : projected S hS F ⟶ projected T hT F :=
  (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (compare hS hT φ)

/-- Projecting the simultaneous identity homotopy. -/
def compareProjectedIdHomotopy : Homotopy (compareProjected hS hS F (𝟙 S)) (𝟙 _) := by
  simpa only [CategoryTheory.Functor.map_id] using F.mapHomotopy (compareIdHomotopy hS)

/-- Projecting the simultaneous composition homotopy. -/
def compareProjectedCompHomotopy (φ : S ⟶ T) (ψ : T ⟶ U) :
    Homotopy (compareProjected hS hU F (φ ≫ ψ))
      (compareProjected hS hT F φ ≫ compareProjected hT hU F ψ) := by
  simpa only [CategoryTheory.Functor.map_comp]
    using F.mapHomotopy (compareCompHomotopy hS hT hU φ ψ)

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [∀ n, Injective ((projected S hS F).X n)]
  [∀ n, Injective ((projected T hT F).X n)]

/-- Each projected comparison lies over the unchanged original component map. -/
def compareResolution (φ : S ⟶ T) :
    InjectiveResolution.Hom (resolution S hS F) (resolution T hT F) (F.map φ) where
  hom := compareProjected hS hT F φ
  ι_f_zero_comp_hom_f_zero := by
    change (augmentation S hS F).f 0 ≫ F.map ((compare hS hT φ).f 0) =
      ((single₀ C).map (F.map φ)).f 0 ≫ (augmentation T hT F).f 0
    rw [augmentation_f_zero, augmentation_f_zero, single₀_map_f_zero,
      ← F.map_comp, compare_augmentation_zero, F.map_comp]

/-- The identity homotopy on the actual integer-indexed resolution. -/
def compareResolutionIdHomotopy :
    Homotopy (compareResolution hS hS F (𝟙 S)).hom' (𝟙 (resolution S hS F).cochainComplex) := by
  simpa only [compareResolution, InjectiveResolution.Hom.hom',
    InjectiveResolution.cochainComplex, resolution, extendMap_id]
    using (compareProjectedIdHomotopy hS F).extend ComplexShape.embeddingUpNat

variable [∀ n, Injective ((projected U hU F).X n)]

/-- Composition coherence on the actual integer-indexed resolutions. -/
def compareResolutionCompHomotopy (φ : S ⟶ T) (ψ : T ⟶ U) :
    Homotopy (compareResolution hS hU F (φ ≫ ψ)).hom'
      ((compareResolution hS hT F φ).hom' ≫ (compareResolution hT hU F ψ).hom') := by
  simpa only [compareResolution, InjectiveResolution.Hom.hom',
    InjectiveResolution.cochainComplex, resolution, extendMap_comp]
    using (compareProjectedCompHomotopy hS hT hU F φ ψ).extend ComplexShape.embeddingUpNat

end Projection

/-- The simultaneous comparison is a map of the original short exact sequences
of integer-indexed injective resolutions. -/
def sequenceCompare (φ : S ⟶ T) : sequence S hS ⟶ sequence T hT where
  τ₁ := (compareResolution hS hT ShortComplex.π₁ φ).hom'
  τ₂ := (compareResolution hS hT ShortComplex.π₂ φ).hom'
  τ₃ := (compareResolution hS hT ShortComplex.π₃ φ).hom'
  comm₁₂ := by
    change (ComplexShape.embeddingUpNat.extendFunctor C).map _ ≫
      (ComplexShape.embeddingUpNat.extendFunctor C).map _ =
      (ComplexShape.embeddingUpNat.extendFunctor C).map _ ≫
        (ComplexShape.embeddingUpNat.extendFunctor C).map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    ext n
    exact ((compare hS hT φ).f n).comm₁₂
  comm₂₃ := by
    change (ComplexShape.embeddingUpNat.extendFunctor C).map _ ≫
      (ComplexShape.embeddingUpNat.extendFunctor C).map _ =
      (ComplexShape.embeddingUpNat.extendFunctor C).map _ ≫
        (ComplexShape.embeddingUpNat.extendFunctor C).map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    ext n
    exact ((compare hS hT φ).f n).comm₂₃

/-- The actual augmented sequence comparison retains the original augmentation
maps in all three columns. -/
@[reassoc]
theorem sequenceCompare_augmentation (φ : S ⟶ T) :
    (InjectiveResolutionSequence.ofShortExact S hS).augmentation ≫ sequenceCompare hS hT φ =
      ((singleFunctor C 0).mapShortComplex).map φ ≫
        (InjectiveResolutionSequence.ofShortExact T hT).augmentation := by
  apply ShortComplex.Hom.ext
  · exact (compareResolution hS hT ShortComplex.π₁ φ).ι'_comp_hom'
  · exact (compareResolution hS hT ShortComplex.π₂ φ).ι'_comp_hom'
  · exact (compareResolution hS hT ShortComplex.π₃ φ).ι'_comp_hom'

end SGA.SGA2.ExposeV.InjectiveHorseshoe
