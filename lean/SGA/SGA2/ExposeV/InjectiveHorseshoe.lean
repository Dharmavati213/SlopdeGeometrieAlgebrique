/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.InjectiveHorseshoeComplex
import SGA.SGA2.ExposeV.InjectiveResolutionSequence

/-! # Compatible short exact sequences of injective resolutions

The injective horseshoe construction supplies an augmented short exact sequence
of actual injective resolutions for every short exact sequence in an abelian
category with enough injectives. The horizontal maps extend the original maps,
and the sequence is split in each degree (not necessarily as a sequence of
complexes).
-/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV
namespace InjectiveHorseshoe

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable (S : ShortComplex C) (hS : S.ShortExact)

instance additive_π₁ : (ShortComplex.π₁ : ShortComplex C ⥤ C).Additive where
  map_add := rfl

instance additive_π₂ : (ShortComplex.π₂ : ShortComplex C ⥤ C).Additive where
  map_add := rfl

instance additive_π₃ : (ShortComplex.π₃ : ShortComplex C ⥤ C).Additive where
  map_add := rfl

instance injective_projected₁ (n : ℕ) : Injective ((projected S hS ShortComplex.π₁).X n) :=
  injective_row_X₁ _

instance injective_projected₂ (n : ℕ) : Injective ((projected S hS ShortComplex.π₂).X n) :=
  injective_row_X₂ _

instance injective_projected₃ (n : ℕ) : Injective ((projected S hS ShortComplex.π₃).X n) :=
  injective_row_X₃ _

/-- The left injective resolution in the horseshoe. -/
abbrev firstResolution : InjectiveResolution S.X₁ := resolution S hS ShortComplex.π₁

/-- The middle injective resolution in the horseshoe. -/
abbrev middleResolution : InjectiveResolution S.X₂ := resolution S hS ShortComplex.π₂

/-- The right injective resolution in the horseshoe. -/
abbrev lastResolution : InjectiveResolution S.X₃ := resolution S hS ShortComplex.π₃

/-- The first horizontal map is a morphism of resolutions over the original `S.f`. -/
def firstMap : InjectiveResolution.Hom (firstResolution S hS) (middleResolution S hS) S.f where
  hom := (ShortComplex.π₁Toπ₂.mapHomologicalComplex (ComplexShape.up ℕ)).app (cocomplex S hS)
  ι_f_zero_comp_hom_f_zero := by
    change (augmentation S hS ShortComplex.π₁).f 0 ≫ (term S hS 0).f =
      ((single₀ C).map S.f).f 0 ≫ (augmentation S hS ShortComplex.π₂).f 0
    rw [augmentation_f_zero, augmentation_f_zero, single₀_map_f_zero]
    exact (ι S hS 0).comm₁₂

/-- The second horizontal map is a morphism of resolutions over the original `S.g`. -/
def lastMap : InjectiveResolution.Hom (middleResolution S hS) (lastResolution S hS) S.g where
  hom := (ShortComplex.π₂Toπ₃.mapHomologicalComplex (ComplexShape.up ℕ)).app (cocomplex S hS)
  ι_f_zero_comp_hom_f_zero := by
    change (augmentation S hS ShortComplex.π₂).f 0 ≫ (term S hS 0).g =
      ((single₀ C).map S.g).f 0 ≫ (augmentation S hS ShortComplex.π₃).f 0
    rw [augmentation_f_zero, augmentation_f_zero, single₀_map_f_zero]
    exact (ι S hS 0).comm₂₃

@[simp]
theorem firstMap_comp_lastMap : (firstMap S hS).hom ≫ (lastMap S hS).hom = 0 := by
  ext n
  exact (term S hS n).zero

/-- The original horizontal maps on the integer-indexed resolution models compose to zero. -/
@[simp]
theorem firstMap_comp_lastMap' : (firstMap S hS).hom' ≫ (lastMap S hS).hom' = 0 := by
  change (ComplexShape.embeddingUpNat.extendFunctor C).map (firstMap S hS).hom ≫
    (ComplexShape.embeddingUpNat.extendFunctor C).map (lastMap S hS).hom = 0
  rw [← CategoryTheory.Functor.map_comp, firstMap_comp_lastMap,
    CategoryTheory.Functor.map_zero]

/-- The constructed short complex of actual integer-indexed resolutions. -/
abbrev sequence : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (firstMap S hS).hom' (lastMap S hS).hom' (firstMap_comp_lastMap' S hS)

/-- In nonnegative degrees the resolution row is the constructed split injective row. -/
def sequenceEvalIso (n : ℕ) :
    (sequence S hS).map (eval C (ComplexShape.up ℤ) n) ≅ term S hS n :=
  ShortComplex.isoMk
    ((firstResolution S hS).cochainComplexXIso n n rfl)
    ((middleResolution S hS).cochainComplexXIso n n rfl)
    ((lastResolution S hS).cochainComplexXIso n n rfl)
    (by
      change _ = (firstMap S hS).hom'.f n ≫ _
      rw [(firstMap S hS).hom'_f n n rfl]
      simp [firstMap, cocomplex])
    (by
      change _ = (lastMap S hS).hom'.f n ≫ _
      rw [(lastMap S hS).hom'_f n n rfl]
      simp [lastMap, cocomplex])

/-- Each degree of the actual resolution sequence has a splitting. -/
def sequenceSplitting (n : ℤ) :
    ((sequence S hS).map (eval C (ComplexShape.up ℤ) n)).Splitting := by
  cases n with
  | ofNat k => exact (splitting (stage S hS k).1).ofIso (sequenceEvalIso S hS k).symm
  | negSucc k =>
    exact ShortComplex.Splitting.ofIsZero _
      (CochainComplex.isZero_of_isStrictlyGE (firstResolution S hS).cochainComplex 0 _ (by lia))
      (CochainComplex.isZero_of_isStrictlyGE (middleResolution S hS).cochainComplex 0 _ (by lia))
      (CochainComplex.isZero_of_isStrictlyGE (lastResolution S hS).cochainComplex 0 _ (by lia))

/-- The actual sequence of resolutions is short exact, with its original maps. -/
theorem sequence_shortExact : (sequence S hS).ShortExact :=
  shortExact_of_degreewise_shortExact _ (fun n => (sequenceSplitting S hS n).shortExact)

end InjectiveHorseshoe

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- The injective horseshoe lemma, retaining the actual augmentations and maps. -/
def InjectiveResolutionSequence.ofShortExact (S : ShortComplex C) (hS : S.ShortExact) :
    InjectiveResolutionSequence S where
  I₁ := InjectiveHorseshoe.firstResolution S hS
  I₂ := InjectiveHorseshoe.middleResolution S hS
  I₃ := InjectiveHorseshoe.lastResolution S hS
  f := (InjectiveHorseshoe.firstMap S hS).hom'
  g := (InjectiveHorseshoe.lastMap S hS).hom'
  zero := InjectiveHorseshoe.firstMap_comp_lastMap' S hS
  shortExact := InjectiveHorseshoe.sequence_shortExact S hS
  comm₁₂ := (InjectiveHorseshoe.firstMap S hS).ι'_comp_hom'
  comm₂₃ := (InjectiveHorseshoe.lastMap S hS).ι'_comp_hom'

/-- Every short exact sequence admits an augmented short exact sequence of
injective resolutions; this is proved by the horseshoe construction. -/
theorem nonempty_injectiveResolutionSequence (S : ShortComplex C) (hS : S.ShortExact) :
    Nonempty (InjectiveResolutionSequence S) :=
  ⟨InjectiveResolutionSequence.ofShortExact S hS⟩

end SGA.SGA2.ExposeV
