/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.InjectiveHomComplexProduct
import SGA.SGA2.ExposeV.HomComplexPairingNaturality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! # Augmented short exact sequences of chosen injective resolutions

This file records the data of an original augmented short exact resolution
sequence and proves that its derived connecting arrow is the original
extension class through the unchanged resolution augmentations. Existence
is proved by the horseshoe construction in `InjectiveHorseshoe.lean` for
abelian categories with enough injectives, rather than assumed here.
-/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A specified augmented short exact sequence of actual injective resolutions.
The exactness and augmentation squares concern the original maps. -/
structure InjectiveResolutionSequence (S : ShortComplex C) where
  I₁ : InjectiveResolution S.X₁
  I₂ : InjectiveResolution S.X₂
  I₃ : InjectiveResolution S.X₃
  f : I₁.cochainComplex ⟶ I₂.cochainComplex
  g : I₂.cochainComplex ⟶ I₃.cochainComplex
  zero : f ≫ g = 0
  shortExact : (ShortComplex.mk f g zero).ShortExact
  comm₁₂ : I₁.ι' ≫ f = (singleFunctor C 0).map S.f ≫ I₂.ι'
  comm₂₃ : I₂.ι' ≫ g = (singleFunctor C 0).map S.g ≫ I₃.ι'

namespace InjectiveResolutionSequence

variable {S : ShortComplex C} (R : InjectiveResolutionSequence S)

/-- The original short complex of the three specified resolutions. -/
abbrev cochainShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk R.f R.g R.zero

/-- The original augmentations, as an actual morphism of short complexes. -/
def augmentation : S.map (singleFunctor C 0) ⟶ R.cochainShortComplex where
  τ₁ := R.I₁.ι'
  τ₂ := R.I₂.ι'
  τ₃ := R.I₃.ι'
  comm₁₂ := R.comm₁₂
  comm₂₃ := R.comm₂₃

variable [HasExt.{w} C] [HasDerivedCategory C]

/-- The original extension class is the derived resolution connecting arrow,
with the unchanged augmentation isomorphisms at both endpoints. -/
@[reassoc]
theorem extClass_augmentation (hS : S.ShortExact) :
    hS.extClass.hom ≫ (injectiveResolutionDerivedIso R.I₁).hom⟦(1 : ℤ)⟧' =
      (injectiveResolutionDerivedIso R.I₃).hom ≫ DerivedCategory.triangleOfSESδ R.shortExact := by
  have hn := DerivedCategory.triangleOfSESδ_naturality
    (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0))
    R.shortExact R.augmentation
  have hd : hS.extClass.hom = DerivedCategory.triangleOfSESδ
      (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) := by
    rw [ShortComplex.ShortExact.extClass_hom]
    dsimp [ShortComplex.ShortExact.singleδ, SingleFunctors.evaluation]
    rw [DerivedCategory.singleFunctorsPostcompQIso_hom_hom,
      DerivedCategory.singleFunctorsPostcompQIso_inv_hom]
    simp only [NatTrans.id_app, Category.id_comp]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hd]
  simpa [injectiveResolutionDerivedIso, DerivedCategory.singleFunctorIsoCompQ, augmentation]
    using hn

/-- The same original connecting-arrow comparison, in the inverse direction. -/
@[reassoc]
theorem extClass_inv_augmentation (hS : S.ShortExact) :
    (injectiveResolutionDerivedIso R.I₃).inv ≫ hS.extClass.hom =
      DerivedCategory.triangleOfSESδ R.shortExact ≫
        (injectiveResolutionDerivedIso R.I₁).inv⟦(1 : ℤ)⟧' := by
  apply (cancel_epi (injectiveResolutionDerivedIso R.I₃).hom).mp
  rw [Iso.hom_inv_id_assoc, ← R.extClass_augmentation_assoc hS,
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

end InjectiveResolutionSequence
end SGA.SGA2.ExposeV
