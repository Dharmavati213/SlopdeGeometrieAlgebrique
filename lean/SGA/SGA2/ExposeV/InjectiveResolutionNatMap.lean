/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.InjectiveResolutionSequence

/-! # Recovering the original nonnegative resolution maps

Extension by zero is fully faithful. Thus any specified map between the
integer-indexed injective resolution complexes comes from a unique map of
their original nonnegative complexes. Augmentation compatibility is retained.
-/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C] {X Y : C}
variable (I : InjectiveResolution X) (J : InjectiveResolution Y)

/-- Recover a specified extended resolution map by full faithfulness. -/
def injectiveResolutionNatMap (φ : I.cochainComplex ⟶ J.cochainComplex) :
    I.cocomplex ⟶ J.cocomplex :=
  (ComplexShape.embeddingUpNat.extendFunctor C).preimage φ

@[simp]
theorem extend_injectiveResolutionNatMap (φ : I.cochainComplex ⟶ J.cochainComplex) :
    extendMap (injectiveResolutionNatMap I J φ) ComplexShape.embeddingUpNat = φ :=
  (ComplexShape.embeddingUpNat.extendFunctor C).map_preimage φ

@[reassoc]
theorem injectiveResolutionNatMap_f (φ : I.cochainComplex ⟶ J.cochainComplex) (n : ℕ) :
    (I.cochainComplexXIso n n rfl).hom ≫ (injectiveResolutionNatMap I J φ).f n ≫
      (J.cochainComplexXIso n n rfl).inv = φ.f n := by
  have h := congr_hom (extend_injectiveResolutionNatMap I J φ) (n : ℤ)
  erw [extendMap_f _ ComplexShape.embeddingUpNat (i := n) rfl] at h
  exact h

/-- The recovered map remains over the original object map. -/
def injectiveResolutionNatHom (f : X ⟶ Y) (φ : I.cochainComplex ⟶ J.cochainComplex)
    (hφ : I.ι' ≫ φ = (singleFunctor C 0).map f ≫ J.ι') :
    InjectiveResolution.Hom I J f where
  hom := injectiveResolutionNatMap I J φ
  ι_f_zero_comp_hom_f_zero := by
    have h := congr_hom hφ 0
    simp only [comp_f, InjectiveResolution.ι'_f_zero] at h
    erw [← injectiveResolutionNatMap_f I J φ 0] at h
    simp only [Category.assoc] at h
    apply (cancel_mono (J.cochainComplexXIso 0 0 rfl).inv).1
    simpa [singleFunctor, singleFunctors, HomologicalComplex.single,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      Category.assoc] using h

@[simp]
theorem injectiveResolutionNatHom_hom' (f : X ⟶ Y)
    (φ : I.cochainComplex ⟶ J.cochainComplex)
    (hφ : I.ι' ≫ φ = (singleFunctor C 0).map f ≫ J.ι') :
    (injectiveResolutionNatHom I J f φ hφ).hom' = φ :=
  extend_injectiveResolutionNatMap I J φ

end SGA.SGA2.ExposeV
