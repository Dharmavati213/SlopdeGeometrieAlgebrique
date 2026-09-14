/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.InjectiveHorseshoeRowInjective
import SGA.SGA2.ExposeV.InjectiveHorseshoe

/-! # The horseshoe as a resolution of the whole short complex

The original horseshoe complex, without changing any object or differential,
is an injective resolution in `ShortComplex C`. Comparison of these resolutions
therefore supplies simultaneous comparison maps and homotopies for all three
columns that preserve the horizontal short-complex maps.
-/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV.InjectiveHorseshoe

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable (S : ShortComplex C) (hS : S.ShortExact)

/-- The unchanged horseshoe augmentation, before projecting to columns. -/
def rowAugmentation : (single₀ (ShortComplex C)).obj S ⟶ cocomplex S hS :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨ι S hS 0, by
    rw [cocomplex_d, ι_d]⟩

@[simp]
theorem rowAugmentation_f_zero : (rowAugmentation S hS).f 0 = ι S hS 0 :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

instance quasiIso_rowAugmentation : QuasiIso (rowAugmentation S hS) := ⟨fun n => by
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨exact_ι_d S hS 0, by change Mono (ι S hS 0); infer_instance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp)
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact cocomplex_exactAt_succ S hS n
    · apply CochainComplex.exactAt_succ_single_obj⟩

/-- The horseshoe is an injective resolution of the entire original short complex. -/
def rowResolution : InjectiveResolution S where
  cocomplex := cocomplex S hS
  injective n := by change Injective (term S hS n); infer_instance
  ι := rowAugmentation S hS

variable {S} {T U : ShortComplex C} (hT : T.ShortExact) (hU : U.ShortExact)

/-- Simultaneous comparison on all three columns, respecting the two original
horizontal arrows at every degree. -/
def compare (φ : S ⟶ T) : cocomplex S hS ⟶ cocomplex T hT :=
  InjectiveResolution.desc φ (rowResolution T hT) (rowResolution S hS)

@[reassoc (attr := simp)]
theorem compare_augmentation (φ : S ⟶ T) :
    rowAugmentation S hS ≫ compare hS hT φ =
      (single₀ (ShortComplex C)).map φ ≫ rowAugmentation T hT :=
  InjectiveResolution.desc_commutes φ (rowResolution T hT) (rowResolution S hS)

@[reassoc (attr := simp)]
theorem compare_augmentation_zero (φ : S ⟶ T) :
    ι S hS 0 ≫ (compare hS hT φ).f 0 = φ ≫ ι T hT 0 := by
  simpa only [comp_f, rowAugmentation_f_zero, single₀_map_f_zero]
    using congr_hom (compare_augmentation hS hT φ) 0

/-- Any two simultaneous lifts of the same original map are homotopic through
maps of short complexes. -/
def compareHomotopy (φ : S ⟶ T) (a b : cocomplex S hS ⟶ cocomplex T hT)
    (ha : rowAugmentation S hS ≫ a = (single₀ (ShortComplex C)).map φ ≫ rowAugmentation T hT)
    (hb : rowAugmentation S hS ≫ b = (single₀ (ShortComplex C)).map φ ≫ rowAugmentation T hT) :
    Homotopy a b :=
  InjectiveResolution.descHomotopy (I := rowResolution S hS) (J := rowResolution T hT)
    φ a b ha hb

/-- Identity coherence is witnessed by a simultaneous horizontal-compatible homotopy. -/
def compareIdHomotopy : Homotopy (compare hS hS (𝟙 S)) (𝟙 (cocomplex S hS)) :=
  InjectiveResolution.descIdHomotopy S (rowResolution S hS)

/-- Composition coherence is witnessed by a simultaneous horizontal-compatible homotopy. -/
def compareCompHomotopy (φ : S ⟶ T) (ψ : T ⟶ U) :
    Homotopy (compare hS hU (φ ≫ ψ)) (compare hS hT φ ≫ compare hT hU ψ) :=
  InjectiveResolution.descCompHomotopy φ ψ
    (rowResolution S hS) (rowResolution T hT) (rowResolution U hU)

end SGA.SGA2.ExposeV.InjectiveHorseshoe
