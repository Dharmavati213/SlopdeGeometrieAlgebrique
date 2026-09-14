/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Homology.SpectralObject.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # The actual additive structure on spectral-object coefficient morphisms -/

noncomputable section

open CategoryTheory Limits ComposableArrows

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {C ι : Type*} [Category C] [Category ι] [Abelian C]

instance {S T : Abelian.SpectralObject C ι} : Zero (S ⟶ T) :=
  ⟨{ hom _ := 0
     comm := by intros; simp }⟩

instance {S T : Abelian.SpectralObject C ι} : Add (S ⟶ T) :=
  ⟨fun φ ψ ↦
    { hom n := φ.hom n + ψ.hom n
      comm := by intros; simp [Preadditive.comp_add, Preadditive.add_comp, φ.comm, ψ.comm] }⟩

instance {S T : Abelian.SpectralObject C ι} : Neg (S ⟶ T) :=
  ⟨fun φ ↦
    { hom n := -φ.hom n
      comm := by intros; simp [Preadditive.comp_neg, Preadditive.neg_comp, φ.comm] }⟩

instance {S T : Abelian.SpectralObject C ι} : Sub (S ⟶ T) :=
  ⟨fun φ ψ ↦
    { hom n := φ.hom n - ψ.hom n
      comm := by intros; simp [Preadditive.comp_sub, Preadditive.sub_comp, φ.comm, ψ.comm] }⟩

instance {S T : Abelian.SpectralObject C ι} : SMul ℕ (S ⟶ T) :=
  ⟨fun k φ ↦
    { hom n := k • φ.hom n
      comm := by intros; simp [Preadditive.comp_nsmul, Preadditive.nsmul_comp, φ.comm] }⟩

instance {S T : Abelian.SpectralObject C ι} : SMul ℤ (S ⟶ T) :=
  ⟨fun k φ ↦
    { hom n := k • φ.hom n
      comm := by intros; simp [Preadditive.comp_zsmul, Preadditive.zsmul_comp, φ.comm] }⟩

instance {S T : Abelian.SpectralObject C ι} : AddCommGroup (S ⟶ T) :=
  Function.Injective.addCommGroup (fun φ : S ⟶ T ↦ φ.hom)
    (fun _ _ h ↦ Abelian.SpectralObject.Hom.ext h)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simp]
theorem spectralObject_zero_hom (S T : Abelian.SpectralObject C ι) (n : ℤ) :
    (0 : S ⟶ T).hom n = 0 := rfl

@[simp]
theorem spectralObject_add_hom {S T : Abelian.SpectralObject C ι} (φ ψ : S ⟶ T) (n : ℤ) :
    (φ + ψ).hom n = φ.hom n + ψ.hom n := rfl

instance spectralObjectPreadditive : Preadditive (Abelian.SpectralObject C ι) where
  add_comp _ _ _ φ ψ χ := by
    apply Abelian.SpectralObject.Hom.ext
    funext n
    exact Preadditive.add_comp _ _ _ (φ.hom n) (ψ.hom n) (χ.hom n)
  comp_add _ _ _ φ ψ χ := by
    apply Abelian.SpectralObject.Hom.ext
    funext n
    exact Preadditive.comp_add _ _ _ (φ.hom n) (ψ.hom n) (χ.hom n)

/-- Evaluation on an actual degree and interval of a spectral object. -/
def spectralObjectEvaluation (n : ℤ) (D : ComposableArrows ι 1) :
    Abelian.SpectralObject C ι ⥤ C where
  obj S := (S.H n).obj D
  map φ := (φ.hom n).app D

instance (n : ℤ) (D : ComposableArrows ι 1) :
    (spectralObjectEvaluation (C := C) n D).Additive where
  map_add := rfl

end SGA.SGA2.ExposeI
