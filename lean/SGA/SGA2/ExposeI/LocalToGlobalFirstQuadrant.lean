/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalE2

/-!
# First-quadrant support of the actual supported spectral sequence

The supported derived object is connective and derived Hom from a sheaf
vanishes below the lower truncation bound. These two facts prove that the
actual spectral object is first quadrant. In particular, every page starting
with E₂ vanishes outside the first quadrant. This does not assert convergence
or supply an abutment filtration.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

local instance supportedFirstQuadrant_hasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

/-- First-quadrant support for the actual spectral object, not an additional
assumption on its pages. -/
instance supportedLocalToGlobalAbelianSpectralObject_isFirstQuadrant (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    (supportedLocalToGlobalAbelianSpectralObject Z I).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    let t := DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} X)
    have h := t.isZero_eTruncLT_obj_obj (supportedDerivedObject Z I) 0 j hj
    have h' := (t.eTruncGE.obj i).map_isZero h
    exact ((supportedDerivedGlobalHom (X := X)).shift n).map_isZero h'
  isZero₂ i j hij n hi := by
    let t := DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} X)
    have hni : ((n + 1 : ℤ) : EInt) ≤ i := by
      induction i using WithBotTop.rec with
      | bot => simp at hi
      | coe i =>
        simp only [WithBotTop.coe_le_coe, WithBotTop.coe_lt_coe] at *
        lia
      | top => exact le_top
    have hge := t.isGE_eTruncGE_obj_obj (n + 1) i hni
      ((t.eTruncLT.obj j).obj (supportedDerivedObject Z I))
    have hshift := t.isGE_shift
      ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj (supportedDerivedObject Z I)))
      (n + 1) n 1 (by lia)
    change IsZero (AddCommGrpCat.of
      (((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X)) ⟶
        ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj
          (supportedDerivedObject Z I)))⟦n⟧))
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact ⟨fun f g => (t.zero f 0 1).trans (t.zero g 0 1).symm⟩

/-- On every page Eᵣ with r ≥ 2, negative second degree vanishes. -/
theorem supportedTruncationSpectralSequence_isZero_of_second_neg (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hq : q < 0) :
    IsZero (((supportedTruncationSpectralSequence Z I).page r).X (p, q)) :=
  Abelian.SpectralObject.isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr _
    ((supportedLocalToGlobalAbelianSpectralObject Z I).isZero₁_of_isFirstQuadrant
      _ _ _ (by simp; lia) _)

/-- On every page Eᵣ with r ≥ 2, negative first degree vanishes. -/
theorem supportedTruncationSpectralSequence_isZero_of_first_neg (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hp : p < 0) :
    IsZero (((supportedTruncationSpectralSequence Z I).page r).X (p, q)) :=
  Abelian.SpectralObject.isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr _
    ((supportedLocalToGlobalAbelianSpectralObject Z I).isZero₂_of_isFirstQuadrant
      _ _ _ _ (by simp; lia))

end SGA.SGA2.ExposeI
