/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.HomComplexNaturality

/-!
# The canonical Hom-complex comparison before imposing injectivity

The actual localization map exists for every pair of complexes, and is
natural in every additive cochain map. K-injectivity proves its bijectivity,
but is not needed to define the map or prove naturality.
-/

noncomputable section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex CochainComplex
open CochainComplex.HomComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The original Hom-complex-to-derived-Hom map, for arbitrary target complexes. -/
def homComplexHomologyDerivedHomMap (K L : CochainComplex C ℤ) (n : ℤ) :
    (HomComplex K L).homology n →+
      (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) where
  toFun x := Linear.homCongr ℤ ((DerivedCategory.quotientCompQhIso C).app K)
    ((DerivedCategory.quotientCompQhIso C).app (L⟦n⟧) ≪≫
      (DerivedCategory.Q.commShiftIso n).app L)
    (DerivedCategory.Qh.map (CohomologyClass.homAddEquiv (HomComplex.homologyAddEquiv K L n x)))
  map_zero' := by simp
  map_add' x y := by
    simp [Linear.homCongr_apply, Preadditive.add_comp, Preadditive.comp_add]

/-- On K-injectives this is exactly the preexisting comparison, not a replacement. -/
@[simp]
theorem homComplexHomologyDerivedHomMap_eq (K L : CochainComplex C ℤ)
    [L.IsKInjective] (n : ℤ) :
    homComplexHomologyDerivedHomMap K L n =
      (homComplexHomologyDerivedHomEquiv K L n).toAddMonoidHom := rfl

/-- Localization of actual Hom cochains commutes with every target cochain map. -/
theorem homComplexHomologyDerivedHomMap_naturality (K : CochainComplex C ℤ)
    {L M : CochainComplex C ℤ} (f : L ⟶ M) (n : ℤ) (x : (HomComplex K L).homology n) :
    homComplexHomologyDerivedHomMap K M n ((homologyMap (homComplexPostcomp K f) n) x) =
      homComplexHomologyDerivedHomMap K L n x ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  simp only [homComplexHomologyDerivedHomMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [homComplexHomologyAddEquiv_naturality]
  simp only [homComplexClassPostcomp, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddEquiv.apply_symm_apply]
  simp [Linear.homCongr_apply, Category.assoc]

end SGA.SGA2.ExposeI
