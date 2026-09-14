/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.HomComplexPrecomposition
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Original cocycles in actual Hom-complex homology -/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

/-- The original group element, represented by a morphism from the free
abelian group on one generator, without a universe restriction. -/
def abElementMap {M : AddCommGrpCat.{v}} (x : M) : AddCommGrpCat.of (ULift.{v} ℤ) ⟶ M :=
  AddCommGrpCat.ofHom (uliftZMultiplesHom M x)

@[simp]
theorem abElementMap_apply {M : AddCommGrpCat.{v}} (x : M) (k : ULift.{v} ℤ) :
    abElementMap x k = k.down • x := by simp [abElementMap]; rfl

@[simp]
theorem abElementMap_zero (M : AddCommGrpCat.{v}) : abElementMap (0 : M) = 0 := by
  ext k
  simp [abElementMap]

@[simp]
theorem abElementMap_comp {M N : AddCommGrpCat.{v}} (x : M) (f : M ⟶ N) :
    abElementMap x ≫ f = abElementMap (f x) := by
  ext k
  simp [abElementMap]

variable {C : Type u} [Category.{v} C] [Abelian C]
  {F G : CochainComplex C ℤ} {n : ℤ}

/-- An original Hom cocycle in the actual categorical cycle object. -/
def homComplexCocycleLift (z : Cocycle F G n) : (HomComplex F G).cycles n :=
  (HomComplex.leftHomologyData F G n).cyclesIso.inv z

@[simp]
theorem homComplexCocycleLift_iCycles (z : Cocycle F G n) :
    (HomComplex F G).iCycles n (homComplexCocycleLift z) = z.1 :=
  ConcreteCategory.congr_hom
    (HomComplex.leftHomologyData F G n).cyclesIso_inv_comp_iCycles z

/-- The original cocycle projected into the actual Hom-complex homology. -/
def homComplexHomologyMk (z : Cocycle F G n) : (HomComplex F G).homology n :=
  (HomComplex F G).homologyπ n (homComplexCocycleLift z)

@[simp]
theorem homComplexHomologyMk_compare (z : Cocycle F G n) :
    HomComplex.homologyAddEquiv F G n (homComplexHomologyMk z) = CohomologyClass.mk z := by
  let D := HomComplex.leftHomologyData F G n
  have h : D.cyclesIso.inv ≫ (HomComplex F G).homologyπ n ≫ D.homologyIso.hom = D.π := by
    erw [D.homologyπ_comp_homologyIso_hom, Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom h z

/-- Every actual Hom-complex homology element has an original cocycle
representative. -/
theorem homComplexHomologyMk_surjective (F G : CochainComplex C ℤ) (n : ℤ) :
    Function.Surjective (homComplexHomologyMk (F := F) (G := G) (n := n)) := by
  intro x
  obtain ⟨z, hz⟩ := (HomComplex.homologyAddEquiv F G n x).mk_surjective
  refine ⟨z, (HomComplex.homologyAddEquiv F G n).injective ?_⟩
  simpa only [homComplexHomologyMk_compare] using hz

/-- The categorical lift of the original element morphism is the same
actual cocycle, evaluated at the free generator. -/
theorem homComplexCocycleLift_eq_liftCycles (z : Cocycle F G n) :
    homComplexCocycleLift z =
      (HomComplex F G).liftCycles (abElementMap z.1) (n + 1) (by simp)
        (by
          rw [abElementMap_comp]
          change abElementMap (M := AddCommGrpCat.of (Cochain F G (n + 1)))
            (δ n (n + 1) z.1) = 0
          rw [z.δ_eq_zero, abElementMap_zero]) (ULift.up 1) := by
  apply (AddCommGrpCat.mono_iff_injective ((HomComplex F G).iCycles n)).mp inferInstance
  rw [homComplexCocycleLift_iCycles]
  symm
  exact (ConcreteCategory.congr_hom
    ((HomComplex F G).liftCycles_i (abElementMap z.1) (n + 1) (by simp)
      (by
        rw [abElementMap_comp]
        change abElementMap (M := AddCommGrpCat.of (Cochain F G (n + 1)))
          (δ n (n + 1) z.1) = 0
        rw [z.δ_eq_zero, abElementMap_zero])) (ULift.up 1)).trans (one_zsmul z.1)

variable [HasDerivedCategory.{w} C] [G.IsKInjective]

/-- The previously specified derived-Hom equivalence sends an original
homology representative to the original shifted chain morphism. -/
theorem homComplexHomologyDerivedHomEquiv_mk (z : Cocycle F G n) :
    ExposeI.homComplexHomologyDerivedHomEquiv F G n (homComplexHomologyMk z) =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q := by
  simp only [ExposeI.homComplexHomologyDerivedHomEquiv, AddEquiv.trans_apply,
    homComplexHomologyMk_compare]
  simp [CohomologyClass.homAddEquiv, CohomologyClass.toHom_mk,
    Linear.homCongr_apply, ShiftedHom.map, Category.assoc,
    DerivedCategory.quotientCompQhIso_hom_naturality_assoc]

end SGA.SGA2.ExposeV
