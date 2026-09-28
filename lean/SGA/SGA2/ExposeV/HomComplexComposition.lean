/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.SourceHomComplex
import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.CategoryTheory.Linear.Basic

/-! # V.1: composition of the original Hom-complex cohomology classes -/

noncomputable section
universe v u
open CategoryTheory Limits Preadditive CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {F G K L : CochainComplex C ℤ}

/-- Composition of the actual graded cocycles, without changing their
component morphisms. -/
def homCocycleComp {i j k : ℤ} (z : Cocycle F G i) (w : Cocycle G K j)
    (h : i + j = k) : Cocycle F K k :=
  Cocycle.mk (z.1.comp w.1 h) (k + 1) rfl (by
    rw [δ_comp z.1 w.1 h (i + 1) (j + 1) (k + 1) rfl rfl rfl]
    simp)

/-- The corresponding shifted chain map is the actual shifted composition. -/
theorem homCocycleComp_equivHomShift {i j k : ℤ} (z : Cocycle F G i)
    (w : Cocycle G K j) (h : i + j = k) :
    Cocycle.equivHomShift.symm (homCocycleComp z w h) =
      ShiftedHom.comp (Cocycle.equivHomShift.symm z)
        (Cocycle.equivHomShift.symm w) (by omega) := by
  ext p
  simp only [Cocycle.equivHomShift_symm_apply, ShiftedHom.comp,
    HomologicalComplex.comp_f, Cocycle.homOf_f, Cocycle.rightShift_coe]
  simp only [shiftFunctor_obj_X', homCocycleComp, Cocycle.mk_coe, Cochain.rightShift_v,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_inv,
    Category.comp_id, shiftFunctor_map_f', Cocycle.homOf_f, Cocycle.rightShift_coe,
    shiftFunctorAdd'_inv_app_f', eqToIso.hom]
  rw [Cochain.comp_v z.1 w.1 h p (p + i) (p + k) rfl (by omega)]
  congr 1
  have aux (a b : ℤ) (hab : a = b) (ha : p + i + j = a) :
      w.1.v (p + i) b (ha.trans hab) =
        w.1.v (p + i) a ha ≫ eqToHom (congrArg K.X hab) := by
    subst b
    simp
  exact aux (p + i + j) (p + k) (by omega) rfl

/-- The original cohomology-class comparison, with its target shift in the
homotopy category rather than before the quotient functor. -/
def homClassShiftedHomAddEquiv (F G : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass F G n ≃+
      ShiftedHom ((HomotopyCategory.quotient C _).obj F)
        ((HomotopyCategory.quotient C _).obj G) n :=
  CohomologyClass.homAddEquiv.trans
    (Linear.homCongr ℤ (Iso.refl _)
      (((HomotopyCategory.quotient C _).commShiftIso n).app G)).toAddEquiv

/-- On an actual cocycle this is precisely the quotient of its shifted
complex morphism, with the quotient functor's canonical shift comparison. -/
theorem homClassShiftedHomAddEquiv_mk {n : ℤ} (z : Cocycle F G n) :
    homClassShiftedHomAddEquiv F G n (CohomologyClass.mk z) =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) (HomotopyCategory.quotient C _) := by
  simp [homClassShiftedHomAddEquiv, CohomologyClass.homAddEquiv,
    CohomologyClass.toHom_mk, Linear.homCongr_apply, ShiftedHom.map]

/-- **V.1, formula (11):** the additive pairing on actual cohomology classes.
The representative formula below proves it is induced by original graded
composition, rather than an unrelated pairing between isomorphic groups. -/
def homClassComp {i j k : ℤ} (h : i + j = k) :
    CohomologyClass F G i →+ (CohomologyClass G K j →+ CohomologyClass F K k) where
  toFun z :=
    { toFun w := (homClassShiftedHomAddEquiv F K k).symm
        (ShiftedHom.comp (homClassShiftedHomAddEquiv F G i z)
          (homClassShiftedHomAddEquiv G K j w) (by omega))
      map_zero' := by simp
      map_add' w w' := by simp }
  map_zero' := by ext w; simp
  map_add' z z' := by ext w; simp

/-- The pairing is the class of the original cochain composite. This also
proves independence of representatives in both arguments. -/
theorem homClassComp_mk {i j k : ℤ} (h : i + j = k) (z : Cocycle F G i)
    (w : Cocycle G K j) :
    homClassComp h (CohomologyClass.mk z) (CohomologyClass.mk w) =
      CohomologyClass.mk (homCocycleComp z w h) := by
  apply (homClassShiftedHomAddEquiv F K k).injective
  simp only [homClassComp, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddEquiv.apply_symm_apply, homClassShiftedHomAddEquiv_mk,
    homCocycleComp_equivHomShift, ShiftedHom.map_comp]

/-- Associativity on the original cohomology classes, in arbitrary degrees. -/
theorem homClassComp_assoc {i j k ij jk n : ℤ} (hij : i + j = ij) (hjk : j + k = jk)
    (hn : i + j + k = n) (z : CohomologyClass F G i) (w : CohomologyClass G K j)
    (t : CohomologyClass K L k) :
    homClassComp (k := n) (by omega) (homClassComp hij z w) t =
      homClassComp (by omega) z (homClassComp hjk w t) := by
  apply (homClassShiftedHomAddEquiv F L n).injective
  simp only [homClassComp, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddEquiv.apply_symm_apply]
  exact ShiftedHom.comp_assoc _ _ _ _ _ (by omega)

/-- The original graded composition as a biadditive operation on the actual
Hom-complex homology groups. -/
def homologyComp {i j k : ℤ} (h : i + j = k) :
    (HomComplex F G).homology i →+
      ((HomComplex G K).homology j →+ (HomComplex F K).homology k) :=
  ((homClassComp h).compl₂ (HomComplex.homologyAddEquiv G K j).toAddMonoidHom).compr₂
    (HomComplex.homologyAddEquiv F K k).symm.toAddMonoidHom |>.comp
      (HomComplex.homologyAddEquiv F G i).toAddMonoidHom

/-- The homology pairing recovers the already verified class-level product. -/
@[simp]
theorem homologyAddEquiv_homologyComp {i j k : ℤ} (h : i + j = k)
    (z : (HomComplex F G).homology i) (w : (HomComplex G K).homology j) :
    HomComplex.homologyAddEquiv F K k (homologyComp h z w) =
      homClassComp h (HomComplex.homologyAddEquiv F G i z)
        (HomComplex.homologyAddEquiv G K j w) := by
  exact (HomComplex.homologyAddEquiv F K k).apply_symm_apply _

end SGA.SGA2.ExposeV
