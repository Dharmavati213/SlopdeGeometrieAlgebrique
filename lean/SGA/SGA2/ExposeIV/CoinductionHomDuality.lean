/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.ModuleBidual
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Actual coinduction and canonical Hom biduality

The coefficient module is the original `Hom_A(B,I)` with the standard
`B`-action, implemented by `ModuleCat.coextendScalars`. The classical
adjunction is linear over `A`, and identifies the original bidual
evaluation maps after restriction of scalars.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite ModuleCat

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- The classical Hom adjunction, as an isomorphism of actual `A`-modules. -/
def coinducedHomDualIso (I : ModuleCat.{u} A) (M : ModuleCat.{u} B) :
    (restrictScalars f).obj
        ((moduleHomDual ((coextendScalars f).obj I)).obj (op M)) ≅
      (moduleHomDual I).obj (op ((restrictScalars f).obj M)) :=
  LinearEquiv.toModuleIso
    (X₁ := (restrictScalars f).obj
      ((moduleHomDual ((coextendScalars f).obj I)).obj (op M)))
    (X₂ := (moduleHomDual I).obj (op ((restrictScalars f).obj M)))
    { __ := ((restrictCoextendScalarsAdj f).homEquiv M I).symm
      map_add' g h := by
        apply ModuleCat.hom_ext
        ext x
        rfl
      map_smul' a g := by
        apply ModuleCat.hom_ext
        ext x
        change (ModuleCat.Hom.hom g x) (1 * f a) = a • (ModuleCat.Hom.hom g x) (1 : B)
        rw [one_mul]
        have h := (ModuleCat.Hom.hom g x).map_smul a (1 : B)
        change (ModuleCat.Hom.hom g x) (f a * 1) =
          a • (ModuleCat.Hom.hom g x) (1 : B) at h
        simpa only [mul_one] using h }

/-- The classical comparison is evaluation at `1` in the coinduced module. -/
@[simp]
theorem coinducedHomDualIso_hom_apply (I : ModuleCat.{u} A) (M : ModuleCat.{u} B)
    (g : M ⟶ (coextendScalars f).obj I) (x : M) :
    ModuleCat.Hom.hom ((coinducedHomDualIso f I M).hom g) x = g x (1 : B) := rfl

/-- The inverse sends `g` to `x ↦ (b ↦ g(bx))`. -/
@[simp]
theorem coinducedHomDualIso_inv_apply (I : ModuleCat.{u} A) (M : ModuleCat.{u} B)
    (g : (restrictScalars f).obj M ⟶ I) (x : M) (b : B) :
    ModuleCat.Hom.hom ((coinducedHomDualIso f I M).inv g) x b = g (b • x) := rfl

/-- The Hom comparison is natural in its original module argument. -/
@[reassoc]
theorem coinducedHomDualIso_naturality (I : ModuleCat.{u} A)
    {M N : ModuleCat.{u} B} (g : M ⟶ N) :
    (restrictScalars f).map
        ((moduleHomDual ((coextendScalars f).obj I)).map g.op) ≫
        (coinducedHomDualIso f I M).hom =
      (coinducedHomDualIso f I N).hom ≫
        (moduleHomDual I).map ((restrictScalars f).map g).op := by
  apply ModuleCat.hom_ext
  ext h
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Restriction of the actual coinduced bidual is the actual original bidual. -/
def coinducedHomBidualIso (I : ModuleCat.{u} A) (M : ModuleCat.{u} B) :
    (restrictScalars f).obj
        ((moduleHomBidual ((coextendScalars f).obj I)).obj M) ≅
      (moduleHomBidual I).obj ((restrictScalars f).obj M) :=
  coinducedHomDualIso f I
      ((moduleHomDual ((coextendScalars f).obj I)).obj (op M)) ≪≫
    (moduleHomDual I).mapIso (coinducedHomDualIso f I M).symm.op

/-- The bidual comparison intertwines the canonical evaluation maps themselves. -/
@[reassoc]
theorem coinducedHomBidualIso_evaluation (I : ModuleCat.{u} A) (M : ModuleCat.{u} B) :
    (restrictScalars f).map (moduleBidualEvaluation ((coextendScalars f).obj I) M) ≫
        (coinducedHomBidualIso f I M).hom =
      moduleBidualEvaluation I ((restrictScalars f).obj M) := by
  apply ModuleCat.hom_ext
  ext x
  apply ModuleCat.hom_ext
  ext g
  change ModuleCat.Hom.hom g ((1 : B) • x) = ModuleCat.Hom.hom g x
  rw [one_smul]

/-- Canonical biduality transfers to genuine coinduction; no choice of a
bidual isomorphism replaces the evaluation map. -/
theorem coinduced_moduleBidualEvaluation_isIso (I : ModuleCat.{u} A)
    (M : ModuleCat.{u} B)
    [IsIso (moduleBidualEvaluation I ((restrictScalars f).obj M))] :
    IsIso (moduleBidualEvaluation ((coextendScalars f).obj I) M) := by
  have h : IsIso ((restrictScalars f).map
      (moduleBidualEvaluation ((coextendScalars f).obj I) M) ≫
      (coinducedHomBidualIso f I M).hom) := by
    rw [coinducedHomBidualIso_evaluation]
    infer_instance
  have : IsIso ((restrictScalars f).map
      (moduleBidualEvaluation ((coextendScalars f).obj I) M)) :=
    IsIso.of_isIso_comp_right _ (coinducedHomBidualIso f I M).hom
  exact isIso_of_reflects_iso _ (restrictScalars f)

/-- A finite original Hom value yields a finite coinduced Hom value over `B`. -/
theorem coinduced_moduleHomDual_finite (I : ModuleCat.{u} A) (M : ModuleCat.{u} B)
    [Module.Finite A ((moduleHomDual I).obj (op ((restrictScalars f).obj M)))] :
    Module.Finite B ((moduleHomDual ((coextendScalars f).obj I)).obj (op M)) := by
  let e := coinducedHomDualIso f I M
  exact Module.Finite.of_surjective
    ((semilinearMapAddEquiv f _ _).symm e.inv)
    ((ModuleCat.epi_iff_surjective e.inv).mp inferInstance)

/-- Genuine coinduction preserves injective coefficient modules, since
restriction of scalars preserves monomorphisms. -/
theorem coinduced_injective (I : ModuleCat.{u} A) [Injective I] :
    Injective ((coextendScalars f).obj I) := by
  let : (coextendScalars f).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (restrictCoextendScalarsAdj f)
  infer_instance

end SGA.SGA2.ExposeIV
