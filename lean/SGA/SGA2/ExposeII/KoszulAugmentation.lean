/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulDegreeZero
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# SGA 2, Exposé II, (7.6): the augmented projective Koszul complex

Koszul complexes over the ring have projective terms. Their augmentation
to the quotient by the generators is compatible with the power transitions.
These facts allow comparison with projective resolutions without assuming
that the generators form a regular sequence.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Koszul complexes with projective coefficients have projective terms. -/
instance koszulComplex_X_projective (M : ModuleCat.{u} R) [Projective M]
    (fs : List R) (i : ℕ) : Projective ((koszulComplex M fs).X i) := by
  induction fs generalizing i with
  | nil =>
    cases i with
    | zero =>
      exact Projective.of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 M).symm inferInstance
    | succ i =>
      exact (koszulComplex_isZero_X M [] (i + 1) (by simp)).projective
  | cons f fs ih =>
    cases i with
    | zero =>
      exact Projective.of_iso
        (homotopyCofiber.XIso (f • 𝟙 (koszulComplex M fs)) 0 (by simp)).symm (ih 0)
    | succ i =>
      have := ih i
      have := ih (i + 1)
      exact Projective.of_iso
        (homotopyCofiber.XIsoBiprod (f • 𝟙 (koszulComplex M fs)) (i + 1) i rfl).symm
        inferInstance

/-- The quotient map in degree zero annihilates the Koszul differential. -/
theorem koszulAugmentation_zero (fs : List R) :
    (koszulComplex (ModuleCat.of R R) fs).d 1 0 ≫
      (koszulZeroIso (ModuleCat.of R R) fs).hom ≫
        ModuleCat.ofHom (koszulIdeal fs).mkQ = 0 := by
  ext x
  change (koszulIdeal fs).mkQ (koszulRingBoundary fs x) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (koszulRingBoundary_range fs ▸ LinearMap.mem_range_self _ x)

/-- The augmentation of the Koszul complex to the quotient by its generators. -/
def koszulAugmentation (fs : List R) :
    koszulComplex (ModuleCat.of R R) fs ⟶
      (ChainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ koszulIdeal fs)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(koszulZeroIso (ModuleCat.of R R) fs).hom ≫ ModuleCat.ofHom (koszulIdeal fs).mkQ,
      koszulAugmentation_zero fs⟩

@[simp]
theorem koszulAugmentation_f_zero (fs : List R) :
    (koszulAugmentation fs).f 0 =
      (koszulZeroIso (ModuleCat.of R R) fs).hom ≫ ModuleCat.ofHom (koszulIdeal fs).mkQ :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The augmentation induces the canonical quotient isomorphism in degree zero. -/
@[reassoc]
theorem koszulAugmentation_homology_zero (fs : List R) :
    homologyMap (koszulAugmentation fs) 0 ≫
      (singleObjHomologySelfIso (ComplexShape.down ℕ) 0
        (ModuleCat.of R (R ⧸ koszulIdeal fs))).hom =
      (koszulHomologyZeroIsoQuotient fs).hom := by
  apply (cancel_epi ((koszulComplex (ModuleCat.of R R) fs).homologyπ 0)).mp
  rw [homologyπ_naturality_assoc, homologyπ_singleObjHomologySelfIso_hom,
    koszulHomologyZeroIsoQuotient_homologyπ]
  simp only [singleObjCyclesSelfIso_hom, cyclesMap_i,
    koszulAugmentation_f_zero, ChainComplex.single₀ObjXSelf, Iso.refl_hom,
    Category.comp_id]

/-- The Koszul augmentation is a quasi-isomorphism in degree zero. -/
instance koszulAugmentation_isIso_homology_zero (fs : List R) :
    IsIso (homologyMap (koszulAugmentation fs) 0) := by
  have : IsIso (homologyMap (koszulAugmentation fs) 0 ≫
      (singleObjHomologySelfIso (ComplexShape.down ℕ) 0
        (ModuleCat.of R (R ⧸ koszulIdeal fs))).hom) := by
    rw [koszulAugmentation_homology_zero]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (singleObjHomologySelfIso (ComplexShape.down ℕ) 0
      (ModuleCat.of R (R ⧸ koszulIdeal fs))).hom

/-- The canonical quotient map between ideals of powers of the generators. -/
def koszulPowerQuotientMap (fs : List R) {n m : ℕ} (hnm : n ≤ m) :
    ModuleCat.of R (R ⧸ koszulIdeal (fs.map fun f ↦ f ^ m)) ⟶
      ModuleCat.of R (R ⧸ koszulIdeal (fs.map fun f ↦ f ^ n)) :=
  ModuleCat.ofHom (Ideal.Quotient.factorₐ R (koszulIdeal_pow_antitone fs hnm)).toLinearMap

/-- Koszul augmentations commute with the actual power transitions. -/
@[reassoc]
theorem koszulAugmentation_naturality (fs : List R) {n m : ℕ} (hnm : n ≤ m) :
    koszulTransition (ModuleCat.of R R) fs hnm ≫
      koszulAugmentation (fs.map fun f ↦ f ^ n) =
    koszulAugmentation (fs.map fun f ↦ f ^ m) ≫
      (ChainComplex.single₀ (ModuleCat.{u} R)).map (koszulPowerQuotientMap fs hnm) := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change (koszulTransition (ModuleCat.of R R) fs hnm).f 0 ≫
      (koszulAugmentation (fs.map fun f ↦ f ^ n)).f 0 =
    (koszulAugmentation (fs.map fun f ↦ f ^ m)).f 0 ≫ koszulPowerQuotientMap fs hnm
  simp only [koszulAugmentation_f_zero, koszulTransition_zero_naturality_assoc,
    Category.assoc]
  rfl

end SGA.SGA2.ExposeII
