/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.LocalCohomologyZero
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The original module-valued Ext and derived-category Ext agree as groups

Both constructions are computed using the same actual projective resolution.
The original `ProjectiveResolution.extMk` sends Hom cocycles onto
derived-category Ext, with precisely the actual coboundaries as its kernel.
This gives homology data valued in the actual Ext group, and hence an additive
comparison of values, not just an equivalence of vanishing conditions.

No finite-generation, regularity, or noetherianity assumptions are required.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

/-- The original three-term linear Hom complex in a positive degree. -/
abbrev projectiveModuleExtShortComplex {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (M : ModuleCat.{u} R) (n : ℕ) :=
  (P.complex.linearYonedaObj R M).sc' n (n + 1) (n + 2)

/-- Forgetting scalar action leaves the actual three-term additive Hom complex. -/
abbrev projectiveAbExtShortComplex {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (M : ModuleCat.{u} R) (n : ℕ) :=
  (projectiveModuleExtShortComplex P M n).map (forget₂ (ModuleCat R) AddCommGrpCat)

/-- The original cocycle-to-derived-Ext map is additive. -/
def projectiveModuleExtCocycleToExt {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (M : ModuleCat.{u} R) (n : ℕ) :
    AddMonoidHom.ker (projectiveAbExtShortComplex P M n).g.hom →+
      Abelian.Ext N M (n + 1) where
  toFun x := P.extMk x.val (n + 2) rfl x.property
  map_zero' := P.extMk_zero (n + 2) rfl
  map_add' x y := (P.add_extMk x.val y.val (n + 2) rfl x.property y.property).symm

/-- Every actual Ext element has an original Hom-cocycle representative. -/
theorem projectiveModuleExtCocycleToExt_surjective {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (M : ModuleCat.{u} R) (n : ℕ) :
    Function.Surjective (projectiveModuleExtCocycleToExt P M n) := by
  intro x
  obtain ⟨f, hf, h⟩ := P.extMk_surjective x (n + 2) rfl
  exact ⟨⟨f, hf⟩, h⟩

set_option backward.isDefEq.respectTransparency false in
/-- The kernel consists of the literal coboundaries of the original Hom complex. -/
theorem projectiveModuleExtCocycleToExt_eq_zero_iff {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (M : ModuleCat.{u} R) (n : ℕ)
    (x : AddMonoidHom.ker (projectiveAbExtShortComplex P M n).g.hom) :
    projectiveModuleExtCocycleToExt P M n x = 0 ↔
      ∃ y, (projectiveAbExtShortComplex P M n).abToCycles y = x := by
  change P.extMk x.val (n + 2) rfl x.property = 0 ↔ _
  rw [P.extMk_eq_zero_iff x.val (n + 2) rfl x.property n rfl]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, Subtype.ext hy⟩,
    fun ⟨y, hy⟩ => ⟨y, congrArg Subtype.val hy⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual derived Ext group is genuine homology data for the original
projective-resolution Hom complex, with its actual cocycle map. -/
def projectiveModuleExtHomologyData {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (M : ModuleCat.{u} R) (n : ℕ) :
    (projectiveAbExtShortComplex P M n).LeftHomologyData where
  K := (projectiveAbExtShortComplex P M n).abLeftHomologyData.K
  H := AddCommGrpCat.of (Abelian.Ext N M (n + 1))
  i := (projectiveAbExtShortComplex P M n).abLeftHomologyData.i
  π := AddCommGrpCat.ofHom (projectiveModuleExtCocycleToExt P M n)
  wi := (projectiveAbExtShortComplex P M n).abLeftHomologyData.wi
  hi := (projectiveAbExtShortComplex P M n).abLeftHomologyData.hi
  wπ := by
    ext y
    exact (projectiveModuleExtCocycleToExt_eq_zero_iff P M n _).mpr ⟨y, rfl⟩
  hπ := by
    apply Classical.choice
    apply (ShortComplex.exact_and_epi_g_iff_g_is_cokernel
      (ShortComplex.mk
        (AddCommGrpCat.ofHom (projectiveAbExtShortComplex P M n).abToCycles)
        (AddCommGrpCat.ofHom (projectiveModuleExtCocycleToExt P M n))
        (by ext y; exact
          (projectiveModuleExtCocycleToExt_eq_zero_iff P M n _).mpr ⟨y, rfl⟩))).mp
    constructor
    · rw [ShortComplex.ab_exact_iff]
      intro x hx
      exact (projectiveModuleExtCocycleToExt_eq_zero_iff P M n x).mp hx
    · exact (AddCommGrpCat.epi_iff_surjective _).mpr
        (projectiveModuleExtCocycleToExt_surjective P M n)

/-- The additive homology of the actual linear Hom complex is the actual
derived Ext group, for any specified projective resolution. -/
def projectiveModuleHomologyIsoExtSucc {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (M : ModuleCat.{u} R) (n : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj
        ((P.complex.linearYonedaObj R M).homology (n + 1)) ≅
      AddCommGrpCat.of (Abelian.Ext N M (n + 1)) :=
  (forget₂ (ModuleCat R) AddCommGrpCat).mapIso
      ((P.complex.linearYonedaObj R M).homologyIsoSc' n (n + 1) (n + 2)
        (by simp) (by simp)) ≪≫
    ((projectiveModuleExtShortComplex P M n).mapHomologyIso
      (forget₂ (ModuleCat R) AddCommGrpCat)).symm ≪≫
    (projectiveModuleExtHomologyData P M n).homologyIso

/-- The original module-valued Ext and actual derived-category Ext agree
in every degree as actual additive groups. -/
def moduleExtIsoAbelianExt (N M : ModuleCat.{u} R) (i : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj
      (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).obj M) ≅
        AddCommGrpCat.of (Abelian.Ext N M i) :=
  match i with
  | 0 => (forget₂ (ModuleCat R) AddCommGrpCat).mapIso ((extZeroIsoHom M).app (op N)) ≪≫
      AddEquiv.toAddCommGrpIso Abelian.Ext.addEquiv₀.symm
  | n + 1 =>
      (forget₂ (ModuleCat R) AddCommGrpCat).mapIso
        ((projectiveResolution N).isoExt (R := R) (n + 1) M) ≪≫
      projectiveModuleHomologyIsoExtSucc (projectiveResolution N) M n

/-- The same genuine comparison exposed as an additive equivalence of values. -/
def moduleExtAddEquivAbelianExt (N M : ModuleCat.{u} R) (i : ℕ) :
    (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).obj M) ≃+
      Abelian.Ext N M i :=
  (moduleExtIsoAbelianExt N M i).addCommGroupIsoToAddEquiv

end SGA.SGA2.ExposeIV
