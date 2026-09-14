/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.ModuleExtDerivedComparison
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The module-valued Ext comparison respects the original scalar actions

The original projective-resolution cocycle map is linear for the canonical
scalar action on derived-category Ext.  Its genuine module-valued homology
data upgrades the additive comparison without any finiteness assumptions.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false

/-- The actual cocycle construction respects the canonical Ext scalar action. -/
theorem projectiveResolution_extMk_smul {N M : ModuleCat.{u} R}
    (P : ProjectiveResolution N) {n : ℕ} (f : P.complex.X n ⟶ M)
    (m : ℕ) (hm : n + 1 = m) (hf : P.complex.d m n ≫ f = 0) (r : R) :
    P.extMk (r • f) m hm (by simp [hf]) = r • P.extMk f m hm hf := by
  rw [Abelian.Ext.smul_eq_comp_mk₀, P.extMk_comp_mk₀]
  simp only [Linear.comp_smul, Category.comp_id]

/-- The original linear cocycle map, not a transported scalar action. -/
def projectiveModuleExtCocycleToExtLinear {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (M : ModuleCat.{u} R) (n : ℕ) :
    LinearMap.ker (projectiveModuleExtShortComplex P M n).g.hom →ₗ[R]
      Abelian.Ext N M (n + 1) where
  toFun x := P.extMk x.val (n + 2) rfl x.property
  map_add' x y := (P.add_extMk x.val y.val (n + 2) rfl x.property y.property).symm
  map_smul' r x := projectiveResolution_extMk_smul P x.val (n + 2) rfl x.property r

set_option backward.isDefEq.respectTransparency false in
/-- Actual Ext, with its canonical module structure, is homology data for the
original module-valued Hom complex. -/
def projectiveModuleExtLinearHomologyData {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (M : ModuleCat.{u} R) (n : ℕ) :
    (projectiveModuleExtShortComplex P M n).LeftHomologyData where
  K := (projectiveModuleExtShortComplex P M n).moduleCatLeftHomologyData.K
  H := ModuleCat.of R (Abelian.Ext N M (n + 1))
  i := (projectiveModuleExtShortComplex P M n).moduleCatLeftHomologyData.i
  π := ModuleCat.ofHom (projectiveModuleExtCocycleToExtLinear P M n)
  wi := (projectiveModuleExtShortComplex P M n).moduleCatLeftHomologyData.wi
  hi := (projectiveModuleExtShortComplex P M n).moduleCatLeftHomologyData.hi
  wπ := by
    ext y
    exact (projectiveModuleExtCocycleToExt_eq_zero_iff P M n _).mpr ⟨y, rfl⟩
  hπ := by
    apply Classical.choice
    apply (ShortComplex.exact_and_epi_g_iff_g_is_cokernel
      (ShortComplex.mk
        (ModuleCat.ofHom (projectiveModuleExtShortComplex P M n).moduleCatToCycles)
        (ModuleCat.ofHom (projectiveModuleExtCocycleToExtLinear P M n))
        (by ext y; exact
          (projectiveModuleExtCocycleToExt_eq_zero_iff P M n _).mpr ⟨y, rfl⟩))).mp
    constructor
    · rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      exact (projectiveModuleExtCocycleToExt_eq_zero_iff P M n x).mp hx
    · exact (ModuleCat.epi_iff_surjective _).mpr
        (projectiveModuleExtCocycleToExt_surjective P M n)

/-- Forgetting the linear homology construction recovers the original
additive homology isomorphism, with the same cocycle map. -/
theorem projectiveModuleExtLinearHomologyData_map_homologyIso {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (M : ModuleCat.{u} R) (n : ℕ) :
    ((projectiveModuleExtLinearHomologyData P M n).map
        (forget₂ (ModuleCat R) AddCommGrpCat)).homologyIso =
      (projectiveModuleExtHomologyData P M n).homologyIso := by
  let γ : ShortComplex.LeftHomologyMapData (𝟙 (projectiveAbExtShortComplex P M n))
      ((projectiveModuleExtLinearHomologyData P M n).map
        (forget₂ (ModuleCat R) AddCommGrpCat))
      (projectiveModuleExtHomologyData P M n) :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by simp; rfl
      commf' := by
        apply (cancel_mono (projectiveModuleExtHomologyData P M n).i).mp
        simp
        rfl
      commπ := by simp; rfl }
  apply Iso.ext
  simpa [γ] using γ.homologyMap_comm.symm

/-- Linear comparison using any actual projective resolution. -/
def projectiveModuleHomologyLinearIsoExtSucc {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (M : ModuleCat.{u} R) (n : ℕ) :
    (P.complex.linearYonedaObj R M).homology (n + 1) ≅
      ModuleCat.of R (Abelian.Ext N M (n + 1)) :=
  (P.complex.linearYonedaObj R M).homologyIsoSc' n (n + 1) (n + 2)
      (by simp) (by simp) ≪≫
    (projectiveModuleExtLinearHomologyData P M n).homologyIso

/-- Forgetting scalars gives exactly the previously constructed additive iso. -/
theorem projectiveModuleHomologyLinearIsoExtSucc_forget {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (M : ModuleCat.{u} R) (n : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).mapIso
        (projectiveModuleHomologyLinearIsoExtSucc P M n) =
      projectiveModuleHomologyIsoExtSucc P M n := by
  unfold projectiveModuleHomologyLinearIsoExtSucc projectiveModuleHomologyIsoExtSucc
  rw [Functor.mapIso_trans,
    (projectiveModuleExtLinearHomologyData P M n).mapHomologyIso_eq,
    projectiveModuleExtLinearHomologyData_map_homologyIso]
  simp

/-- Actual module-valued Ext is canonically isomorphic to derived Ext endowed
with its original module structure. -/
def moduleExtLinearIsoAbelianExt (N M : ModuleCat.{u} R) (i : ℕ) :
    (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).obj M) ≅
      ModuleCat.of R (Abelian.Ext N M i) :=
  match i with
  | 0 => (extZeroIsoHom M).app (op N) ≪≫
      (Abelian.Ext.linearEquiv₀ (R := R)).symm.toModuleIso
  | n + 1 => (projectiveResolution N).isoExt (R := R) (n + 1) M ≪≫
      projectiveModuleHomologyLinearIsoExtSucc (projectiveResolution N) M n

/-- The module isomorphism is precisely the original additive comparison. -/
theorem moduleExtLinearIsoAbelianExt_forget (N M : ModuleCat.{u} R) (i : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).mapIso (moduleExtLinearIsoAbelianExt N M i) =
      moduleExtIsoAbelianExt N M i := by
  cases i with
  | zero => rfl
  | succ n =>
      dsimp only [moduleExtLinearIsoAbelianExt, moduleExtIsoAbelianExt]
      rw [Functor.mapIso_trans, projectiveModuleHomologyLinearIsoExtSucc_forget]

/-- The original additive Ext comparison, upgraded to a linear equivalence. -/
def moduleExtLinearEquivAbelianExt (N M : ModuleCat.{u} R) (i : ℕ) :
    (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).obj M) ≃ₗ[R]
      Abelian.Ext N M i :=
  (moduleExtLinearIsoAbelianExt N M i).toLinearEquiv

/-- The underlying additive equivalence is unchanged. -/
theorem moduleExtLinearEquivAbelianExt_toAddEquiv (N M : ModuleCat.{u} R) (i : ℕ) :
    (moduleExtLinearEquivAbelianExt N M i).toAddEquiv =
      moduleExtAddEquivAbelianExt N M i := by
  exact congrArg Iso.addCommGroupIsoToAddEquiv (moduleExtLinearIsoAbelianExt_forget N M i)

end SGA.SGA2.ExposeIV
