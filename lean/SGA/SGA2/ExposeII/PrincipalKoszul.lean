/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.PrincipalSystem
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# SGA 2, Exposé II, Lemma 11: the one-generator Koszul complex

The principal Koszul chain complex has `M` in degrees zero and one, with
differential multiplication by `f`, and zero in all other degrees. We identify
its zeroth homology with `M / fM`, its first homology with the annihilator of `f`,
and prove that homology in degrees greater than one vanishes. The chain maps for
powers of `f` induce the annihilator transitions, so positive homology forms an
essentially zero inverse system when `M` is noetherian. The induction for several
generators is completed in `KoszulProZero.lean`.
-/

universe u

open CategoryTheory Limits Opposite ZeroObject

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/-- The terms of the one-generator Koszul complex. -/
def principalKoszulX : ℕ → ModuleCat.{u} R
  | 0 => M
  | 1 => M
  | _ + 2 => ModuleCat.of R PUnit

/-- Multiplication by `f` is the only nonzero differential. -/
def principalKoszulD (f : R) : ∀ n, principalKoszulX M (n + 1) ⟶ principalKoszulX M n
  | 0 => ModuleCat.ofHom (f • (LinearMap.id : M →ₗ[R] M))
  | _ + 1 => 0

/-- The Koszul chain complex on a single element with coefficients in `M`. -/
def principalKoszul (f : R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (principalKoszulX M) (principalKoszulD M f) (by
    intro n
    cases n <;> exact zero_comp)

@[simp]
theorem principalKoszul_d_one_zero (f : R) :
    (principalKoszul M f).d 1 0 = ModuleCat.ofHom (f • (LinearMap.id : M →ₗ[R] M)) := by
  exact ChainComplex.of_d (principalKoszulX M) (principalKoszulD M f) 0

@[simp]
theorem principalKoszul_d_succ_succ (f : R) (n : ℕ) :
    (principalKoszul M f).d (n + 2) (n + 1) = 0 := by
  exact ChainComplex.of_d (principalKoszulX M) (principalKoszulD M f) (n + 1)

/-- II.11: a principal Koszul complex has no homology above degree one. -/
theorem principalKoszul_isZero_homology (f : R) (i : ℕ) (hi : 1 < i) :
    IsZero ((principalKoszul M f).homology i) := by
  apply ShortComplex.isZero_homology_of_isZero_X₂
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ i by omega)
  change IsZero (principalKoszulX M (2 + n))
  rw [Nat.add_comm]
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)

/-- Zeroth principal Koszul homology is the quotient `M / fM`, as used in the
inductive exact sequence of II.11. -/
noncomputable def principalKoszulHomologyZeroIso (f : R) :
    (principalKoszul M f).homology 0 ≅
      ModuleCat.of R (M ⧸ LinearMap.range (f • (LinearMap.id : M →ₗ[R] M))) :=
  (principalKoszul M f).homologyIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    ((principalKoszul M f).sc' 1 0 0).asIsoHomologyι
      ((principalKoszul M f).shape 0 0 (by simp)) ≪≫
    ((principalKoszul M f).sc' 1 0 0).moduleCatOpcyclesIso

/-- The kernel of multiplication by `f` is its annihilator. -/
def principalKoszulCyclesEquiv (f : R) :
    LinearMap.ker ((principalKoszul M f).d 1 0).hom ≃ₗ[R]
      Submodule.torsionBy R M f :=
  LinearEquiv.ofEq _ _ (by
    ext x
    rw [principalKoszul_d_one_zero]
    change f • x = 0 ↔ f • x = 0
    rfl)

/-- II.11: first Koszul homology on one generator is its annihilator. -/
noncomputable def principalKoszulHomologyOneIso (f : R) :
    (principalKoszul M f).homology 1 ≅ ModuleCat.of R (Submodule.torsionBy R M f) :=
  (principalKoszul M f).homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    (((principalKoszul M f).sc' 2 1 0).asIsoHomologyπ
      (principalKoszul_d_succ_succ M f 0)).symm ≪≫
    ((principalKoszul M f).sc' 2 1 0).moduleCatCyclesIso ≪≫
    (principalKoszulCyclesEquiv M f).toModuleIso

/-- Under the homology identification, a cycle maps to its underlying element. -/
@[reassoc (attr := simp)]
theorem principalKoszulHomologyOneIso_hom_subtype (f : R) :
    (principalKoszul M f).homologyπ 1 ≫ (principalKoszulHomologyOneIso M f).hom ≫
      ModuleCat.ofHom (Submodule.torsionBy R M f).subtype =
    (principalKoszul M f).iCycles 1 := by
  have he : (principalKoszulCyclesEquiv M f).toModuleIso.hom ≫
      ModuleCat.ofHom (Submodule.torsionBy R M f).subtype =
      ((principalKoszul M f).sc' 2 1 0).moduleCatLeftHomologyData.i := by
    ext x
    rfl
  dsimp only [principalKoszulHomologyOneIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, he, HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    ShortComplex.homologyπ_comp_asIsoHomologyπ_inv_assoc,
    ShortComplex.moduleCatCyclesIso_hom_i]
  simp

/-- The inverse transition map on principal Koszul complexes: the identity in
degree zero and multiplication by `f ^ (m - n)` in degree one. -/
def principalKoszulTransition (f : R) {n m : ℕ} (hnm : n ≤ m) :
    principalKoszul M (f ^ m) ⟶ principalKoszul M (f ^ n) :=
  ChainComplex.ofHom (fun i ↦ match i with
    | 0 => 𝟙 M
    | 1 => ModuleCat.ofHom (f ^ (m - n) • (LinearMap.id : M →ₗ[R] M))
    | _ + 2 => 0) (by
      intro i
      cases i with
      | zero =>
        ext x
        change f ^ n • (f ^ (m - n) • x) = f ^ m • x
        rw [← mul_smul, ← pow_add, Nat.add_sub_of_le hnm]
      | succ i =>
        cases i with
        | zero =>
          ext x
          change (0 : M) = f ^ (m - n) • (0 : M)
          simp
        | succ i =>
          ext x
          exact Subsingleton.elim (α := PUnit) _ _)

@[simp]
theorem principalKoszulTransition_f_zero (f : R) {n m : ℕ} (hnm : n ≤ m) :
    (principalKoszulTransition M f hnm).f 0 = 𝟙 M := rfl

@[simp]
theorem principalKoszulTransition_f_one (f : R) {n m : ℕ} (hnm : n ≤ m) :
    (principalKoszulTransition M f hnm).f 1 =
      ModuleCat.ofHom (f ^ (m - n) • (LinearMap.id : M →ₗ[R] M)) := rfl

/-- The isomorphism with annihilators identifies the map induced on homology
with the scalar transition map in the proof of II.11. -/
theorem principalKoszulHomologyOneIso_naturality (f : R) {n m : ℕ} (hnm : n ≤ m) :
    HomologicalComplex.homologyMap (principalKoszulTransition M f hnm) 1 ≫
      (principalKoszulHomologyOneIso M (f ^ n)).hom =
    (principalKoszulHomologyOneIso M (f ^ m)).hom ≫
      ModuleCat.ofHom (torsionTransition (M := M) f hnm) := by
  let ι := ModuleCat.ofHom (Submodule.torsionBy R M (f ^ n)).subtype
  have : Mono ι := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  apply (cancel_mono ι).mp
  apply (cancel_epi ((principalKoszul M (f ^ m)).homologyπ 1)).mp
  have ht : ModuleCat.ofHom (torsionTransition (M := M) f hnm) ≫ ι =
      ModuleCat.ofHom (Submodule.torsionBy R M (f ^ m)).subtype ≫
        (principalKoszulTransition M f hnm).f 1 := by
    ext x
    rfl
  dsimp only [ι] at *
  simp only [Category.assoc, ht,
    HomologicalComplex.homologyπ_naturality_assoc,
    principalKoszulHomologyOneIso_hom_subtype,
    principalKoszulHomologyOneIso_hom_subtype_assoc,
    HomologicalComplex.cyclesMap_i]

@[simp]
theorem principalKoszulTransition_self (f : R) (n : ℕ) :
    principalKoszulTransition M f (le_refl n) = 𝟙 _ := by
  ext i x
  match i with
  | 0 => rfl
  | 1 =>
    change f ^ (n - n) • x = x
    simp
  | _ + 2 => exact Subsingleton.elim (α := PUnit) _ _

/-- Principal Koszul chain transitions compose. -/
theorem principalKoszulTransition_comp (f : R) {n m k : ℕ}
    (hnm : n ≤ m) (hmk : m ≤ k) :
    principalKoszulTransition M f hmk ≫ principalKoszulTransition M f hnm =
      principalKoszulTransition M f (hnm.trans hmk) := by
  ext i x
  match i with
  | 0 => rfl
  | 1 =>
    change f ^ (m - n) • (f ^ (k - m) • x) = f ^ (k - n) • x
    rw [← mul_smul, ← pow_add]
    congr 2
    omega
  | _ + 2 => exact Subsingleton.elim (α := PUnit) _ _

/-- The inverse system of principal Koszul chain complexes. -/
def principalKoszulSystem (f : R) : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj n := principalKoszul M (f ^ n.unop)
  map h := principalKoszulTransition M f (leOfHom h.unop)
  map_id n := principalKoszulTransition_self M f n.unop
  map_comp h k := (principalKoszulTransition_comp M f
    (leOfHom k.unop) (leOfHom h.unop)).symm

/-- The inverse system of principal Koszul homology modules in degree `i`. -/
noncomputable def principalKoszulHomologySystem (f : R) (i : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  principalKoszulSystem M f ⋙ HomologicalComplex.homologyFunctor _ _ i

/-- The degree-one Koszul homology system is the principal annihilator system. -/
noncomputable def principalKoszulHomologySystemOneIso (f : R) :
    principalKoszulHomologySystem M f 1 ≅ principalAnnihilatorSystem M f :=
  NatIso.ofComponents (fun n ↦ principalKoszulHomologyOneIso M (f ^ n.unop))
    (fun h ↦ principalKoszulHomologyOneIso_naturality M f (leOfHom h.unop))

/-- II.11 in the one-generator case: every positive Koszul homology inverse
system of a noetherian module is essentially zero. -/
theorem principalKoszulHomologySystem_isEssentiallyZero [IsNoetherian R M]
    (f : R) (i : ℕ) (hi : 0 < i) :
    IsEssentiallyZero (principalKoszulHomologySystem M f i) := by
  by_cases h : i = 1
  · subst h
    exact IsEssentiallyZero.of_mono (principalKoszulHomologySystemOneIso M f).hom
      (principalAnnihilatorSystem_isEssentiallyZero M f)
  · intro n
    refine ⟨n, 𝟙 n, ?_⟩
    exact (principalKoszul_isZero_homology M (f ^ n.unop) i (by omega)).eq_of_src _ _

/-- II.11, principal case: a single bound works for every positive homological
degree and every target power. -/
theorem exists_uniform_principalKoszul_homologyMap_eq_zero [IsNoetherian R M] (f : R) :
    ∃ c : ℕ, ∀ (i : ℕ), 0 < i → ∀ (n m : ℕ) (hnm : n ≤ m), n + c ≤ m →
      HomologicalComplex.homologyMap (principalKoszulTransition M f hnm) i = 0 := by
  obtain ⟨c, hc⟩ := exists_uniform_torsionTransition_eq_zero (M := M) f
  refine ⟨c, fun i hi n m hnm hcm ↦ ?_⟩
  by_cases h : i = 1
  · subst h
    apply (cancel_mono (principalKoszulHomologyOneIso M (f ^ n)).hom).mp
    rw [principalKoszulHomologyOneIso_naturality, hc n m hnm hcm]
    simp
  · exact (principalKoszul_isZero_homology M (f ^ m) i (by omega)).eq_of_src _ _

end SGA.SGA2.ExposeII
