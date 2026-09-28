/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# SGA 2, Exposé II, Lemma 11: the principal annihilator system

This file formalizes the algebraic argument in the one-generator case of II.11.
For an element `f` of a commutative ring and a module `M`, the annihilators of
`f ^ n` form an increasing sequence, with inverse transition maps given by
multiplication by `f ^ (m - n)`. For a noetherian module the sequence stabilizes;
a single power of `f` then kills every annihilator, so these transition maps
vanish uniformly once `m - n` is sufficiently large. In particular, the inverse
system is essentially zero in the sense of II.9(c).

`PrincipalKoszul.lean` identifies these annihilators with degree-one Koszul
homology and proves the one-generator case of II.11. `VariableAnnihilators.lean`
handles varying coefficients. `KoszulCofiber.lean` constructs the exact
sequence, and `KoszulProZero.lean` completes the multiple-generator induction.
-/

universe u v

namespace SGA.SGA2.ExposeII

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

section Naturality

variable {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The map on annihilators induced by a module homomorphism. -/
def torsionByMap (a : R) (φ : M →ₗ[R] N) :
    Submodule.torsionBy R M a →ₗ[R] Submodule.torsionBy R N a where
  toFun x := ⟨φ x, by
    change a • φ (x : M) = 0
    rw [← map_smul, Submodule.smul_coe_torsionBy, map_zero]⟩
  map_add' x y := Subtype.ext (φ.map_add x y)
  map_smul' r x := Subtype.ext (φ.map_smul r x)

@[simp]
theorem torsionByMap_apply (a : R) (φ : M →ₗ[R] N) (x : Submodule.torsionBy R M a) :
    (torsionByMap a φ x : N) = φ (x : M) := rfl

@[simp]
theorem torsionByMap_id (a : R) :
    torsionByMap a (LinearMap.id : M →ₗ[R] M) = LinearMap.id := rfl

/-- Passing to annihilators respects composition of module homomorphisms. -/
theorem torsionByMap_comp (a : R) (φ : M →ₗ[R] N) (ψ : N →ₗ[R] P) :
    torsionByMap a (ψ.comp φ) = (torsionByMap a ψ).comp (torsionByMap a φ) := rfl

end Naturality

/-- II.11: the annihilators of successive powers of an element form an
increasing sequence of submodules. -/
theorem torsionBy_pow_monotone (f : R) :
    Monotone fun n : ℕ ↦ Submodule.torsionBy R M (f ^ n) := by
  intro n m hnm
  exact Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow f hnm)

/-- The inverse transition map on the principal annihilator system of II.11. -/
def torsionTransition (f : R) {n m : ℕ} (hnm : n ≤ m) :
    Submodule.torsionBy R M (f ^ m) →ₗ[R] Submodule.torsionBy R M (f ^ n) where
  toFun x := ⟨f ^ (m - n) • (x : M), by
    change f ^ n • (f ^ (m - n) • (x : M)) = 0
    rw [← mul_smul, ← pow_add, Nat.add_sub_of_le hnm]
    exact x.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact smul_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    exact smul_comm _ _ _

@[simp]
theorem torsionTransition_apply (f : R) {n m : ℕ} (hnm : n ≤ m)
    (x : Submodule.torsionBy R M (f ^ m)) :
    (torsionTransition f hnm x : M) = f ^ (m - n) • (x : M) := rfl

@[simp]
theorem torsionTransition_self (f : R) (n : ℕ) :
    torsionTransition (M := M) f (le_refl n) = LinearMap.id := by
  ext x
  simp [torsionTransition]

/-- The principal annihilator transition maps compose as an inverse system. -/
theorem torsionTransition_comp (f : R) {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    (torsionTransition (M := M) f hnm).comp (torsionTransition f hmk) =
      torsionTransition f (hnm.trans hmk) := by
  ext x
  change f ^ (m - n) • (f ^ (k - m) • (x : M)) = f ^ (k - n) • (x : M)
  rw [← mul_smul, ← pow_add]
  congr 2
  omega

/-- The transition maps commute with the maps on annihilators induced by
module homomorphisms, as used in the factorization in the proof of II.11. -/
theorem torsionTransition_naturality {N : Type*} [AddCommGroup N] [Module R N]
    (f : R) (φ : M →ₗ[R] N) {n m : ℕ} (hnm : n ≤ m) :
    (torsionByMap (f ^ n) φ).comp (torsionTransition f hnm) =
      (torsionTransition f hnm).comp (torsionByMap (f ^ m) φ) := by
  ext x
  exact φ.map_smul (f ^ (m - n)) (x : M)

/-- II.11: the annihilators of powers of `f` eventually stabilize on a
noetherian module. -/
theorem exists_torsionBy_pow_stable [IsNoetherian R M] (f : R) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      Submodule.torsionBy R M (f ^ n) = Submodule.torsionBy R M (f ^ c) := by
  obtain ⟨c, hc⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R M) ⟨_, torsionBy_pow_monotone (M := M) f⟩
  exact ⟨c, fun n hn ↦ (hc n hn).symm⟩

/-- The stationary value of the principal annihilator sequence contains all
its terms, including the finitely many terms before stabilization. -/
theorem torsionBy_pow_le_of_stable (f : R) {c : ℕ}
    (hc : ∀ n : ℕ, c ≤ n →
      Submodule.torsionBy R M (f ^ n) = Submodule.torsionBy R M (f ^ c)) (n : ℕ) :
    Submodule.torsionBy R M (f ^ n) ≤ Submodule.torsionBy R M (f ^ c) := by
  rcases le_total n c with hn | hn
  · exact torsionBy_pow_monotone f hn
  · exact (hc n hn).le

/-- II.11: a single power of `f` annihilates every element annihilated by
some power of `f`, when the module is noetherian. -/
theorem exists_uniform_pow_smul_eq_zero [IsNoetherian R M] (f : R) :
    ∃ c : ℕ, ∀ n : ℕ, ∀ x : M, f ^ n • x = 0 → f ^ c • x = 0 := by
  obtain ⟨c, hc⟩ := exists_torsionBy_pow_stable (M := M) f
  exact ⟨c, fun n x hx ↦ torsionBy_pow_le_of_stable f hc n hx⟩

/-- A uniform bound on principal torsion gives a uniform bound for vanishing
of the inverse transition maps. No noetherian hypothesis is needed here. -/
theorem torsionTransition_eq_zero_of_uniform_bound (f : R) {c : ℕ}
    (hc : ∀ n : ℕ, ∀ x : M, f ^ n • x = 0 → f ^ c • x = 0)
    {n m : ℕ} (hnm : n ≤ m) (hcm : n + c ≤ m) :
    torsionTransition (M := M) f hnm = 0 := by
  ext x
  change f ^ (m - n) • (x : M) = 0
  have hc' : c ≤ m - n := by omega
  have hx : (x : M) ∈ Submodule.torsionBy R M (f ^ c) := hc m x x.property
  exact torsionBy_pow_monotone f hc' hx

/-- II.11, one-generator algebraic core: all sufficiently long transition
maps vanish, with one bound independent of the target index. -/
theorem exists_uniform_torsionTransition_eq_zero [IsNoetherian R M] (f : R) :
    ∃ c : ℕ, ∀ (n m : ℕ) (hnm : n ≤ m), n + c ≤ m →
      torsionTransition (M := M) f hnm = 0 := by
  obtain ⟨c, hc⟩ := exists_uniform_pow_smul_eq_zero (M := M) f
  exact ⟨c, fun _ _ hnm hcm ↦ torsionTransition_eq_zero_of_uniform_bound f hc hnm hcm⟩

/-- II.11, one-generator algebraic core, using the strict inequality in the
definition of essentially zero from II.9(c). -/
theorem principal_annihilator_system_essentially_zero [IsNoetherian R M] (f : R)
    (n : ℕ) : ∃ (m : ℕ) (hnm : n < m), torsionTransition (M := M) f hnm.le = 0 := by
  obtain ⟨c, hc⟩ := exists_uniform_torsionTransition_eq_zero (M := M) f
  refine ⟨n + c + 1, by omega, hc n (n + c + 1) (by omega) (by omega)⟩

end SGA.SGA2.ExposeII
