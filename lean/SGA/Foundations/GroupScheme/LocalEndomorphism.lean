/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Nakayama

/-!
# Local endomorphisms acting on `𝔪/𝔪²` by an invertible scalar

Let `R` be a noetherian local ring with maximal ideal `𝔪`, `φ : R → R` a local endomorphism and
`c ∈ R` a unit such that `φ t - c t ∈ 𝔪²` for all `t ∈ 𝔪` (`φ` acts on the cotangent space as
multiplication by `c`). Then

* `φ(𝔪) R = 𝔪` (`IsLocalRing.map_maximalIdeal_eq_of_sub_mul_mem_sq`, by Nakayama);
* `φ` is injective (`IsLocalRing.injective_of_sub_mul_mem_sq`): `φ` acts on `𝔪ᵈ/𝔪ᵈ⁺¹` as
  multiplication by `cᵈ`, and `⋂ 𝔪ᵈ = 0` (Krull).

We also record that `k ⊕ M` (square-zero extension of a field) is a local ring and that the maps
`k ⊕ M → k` and `k ⊕ M → k ⊕ N` are local (`TrivSqZeroExt.isLocalRing_of_field`, …).

This is used for multiplication by `n` on a group scheme at the origin, `n` invertible
(Mumford, *Abelian varieties*, §4).
-/

open IsLocalRing

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] {φ : R →+* R} [IsLocalHom φ] {c : R}

/-- If `φ` acts on `𝔪/𝔪²` as multiplication by `c`, it acts on `𝔪ᵈ/𝔪ᵈ⁺¹` as multiplication by
`cᵈ` (`d ≥ 1`). -/
lemma sub_pow_mul_mem_maximalIdeal_pow (h : ∀ t ∈ maximalIdeal R, φ t - c * t ∈ maximalIdeal R ^ 2)
    (d : ℕ) {x : R} (hx : x ∈ maximalIdeal R ^ (d + 1)) :
    φ x - c ^ (d + 1) * x ∈ maximalIdeal R ^ (d + 2) := by
  -- `φ` preserves the powers of `𝔪`
  have hpow (e : ℕ) {t : R} (ht : t ∈ maximalIdeal R ^ e) : φ t ∈ maximalIdeal R ^ e := by
    have := Ideal.pow_right_mono (map_maximalIdeal_le φ) e
    rw [← Ideal.map_pow] at this
    exact this (Ideal.mem_map_of_mem φ ht)
  induction d generalizing x with
  | zero => simpa using h x (by simpa using hx)
  | succ d ih =>
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx (fun t ht z hz ↦ ?_) (fun x y hx hy ↦ ?_)
    · have e : φ (t * z) - c ^ (d + 1 + 1) * (t * z) =
          (φ t - c * t) * φ z + c * t * (φ z - c ^ (d + 1) * z) := by
        rw [map_mul]
        ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · rw [show d + 1 + 2 = 2 + (d + 1) by ring, pow_add]
        exact Ideal.mul_mem_mul (h t ht) (hpow _ hz)
      · rw [show d + 1 + 2 = 1 + (d + 2) by ring, pow_add, pow_one]
        exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ ht) (ih hz)
    · have e : φ (x + y) - c ^ (d + 1 + 1) * (x + y) =
          (φ x - c ^ (d + 1 + 1) * x) + (φ y - c ^ (d + 1 + 1) * y) := by
        rw [map_add]
        ring
      rw [e]
      exact Ideal.add_mem _ hx hy

variable [IsNoetherianRing R]

/-- If `φ` acts on `𝔪/𝔪²` as multiplication by a unit, then `φ(𝔪) R = 𝔪` (Nakayama). -/
theorem map_maximalIdeal_eq_of_sub_mul_mem_sq (hc : IsUnit c)
    (h : ∀ t ∈ maximalIdeal R, φ t - c * t ∈ maximalIdeal R ^ 2) :
    Ideal.map φ (maximalIdeal R) = maximalIdeal R := by
  refine le_antisymm (map_maximalIdeal_le φ) ?_
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
    (le_of_eq (jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm) fun t ht ↦ ?_
  obtain ⟨u, rfl⟩ := hc
  have e : t = (u⁻¹ : Rˣ) * φ t - (u⁻¹ : Rˣ) * (φ t - u * t) := by
    rw [mul_sub, sub_sub_cancel, ← mul_assoc, Units.inv_mul, one_mul]
  rw [e]
  refine Submodule.sub_mem _ (Submodule.mem_sup_left (Ideal.mul_mem_left _ _
    (Ideal.mem_map_of_mem φ ht))) (Submodule.mem_sup_right ?_)
  rw [smul_eq_mul, ← pow_two]
  exact Ideal.mul_mem_left _ _ (h t ht)

/-- If `φ` acts on `𝔪/𝔪²` as multiplication by a unit, then `φ` is injective. -/
theorem injective_of_sub_mul_mem_sq (hc : IsUnit c)
    (h : ∀ t ∈ maximalIdeal R, φ t - c * t ∈ maximalIdeal R ^ 2) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra hne
  have hf𝔪 : f ∈ maximalIdeal R := by
    by_contra hu
    have : IsUnit (φ f) := ((mem_maximalIdeal _).not.mp hu |> not_not.mp).map φ
    rw [hf] at this
    exact not_isUnit_zero this
  -- Krull: `f ∉ 𝔪ᵈ⁺¹` for some `d`.
  have hex : ∃ d : ℕ, f ∉ maximalIdeal R ^ (d + 1) := by
    by_contra hall
    push Not at hall
    have : f ∈ ⨅ d : ℕ, maximalIdeal R ^ d := by
      refine Submodule.mem_iInf _ |>.mpr fun d ↦ ?_
      cases d with
      | zero => simp
      | succ d => exact hall d
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top] at this
    exact hne this
  classical
  let d := Nat.find hex
  have hd : f ∉ maximalIdeal R ^ (d + 1) := Nat.find_spec hex
  have hd0 : d ≠ 0 := fun h0 ↦ hd (by rw [h0, zero_add, pow_one]; exact hf𝔪)
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hd0
  have hfd : f ∈ maximalIdeal R ^ (e + 1) := by
    have := Nat.find_min hex (show e < d by omega)
    push Not at this
    exact this
  have key := sub_pow_mul_mem_maximalIdeal_pow h e hfd
  rw [hf, zero_sub, neg_mem_iff] at key
  apply hd
  rw [he]
  obtain ⟨u, rfl⟩ := hc
  have : f = ((u ^ (e + 1))⁻¹ : Rˣ) * ((u : R) ^ (e + 1) * f) := by
    rw [← mul_assoc, ← Units.val_pow_eq_pow_val, Units.inv_mul, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ key

end IsLocalRing

namespace TrivSqZeroExt

variable {k : Type*} [Field k] (M : Type*) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
  [IsCentralScalar k M]

/-- `k ⊕ M` with `M² = 0` is a local ring, for a field `k`. -/
theorem isLocalRing_of_field : IsLocalRing (TrivSqZeroExt k M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a ↦ by
    rw [isUnit_iff_isUnit_fst, isUnit_iff_isUnit_fst, fst_sub, fst_one]
    rcases eq_or_ne a.fst 0 with ha | ha
    · right
      rw [ha, sub_zero]
      exact isUnit_one
    · exact Or.inl ha.isUnit

attribute [local instance] isLocalRing_of_field

/-- The projection `k ⊕ M → k` is a local homomorphism. -/
lemma isLocalHom_fstHom : IsLocalHom (fstHom k k M).toRingHom :=
  ⟨fun _ hx ↦ isUnit_iff_isUnit_fst.mpr hx⟩

/-- The map `k ⊕ M → k ⊕ N` induced by a linear map `M → N` is a local homomorphism. -/
lemma isLocalHom_map {M N : Type*} [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
    [IsCentralScalar k M] [AddCommGroup N] [Module k N] [Module kᵐᵒᵖ N] [IsCentralScalar k N]
    (f : M →ₗ[k] N) : IsLocalHom (map f).toRingHom :=
  ⟨fun x hx ↦ by
    rw [isUnit_iff_isUnit_fst] at hx ⊢
    simpa using hx⟩

/-- The structure map `k → k ⊕ M` is a local homomorphism. -/
lemma isLocalHom_algebraMap : IsLocalHom (algebraMap k (TrivSqZeroExt k M)) :=
  ⟨fun a ha ↦ by
    rw [isUnit_iff_isUnit_fst, algebraMap_eq_inl, fst_inl] at ha
    exact ha⟩

end TrivSqZeroExt
