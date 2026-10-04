/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Computations in the exterior algebra

Auxiliary lemmas for computing products in mathlib's `ExteriorAlgebra R M`:

* `ExteriorAlgebra.ι_mul_ι_comm`: generators anticommute;
* `ExteriorAlgebra.ιMulti_mul_ι`: `(v₀ ∧ ⋯ ∧ v_{k-1}) ∧ w = (-1)ᵏ w ∧ v₀ ∧ ⋯ ∧ v_{k-1}`;
* `ExteriorAlgebra.ι_mul_ι_mem_center`: a product `ι x * ι y` of two generators is central;
* `ExteriorAlgebra.ιMulti_mul_ιMulti_eq_prod`: the interleaving formula
  `(a₀ ∧ ⋯ ∧ a_{p-1}) ∧ (b₀ ∧ ⋯ ∧ b_{p-1}) = (-1)^(p choose 2) ∏ₖ (aₖ ∧ bₖ)`;
* `Finset.sum_pow_of_mul_self_eq_zero`: in a commutative semiring, if `f i * f i = 0` for all
  `i`, then `(∑ᵢ f i)ᵐ = m! ∑_{|T| = m} ∏_{i ∈ T} f i`.

Reference: N. Bourbaki, *Algebra I*, Ch. III, §7.
-/

open scoped BigOperators

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Generators of the exterior algebra anticommute. -/
theorem ι_mul_ι_comm (x y : M) : ι R x * ι R y = -(ι R y * ι R x) :=
  eq_neg_of_add_eq_zero_left (ι_add_mul_swap x y)

/-- `(v₀ ∧ ⋯ ∧ v_{k-1}) ∧ w = (-1)ᵏ w ∧ v₀ ∧ ⋯ ∧ v_{k-1}`. -/
theorem ιMulti_mul_ι {k : ℕ} (v : Fin k → M) (w : M) :
    ιMulti R k v * ι R w = ((-1 : R) ^ k) • (ι R w * ιMulti R k v) := by
  induction k with
  | zero => simp [ιMulti_zero_apply]
  | succ k ih =>
    rw [ιMulti_succ_apply, mul_assoc, ih, mul_smul_comm, ← mul_assoc, ι_mul_ι_comm, neg_mul,
      mul_assoc, smul_neg, ← neg_smul, pow_succ, mul_neg_one]

/-- A product `ι x * ι y` of two generators commutes with every element. -/
theorem ι_mul_ι_mul_comm (x y : M) (z : ExteriorAlgebra R M) :
    ι R x * ι R y * z = z * (ι R x * ι R y) := by
  induction z using ExteriorAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r _).symm
  | ι m =>
    rw [mul_assoc, ι_mul_ι_comm y m, mul_neg, ← mul_assoc, ι_mul_ι_comm x m, neg_mul, neg_neg,
      mul_assoc]
  | add a b ha hb => rw [mul_add, add_mul, ha, hb]
  | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]

/-- A product `ι x * ι y` of two generators is central. -/
theorem ι_mul_ι_mem_center (x y : M) :
    ι R x * ι R y ∈ Subalgebra.center R (ExteriorAlgebra R M) :=
  Subalgebra.mem_center_iff.2 fun z ↦ (ι_mul_ι_mul_comm x y z).symm

/-- **Interleaving**: `(a₀ ∧ ⋯ ∧ a_{p-1}) ∧ (b₀ ∧ ⋯ ∧ b_{p-1}) = (-1)^(p choose 2) ∏ₖ (aₖ ∧ bₖ)`
(ordered product). -/
theorem ιMulti_mul_ιMulti_eq_prod {p : ℕ} (a b : Fin p → M) :
    ιMulti R p a * ιMulti R p b =
      ((-1 : R) ^ p.choose 2) • (List.ofFn fun k ↦ ι R (a k) * ι R (b k)).prod := by
  induction p with
  | zero => simp [ιMulti_zero_apply]
  | succ p ih =>
    calc ιMulti R (p + 1) a * ιMulti R (p + 1) b
        = ι R (a 0) * ((ιMulti R p (Matrix.vecTail a) * ι R (b 0)) *
            ιMulti R p (Matrix.vecTail b)) := by
          rw [ιMulti_succ_apply, ιMulti_succ_apply]
          simp only [mul_assoc]
      _ = ((-1 : R) ^ p) • (ι R (a 0) * ι R (b 0) *
            (ιMulti R p (Matrix.vecTail a) * ιMulti R p (Matrix.vecTail b))) := by
          rw [ιMulti_mul_ι, smul_mul_assoc, mul_smul_comm]
          simp only [mul_assoc]
      _ = _ := by
          rw [ih, mul_smul_comm, smul_smul, List.ofFn_succ, List.prod_cons,
            Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
          rfl

end ExteriorAlgebra

namespace Finset

/-- In a commutative semiring, if `f i * f i = 0` for all `i`, then
`(∑_{i ∈ s} f i)ᵐ = m! • ∑_{T ⊆ s, |T| = m} ∏_{i ∈ T} f i`. -/
theorem sum_pow_of_mul_self_eq_zero {ι A : Type*} [CommSemiring A]
    (s : Finset ι) (f : ι → A) (hf : ∀ i, f i * f i = 0) (m : ℕ) :
    (∑ i ∈ s, f i) ^ m = m.factorial • ∑ T ∈ s.powersetCard m, ∏ i ∈ T, f i := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    -- the key double counting: pairs `(T, i)` with `|T| = m`, `i ∈ s \ T` versus pairs `(T', i)`
    -- with `|T'| = m + 1`, `i ∈ T'`
    have key : ∑ T ∈ s.powersetCard m, ∑ i ∈ s, (∏ j ∈ T, f j) * f i =
        (m + 1) • ∑ T ∈ s.powersetCard (m + 1), ∏ j ∈ T, f j := by
      have h1 : ∀ T ∈ s.powersetCard m, ∑ i ∈ s, (∏ j ∈ T, f j) * f i =
          ∑ i ∈ s \ T, ∏ j ∈ insert i T, f j := by
        intro T hT
        have hTs : T ⊆ s := (mem_powersetCard.1 hT).1
        rw [← sum_sdiff hTs, sum_eq_zero (s := T) (fun i hi ↦ ?_), add_zero]
        · refine sum_congr rfl fun i hi ↦ ?_
          rw [prod_insert (mem_sdiff.1 hi).2, mul_comm]
        · rw [← mul_prod_erase T f hi, mul_comm, ← mul_assoc, hf, zero_mul]
      rw [sum_congr rfl h1, sum_sigma', nsmul_eq_mul, mul_comm, sum_mul]
      have h2 : ∀ T ∈ s.powersetCard (m + 1), (∏ j ∈ T, f j) * ((m + 1 : ℕ) : A) =
          ∑ i ∈ T, ∏ j ∈ T, f j := by
        intro T hT
        rw [sum_const, (mem_powersetCard.1 hT).2, nsmul_eq_mul, mul_comm]
      rw [sum_congr rfl h2, sum_sigma']
      refine sum_bij' (fun x _ ↦ ⟨insert x.2 x.1, x.2⟩) (fun y _ ↦ ⟨y.1.erase y.2, y.2⟩)
        ?_ ?_ ?_ ?_ ?_
      · rintro ⟨T, i⟩ h
        simp only [mem_sigma, mem_powersetCard, mem_sdiff] at h ⊢
        refine ⟨⟨insert_subset h.2.1 h.1.1, ?_⟩, mem_insert_self _ _⟩
        rw [card_insert_of_notMem h.2.2, h.1.2]
      · rintro ⟨T, i⟩ h
        simp only [mem_sigma, mem_powersetCard, mem_sdiff] at h ⊢
        refine ⟨⟨(erase_subset _ _).trans h.1.1, ?_⟩, h.1.1 h.2, notMem_erase _ _⟩
        rw [card_erase_of_mem h.2, h.1.2, Nat.add_sub_cancel]
      · rintro ⟨T, i⟩ h
        simp only [mem_sigma, mem_powersetCard, mem_sdiff] at h
        simp [erase_insert h.2.2]
      · rintro ⟨T, i⟩ h
        simp only [mem_sigma] at h
        simp [insert_erase h.2]
      · rintro ⟨T, i⟩ _
        rfl
    rw [pow_succ, ih, smul_mul_assoc, sum_mul]
    simp_rw [mul_sum]
    rw [key, smul_smul, Nat.factorial_succ, mul_comm (m + 1)]

end Finset
