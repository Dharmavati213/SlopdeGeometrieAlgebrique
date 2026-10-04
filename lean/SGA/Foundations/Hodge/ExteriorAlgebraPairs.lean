/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.ExteriorAlgebraAux
import Mathlib.Order.Hom.PowersetCard

/-!
# Products of pairs of generators in the exterior algebra

Let `a, b : Fin n → M` be two families of vectors and `Pⱼ = aⱼ ∧ bⱼ = ι aⱼ * ι bⱼ`. The `Pⱼ` are
central and square to zero, so they generate a commutative subalgebra in which
`(∑ⱼ Pⱼ)ᵐ = m! ∑_{|T| = m} ∏_{j ∈ T} Pⱼ`. This file computes, for `p + m = n`,

  `(∑_J c_J a_J) ∧ (∑_J d_J b_J) ∧ (∑ⱼ Pⱼ)ᵐ = m! (-1)^(p choose 2) (∑_J c_J d_J) ∏ⱼ Pⱼ`

where `J` runs over the subsets of `{0, …, n-1}` of cardinality `p` and `a_J`, `b_J` are the
products of the `aⱼ`, `bⱼ`, `j ∈ J`, in increasing order
(`ExteriorAlgebra.sum_mul_sum_mul_pow_sum_pairCenter`). This is the algebraic heart of the
positivity of `i^{p²} θ ∧ θ̄ ∧ ωᵐ` for forms `θ` of type `(p, 0)` and a Kähler form `ω`
(`Foundations/Hodge/KahlerPositivity.lean`).

Main results:
* `ExteriorAlgebra.ιMulti_mem_exteriorPower`, `ExteriorAlgebra.mul_mem_exteriorPower`,
  `ExteriorAlgebra.pow_mem_exteriorPower`: membership in the exterior powers;
* `ExteriorAlgebra.ιMulti_mul_ι_self`: `(v₀ ∧ ⋯ ∧ v_{k-1}) ∧ vᵢ = 0`;
* `ExteriorAlgebra.pairCenter R a b j = Pⱼ`, as an element of the center;
* `ExteriorAlgebra.ιMulti_mul_ιMulti_eq_prod_pairCenter`:
  `a_J ∧ b_J = (-1)^(p choose 2) ∏_{j ∈ J} Pⱼ`;
* `ExteriorAlgebra.sum_mul_sum_mul_pow_sum_pairCenter`: the formula above.

Reference: N. Bourbaki, *Algebra I*, Ch. III, §7; D. Huybrechts, *Complex geometry*, §1.2.
-/

open scoped BigOperators

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Membership in exterior powers -/

lemma ιMulti_mem_exteriorPower {k : ℕ} (v : Fin k → M) : ιMulti R k v ∈ ⋀[R]^k M :=
  ιMulti_range R k (Set.mem_range_self v)

lemma mul_mem_exteriorPower {a b : ℕ} {x y : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^a M)
    (hy : y ∈ ⋀[R]^b M) : x * y ∈ ⋀[R]^(a + b) M := by
  change x * y ∈ LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ (a + b)
  rw [pow_add]
  exact Submodule.mul_mem_mul hx hy

lemma ι_mul_ι_mem_exteriorPower (x y : M) : ι R x * ι R y ∈ ⋀[R]^2 M := by
  have h := ιMulti_mem_exteriorPower (R := R) ![x, y]
  simpa [Matrix.vecTail] using h

lemma pow_mem_exteriorPower {a : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^a M) (m : ℕ) :
    x ^ m ∈ ⋀[R]^(a * m) M := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.mul_succ]
    exact mul_mem_exteriorPower ih hx

/-! ### Vanishing -/

/-- `ι w ∧ (v₀ ∧ ⋯ ∧ v_{k-1}) = ιMulti (w, v₀, …, v_{k-1})`. -/
lemma ι_mul_ιMulti {k : ℕ} (w : M) (v : Fin k → M) :
    ι R w * ιMulti R k v = ιMulti R (k + 1) (Fin.cons w v) := by
  rw [ιMulti_succ_apply]
  rfl

/-- `(v₀ ∧ ⋯ ∧ v_{k-1}) ∧ vᵢ = 0`. -/
lemma ιMulti_mul_ι_self {k : ℕ} (v : Fin k → M) (i : Fin k) : ιMulti R k v * ι R (v i) = 0 := by
  rw [ιMulti_mul_ι, ι_mul_ιMulti, ιMulti_eq_zero_of_not_inj, smul_zero]
  intro h
  have := h (a₁ := 0) (a₂ := i.succ) (by simp)
  exact Fin.succ_ne_zero i this.symm

/-- `(a ∧ b) ∧ (a ∧ b) = 0`. -/
lemma ι_mul_ι_mul_self (x y : M) : ι R x * ι R y * (ι R x * ι R y) = 0 := by
  calc ι R x * ι R y * (ι R x * ι R y) = ι R x * (ι R y * ι R x) * ι R y := by
        simp only [mul_assoc]
    _ = -(ι R x * ι R x * ι R y * ι R y) := by
        rw [ι_mul_ι_comm y x]
        simp only [mul_neg, neg_mul, mul_assoc]
    _ = 0 := by rw [ι_sq_zero, zero_mul, zero_mul, neg_zero]

/-! ### Products of pairs -/

section Pairs

variable {n : ℕ} (a b : Fin n → M)

variable (R) in
/-- `Pⱼ = aⱼ ∧ bⱼ`, as an element of the center of the exterior algebra. -/
def pairCenter (j : Fin n) : Subalgebra.center R (ExteriorAlgebra R M) :=
  ⟨ι R (a j) * ι R (b j), ι_mul_ι_mem_center _ _⟩

@[simp]
lemma coe_pairCenter (j : Fin n) :
    (pairCenter R a b j : ExteriorAlgebra R M) = ι R (a j) * ι R (b j) :=
  rfl

lemma pairCenter_mul_self (j : Fin n) : pairCenter R a b j * pairCenter R a b j = 0 :=
  Subtype.ext (ι_mul_ι_mul_self (a j) (b j))

lemma pairCenter_comm (j : Fin n) (x : ExteriorAlgebra R M) :
    (pairCenter R a b j : ExteriorAlgebra R M) * x = x * pairCenter R a b j :=
  (Subalgebra.mem_center_iff.1 (pairCenter R a b j).2 x).symm

/-- `(∑ⱼ Pⱼ)ᵐ = m! ∑_{|T| = m} ∏_{j ∈ T} Pⱼ`. -/
lemma sum_pairCenter_pow (m : ℕ) :
    (∑ j, pairCenter R a b j) ^ m =
      m.factorial • ∑ T ∈ Finset.univ.powersetCard m, ∏ j ∈ T, pairCenter R a b j :=
  Finset.sum_pow_of_mul_self_eq_zero _ _ (pairCenter_mul_self a b) m

/-- If `j ∈ T` and `aⱼ` occurs in `x`, then `x ∧ y ∧ ∏_{l ∈ T} Pₗ = 0`. -/
lemma ιMulti_mul_mul_prod_pairCenter_left {k : ℕ} (e : Fin k → Fin n) (y : ExteriorAlgebra R M)
    (T : Finset (Fin n)) (i : Fin k) (hi : e i ∈ T) :
    ιMulti R k (a ∘ e) * y * ((∏ l ∈ T, pairCenter R a b l : Subalgebra.center R _) :
      ExteriorAlgebra R M) = 0 := by
  classical
  rw [← Finset.mul_prod_erase T _ hi, Subalgebra.coe_mul, ← mul_assoc, mul_assoc _ y,
    ← pairCenter_comm, ← mul_assoc, coe_pairCenter, ← mul_assoc]
  have : ιMulti R k (a ∘ e) * ι R (a (e i)) = 0 := ιMulti_mul_ι_self (a ∘ e) i
  rw [this]
  simp

/-- If `j ∈ T` and `bⱼ` occurs in `y`, then `x ∧ y ∧ ∏_{l ∈ T} Pₗ = 0`. -/
lemma mul_ιMulti_mul_prod_pairCenter_right {k : ℕ} (e : Fin k → Fin n) (x : ExteriorAlgebra R M)
    (T : Finset (Fin n)) (i : Fin k) (hi : e i ∈ T) :
    x * ιMulti R k (b ∘ e) * ((∏ l ∈ T, pairCenter R a b l : Subalgebra.center R _) :
      ExteriorAlgebra R M) = 0 := by
  classical
  rw [← Finset.mul_prod_erase T _ hi, Subalgebra.coe_mul, ← mul_assoc, coe_pairCenter,
    ι_mul_ι_comm, mul_neg, neg_mul, ← mul_assoc, mul_assoc x]
  have : ιMulti R k (b ∘ e) * ι R (b (e i)) = 0 := ιMulti_mul_ι_self (b ∘ e) i
  rw [this]
  simp

/-- **Interleaving**: `a_e ∧ b_e = (-1)^(k choose 2) ∏ᵢ P_{e i}`. -/
lemma ιMulti_mul_ιMulti_eq_prod_pairCenter {k : ℕ} (e : Fin k → Fin n) :
    ιMulti R k (a ∘ e) * ιMulti R k (b ∘ e) =
      ((-1 : R) ^ k.choose 2) •
        ((∏ i, pairCenter R a b (e i) : Subalgebra.center R _) : ExteriorAlgebra R M) := by
  rw [ιMulti_mul_ιMulti_eq_prod]
  congr 1
  rw [← List.prod_ofFn, SubmonoidClass.coe_list_prod, List.map_ofFn]
  rfl

omit [AddCommGroup M] [Module R M] in
private lemma prod_orderEmbOfFin {β : Type*} [CommMonoid β] {p : ℕ} (s : Finset (Fin n))
    (h : s.card = p) (f : Fin n → β) : ∏ i, f (s.orderEmbOfFin h i) = ∏ j ∈ s, f j := by
  conv_rhs => rw [← Finset.image_orderEmbOfFin_univ s h]
  rw [Finset.prod_image fun x _ y _ hxy ↦ (s.orderEmbOfFin h).injective hxy]

/-- `a_J ∧ b_J = (-1)^(p choose 2) ∏_{j ∈ J} Pⱼ` for a subset `J` of cardinality `p`. -/
lemma ιMulti_mul_ιMulti_powersetCard {p : ℕ} (J : Set.powersetCard (Fin n) p) :
    ιMulti R p (a ∘ Set.powersetCard.ofFinEmbEquiv.symm J) *
        ιMulti R p (b ∘ Set.powersetCard.ofFinEmbEquiv.symm J) =
      ((-1 : R) ^ p.choose 2) •
        ((∏ j ∈ (J : Finset (Fin n)), pairCenter R a b j : Subalgebra.center R _) :
          ExteriorAlgebra R M) := by
  rw [ιMulti_mul_ιMulti_eq_prod_pairCenter]
  congr 2
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  exact prod_orderEmbOfFin _ _ _

/-- The terms of the product `(∑_J c_J a_J) ∧ (∑_J d_J b_J) ∧ (∑ⱼ Pⱼ)ᵐ`: for `p + m = n`,
`a_J ∧ b_{J'} ∧ ∏_{j ∈ T} Pⱼ` vanishes unless `J = J'` and `T` is the complement of `J`. -/
lemma ιMulti_mul_ιMulti_mul_prod_pairCenter {p m : ℕ} (hpm : p + m = n)
    (J J' : Set.powersetCard (Fin n) p) (T : Finset (Fin n)) (hT : T.card = m) :
    ιMulti R p (a ∘ Set.powersetCard.ofFinEmbEquiv.symm J) *
        ιMulti R p (b ∘ Set.powersetCard.ofFinEmbEquiv.symm J') *
          ((∏ j ∈ T, pairCenter R a b j : Subalgebra.center R _) : ExteriorAlgebra R M) =
      if J = J' ∧ T = (J : Finset (Fin n))ᶜ then
        ((-1 : R) ^ p.choose 2) •
          ((∏ j, pairCenter R a b j : Subalgebra.center R _) : ExteriorAlgebra R M)
      else 0 := by
  classical
  have hcompl : ∀ J₀ : Set.powersetCard (Fin n) p, Disjoint (J₀ : Finset (Fin n)) T →
      T = (J₀ : Finset (Fin n))ᶜ := by
    intro J₀ hd
    refine Finset.eq_of_subset_of_card_le (fun j hj ↦ Finset.mem_compl.2 fun hj' ↦
      Finset.disjoint_left.1 hd hj' hj) ?_
    rw [Finset.card_compl, Set.powersetCard.card_eq, Fintype.card_fin, hT]
    omega
  by_cases h1 : Disjoint (J : Finset (Fin n)) T
  · have hTJ := hcompl J h1
    by_cases h2 : Disjoint (J' : Finset (Fin n)) T
    · have hJJ : J = J' := by
        have hTJ' := hcompl J' h2
        apply Subtype.ext
        rw [← compl_compl (J : Finset (Fin n)), ← hTJ, hTJ', compl_compl]
      subst hJJ
      rw [ite_eq_left ⟨rfl, hTJ⟩, ιMulti_mul_ιMulti_powersetCard, smul_mul_assoc,
        ← Subalgebra.coe_mul,
        hTJ, Finset.prod_mul_prod_compl]
    · obtain ⟨j, hj, hjT⟩ := Finset.not_disjoint_iff.1 h2
      obtain ⟨i, rfl⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem J' j).2 hj
      rw [ite_eq_right (by rintro ⟨rfl, -⟩; exact h2 h1)]
      exact mul_ιMulti_mul_prod_pairCenter_right a b _ _ T i hjT
  · obtain ⟨j, hj, hjT⟩ := Finset.not_disjoint_iff.1 h1
    obtain ⟨i, rfl⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem J j).2 hj
    rw [ite_eq_right fun h ↦ h1 (by rw [h.2]; exact disjoint_compl_right)]
    exact ιMulti_mul_mul_prod_pairCenter_left a b _ _ T i hjT

/-- **The main identity**: for `p + m = n`,
`(∑_J c_J a_J) ∧ (∑_J d_J b_J) ∧ (∑ⱼ Pⱼ)ᵐ = m! (-1)^(p choose 2) (∑_J c_J d_J) ∏ⱼ Pⱼ`. -/
theorem sum_mul_sum_mul_pow_sum_pairCenter {p m : ℕ} (hpm : p + m = n)
    (c d : Set.powersetCard (Fin n) p → R) :
    (∑ J, c J • ιMulti R p (a ∘ Set.powersetCard.ofFinEmbEquiv.symm J)) *
        (∑ J, d J • ιMulti R p (b ∘ Set.powersetCard.ofFinEmbEquiv.symm J)) *
          (((∑ j, pairCenter R a b j) ^ m : Subalgebra.center R _) : ExteriorAlgebra R M) =
      ((m.factorial : R) * (-1) ^ p.choose 2 * ∑ J, c J * d J) •
        ((∏ j, pairCenter R a b j : Subalgebra.center R _) : ExteriorAlgebra R M) := by
  classical
  set top := ((∏ j, pairCenter R a b j : Subalgebra.center R _) : ExteriorAlgebra R M)
  have hcard : ∀ J : Set.powersetCard (Fin n) p,
      (J : Finset (Fin n))ᶜ ∈ Finset.univ.powersetCard m := by
    intro J
    rw [Finset.mem_powersetCard, Finset.card_compl, Set.powersetCard.card_eq, Fintype.card_fin]
    exact ⟨Finset.subset_univ _, by omega⟩
  have hQ : ∀ J J' : Set.powersetCard (Fin n) p,
      ιMulti R p (a ∘ Set.powersetCard.ofFinEmbEquiv.symm J) *
        ιMulti R p (b ∘ Set.powersetCard.ofFinEmbEquiv.symm J') *
          (((∑ j, pairCenter R a b j) ^ m : Subalgebra.center R _) : ExteriorAlgebra R M) =
        if J = J' then ((m.factorial : R) * (-1) ^ p.choose 2) • top else 0 := by
    intro J J'
    rw [sum_pairCenter_pow, AddSubmonoidClass.coe_nsmul, AddSubmonoidClass.coe_finsetSum,
      mul_smul_comm, Finset.mul_sum, Finset.sum_congr rfl fun T hT ↦
        ιMulti_mul_ιMulti_mul_prod_pairCenter a b hpm J J' T (Finset.mem_powersetCard.1 hT).2]
    by_cases hJ : J = J'
    · rw [ite_eq_left hJ,
        Finset.sum_eq_single_of_mem _ (hcard J) fun T _ hT ↦ ite_eq_right fun h ↦ hT h.2,
        ite_eq_left ⟨hJ, rfl⟩, ← Nat.cast_smul_eq_nsmul R, smul_smul]
    · rw [ite_eq_right hJ, Finset.sum_eq_zero fun T _ ↦ ite_eq_right fun h ↦ hJ h.1, smul_zero]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  simp_rw [Finset.sum_mul, smul_mul_smul_comm, smul_mul_assoc, hQ, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun J _ ↦ by ring

end Pairs

end ExteriorAlgebra
