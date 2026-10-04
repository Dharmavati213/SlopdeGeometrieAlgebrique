/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Semistable.IntegerMatrix
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Numerical types

The special fibre `∑ mᵢ Cᵢ` of a proper regular model of a smooth curve over a discrete valuation
ring is recorded by its *numerical type* (Stacks, Section 0C6Y): multiplicities `mᵢ > 0`, the
intersection matrix `aᵢⱼ = Cᵢ · Cⱼ`, the weights `wᵢ = [H⁰(Cᵢ, 𝒪) : k]` and the genera
`gᵢ = dim H¹(Cᵢ, 𝒪) / wᵢ` of the components. The semistable reduction theorem uses a bound on the
`ℓ`-torsion of its Picard group `Coker(aᵢⱼ / wᵢ)` (Stacks, Tag 0C9X).

**Deviation.** We only treat numerical types with all weights `wᵢ = 1`: this is the case of an
algebraically closed residue field `k` (then `H⁰(Cᵢ, 𝒪) = k` for every integral proper curve `Cᵢ`
over `k`), which is the case of `SemistableReductionStatement`. With `wᵢ = 1` the Picard group is
`Coker(A)` (Stacks, Tag 0C7H).

## Main definitions

* `AlgebraicGeometry.NumericalType ι`: a numerical type with index set `ι` and weights `1` (Stacks,
  Definition 0C6Z with `wᵢ = 1`);
* `NumericalType.genus`: `g = 1 + ∑ mᵢ (gᵢ - 1 - aᵢᵢ / 2)`, an integer (Stacks, Tag 0C71);
* `NumericalType.topGenus`: `g_top = 1 - n + e` (Stacks, Tag 0C79), nonnegative (Tag 0C78);
* `NumericalType.Pic`: `Coker(A)` (Stacks, Definition 0C7H with `wᵢ = 1`);
* `NumericalType.IsMinusOneIndex`, `IsMinusTwoIndex`, `IsMinimal` (Stacks, Definitions 0C76, 0C7E,
  0C7A).

## Main results

* `NumericalType.card_torsionBy_pic_le`: `|Pic(T)[ℓ]| ≤ ℓ^{g_top}` for a prime `ℓ` dividing no
  `mᵢ` and no nonzero `aᵢⱼ` (Stacks, Tag 0C6X applied to `T`, as in the proof of Tag 0C9X);
* `NumericalType.diag_neg` (Stacks, Tag 0C74), `diag_eq_zero_of_card_eq_one` (part of Tag 0C73);
* `NumericalType.isMinusOneIndex_of_contrib_neg` (Tag 0C75),
  `NumericalType.isMinusTwoIndex_of_contrib_eq_zero` (Tag 0C7D), `NumericalType.one_le_genus`
  (Tag 0C7B);
* `NumericalType.mul_le_of_pos` (Stacks, Tag 0C9U) and the bounds of Stacks, Tag 0C9V
  (`card_nonMinusTwo_le`, `g_lt_genus`, `mul_neg_diag_le`, `mul_le_six_mul`).

## References

* [Stacks Project, Section 0C6Y (Numerical types), Section 0C7G (Picard group of a numerical
  type), Section 0C9T (Bounding invariants)](https://stacks.math.columbia.edu/tag/0C6Y)
-/

namespace AlgebraicGeometry

open Matrix Finset

/-- A *numerical type* with all weights equal to `1` (Stacks, Definition 0C6Z with `wᵢ = 1`):
multiplicities `mᵢ > 0`, genera `gᵢ ≥ 0` and a symmetric integer matrix `A = (aᵢⱼ)` with `aᵢⱼ ≥ 0`
for `i ≠ j`, connected (no proper nonempty `I` with `aᵢⱼ = 0` for all `i ∈ I`, `j ∉ I`), with
`∑ⱼ aᵢⱼ mⱼ = 0` for all `i`. Stacks also requires `n ≥ 1`; here `Nonempty ι` is assumed where it is
needed. -/
structure NumericalType (ι : Type*) [Fintype ι] where
  /-- The multiplicities `mᵢ` of the components. -/
  m : ι → ℤ
  /-- The intersection matrix `aᵢⱼ`. -/
  a : Matrix ι ι ℤ
  /-- The genera `gᵢ` of the components. -/
  g : ι → ℤ
  m_pos : ∀ i, 0 < m i
  g_nonneg : ∀ i, 0 ≤ g i
  isSymm : a.IsSymm
  nonneg : ∀ i j, i ≠ j → 0 ≤ a i j
  connected : ∀ I : Set ι, I.Nonempty → I ≠ Set.univ → ∃ i ∈ I, ∃ j ∉ I, a i j ≠ 0
  mulVec_eq_zero : a *ᵥ m = 0

namespace NumericalType

variable {ι : Type*} [Fintype ι] (T : NumericalType ι)

lemma a_symm (i j : ι) : T.a i j = T.a j i := T.isSymm.apply j i

lemma sum_mul_eq_zero (i : ι) : ∑ j, T.a i j * T.m j = 0 := by
  simpa [mulVec, dotProduct] using congrFun T.mulVec_eq_zero i

/-- `aᵢᵢ mᵢ = -∑_{j ≠ i} aᵢⱼ mⱼ`. -/
lemma diag_mul_eq [DecidableEq ι] (i : ι) :
    T.a i i * T.m i = -∑ j ∈ univ.erase i, T.a i j * T.m j := by
  have h := T.sum_mul_eq_zero i
  rw [← Finset.add_sum_erase _ _ (mem_univ i)] at h
  linarith

lemma sum_erase_nonneg [DecidableEq ι] (i : ι) : 0 ≤ ∑ j ∈ univ.erase i, T.a i j * T.m j :=
  Finset.sum_nonneg fun j hj ↦
    mul_nonneg (T.nonneg i j (Finset.ne_of_mem_erase hj).symm) (T.m_pos j).le

section Parity

/-- `∑ᵢ aᵢᵢ mᵢ² = -2 ∑_{i < j} aᵢⱼ mᵢ mⱼ` for any linear order on `ι`. -/
private lemma sum_diag_sq [LinearOrder ι] :
    ∑ i, T.a i i * T.m i ^ 2 =
      -(2 * ∑ i, ∑ j, if i < j then T.a i j * T.m i * T.m j else 0) := by
  classical
  -- `∑ᵢ mᵢ (∑ⱼ aᵢⱼ mⱼ) = 0`
  have h0 : ∑ i, ∑ j, T.a i j * T.m i * T.m j = 0 := by
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have := T.sum_mul_eq_zero i
    calc ∑ j, T.a i j * T.m i * T.m j = T.m i * ∑ j, T.a i j * T.m j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = 0 := by rw [this, mul_zero]
  have hsplit : ∀ i j, T.a i j * T.m i * T.m j =
      (if i < j then T.a i j * T.m i * T.m j else 0) +
      (if j < i then T.a i j * T.m i * T.m j else 0) +
      (if i = j then T.a i j * T.m i * T.m j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.not_gt, h.ne]
    · simp only [lt_self_iff_false, ↓reduceIte, zero_add]
    · simp [h, h.not_gt, h.ne']
  have hlow : ∑ i, ∑ j, (if j < i then T.a i j * T.m i * T.m j else 0) =
      ∑ i, ∑ j, (if i < j then T.a i j * T.m i * T.m j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs
    · rw [T.a_symm]; ring
    · rfl
  have hdiag : ∑ i, ∑ j, (if i = j then T.a i j * T.m i * T.m j else 0) =
      ∑ i, T.a i i * T.m i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_ite_eq]
    simp only [mem_univ, ↓reduceIte]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hsplit i j] at h0
  simp only [Finset.sum_add_distrib] at h0
  rw [hlow, hdiag] at h0
  linarith

/-- Stacks, Tag 0C71: `∑ᵢ aᵢᵢ mᵢ` is even, so that the genus is an integer. -/
theorem even_sum_diag_mul : Even (∑ i, T.a i i * T.m i) := by
  classical
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have h := T.sum_diag_sq
  have heven : ∀ i, Even (T.a i i * T.m i ^ 2 - T.a i i * T.m i) := fun i ↦ by
    have : T.a i i * T.m i ^ 2 - T.a i i * T.m i = T.a i i * (T.m i * (T.m i - 1)) := by ring
    rw [this]
    exact (Int.even_mul_pred_self (T.m i)).mul_left _
  have hsum : Even (∑ i, (T.a i i * T.m i ^ 2 - T.a i i * T.m i)) :=
    Finset.even_sum _ fun i _ ↦ heven i
  rw [Finset.sum_sub_distrib, h] at hsum
  have h2 : Even (-(2 * ∑ i, ∑ j, if i < j then T.a i j * T.m i * T.m j else 0)) :=
    (even_two_mul _).neg
  have := h2.sub hsum
  simpa using this

end Parity

/-- The genus `g = 1 + ∑ mᵢ (gᵢ - 1 - aᵢᵢ / 2)` of a numerical type (Stacks, Definition 0C72); it
is an integer by `even_sum_diag_mul`, see `two_mul_genus`. -/
def genus : ℤ := 1 + ∑ i, T.m i * (T.g i - 1) - (∑ i, T.a i i * T.m i) / 2

/-- Twice the contribution `mᵢ (gᵢ - 1 - aᵢᵢ / 2)` of the index `i` to the genus. -/
def contrib (i : ι) : ℤ := T.m i * (2 * (T.g i - 1) - T.a i i)

theorem two_mul_genus : 2 * T.genus = 2 + ∑ i, T.contrib i := by
  obtain ⟨k, hk⟩ := T.even_sum_diag_mul
  have h2 : (∑ i, T.a i i * T.m i) / 2 = k := by omega
  simp only [genus, contrib, h2]
  have : ∑ i, T.m i * (2 * (T.g i - 1) - T.a i i) =
      2 * ∑ i, T.m i * (T.g i - 1) - ∑ i, T.a i i * T.m i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [this, hk]
  ring

/-- Stacks, Tag 0C73 (first part): if `n = 1`, then `a₁₁ = 0`. -/
theorem diag_eq_zero_of_card_eq_one (h : Fintype.card ι = 1) (i : ι) : T.a i i = 0 := by
  classical
  have hsub : ∀ j, j = i := fun j ↦ Fintype.card_le_one_iff.mp h.le j i
  have := T.sum_mul_eq_zero i
  rw [Finset.sum_eq_single i (fun j _ hj ↦ absurd (hsub j) hj) (by simp)] at this
  exact (mul_eq_zero.mp this).resolve_right (T.m_pos i).ne'

/-- Stacks, Tag 0C74: if `n > 1`, all diagonal entries `aᵢᵢ` are negative. -/
theorem diag_neg (h : 1 < Fintype.card ι) (i : ι) : T.a i i < 0 := by
  classical
  have hdm := T.diag_mul_eq i
  -- some `j ≠ i` has `aᵢⱼ > 0`, by connectedness applied to `{i}`
  obtain ⟨i', hi', j, hj, hij⟩ := T.connected {i} (Set.singleton_nonempty i) (by
    intro hu
    have : (Set.univ : Set ι).Subsingleton := hu ▸ Set.subsingleton_singleton
    have := Fintype.card_le_one_iff_subsingleton.mpr
      ⟨fun x y ↦ this (Set.mem_univ x) (Set.mem_univ y)⟩
    omega)
  rw [Set.mem_singleton_iff] at hi'
  subst hi'
  have hji : j ≠ i' := hj
  have hpos : 0 < T.a i' j * T.m j :=
    mul_pos (lt_of_le_of_ne (T.nonneg i' j hji.symm) (Ne.symm hij)) (T.m_pos j)
  have hsum : 0 < ∑ k ∈ univ.erase i', T.a i' k * T.m k :=
    lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun k ↦ T.a i' k * T.m k)
      (fun k hk ↦ mul_nonneg (T.nonneg i' k (Finset.ne_of_mem_erase hk).symm) (T.m_pos k).le)
      (Finset.mem_erase.mpr ⟨hji, mem_univ j⟩))
  have : T.a i' i' * T.m i' < 0 := by linarith
  exact neg_of_mul_neg_left this (T.m_pos i').le

/-- `i` is a *`(-1)`-index* (Stacks, Definition 0C76 with `wᵢ = 1`): `gᵢ = 0` and `aᵢᵢ = -1`. -/
def IsMinusOneIndex (i : ι) : Prop := T.g i = 0 ∧ T.a i i = -1

/-- `i` is a *`(-2)`-index* (Stacks, Definition 0C7E with `wᵢ = 1`): `gᵢ = 0` and `aᵢᵢ = -2`. -/
def IsMinusTwoIndex (i : ι) : Prop := T.g i = 0 ∧ T.a i i = -2

instance (i : ι) : Decidable (T.IsMinusOneIndex i) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (i : ι) : Decidable (T.IsMinusTwoIndex i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A numerical type is *minimal* if it has no `(-1)`-index (Stacks, Definition 0C7A). -/
def IsMinimal : Prop := ∀ i, ¬ T.IsMinusOneIndex i

/-- Stacks, Tag 0C75: if `n > 1` and the contribution of `i` to the genus is negative, then `i` is
a `(-1)`-index. -/
theorem isMinusOneIndex_of_contrib_neg (h : 1 < Fintype.card ι) {i : ι} (hi : T.contrib i < 0) :
    T.IsMinusOneIndex i := by
  have ha := T.diag_neg h i
  have hm := T.m_pos i
  have hg := T.g_nonneg i
  have : 2 * (T.g i - 1) - T.a i i < 0 := by
    by_contra hc
    exact absurd hi (not_lt.mpr (mul_nonneg hm.le (not_lt.mp hc)))
  exact ⟨by omega, by omega⟩

/-- Stacks, Tag 0C7D: if `n > 1` and the contribution of `i` to the genus is zero, then `i` is a
`(-2)`-index. -/
theorem isMinusTwoIndex_of_contrib_eq_zero (h : 1 < Fintype.card ι) {i : ι}
    (hi : T.contrib i = 0) : T.IsMinusTwoIndex i := by
  have ha := T.diag_neg h i
  have hm := T.m_pos i
  have hg := T.g_nonneg i
  have : 2 * (T.g i - 1) - T.a i i = 0 :=
    (mul_eq_zero.mp hi).resolve_left hm.ne'
  exact ⟨by omega, by omega⟩

lemma contrib_nonneg (hT : T.IsMinimal) (h : 1 < Fintype.card ι) (i : ι) : 0 ≤ T.contrib i :=
  not_lt.mp fun hi ↦ hT i (T.isMinusOneIndex_of_contrib_neg h hi)

lemma one_le_contrib (hT : T.IsMinimal) (h : 1 < Fintype.card ι) {i : ι}
    (hi : ¬ T.IsMinusTwoIndex i) : 1 ≤ T.contrib i := by
  rcases (T.contrib_nonneg hT h i).lt_or_eq with h' | h'
  · exact h'
  · exact absurd (T.isMinusTwoIndex_of_contrib_eq_zero h h'.symm) hi

/-- Stacks, Tag 0C7B: a minimal numerical type with `n > 1` has genus `≥ 1`. -/
theorem one_le_genus (hT : T.IsMinimal) (h : 1 < Fintype.card ι) : 1 ≤ T.genus := by
  have h2 := T.two_mul_genus
  have : 0 ≤ ∑ i, T.contrib i := Finset.sum_nonneg fun i _ ↦ T.contrib_nonneg hT h i
  omega

/-- Stacks, Tag 0C9U (with `wᵢ = 1`): if `aᵢⱼ > 0` for some `i ≠ j`, then
`mᵢ aᵢⱼ ≤ mⱼ |aⱼⱼ|` and `mᵢ ≤ mⱼ |aⱼⱼ|`. -/
theorem mul_le_of_pos {i j : ι} (hij : i ≠ j) (ha : 0 < T.a i j) :
    T.m i * T.a i j ≤ T.m j * -T.a j j ∧ T.m i ≤ T.m j * -T.a j j := by
  classical
  have hdm := T.diag_mul_eq j
  have hle : T.a j i * T.m i ≤ ∑ k ∈ univ.erase j, T.a j k * T.m k :=
    Finset.single_le_sum (f := fun k ↦ T.a j k * T.m k)
      (fun k hk ↦ mul_nonneg (T.nonneg j k (Finset.ne_of_mem_erase hk).symm) (T.m_pos k).le)
      (Finset.mem_erase.mpr ⟨hij, mem_univ i⟩)
  rw [← T.a_symm] at hle
  have h1 : T.m i * T.a i j ≤ T.m j * -T.a j j := by linarith
  refine ⟨h1, le_trans ?_ h1⟩
  have hm := T.m_pos i
  nlinarith

section Bounds

/-- The set `J` of indices which are not `(-2)`-indices (Stacks, Tag 0C9V). -/
noncomputable def nonMinusTwo : Finset ι := by
  classical exact univ.filter fun i ↦ ¬ T.IsMinusTwoIndex i

lemma mem_nonMinusTwo {i : ι} : i ∈ T.nonMinusTwo ↔ ¬ T.IsMinusTwoIndex i := by
  classical
  simp [nonMinusTwo]

variable (hT : T.IsMinimal) (h : 1 < Fintype.card ι)
include hT h

lemma contrib_le (i : ι) : T.contrib i ≤ 2 * T.genus - 2 := by
  classical
  have h2 := T.two_mul_genus
  have := Finset.single_le_sum (f := T.contrib) (fun j _ ↦ T.contrib_nonneg hT h j) (mem_univ i)
  omega

/-- Stacks, Tag 0C9V (1): a minimal numerical type with `n > 1` has at most `2g - 2`
non-`(-2)`-indices. -/
theorem card_nonMinusTwo_le : (T.nonMinusTwo.card : ℤ) ≤ 2 * T.genus - 2 := by
  classical
  have h2 := T.two_mul_genus
  have h1 : (T.nonMinusTwo.card : ℤ) ≤ ∑ i ∈ T.nonMinusTwo, T.contrib i := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact Finset.sum_le_sum fun i hi ↦ T.one_le_contrib hT h (T.mem_nonMinusTwo.mp hi)
  have h3 : ∑ i ∈ T.nonMinusTwo, T.contrib i ≤ ∑ i, T.contrib i :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
      fun i _ _ ↦ T.contrib_nonneg hT h i
  omega

/-- Stacks, Tag 0C9V (2): for a minimal numerical type with `n > 1` and genus `g ≥ 2`, a
non-`(-2)`-index `j` has `gⱼ < g`. -/
theorem g_lt_genus (hg : 2 ≤ T.genus) (j : ι) : T.g j < T.genus := by
  have hc := T.contrib_le hT h j
  have ha := T.diag_neg h j
  have hm := T.m_pos j
  rcases (T.g_nonneg j).eq_or_lt with h0 | hpos
  · omega
  · -- `contrib j > mⱼ (2 gⱼ - 2) ≥ 2 gⱼ - 2`
    have h1 : T.m j * (2 * (T.g j - 1)) < T.contrib j := by
      simp only [contrib]
      nlinarith
    have h2 : 2 * (T.g j - 1) ≤ T.m j * (2 * (T.g j - 1)) := by
      have : 0 ≤ 2 * (T.g j - 1) := by omega
      nlinarith
    omega

/-- Stacks, Tag 0C9V (3): for a minimal numerical type with `n > 1`, a non-`(-2)`-index `j` has
`mⱼ |aⱼⱼ| ≤ 6g - 6`. -/
theorem mul_neg_diag_le {j : ι} (hj : ¬ T.IsMinusTwoIndex j) :
    T.m j * -T.a j j ≤ 6 * T.genus - 6 := by
  have hc := T.contrib_le hT h j
  have hg1 := T.one_le_genus hT h
  have ha := T.diag_neg h j
  have hm := T.m_pos j
  have hg := T.g_nonneg j
  rcases hg.eq_or_lt with h0 | hpos
  · -- `gⱼ = 0` and `aⱼⱼ = -k` with `k ≥ 3`
    have hk : T.a j j ≤ -3 := by
      have h1 : T.a j j ≠ -1 := fun h1 ↦ hT j ⟨h0.symm, h1⟩
      have h2 : T.a j j ≠ -2 := fun h2 ↦ hj ⟨h0.symm, h2⟩
      omega
    have : T.contrib j = T.m j * (-2 - T.a j j) := by
      simp only [contrib, ← h0]; ring
    -- `mⱼ k ≤ 3 mⱼ (k - 2)`
    nlinarith
  · have : T.m j * -T.a j j ≤ T.contrib j := by
      simp only [contrib]
      nlinarith
    omega

/-- Stacks, Tag 0C9V (4): for a minimal numerical type with `n > 1`, a non-`(-2)`-index `j` and any
index `i`, `mᵢ aᵢⱼ ≤ 6g - 6`. -/
theorem mul_le_six_mul {j : ι} (hj : ¬ T.IsMinusTwoIndex j) (i : ι) :
    T.m i * T.a i j ≤ 6 * T.genus - 6 := by
  have h3 := T.mul_neg_diag_le hT h hj
  by_cases hij : i = j
  · subst hij
    have := T.diag_neg h i
    have := T.m_pos i
    nlinarith
  rcases (T.nonneg i j hij).lt_or_eq with hpos | h0
  · exact (T.mul_le_of_pos hij hpos).1.trans h3
  · rw [← h0, mul_zero]
    have := T.m_pos j
    have := T.diag_neg h j
    nlinarith

end Bounds

section Picard

variable [LinearOrder ι]

/-- The topological genus `g_top = 1 - n + e` of a numerical type, `e` the number of pairs
`i < j` with `aᵢⱼ ≠ 0` (Stacks, Definition 0C79). -/
def topGenus : ℤ := 1 - Fintype.card ι + T.a.edgeFinset.card

/-- The topological genus does not depend on the order of the indices: it is `Matrix.topGenus` of
the intersection matrix. -/
lemma topGenus_eq_matrix_topGenus [DecidableEq ι] : T.topGenus = T.a.topGenus :=
  (Matrix.topGenus_eq T.isSymm).symm

/-- Stacks, Tag 0C78: the topological genus is nonnegative (a connected graph on `n ≥ 1` vertices
has at least `n - 1` edges). Here deduced from the bound `dim ker A + n ≤ 2 + e` over `ℚ`
(`Matrix.finrank_ker_mulVecLin_add_card_le`) and `m ∈ ker A`. -/
theorem topGenus_nonneg : 0 ≤ T.topGenus := by
  classical
  set Aq := T.a.map (Int.castRingHom ℚ)
  have hAq : Aq.IsSymm := T.isSymm.map _
  have hm : ∀ i, ((T.m i : ℚ)) ≠ 0 := fun i ↦ by exact_mod_cast (T.m_pos i).ne'
  have hne : ∀ i j, Aq i j ≠ 0 ↔ T.a i j ≠ 0 := fun i j ↦ by simp [Aq]
  have hAqm : Aq *ᵥ (fun i ↦ (T.m i : ℚ)) = 0 := by
    ext i
    have := congrFun T.mulVec_eq_zero i
    simp only [mulVec, dotProduct, Pi.zero_apply] at this ⊢
    simp only [Aq, map_apply, eq_intCast]
    exact_mod_cast this
  have hconn : ∀ I : Set ι, I.Nonempty → I ≠ Set.univ → ∃ i ∈ I, ∃ j ∉ I, Aq i j ≠ 0 :=
    fun I hI hI' ↦ by
      obtain ⟨i, hi, j, hj, hij⟩ := T.connected I hI hI'
      exact ⟨i, hi, j, hj, (hne i j).mpr hij⟩
  have hedge : Aq.edgeFinset = T.a.edgeFinset := by
    ext p
    simp only [edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and, hne]
  have hker := finrank_ker_mulVecLin_add_card_le Aq hAq _ hm hAqm hconn
  rw [hedge] at hker
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp only [topGenus, Fintype.card_eq_zero, Nat.cast_zero, sub_zero]
    positivity
  have hpos : 0 < Module.finrank ℚ (LinearMap.ker Aq.mulVecLin) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨fun i ↦ (T.m i : ℚ), by rw [LinearMap.mem_ker, mulVecLin_apply, hAqm]⟩, ?_⟩
    intro h0
    exact hm i₀ (congrFun (congrArg Subtype.val h0) i₀)
  simp only [topGenus]
  omega

/-- The Picard group of a numerical type with weights `1`: `Coker(A) = ℤⁿ / A ℤⁿ` (Stacks,
Definition 0C7H with `wᵢ = 1`). -/
abbrev Pic : Type _ := (ι → ℤ) ⧸ LinearMap.range T.a.mulVecLin

/-- Stacks, Tag 0C6X for a numerical type (as used in the proof of Tag 0C9X): if the prime `ℓ`
divides none of the multiplicities `mᵢ` and none of the nonzero `aᵢⱼ`, then
`|Pic(T)[ℓ]| ≤ ℓ^{g_top}`, i.e. `dim_{𝔽_ℓ} Pic(T)[ℓ] ≤ g_top`. -/
theorem card_torsionBy_pic_le [Nonempty ι] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓm : ∀ i, ¬ (ℓ : ℤ) ∣ T.m i) (hℓa : ∀ i j, T.a i j ≠ 0 → ¬ (ℓ : ℤ) ∣ T.a i j) :
    Nat.card (Submodule.torsionBy ℤ T.Pic (ℓ : ℤ)) ≤ ℓ ^ T.topGenus.toNat := by
  have h := card_torsionBy_cokernel_mul_pow_le T.a T.isSymm T.m T.mulVec_eq_zero T.connected ℓ
    hℓm hℓa
  have htop := T.topGenus_nonneg
  have he : 1 + T.a.edgeFinset.card = T.topGenus.toNat + Fintype.card ι := by
    simp only [topGenus] at htop ⊢
    omega
  rw [he, pow_add] at h
  exact Nat.le_of_mul_le_mul_right h (pow_pos (Fact.out : ℓ.Prime).pos _)

end Picard

end NumericalType

end AlgebraicGeometry
