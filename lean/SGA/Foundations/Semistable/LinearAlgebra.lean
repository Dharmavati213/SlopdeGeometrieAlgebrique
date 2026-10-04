/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Linear algebra of intersection matrices of fibres

The intersection matrix `(Cᵢ · Cⱼ)` of the components of a fibre of a regular arithmetic surface
is symmetric, nonnegative off the diagonal, connected, and kills the vector of multiplicities
`m = (mᵢ)` of the fibre. Such a matrix is negative semi-definite with kernel `𝕜 m` (Stacks,
Tag 0C5X; "Zariski's lemma", Liu, *Algebraic Geometry and Arithmetic Curves*, 9.1.23). This is the
linear algebra behind the intersection theory on fibres used in the proof of the semistable
reduction theorem (Stacks, Section 55.2).

## Main results

For a symmetric matrix `A` over a linearly ordered field with `A i j ≥ 0` for `i ≠ j`, and a
vector `m` with positive entries and `A m = 0`:

* `Matrix.two_mul_dotProduct_mulVec_eq`: `2 xᵀ A x = - ∑ᵢⱼ aᵢⱼ mᵢ mⱼ (xᵢ/mᵢ - xⱼ/mⱼ)²`;
* `Matrix.dotProduct_mulVec_nonpos`: `xᵀ A x ≤ 0` (Stacks, Tag 0C5X);
* `Matrix.exists_eq_smul_of_dotProduct_mulVec_eq_zero`: if moreover `A` is *connected* (no proper
  nonempty set of indices is closed under `aᵢⱼ ≠ 0`), then `xᵀ A x = 0` only for multiples
  `x = q m` (Stacks, Tag 0C5X);
* `Matrix.exists_eq_smul_of_mulVec_eq_zero`: under the same hypotheses the kernel of `A` is `𝕜 m`;
* `Matrix.finrank_ker_mulVecLin_add_card_le`: over any field, for `A` symmetric with `A m = 0`,
  `mᵢ ≠ 0` and connected graph, `dim ker A ≤ 2 - n + e` with `e` the number of edges (the core of
  Stacks, Tag 0C6X: applied to `A mod ℓ` it bounds `dim_{𝔽_ℓ} Coker(A)[ℓ]` by `1 - n + e`; the
  passage from `ker (A mod ℓ)` to `Coker(A)[ℓ]` is not done here). The proof factors the weighted
  Laplacian `diag(m) A diag(m) = -Dᵀ W D` through the incidence matrix `D` of the graph instead of
  Stacks' lattice argument (Tags 0C6V, 0C6W);
* `LinearMap.finrank_ker_comp_le`: `dim ker (g ∘ f) ≤ dim ker f + dim ker g`.

## References

* [Stacks Project, Section 55.2 (Linear algebra), Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X)
* [Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Lemma 9.1.23]
-/

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The identity behind Stacks, Tag 0C5X: if `A` is symmetric, `A m = 0` and all `mᵢ ≠ 0`, then
`2 xᵀ A x = - ∑ᵢⱼ aᵢⱼ mᵢ mⱼ (xᵢ/mᵢ - xⱼ/mⱼ)²`. -/
theorem two_mul_dotProduct_mulVec_eq (A : Matrix n n 𝕜) (hA : A.IsSymm) (m : n → 𝕜)
    (hm : ∀ i, m i ≠ 0) (hAm : A *ᵥ m = 0) (x : n → 𝕜) :
    2 * (x ⬝ᵥ (A *ᵥ x)) =
      -∑ i, ∑ j, A i j * m i * m j * (x i / m i - x j / m j) ^ 2 := by
  have hrow : ∀ i, ∑ j, A i j * m j = 0 := fun i ↦ by
    simpa [mulVec, dotProduct] using congrFun hAm i
  have hcol : ∀ j, ∑ i, A i j * m i = 0 := fun j ↦ by
    rw [← hrow j]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hA.apply j i]
  have hterm : ∀ i j, A i j * m i * m j * (x i / m i - x j / m j) ^ 2 =
      (x i ^ 2 / m i) * (A i j * m j) + (x j ^ 2 / m j) * (A i j * m i) -
        2 * (x i * (A i j * x j)) := fun i j ↦ by
    field_simp [hm i, hm j]
    ring
  have hP : ∑ i, ∑ j, (x i ^ 2 / m i) * (A i j * m j) = 0 := by
    simp_rw [← Finset.mul_sum, hrow, mul_zero, Finset.sum_const_zero]
  have hQ : ∑ i, ∑ j, (x j ^ 2 / m j) * (A i j * m i) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hcol, mul_zero, Finset.sum_const_zero]
  have hR : ∑ i, ∑ j, x i * (A i j * x j) = x ⬝ᵥ (A *ᵥ x) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
  calc 2 * (x ⬝ᵥ (A *ᵥ x))
      = -(∑ i, ∑ j, (x i ^ 2 / m i) * (A i j * m j) +
          ∑ i, ∑ j, (x j ^ 2 / m j) * (A i j * m i) -
          2 * ∑ i, ∑ j, x i * (A i j * x j)) := by rw [hP, hQ, hR]; ring
    _ = -∑ i, ∑ j, A i j * m i * m j * (x i / m i - x j / m j) ^ 2 := by
      simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

omit [Fintype n] in
private lemma term_nonneg (A : Matrix n n 𝕜) (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (m : n → 𝕜)
    (hm : ∀ i, 0 < m i) (x : n → 𝕜) (i j : n) :
    0 ≤ A i j * m i * m j * (x i / m i - x j / m j) ^ 2 := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · exact mul_nonneg (mul_nonneg (mul_nonneg (hoff i j hij) (hm i).le) (hm j).le)
      (sq_nonneg _)

/-- Stacks, Tag 0C5X (first half): a symmetric matrix with nonnegative off-diagonal entries that
kills a vector with positive entries is negative semi-definite. -/
theorem dotProduct_mulVec_nonpos (A : Matrix n n 𝕜) (hA : A.IsSymm)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (m : n → 𝕜) (hm : ∀ i, 0 < m i) (hAm : A *ᵥ m = 0)
    (x : n → 𝕜) : x ⬝ᵥ (A *ᵥ x) ≤ 0 := by
  have h := two_mul_dotProduct_mulVec_eq A hA m (fun i ↦ (hm i).ne') hAm x
  have hsum : 0 ≤ ∑ i, ∑ j, A i j * m i * m j * (x i / m i - x j / m j) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ term_nonneg A hoff m hm x i j
  linarith

/-- Stacks, Tag 0C5X (second half): if moreover `A` is connected (every proper nonempty set `I`
of indices has `aᵢⱼ ≠ 0` for some `i ∈ I`, `j ∉ I`), then `xᵀ A x = 0` only for the multiples
`x = q m` of `m`. -/
theorem exists_eq_smul_of_dotProduct_mulVec_eq_zero (A : Matrix n n 𝕜) (hA : A.IsSymm)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (m : n → 𝕜) (hm : ∀ i, 0 < m i) (hAm : A *ᵥ m = 0)
    (hconn : ∀ I : Set n, I.Nonempty → I ≠ Set.univ → ∃ i ∈ I, ∃ j ∉ I, A i j ≠ 0)
    (x : n → 𝕜) (hx : x ⬝ᵥ (A *ᵥ x) = 0) : ∃ q : 𝕜, x = q • m := by
  classical
  have h := two_mul_dotProduct_mulVec_eq A hA m (fun i ↦ (hm i).ne') hAm x
  rw [hx, mul_zero, zero_eq_neg] at h
  have hzero : ∀ i j, A i j * m i * m j * (x i / m i - x j / m j) ^ 2 = 0 := by
    intro i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      term_nonneg A hoff m hm x i j).mp h i (Finset.mem_univ i)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ term_nonneg A hoff m hm x i j).mp h1 j
      (Finset.mem_univ j)
  -- the ratios `xᵢ/mᵢ` agree along every edge `aᵢⱼ ≠ 0`
  have hedge : ∀ i j, A i j ≠ 0 → x i / m i = x j / m j := by
    intro i j hij
    have := hzero i j
    have hmi := (hm i).ne'
    have hmj := (hm j).ne'
    simp only [mul_eq_zero, hij, hmi, hmj, false_or, pow_eq_zero_iff, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true] at this
    exact sub_eq_zero.mp this
  rcases isEmpty_or_nonempty n with hn | hne
  · exact ⟨0, funext fun i ↦ (IsEmpty.false i).elim⟩
  obtain ⟨i₀⟩ := hne
  refine ⟨x i₀ / m i₀, funext fun i ↦ ?_⟩
  -- the set of indices with the same ratio as `i₀` is everything
  set I : Set n := {i | x i / m i = x i₀ / m i₀}
  have hI : I = Set.univ := by
    by_contra hne
    obtain ⟨i, hi, j, hj, hij⟩ := hconn I ⟨i₀, rfl⟩ hne
    exact hj ((hedge i j hij).symm.trans hi)
  have hi : x i / m i = x i₀ / m i₀ := by
    have : i ∈ I := hI ▸ Set.mem_univ i
    exact this
  rw [Pi.smul_apply, smul_eq_mul, ← hi, div_mul_cancel₀ _ (hm i).ne']

/-- Under the hypotheses of `exists_eq_smul_of_dotProduct_mulVec_eq_zero`, the kernel of `A` is
the line `𝕜 m` (Stacks, Tag 0C5X). -/
theorem exists_eq_smul_of_mulVec_eq_zero (A : Matrix n n 𝕜) (hA : A.IsSymm)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (m : n → 𝕜) (hm : ∀ i, 0 < m i) (hAm : A *ᵥ m = 0)
    (hconn : ∀ I : Set n, I.Nonempty → I ≠ Set.univ → ∃ i ∈ I, ∃ j ∉ I, A i j ≠ 0)
    (x : n → 𝕜) (hx : A *ᵥ x = 0) : ∃ q : 𝕜, x = q • m :=
  exists_eq_smul_of_dotProduct_mulVec_eq_zero A hA hoff m hm hAm hconn x
    (by rw [hx, dotProduct_zero])

end Matrix

section Kernel

open Module

/-- The dimension of the kernel of a composite of linear maps is at most the sum of the
dimensions of the kernels. -/
theorem _root_.LinearMap.finrank_ker_comp_le {K V W U : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    [FiniteDimensional K V] [FiniteDimensional K W] (g : W →ₗ[K] U) (f : V →ₗ[K] W) :
    finrank K (LinearMap.ker (g ∘ₗ f)) ≤
      finrank K (LinearMap.ker f) + finrank K (LinearMap.ker g) := by
  -- `f` maps `ker (g ∘ f)` to `ker g`, with kernel `ker f`
  let f' : LinearMap.ker (g ∘ₗ f) →ₗ[K] LinearMap.ker g :=
    (f.domRestrict (LinearMap.ker (g ∘ₗ f))).codRestrict (LinearMap.ker g) fun x ↦ x.2
  have hker : finrank K (LinearMap.ker f') ≤ finrank K (LinearMap.ker f) := by
    let i : LinearMap.ker f' →ₗ[K] LinearMap.ker f :=
      { toFun := fun x ↦ ⟨x.1.1, congrArg Subtype.val (LinearMap.mem_ker.mp x.2)⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    exact LinearMap.finrank_le_finrank_of_injective (f := i) fun x y h ↦ by
      ext
      exact congrArg (fun z : LinearMap.ker f ↦ (z : V)) h
  have := LinearMap.finrank_range_add_finrank_ker f'
  have hrange : finrank K (LinearMap.range f') ≤ finrank K (LinearMap.ker g) :=
    Submodule.finrank_le _
  omega

end Kernel

namespace Matrix

/-- The edges `{(i, j) | i < j, aᵢⱼ ≠ 0}` of the graph of a square matrix. -/
def edgeFinset {R : Type*} [Zero R] [DecidableEq R] {n : Type*} [Fintype n] [LinearOrder n]
    (A : Matrix n n R) : Finset (n × n) :=
  Finset.univ.filter fun p ↦ p.1 < p.2 ∧ A p.1 p.2 ≠ 0

section OffDiag

variable {R : Type*} [Zero R] [DecidableEq R] {n : Type*} [Fintype n] [DecidableEq n]

/-- The ordered pairs `(i, j)`, `i ≠ j`, with `aᵢⱼ ≠ 0`. -/
def offDiagSupport (A : Matrix n n R) : Finset (n × n) :=
  Finset.univ.filter fun p ↦ p.1 ≠ p.2 ∧ A p.1 p.2 ≠ 0

/-- The topological genus `1 - n + e` of the graph of a square matrix, `e` the number of unordered
pairs `{i, j}`, `i ≠ j`, with `aᵢⱼ ≠ 0` (Stacks, Definition 0C79), computed as half the number of
ordered such pairs, so that no order of the indices is needed (meaningful for symmetric `A`; see
`Matrix.card_offDiagSupport_eq_two_mul`). -/
def topGenus (A : Matrix n n R) : ℤ :=
  1 - Fintype.card n + ((A.offDiagSupport.card / 2 : ℕ) : ℤ)

/-- For a symmetric matrix, the ordered pairs `(i, j)`, `i ≠ j`, with `aᵢⱼ ≠ 0` are twice as many
as the edges `i < j`. -/
lemma card_offDiagSupport_eq_two_mul [LinearOrder n] {A : Matrix n n R} (hA : A.IsSymm) :
    A.offDiagSupport.card = 2 * A.edgeFinset.card := by
  have h : A.offDiagSupport =
      A.edgeFinset ∪ A.edgeFinset.map (Equiv.prodComm n n).toEmbedding := by
    ext ⟨i, j⟩
    simp only [offDiagSupport, edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply,
      Prod.swap_prod_mk]
    constructor
    · rintro ⟨hij, ha⟩
      rcases lt_or_gt_of_ne hij with h | h
      · exact Or.inl ⟨h, ha⟩
      · exact Or.inr ⟨h, by rwa [hA.apply i j]⟩
    · rintro (⟨h, ha⟩ | ⟨h, ha⟩)
      · exact ⟨h.ne, ha⟩
      · exact ⟨h.ne', by rwa [hA.apply i j] at ha⟩
  have hd : Disjoint A.edgeFinset (A.edgeFinset.map (Equiv.prodComm n n).toEmbedding) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp only [edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
      Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk] at h1 h2
    exact lt_asymm h1.1 h2.1
  rw [h, Finset.card_union_of_disjoint hd, Finset.card_map]
  ring

/-- For a symmetric matrix, `topGenus A = 1 - n + #{(i, j) | i < j, aᵢⱼ ≠ 0}` for any order. -/
lemma topGenus_eq [LinearOrder n] {A : Matrix n n R} (hA : A.IsSymm) :
    A.topGenus = 1 - Fintype.card n + A.edgeFinset.card := by
  rw [topGenus, card_offDiagSupport_eq_two_mul hA, Nat.mul_div_cancel_left _ two_pos]

end OffDiag

section Laplacian

open Module

variable {F : Type*} [Field F] [DecidableEq F] {n : Type*} [Fintype n] [DecidableEq n]
  [LinearOrder n]

/-- The weighted Laplacian identity behind Stacks, Tag 0C6X: for `A` symmetric with `A m = 0`, and
`wᵢⱼ = mᵢ aᵢⱼ mⱼ`, the sum `∑_{i<j} wᵢⱼ (yᵢ - yⱼ) ([k = i] - [k = j])` over the edges is
`-mₖ (A (m ⊙ y))ₖ`. -/
private lemma laplacian_sum (A : Matrix n n F) (hA : A.IsSymm) (m : n → F) (hAm : A *ᵥ m = 0)
    (y : n → F) (k : n) :
    ∑ p ∈ A.edgeFinset, m p.1 * A p.1 p.2 * m p.2 * (y p.1 - y p.2) *
      ((if k = p.1 then 1 else 0) - (if k = p.2 then 1 else 0)) =
      -(m k * (A *ᵥ fun j ↦ m j * y j) k) := by
  set φ : n × n → F := fun p ↦ m p.1 * A p.1 p.2 * m p.2 * (y p.1 - y p.2) *
    ((if k = p.1 then 1 else 0) - (if k = p.2 then 1 else 0))
  -- extend the sum to all pairs `i < j`
  have h1 : ∑ p ∈ A.edgeFinset, φ p =
      ∑ p ∈ Finset.univ.filter (fun p : n × n ↦ p.1 < p.2), φ p := by
    refine Finset.sum_subset (fun p hp ↦ ?_) (fun p hp hpE ↦ ?_)
    · simp only [edgeFinset, Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.1⟩
    · simp only [edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and, not_and,
        not_not] at hp hpE
      simp [φ, hpE hp]
  have hsym : ∀ i j, A i j = A j i := fun i j ↦ hA.apply j i
  have hrow : ∀ i, ∑ j, A i j * m j = 0 := fun i ↦ by
    simpa [mulVec, dotProduct] using congrFun hAm i
  rw [h1, Finset.sum_filter, Fintype.sum_prod_type]
  -- split `[k = i] - [k = j]`
  have h2 : ∀ i j, (if i < j then φ (i, j) else 0) =
      (if k = i then (if i < j then m i * A i j * m j * (y i - y j) else 0) else 0) -
      (if k = j then (if i < j then m i * A i j * m j * (y i - y j) else 0) else 0) := by
    intro i j
    by_cases hij : i < j
    · by_cases hki : k = i
      · subst hki
        simp [φ, hij, hij.ne]
      · by_cases hkj : k = j
        · subst hkj
          simp [φ, hij, hki]
        · simp [φ, hij, hki, hkj]
    · simp [φ, hij]
  simp_rw [h2, Finset.sum_sub_distrib]
  have e1 : (∑ i, ∑ j, if k = i then (if i < j then m i * A i j * m j * (y i - y j) else 0)
      else 0) = ∑ j, if k < j then m k * A k j * m j * (y k - y j) else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_ite_eq]
    simp
  have e2 : (∑ i, ∑ j, if k = j then (if i < j then m i * A i j * m j * (y i - y j) else 0)
      else 0) = ∑ i, if i < k then m i * A i k * m k * (y i - y k) else 0 := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_ite_eq]
    simp
  rw [e1, e2]
  -- combine the two sums into `∑ⱼ wₖⱼ (yₖ - yⱼ)`
  have h3 : ∀ j, (if k < j then m k * A k j * m j * (y k - y j) else 0) -
      (if j < k then m j * A j k * m k * (y j - y k) else 0) =
      m k * A k j * m j * (y k - y j) := by
    intro j
    rcases lt_trichotomy k j with h | rfl | h
    · simp [h, h.not_gt]
    · simp
    · rw [hsym j k]
      simp [h, h.not_gt]
      ring
  rw [← Finset.sum_sub_distrib]
  simp_rw [h3]
  have h4 : ∑ j, m k * A k j * m j * (y k - y j) =
      m k * y k * ∑ j, A k j * m j - m k * ∑ j, A k j * (m j * y j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [h4, hrow k, mul_zero, zero_sub]
  simp [mulVec, dotProduct]

omit [DecidableEq n] in
/-- Stacks, Tag 0C6X, over a field (the core of the bound on `ℓ`-torsion in `Coker(A)`): let `A`
be a symmetric matrix over a field `F` and `m` a vector with nonzero entries such that `A m = 0`
and the graph of `A` (an edge `{i, j}` for `aᵢⱼ ≠ 0`, `i ≠ j`) is connected. Then
`dim ker A ≤ 2 - n + e`, where `e` is the number of edges. (For an integer matrix as in Tag 0C6X
reduced modulo a prime `ℓ` prime to the `aᵢⱼ` and `mᵢ`, this gives
`dim_{𝔽_ℓ} Coker(A)[ℓ] ≤ 1 - n + e`.) The proof writes `diag(m) A diag(m) = -Dᵀ W D` with `D` the
incidence matrix of the graph and `W` the invertible diagonal matrix of weights `mᵢ aᵢⱼ mⱼ`. -/
theorem finrank_ker_mulVecLin_add_card_le (A : Matrix n n F) (hA : A.IsSymm) (m : n → F)
    (hm : ∀ i, m i ≠ 0) (hAm : A *ᵥ m = 0)
    (hconn : ∀ I : Set n, I.Nonempty → I ≠ Set.univ → ∃ i ∈ I, ∃ j ∉ I, A i j ≠ 0) :
    finrank F (LinearMap.ker A.mulVecLin) + Fintype.card n ≤ 2 + A.edgeFinset.card := by
  classical
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · have := Submodule.finrank_le (LinearMap.ker A.mulVecLin)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_zero] at this
    rw [Fintype.card_eq_zero]
    omega
  let E := A.edgeFinset
  let D : Matrix E n F := fun e k ↦ (if k = e.1.1 then 1 else 0) - (if k = e.1.2 then 1 else 0)
  let b : E → F := fun e ↦ m e.1.1 * A e.1.1 e.1.2 * m e.1.2
  let G : Matrix n E F := Dᵀ * diagonal b
  have hb : ∀ e, b e ≠ 0 := fun e ↦ by
    have he := e.2
    simp only [E, edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact mul_ne_zero (mul_ne_zero (hm _) he.2) (hm _)
  have hD : ∀ y e, (D *ᵥ y) e = y e.1.1 - y e.1.2 := fun y e ↦ by
    simp [D, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
  have hkey : ∀ y, (G * D) *ᵥ y = -(fun k ↦ m k * (A *ᵥ fun j ↦ m j * y j) k) := by
    intro y
    funext k
    rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, Pi.neg_apply,
      ← laplacian_sum A hA m hAm y k]
    simp only [vecMul, dotProduct, mulVec_diagonal, hD]
    rw [← Finset.sum_coe_sort E]
  -- step 1: `ker A` embeds into `ker (G D)` through `x ↦ x / m`
  let ψ : (n → F) →ₗ[F] (n → F) :=
    { toFun := fun x i ↦ (m i)⁻¹ * x i
      map_add' := fun x y ↦ by ext; simp [mul_add]
      map_smul' := fun c x ↦ by ext; simp; ring }
  have hψ : ∀ x ∈ LinearMap.ker A.mulVecLin, ψ x ∈ LinearMap.ker (G * D).mulVecLin := by
    intro x hx
    rw [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
    rw [hkey]
    have : (fun j ↦ m j * ψ x j) = x := by
      funext j
      simp [ψ, ← mul_assoc, mul_inv_cancel₀ (hm j)]
    rw [this, hx]
    funext k
    simp
  have h1 : finrank F (LinearMap.ker A.mulVecLin) ≤
      finrank F (LinearMap.ker (G * D).mulVecLin) := by
    refine LinearMap.finrank_le_finrank_of_injective
      (f := ((ψ.domRestrict _).codRestrict _ fun x ↦ hψ x.1 x.2)) fun x y h ↦ ?_
    ext i
    have := congrFun (congrArg Subtype.val h) i
    simp only [ψ] at this
    exact mul_left_cancel₀ (inv_ne_zero (hm i)) this
  -- step 2: `dim ker (G D) ≤ dim ker D + dim ker G`
  have h2 := LinearMap.finrank_ker_comp_le G.mulVecLin D.mulVecLin
  rw [← mulVecLin_mul] at h2
  -- step 3: `ker D` is the line of constant vectors
  have h3 : finrank F (LinearMap.ker D.mulVecLin) ≤ 1 := by
    have hle : LinearMap.ker D.mulVecLin ≤ F ∙ (fun _ ↦ (1 : F)) := by
      intro x hx
      rw [LinearMap.mem_ker, mulVecLin_apply] at hx
      have hedge : ∀ i j, A i j ≠ 0 → i ≠ j → x i = x j := by
        intro i j hij hne
        rcases lt_or_gt_of_ne hne with h | h
        · have := congrFun hx ⟨(i, j), by simp [E, edgeFinset, h, hij]⟩
          rw [hD] at this
          exact sub_eq_zero.mp this
        · have hji : A j i ≠ 0 := by rwa [hA.apply i j]
          have := congrFun hx ⟨(j, i), by simp [E, edgeFinset, h, hji]⟩
          rw [hD] at this
          exact (sub_eq_zero.mp this).symm
      set I : Set n := {i | x i = x i₀}
      have hI : I = Set.univ := by
        by_contra hne
        obtain ⟨i, hi, j, hj, hij⟩ := hconn I ⟨i₀, rfl⟩ hne
        have hne' : i ≠ j := fun h ↦ hj (h ▸ hi)
        exact hj ((hedge i j hij hne').symm.trans hi)
      rw [Submodule.mem_span_singleton]
      refine ⟨x i₀, funext fun i ↦ ?_⟩
      have : i ∈ I := hI ▸ Set.mem_univ i
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      exact this.symm
    calc finrank F (LinearMap.ker D.mulVecLin) ≤ finrank F (F ∙ (fun _ ↦ (1 : F))) :=
          Submodule.finrank_mono hle
      _ = 1 := finrank_span_singleton fun h ↦ by simpa using congrFun h i₀
      _ ≤ 1 := le_rfl
  -- step 4: `rank G = rank D`
  have h4 : G.rank = D.rank := by
    have hdet : (diagonal b).det ∈ nonZeroDivisors F := by
      rw [det_diagonal]
      exact mem_nonZeroDivisors_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun e _ ↦ hb e)
    rw [rank_mul_eq_left_of_det_mem_nonZeroDivisors _ _ hdet, rank_transpose]
  -- rank-nullity
  have rnD := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  have rnG := LinearMap.finrank_range_add_finrank_ker G.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at rnD rnG
  have hcardE : Fintype.card E = A.edgeFinset.card := Fintype.card_coe _
  change D.rank + _ = _ at rnD
  change G.rank + _ = _ at rnG
  omega

end Laplacian

end Matrix
