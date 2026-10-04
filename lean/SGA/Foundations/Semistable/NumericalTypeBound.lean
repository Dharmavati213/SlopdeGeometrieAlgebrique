/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Semistable.NumericalType
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Bounding the multiplicities of a minimal numerical type

For a minimal numerical type with weights `1`, `n > 1` indices and genus `g ≥ 2`, all the
products `mᵢ |aᵢⱼ|` are bounded by a constant depending only on `g` (Stacks, Tag 0C9W). Hence for a
prime `ℓ` larger than that constant, `dim_{𝔽_ℓ} Pic(T)[ℓ] ≤ g_top` (Stacks, Tag 0C9X). The same
holds in genus `1` when some multiplicity is `1`.

## The argument

Stacks bounds `mᵢ` on the `(-2)`-indices through the classification of the possible
configurations of `(-2)`-indices (Stacks, Section 0C7L). We use a shorter argument which only
needs a few configurations ("affine diagrams") to be excluded. It works for any set `P` of indices
with `aᵢᵢ = -2` on `P` and some index outside `P`. The matrix `A` is negative definite on vectors
vanishing at some index (`NumericalType.dotProduct_mulVec_neg`, from Zariski's lemma); a vector
`y ≥ 0` supported on `P` with `∑ yᵢ² ≤ ∑_{edges} yᵢ yⱼ` would contradict this
(`NumericalType.false_of_test`). Testing this on a double edge, a vertex with four neighbours, a
triangle, a square, the diagram `Ẽ₈` and the diagrams `D̃ₙ` shows, for a connected component `W`
of the graph of `P` (`NumericalType.indexGraph`): `aᵢⱼ ∈ {0, 1}` inside `W`, every vertex has at
most `3` neighbours, and one of the following holds.

* Every vertex of `W` has at most `2` neighbours. Then `u = 1` satisfies `∑_{j ∼ i} uⱼ ≤ 2 uᵢ`.
* Some vertex `v` has three neighbours, two of which are leaves. Then `v` is the only vertex with
  three neighbours (no `D̃ₙ`), and `u = 1` on the two leaves, `u = 2` elsewhere, satisfies
  `∑_{j ∼ i} uⱼ ≤ 2 uᵢ`.
* Some vertex `v` has three neighbours, at most one of which is a leaf. Then every vertex of `W` is
  within distance `4` of `v` (no `Ẽ₈`).

In the first two cases a maximum principle (`NumericalType.m_le_of_superharmonic`) bounds `m` on
`W` by `2 B`, where `B` bounds `m` at the vertices of `W` meeting an index outside `P`. In the last
case `m` at most doubles along each edge (Stacks, Tag 0C9U) and `W` has diameter at most `8`, so
`m ≤ 2⁸ B` on `W` (`NumericalType.m_le_of_attached_le`).

For genus `g ≥ 2` we take for `P` the `(-2)`-indices and `B = 6g - 6` (Stacks, Tag 0C9V). For genus
`1`, every index of a minimal type with `n > 1` is a `(-2)`-index, and given an index `i₀` with
`mᵢ₀ = 1` (a rational point, Stacks, Tag 0CE8) we take `P = {i ≠ i₀}` and `B = 2`; this replaces
the classification of minimal numerical types of genus `1` (Stacks, Tag 0C8T).

## Main results

For a minimal numerical type `T` with weights `1` and `n > 1`:

* `AlgebraicGeometry.NumericalType.m_le_of_attached_le`: the general bound `mᵢ ≤ 2⁸ B` (for any
  numerical type, `P` and `B` as above);
* genus `g ≥ 2`: `AlgebraicGeometry.NumericalType.m_le_of_isMinusTwoIndex` (`mᵢ ≤ 2⁸ (6g - 6)` for
  a `(-2)`-index `i`), `mul_abs_le` (Stacks, Tag 0C9W, with the constant `2⁹ (6g - 6)` instead of
  `768 g`: `mᵢ |aᵢⱼ| ≤ 2⁹ (6g - 6)`), `card_torsionBy_pic_le_of_lt` (part of Stacks, Tag 0C9X: for
  a prime `ℓ > 2⁹ (6g - 6)`, `|Pic(T)[ℓ]| ≤ ℓ^{g_top}`);
* genus `1` with some `mᵢ₀ = 1`: `m_le_of_genus_eq_one` (`mᵢ ≤ 2⁹`), `mul_abs_le_of_genus_eq_one`
  (`mᵢ |aᵢⱼ| ≤ 2¹⁰`), `card_torsionBy_pic_le_of_genus_eq_one` (for a prime `ℓ > 2¹⁰`,
  `|Pic(T)[ℓ]| ≤ ℓ^{g_top}`).

The case `n = 1` is `card_torsionBy_pic_le_one_of_card_eq_one` (`Pic(T) = ℤ`);
`mul_abs_le_of_isMinimal` is Tag 0C9W and `card_torsionBy_pic_le_of_isMinimal` the inequality
`dim Pic(T)[ℓ] ≤ g_top` of Tag 0C9X, for all minimal types of genus `≥ 2`. Not proved here: the
inequality `g_top ≤ g` of Tag 0C9X (Tag 0C7C), and the first assertion of Tag 0C9X, `dim ≤ g` for
non-minimal types (by contracting `(-1)`-indices, Tags 0C77 and 0C7J); the application, Stacks
Section 0CEI, only needs minimal types and `dim ≤ g_top`.

## References

* [Stacks Project, Tags 0C9U, 0C9V, 0C9W, 0C9X](https://stacks.math.columbia.edu/tag/0C9T)
-/

namespace AlgebraicGeometry

namespace NumericalType

open Matrix Finset

variable {ι : Type*} [Fintype ι] (T : NumericalType ι)

section Definite

/-- The matrix of a numerical type is negative definite on integer vectors vanishing at some index
(Stacks, Tag 0C5X: `xᵀ A x ≤ 0`, with equality only on the line through `m`). -/
theorem dotProduct_mulVec_neg (x : ι → ℤ) (hx : x ≠ 0) (j : ι) (hj : x j = 0) :
    x ⬝ᵥ (T.a *ᵥ x) < 0 := by
  set Aq := T.a.map (Int.castRingHom ℚ)
  set xq : ι → ℚ := fun i ↦ (x i : ℚ)
  set mq : ι → ℚ := fun i ↦ (T.m i : ℚ)
  have hcast : ((x ⬝ᵥ (T.a *ᵥ x) : ℤ) : ℚ) = xq ⬝ᵥ (Aq *ᵥ xq) := by
    simp [xq, Aq, dotProduct, mulVec, Finset.mul_sum]
  have hAq : Aq.IsSymm := T.isSymm.map _
  have hoff : ∀ i k, i ≠ k → 0 ≤ Aq i k := fun i k hik ↦ by
    simpa [Aq] using T.nonneg i k hik
  have hm : ∀ i, 0 < mq i := fun i ↦ by simpa [mq] using T.m_pos i
  have hAm : Aq *ᵥ mq = 0 := by
    ext i
    have := congrFun T.mulVec_eq_zero i
    simp only [mulVec, dotProduct, Pi.zero_apply] at this ⊢
    simp only [Aq, mq, map_apply, eq_intCast]
    exact_mod_cast this
  have hconn : ∀ I : Set ι, I.Nonempty → I ≠ Set.univ → ∃ i ∈ I, ∃ k ∉ I, Aq i k ≠ 0 :=
    fun I hI hI' ↦ by
      obtain ⟨i, hi, k, hk, hik⟩ := T.connected I hI hI'
      exact ⟨i, hi, k, hk, by simpa [Aq] using hik⟩
  have hle := dotProduct_mulVec_nonpos Aq hAq hoff mq hm hAm xq
  rcases hle.lt_or_eq with hlt | heq
  · rw [← hcast] at hlt
    exact_mod_cast hlt
  · obtain ⟨q, hq⟩ := exists_eq_smul_of_dotProduct_mulVec_eq_zero Aq hAq hoff mq hm hAm hconn xq
      heq
    have hq0 : q = 0 := by
      have := congrFun hq j
      simp only [xq, hj, Int.cast_zero, Pi.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_right (hm j).ne'
    exfalso
    apply hx
    ext i
    have := congrFun hq i
    simp only [xq, hq0, zero_smul, Pi.zero_apply, Int.cast_eq_zero] at this
    exact this

/-- The test-vector criterion: a nonzero vector `y ≥ 0` supported on `(-2)`-indices and vanishing
somewhere, with a set `E` of edges (pairs `(i, j)`, `i ≠ j`, no pair listed in both orientations)
and lower bounds `0 ≤ c_e ≤ a_e` for which `∑ yᵢ² ≤ ∑_{e ∈ E} c_e y_{e₁} y_{e₂}`, cannot exist. -/
theorem false_of_test (P : ι → Prop) (hP : ∀ i, P i → T.a i i = -2) (y : ι → ℤ)
    (hy0 : ∀ i, 0 ≤ y i)
    (hN : ∀ i, y i ≠ 0 → P i) (hne : ∃ i, y i ≠ 0) (hz : ∃ j, y j = 0)
    (E : Finset (ι × ι)) (c : ι × ι → ℤ)
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ 0 ≤ c e ∧ c e ≤ T.a e.1 e.2) (hEs : ∀ e ∈ E, e.swap ∉ E)
    (hsum : ∑ i, y i ^ 2 ≤ ∑ e ∈ E, c e * y e.1 * y e.2) : False := by
  classical
  obtain ⟨j, hj⟩ := hz
  have hy : y ≠ 0 := fun h ↦ by
    obtain ⟨i, hi⟩ := hne
    exact hi (congrFun h i)
  have hneg := T.dotProduct_mulVec_neg y hy j hj
  -- write the quadratic form as a sum over pairs
  set F : ι × ι → ℤ := fun x ↦ y x.1 * T.a x.1 x.2 * y x.2
  have hQ : y ⬝ᵥ (T.a *ᵥ y) = ∑ x ∈ univ ×ˢ univ, F x := by
    rw [Finset.sum_product]
    simp only [dotProduct, mulVec, Finset.mul_sum, F]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  set D := (univ ×ˢ univ : Finset (ι × ι)).filter fun x ↦ x.1 = x.2
  set O := (univ ×ˢ univ : Finset (ι × ι)).filter fun x ↦ x.1 ≠ x.2
  have hsplit : ∑ x ∈ univ ×ˢ univ, F x = ∑ x ∈ D, F x + ∑ x ∈ O, F x :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- the diagonal part is `-2 ∑ yᵢ²`
  have hD : ∑ x ∈ D, F x = -2 * ∑ i, y i ^ 2 := by
    have : ∑ x ∈ D, F x = ∑ i, F (i, i) := by
      refine Finset.sum_nbij' (fun x ↦ x.1) (fun i ↦ (i, i)) ?_ ?_ ?_ ?_ ?_
      · simp
      · simp [D]
      · intro x hx
        simp only [D, Finset.mem_filter] at hx
        exact Prod.ext rfl hx.2
      · simp
      · intro x hx
        simp only [D, Finset.mem_filter] at hx
        simp only [F]
        rw [hx.2]
    rw [this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [F]
    by_cases hi : y i = 0
    · simp [hi]
    · rw [hP i (hN i hi)]
      ring
  -- the off-diagonal part dominates the edges in both orientations
  have hO : 2 * ∑ e ∈ E, c e * y e.1 * y e.2 ≤ ∑ x ∈ O, F x := by
    have hdisj : Disjoint E (E.image Prod.swap) := by
      rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨e', he'E, rfl⟩ := Finset.mem_image.mp he'
      exact hEs e' he'E he
    have hsub : E ∪ E.image Prod.swap ⊆ O := by
      intro e he
      simp only [O, Finset.mem_filter, Finset.mem_product, mem_univ, true_and]
      rcases Finset.mem_union.mp he with he | he
      · exact (hE e he).1
      · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
        exact (hE e' he').1.symm
    have hnonneg : ∀ x ∈ O, x ∉ E ∪ E.image Prod.swap → 0 ≤ F x := fun x hx _ ↦ by
      simp only [O, Finset.mem_filter] at hx
      exact mul_nonneg (mul_nonneg (hy0 _) (T.nonneg _ _ hx.2)) (hy0 _)
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
    rw [Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ h ↦ Prod.swap_injective h)] at h1
    have h2 : ∀ e ∈ E, c e * y e.1 * y e.2 ≤ F e := fun e he ↦ by
      simp only [F]
      have := (hE e he).2.2
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (hy0 e.1)) (hy0 e.2)
      linarith
    have h3 : ∀ e ∈ E, F e.swap = F e := fun e _ ↦ by
      simp only [F, Prod.fst_swap, Prod.snd_swap, T.a_symm e.2 e.1]
      ring
    rw [Finset.sum_congr rfl h3] at h1
    have h4 := Finset.sum_le_sum h2
    linarith
  rw [hQ, hsplit, hD] at hneg
  linarith

/-- The test-vector criterion for a configuration given by distinct `(-2)`-indices `f p`,
`p : Fin k`, weights `w p ≥ 0`, edges `E` and lower bounds `0 ≤ c_e ≤ a_e` along the edges, when
some index is not a `(-2)`-index. -/
theorem false_of_fin_test (P : ι → Prop) (hP : ∀ i, P i → T.a i i = -2) (hJ : ∃ j, ¬ P j)
    {k : ℕ} (f : Fin k → ι)
    (hf : Function.Injective f) (hN : ∀ p, P (f p)) (w : Fin k → ℤ)
    (hw : ∀ p, 0 ≤ w p) (hne : ∃ p, w p ≠ 0) (E : Finset (Fin k × Fin k))
    (c : Fin k × Fin k → ℤ)
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ 0 ≤ c e ∧ c e ≤ T.a (f e.1) (f e.2)) (hEs : ∀ e ∈ E, e.swap ∉ E)
    (hsum : ∑ p, w p ^ 2 ≤ ∑ e ∈ E, c e * w e.1 * w e.2) : False := by
  classical
  set y : ι → ℤ := Function.extend f w 0
  have hyf : ∀ p, y (f p) = w p := fun p ↦ hf.extend_apply w 0 p
  have hyo : ∀ i, i ∉ Set.range f → y i = 0 := fun i hi ↦ by
    simp only [y]
    rw [Function.extend_apply' _ _ _ (by simpa using hi)]
    rfl
  have hfe : Function.Injective (Prod.map f f) := hf.prodMap hf
  set c' : ι × ι → ℤ := Function.extend (Prod.map f f) c 0
  have hc' : ∀ e, c' (Prod.map f f e) = c e := fun e ↦ hfe.extend_apply c 0 e
  refine T.false_of_test P hP y (fun i ↦ ?_) (fun i hi ↦ ?_) ?_ ?_ (E.map ⟨_, hfe⟩) c'
    ?_ ?_ ?_
  · by_cases hi : i ∈ Set.range f
    · obtain ⟨p, rfl⟩ := hi
      rw [hyf]
      exact hw p
    · rw [hyo i hi]
  · by_cases hi' : i ∈ Set.range f
    · obtain ⟨p, rfl⟩ := hi'
      exact hN p
    · exact absurd (hyo i hi') hi
  · obtain ⟨p, hp⟩ := hne
    exact ⟨f p, by rwa [hyf]⟩
  · obtain ⟨j, hj⟩ := hJ
    refine ⟨j, hyo j ?_⟩
    rintro ⟨p, rfl⟩
    exact hj (hN p)
  · intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
    have := hE e' he'
    refine ⟨fun h ↦ this.1 (hf h), ?_, ?_⟩
    · simp only [Function.Embedding.coeFn_mk]
      rw [hc']
      exact this.2.1
    · simp only [Function.Embedding.coeFn_mk]
      rw [hc']
      exact this.2.2
  · intro e he hes
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
    obtain ⟨e'', he'', h⟩ := Finset.mem_map.mp hes
    have h' : Prod.map f f e'' = Prod.map f f e'.swap := by
      simp only [Function.Embedding.coeFn_mk] at h
      rw [h]
      rfl
    have : e'' = e'.swap := hfe h'
    exact hEs e' he' (this ▸ he'')
  · have h1 : ∑ i, y i ^ 2 = ∑ p, w p ^ 2 :=
      (Fintype.sum_of_injective f hf (fun p ↦ w p ^ 2) (fun i ↦ y i ^ 2)
        (fun i hi ↦ by rw [hyo i hi]; ring) (fun p ↦ by rw [hyf])).symm
    rw [h1, Finset.sum_map]
    simpa [hyf, hc'] using hsum

end Definite

section Graph

/-- The graph on the indices satisfying `P`: `i ∼ j` iff `i ≠ j` satisfy `P` and `aᵢⱼ ≠ 0`. For
`P` the set of `(-2)`-indices this is the graph of `(-2)`-indices. -/
def indexGraph (P : ι → Prop) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ P i ∧ P j ∧ T.a i j ≠ 0
  symm := ⟨fun i j h ↦ ⟨h.1.symm, h.2.2.1, h.2.1, by rw [T.a_symm]; exact h.2.2.2⟩⟩
  loopless := ⟨fun i h ↦ h.1 rfl⟩

variable {T}

lemma indexGraph_adj {P : ι → Prop} {i j : ι} : (T.indexGraph P).Adj i j ↔
    i ≠ j ∧ P i ∧ P j ∧ T.a i j ≠ 0 := Iff.rfl

lemma one_le_a_of_adj {P : ι → Prop} {i j : ι} (h : (T.indexGraph P).Adj i j) : 1 ≤ T.a i j := by
  have := T.nonneg i j h.1
  have := h.2.2.2
  omega

lemma of_reachable {P : ι → Prop} {i j : ι} (hi : P i)
    (h : (T.indexGraph P).Reachable i j) : P j := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hi
  | cons hadj _ ih => exact ih hadj.2.2.1

/-- A predecessor on a shortest path: if `x ≠ v` is reachable from `v`, it has a neighbour one
step closer to `v`. -/
lemma exists_adj_dist_add_one {P : ι → Prop} {v x : ι} (hr : (T.indexGraph P).Reachable v x)
    (hx : x ≠ v) :
    ∃ y, (T.indexGraph P).Adj y x ∧ (T.indexGraph P).dist v y + 1 = (T.indexGraph P).dist v x := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  cases hq : p.reverse with
  | nil => exact absurd rfl hx
  | cons h q =>
    rename_i y
    refine ⟨y, h.symm, ?_⟩
    have hlen : q.length + 1 = (T.indexGraph P).dist v x := by
      rw [← hp, ← SimpleGraph.Walk.length_reverse p, hq, SimpleGraph.Walk.length_cons]
    have h1 : (T.indexGraph P).dist v y ≤ q.length := by
      rw [SimpleGraph.dist_comm]
      exact SimpleGraph.dist_le q
    have h2 : (T.indexGraph P).dist v x ≤ (T.indexGraph P).dist v y + 1 := by
      have hr' : (T.indexGraph P).Reachable y x := h.symm.reachable
      have := hr'.dist_triangle_right v
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr h.symm] at this
      exact this
    omega

/-- A shortest path `v = p 0, p 1, …, p n = x` with `dist v (p j) = j`. -/
lemma exists_path {P : ι → Prop} (v : ι) : ∀ (n : ℕ) (x : ι), (T.indexGraph P).Reachable v x →
    (T.indexGraph P).dist v x = n → ∃ p : ℕ → ι, p 0 = v ∧ p n = x ∧
      (∀ j ≤ n, (T.indexGraph P).dist v (p j) = j) ∧
      ∀ j < n, (T.indexGraph P).Adj (p j) (p (j + 1)) := by
  intro n
  induction n with
  | zero =>
    intro x hr hd
    have hx : v = x := (hr.dist_eq_zero_iff).mp hd
    subst hx
    exact ⟨fun _ ↦ v, rfl, rfl, fun j hj ↦ by simp [Nat.le_zero.mp hj], fun j hj ↦ absurd hj
      (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro x hr hd
    have hx : x ≠ v := by
      rintro rfl
      simp at hd
    obtain ⟨y, hyx, hyd⟩ := exists_adj_dist_add_one hr hx
    have hry : (T.indexGraph P).Reachable v y := hr.trans hyx.symm.reachable
    obtain ⟨p, hp0, hpn, hpd, hpa⟩ := ih y hry (by omega)
    refine ⟨fun j ↦ if j ≤ n then p j else x, by simp [hp0], by simp, fun j hj ↦ ?_,
      fun j hj ↦ ?_⟩
    · by_cases hjn : j ≤ n
      · simp only [hjn, ↓reduceIte]
        exact hpd j hjn
      · have : j = n + 1 := by omega
        simp only [hjn, ↓reduceIte]
        rw [hd, this]
    · by_cases hjn : j + 1 ≤ n
      · simp only [show j ≤ n by omega, hjn, ↓reduceIte]
        exact hpa j (by omega)
      · have : j = n := by omega
        subst this
        simp only [le_refl, ↓reduceIte, hjn]
        rw [hpn]
        exact hyx

lemma dist_le_of_adj {P : ι → Prop} {v x y : ι} (h : (T.indexGraph P).Adj x y) :
    (T.indexGraph P).dist v y ≤ (T.indexGraph P).dist v x + 1 := by
  have := (h.reachable).dist_triangle_right v
  rwa [SimpleGraph.dist_eq_one_iff_adj.mpr h] at this

variable (T)

end Graph

section Tests

variable {T} {P : ι → Prop} (hP : ∀ i, P i → T.a i i = -2) (hJ : ∃ j, ¬ P j)
include hP hJ

/-- Two `(-2)`-indices are joined by at most a simple edge: `aᵢⱼ ≤ 1`. -/
lemma a_le_one {i j : ι} (hij : i ≠ j) (hi : P i) (hj : P j) :
    T.a i j ≤ 1 := by
  by_contra! h
  refine T.false_of_fin_test P hP hJ ![i, j] ?_ ?_ ![1, 1] ?_ ⟨0, by simp⟩ {(0, 1)} (fun _ ↦ 2) ?_
    (by decide) (by decide)
  · intro p q h
    fin_cases p <;> fin_cases q <;> simp_all [eq_comm]
  · intro p
    fin_cases p <;> assumption
  · intro p
    fin_cases p <;> simp
  · intro e he
    simp only [Finset.mem_singleton] at he
    subst he
    exact ⟨by decide, by norm_num, show 2 ≤ T.a i j by omega⟩

lemma a_eq_one_of_adj {i j : ι} (h : (T.indexGraph P).Adj i j) : T.a i j = 1 :=
  le_antisymm (a_le_one hP hJ h.1 h.2.1 h.2.2.1) (one_le_a_of_adj h)

/-- A `(-2)`-index has at most three neighbours among the `(-2)`-indices. -/
lemma card_le_three_of_adj (x : ι) (s : Finset ι) (hs : ∀ y ∈ s, (T.indexGraph P).Adj x y) :
    s.card ≤ 3 := by
  by_contra! h
  have hl := s.nodup_toList
  have hlen : 4 ≤ s.toList.length := by rw [Finset.length_toList]; omega
  have hmem : ∀ (n : ℕ) (hn : n < s.toList.length), (T.indexGraph P).Adj x s.toList[n] := by
    intro n hn
    have := List.getElem_mem hn
    rw [Finset.mem_toList] at this
    exact hs _ this
  have hne : ∀ (n m : ℕ) (hn : n < s.toList.length) (hm : m < s.toList.length), n ≠ m →
      s.toList[n] ≠ s.toList[m] := fun n m hn hm hnm h ↦
    hnm ((List.Nodup.getElem_inj_iff hl).mp h)
  have h0 := hmem 0 (by omega)
  have h1 := hmem 1 (by omega)
  have h2 := hmem 2 (by omega)
  have h3 := hmem 3 (by omega)
  have h01 := hne 0 1 (by omega) (by omega) (by decide)
  have h02 := hne 0 2 (by omega) (by omega) (by decide)
  have h03 := hne 0 3 (by omega) (by omega) (by decide)
  have h12 := hne 1 2 (by omega) (by omega) (by decide)
  have h13 := hne 1 3 (by omega) (by omega) (by decide)
  have h23 := hne 2 3 (by omega) (by omega) (by decide)
  have hx0 := h0.1
  have hx1 := h1.1
  have hx2 := h2.1
  have hx3 := h3.1
  refine T.false_of_fin_test P hP hJ ![x, s.toList[0], s.toList[1], s.toList[2], s.toList[3]] ?_ ?_
    ![2, 1, 1, 1, 1] ?_ ⟨0, by simp⟩ {(0, 1), (0, 2), (0, 3), (0, 4)} (fun _ ↦ 1) ?_
    (by decide) (by decide)
  · intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [eq_comm]
  · intro p
    fin_cases p
    exacts [h0.2.1, h0.2.2.1, h1.2.2.1, h2.2.2.1, h3.2.2.1]
  · intro p
    fin_cases p <;> simp
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨by decide, by norm_num, by simpa using one_le_a_of_adj h0⟩
    · exact ⟨by decide, by norm_num, by simpa using one_le_a_of_adj h1⟩
    · exact ⟨by decide, by norm_num, by simpa using one_le_a_of_adj h2⟩
    · exact ⟨by decide, by norm_num, by simpa using one_le_a_of_adj h3⟩

/-- The graph of `(-2)`-indices has no triangle. -/
lemma not_triangle {x y z : ι} (hxy : (T.indexGraph P).Adj x y) (hyz : (T.indexGraph P).Adj y z)
    (hxz : (T.indexGraph P).Adj x z) : False := by
  have h1 := hxy.1
  have h2 := hyz.1
  have h3 := hxz.1
  refine T.false_of_fin_test P hP hJ ![x, y, z] ?_ ?_ ![1, 1, 1] ?_ ⟨0, by simp⟩
    {(0, 1), (1, 2), (0, 2)} (fun _ ↦ 1) ?_ (by decide) (by decide)
  · intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [eq_comm]
  · intro p
    fin_cases p
    exacts [hxy.2.1, hxy.2.2.1, hyz.2.2.1]
  · intro p
    fin_cases p <;> simp
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨by decide, by norm_num, by simpa using one_le_a_of_adj hxy⟩
    · exact ⟨by decide, by norm_num, by simpa using one_le_a_of_adj hyz⟩
    · exact ⟨by decide, by norm_num, by simpa using one_le_a_of_adj hxz⟩

/-- The graph of `(-2)`-indices has no square: if `x ∼ y ∼ z ∼ t ∼ x` with `x ≠ z` and `y ≠ t`,
contradiction. -/
lemma not_square {x y z t : ι} (hxy : (T.indexGraph P).Adj x y) (hyz : (T.indexGraph P).Adj y z)
    (hzt : (T.indexGraph P).Adj z t) (htx : (T.indexGraph P).Adj t x) (hxz : x ≠ z)
    (hyt : y ≠ t) : False := by
  have h1 := hxy.1
  have h2 := hyz.1
  have h3 := hzt.1
  have h4 := htx.1
  refine T.false_of_fin_test P hP hJ ![x, y, z, t] ?_ ?_ ![1, 1, 1, 1] ?_ ⟨0, by simp⟩
    {(0, 1), (1, 2), (2, 3), (3, 0)} (fun _ ↦ 1) ?_ (by decide) (by decide)
  · intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [eq_comm]
  · intro p
    fin_cases p
    exacts [hxy.2.1, hxy.2.2.1, hyz.2.2.1, hzt.2.2.1]
  · intro p
    fin_cases p <;> simp
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨by decide, by norm_num, by simpa using one_le_a_of_adj hxy⟩
    · exact ⟨by decide, by norm_num, by simpa using one_le_a_of_adj hyz⟩
    · exact ⟨by decide, by norm_num, by simpa using one_le_a_of_adj hzt⟩
    · exact ⟨by decide, by norm_num, by simpa using one_le_a_of_adj htx⟩

/-- No `Ẽ₈`: let `v ∼ b`, `v ∼ a ∼ a'` (`a' ≠ v`) and a shortest path `v = p 0 ∼ p 1 ∼ ⋯ ∼ p 5` with
`b, a, p 1` distinct. Contradiction (the vector `6, 3, 4, 2, 5, 4, 3, 2, 1` on
`v, b, a, a', p 1, …, p 5` is isotropic for the `Ẽ₈` diagram). -/
lemma not_E8 {v b a a' : ι} (p : ℕ → ι) (hp0 : p 0 = v)
    (hpd : ∀ j ≤ 5, (T.indexGraph P).dist v (p j) = j)
    (hpa : ∀ j < 5, (T.indexGraph P).Adj (p j) (p (j + 1))) (hb : (T.indexGraph P).Adj v b)
    (ha : (T.indexGraph P).Adj v a) (ha' : (T.indexGraph P).Adj a a') (ha'v : a' ≠ v)
    (hab : a ≠ b) (hbp : b ≠ p 1) (hap : a ≠ p 1) : False := by
  subst hp0
  set v := p 0
  have hdb : (T.indexGraph P).dist v b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hb
  have hda : (T.indexGraph P).dist v a = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr ha
  have hda' : (T.indexGraph P).dist v a' = 2 := by
    have h1 := dist_le_of_adj (v := v) ha'
    have h2 : (T.indexGraph P).dist v a' ≠ 0 := by
      rw [ne_eq, (ha.reachable.trans ha'.reachable).dist_eq_zero_iff]
      exact Ne.symm ha'v
    have h3 : (T.indexGraph P).dist v a' ≠ 1 := by
      intro h
      exact not_triangle hP hJ ha ha' (SimpleGraph.dist_eq_one_iff_adj.mp h)
    omega
  have ha'p2 : a' ≠ p 2 := by
    intro h
    rw [h] at ha'
    exact not_square hP hJ ha ha' (hpa 1 (by norm_num)).symm (hpa 0 (by norm_num)).symm
      (fun h' ↦ by have := hpd 2 (by norm_num); rw [← h'] at this; simp [v] at this) hap
  have hd := fun j (hj : j ≤ 5) ↦ hpd j hj
  have hd1 := hd 1 (by norm_num)
  have hd2 := hd 2 (by norm_num)
  have hd3 := hd 3 (by norm_num)
  have hd4 := hd 4 (by norm_num)
  have hd5 := hd 5 (by norm_num)
  have hd0 : (T.indexGraph P).dist v v = 0 := SimpleGraph.dist_self
  set f : Fin 9 → ι := ![v, b, a, a', p 1, p 2, p 3, p 4, p 5] with hf
  have hlab : ∀ q, (T.indexGraph P).dist v (f q) = ![0, 1, 1, 2, 1, 2, 3, 4, 5] q := by
    intro q
    fin_cases q <;> simp [f, hdb, hda, hda', hd1, hd2, hd3, hd4, hd5]
  have hinj : Function.Injective f := by
    intro q r hqr
    have hl := congrArg ((T.indexGraph P).dist v) hqr
    rw [hlab, hlab] at hl
    fin_cases q <;> fin_cases r <;> first
      | rfl
      | exact absurd hl (by decide)
      | exact absurd hqr hab.symm | exact absurd hqr hab | exact absurd hqr hbp
      | exact absurd hqr hbp.symm | exact absurd hqr hap | exact absurd hqr hap.symm
      | exact absurd hqr ha'p2 | exact absurd hqr ha'p2.symm
  have hadj : ∀ j < 5, (T.indexGraph P).Adj (p j) (p (j + 1)) := hpa
  refine T.false_of_fin_test P hP hJ f hinj ?_ ![6, 3, 4, 2, 5, 4, 3, 2, 1] ?_ ⟨0, by simp⟩
    {(0, 1), (0, 2), (2, 3), (0, 4), (4, 5), (5, 6), (6, 7), (7, 8)} (fun _ ↦ 1) ?_ (by decide)
    (by decide)
  · intro q
    fin_cases q
    exacts [hb.2.1, hb.2.2.1, ha.2.2.1, ha'.2.2.1, (hadj 0 (by norm_num)).2.2.1,
      (hadj 1 (by norm_num)).2.2.1, (hadj 2 (by norm_num)).2.2.1, (hadj 3 (by norm_num)).2.2.1,
      (hadj 4 (by norm_num)).2.2.1]
  · intro q
    fin_cases q <;> simp
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, by norm_num, by simpa [f] using one_le_a_of_adj hb⟩
    · exact ⟨by decide, by norm_num, by simpa [f] using one_le_a_of_adj ha⟩
    · exact ⟨by decide, by norm_num, by simpa [f] using one_le_a_of_adj ha'⟩
    · exact ⟨by decide, by norm_num, by simpa [f] using one_le_a_of_adj (hadj 0 (by norm_num))⟩
    · exact ⟨by decide, by norm_num, by simpa [f] using one_le_a_of_adj (hadj 1 (by norm_num))⟩
    · exact ⟨by decide, by norm_num, by simpa [f] using one_le_a_of_adj (hadj 2 (by norm_num))⟩
    · exact ⟨by decide, by norm_num, by simpa [f] using one_le_a_of_adj (hadj 3 (by norm_num))⟩
    · exact ⟨by decide, by norm_num, by simpa [f] using one_le_a_of_adj (hadj 4 (by norm_num))⟩

/-- No `D̃ₙ`: let `v` have two distinct neighbours `l₁, l₂` which are leaves (their only neighbour
is `v`), let `v = p 0 ∼ p 1 ∼ ⋯ ∼ p n = w` (`n ≥ 1`) be a shortest path, and let `w` have two
distinct neighbours `c₁, c₂` other than `p (n - 1)`. Contradiction (the vector which is `2` on the
path and `1` on `l₁, l₂, c₁, c₂` is isotropic for the `D̃` diagram). -/
lemma not_Dtilde {l₁ l₂ c₁ c₂ : ι} (n : ℕ) (hn : 1 ≤ n) (p : ℕ → ι)
    (hpd : ∀ j ≤ n, (T.indexGraph P).dist (p 0) (p j) = j)
    (hpa : ∀ j < n, (T.indexGraph P).Adj (p j) (p (j + 1)))
    (hl₁ : (T.indexGraph P).Adj (p 0) l₁) (hl₂ : (T.indexGraph P).Adj (p 0) l₂) (hl : l₁ ≠ l₂)
    (hleaf₁ : ∀ y, (T.indexGraph P).Adj l₁ y → y = p 0)
    (hleaf₂ : ∀ y, (T.indexGraph P).Adj l₂ y → y = p 0)
    (hc₁ : (T.indexGraph P).Adj (p n) c₁) (hc₂ : (T.indexGraph P).Adj (p n) c₂) (hc : c₁ ≠ c₂)
    (hc₁p : c₁ ≠ p (n - 1)) (hc₂p : c₂ ≠ p (n - 1)) : False := by
  classical
  set δ := (T.indexGraph P).dist (p 0)
  have hpinj : ∀ i ≤ n, ∀ j ≤ n, p i = p j → i = j := fun i hi j hj h ↦ by
    have := congrArg δ h
    rwa [hpd i hi, hpd j hj] at this
  -- the leaves are not on the path
  have hlP : ∀ l, (T.indexGraph P).Adj (p 0) l → (∀ y, (T.indexGraph P).Adj l y → y = p 0) →
      ∀ j ≤ n, p j ≠ l := by
    intro l hl hleaf j hj h
    have hj1 : j = 1 := by
      have h1 := hpd j hj
      have h2 : δ l = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hl
      rw [h] at h1
      omega
    subst hj1
    by_cases hn2 : 2 ≤ n
    · have h2 := hleaf (p 2) (h ▸ hpa 1 (by omega))
      have := hpinj 2 hn2 0 (by omega) h2
      omega
    · have hn1 : n = 1 := by omega
      subst hn1
      exact hc₁p (hleaf c₁ (h ▸ hc₁))
  -- the neighbours of `w` are not on the path
  have hcP : ∀ c, (T.indexGraph P).Adj (p n) c → c ≠ p (n - 1) → ∀ j ≤ n, p j ≠ c := by
    intro c hc hcp j hj h
    have h1 : δ (p n) ≤ δ c + 1 := dist_le_of_adj hc.symm
    rw [← h, hpd j hj, hpd n le_rfl] at h1
    rcases (show j = n ∨ j = n - 1 by omega) with rfl | rfl
    · exact hc.ne h
    · exact hcp h.symm
  -- the neighbours of `w` are not the leaves
  have hcl : ∀ c l, (T.indexGraph P).Adj (p n) c → (∀ y, (T.indexGraph P).Adj l y → y = p 0) →
      c ≠ l := by
    intro c l hc hleaf h
    subst h
    have := hpinj n le_rfl 0 (by omega) (hleaf (p n) hc.symm)
    omega
  have h1₁ := hlP l₁ hl₁ hleaf₁
  have h1₂ := hlP l₂ hl₂ hleaf₂
  have h2₁ := hcP c₁ hc₁ hc₁p
  have h2₂ := hcP c₂ hc₂ hc₂p
  have h3₁₁ := hcl c₁ l₁ hc₁ hleaf₁
  have h3₁₂ := hcl c₁ l₂ hc₁ hleaf₂
  have h3₂₁ := hcl c₂ l₁ hc₂ hleaf₁
  have h3₂₂ := hcl c₂ l₂ hc₂ hleaf₂
  set Sp := (Finset.range (n + 1)).image p with hSp
  set O : Finset ι := {l₁, l₂, c₁, c₂} with hO
  have hmemP : ∀ x, x ∈ Sp ↔ ∃ j ≤ n, p j = x := fun x ↦ by
    simp [Sp]
  have hl₁P : l₁ ∉ Sp := fun h ↦ by
    obtain ⟨j, hj, hjx⟩ := (hmemP _).mp h
    exact h1₁ j hj hjx
  have hl₂P : l₂ ∉ Sp := fun h ↦ by
    obtain ⟨j, hj, hjx⟩ := (hmemP _).mp h
    exact h1₂ j hj hjx
  have hc₁P : c₁ ∉ Sp := fun h ↦ by
    obtain ⟨j, hj, hjx⟩ := (hmemP _).mp h
    exact h2₁ j hj hjx
  have hc₂P : c₂ ∉ Sp := fun h ↦ by
    obtain ⟨j, hj, hjx⟩ := (hmemP _).mp h
    exact h2₂ j hj hjx
  have hpP : ∀ j ≤ n, p j ∈ Sp := fun j hj ↦ (hmemP _).mpr ⟨j, hj, rfl⟩
  have hdisj : Disjoint Sp O := by
    rw [Finset.disjoint_right]
    intro x hx
    simp only [O, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcardP : Sp.card = n + 1 := by
    rw [hSp, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hpinj i (by omega) j (by omega) h
  have hcardO : O.card = 4 := by
    rw [hO, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair hc]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm h3₁₂, Ne.symm h3₂₂⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hl, Ne.symm h3₁₁, Ne.symm h3₂₁⟩
  set y : ι → ℤ := fun x ↦ if x ∈ Sp then 2 else if x ∈ O then 1 else 0 with hy
  have hyP : ∀ x ∈ Sp, y x = 2 := fun x hx ↦ by simp [y, hx]
  have hyO : ∀ x ∈ O, y x = 1 := fun x hx ↦ by
    have : x ∉ Sp := Finset.disjoint_right.mp hdisj hx
    simp [y, hx, this]
  have hyl₁ : y l₁ = 1 := hyO l₁ (by simp [O])
  have hyl₂ : y l₂ = 1 := hyO l₂ (by simp [O])
  have hyc₁ : y c₁ = 1 := hyO c₁ (by simp [O])
  have hyc₂ : y c₂ = 1 := hyO c₂ (by simp [O])
  have hyp : ∀ j ≤ n, y (p j) = 2 := fun j hj ↦ hyP _ (hpP j hj)
  have hy0 : ∀ x, x ∉ Sp → x ∉ O → y x = 0 := fun x h1 h2 ↦ by simp [y, h1, h2]
  -- the `(-2)`-indices involved
  have hNp : ∀ j ≤ n, P (p j) := fun j hj ↦ by
    rcases (show j < n ∨ j = n by omega) with h | rfl
    · exact (hpa j h).2.1
    · exact hc₁.2.1
  have hNO : ∀ x ∈ O, P x := fun x hx ↦ by
    simp only [O, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [hl₁.2.2.1, hl₂.2.2.1, hc₁.2.2.1, hc₂.2.2.1]
  have hNP : ∀ x ∈ Sp, P x := fun x hx ↦ by
    obtain ⟨j, hj, rfl⟩ := (hmemP x).mp hx
    exact hNp j hj
  -- the edges
  set E₁ := (Finset.range n).image fun j ↦ (p j, p (j + 1)) with hE₁
  set E₂ : Finset (ι × ι) := {(p 0, l₁), (p 0, l₂), (p n, c₁), (p n, c₂)} with hE₂
  have hmemE₁ : ∀ e, e ∈ E₁ ↔ ∃ j < n, (p j, p (j + 1)) = e := fun e ↦ by simp [E₁]
  have hE₁₂ : Disjoint E₁ E₂ := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨j, hj, rfl⟩ := (hmemE₁ e).mp he
    simp only [E₂, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at he'
    rcases he' with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact h1₁ (j + 1) (by omega) h
    · exact h1₂ (j + 1) (by omega) h
    · exact h2₁ (j + 1) (by omega) h
    · exact h2₂ (j + 1) (by omega) h
  refine T.false_of_test P hP y (fun x ↦ ?_) (fun x hx ↦ ?_) ⟨p 0, by rw [hyp 0 (by omega)]; simp⟩
    ?_ (E₁ ∪ E₂) (fun _ ↦ 1) ?_ ?_ ?_
  · simp only [y]
    split_ifs <;> norm_num
  · by_cases h1 : x ∈ Sp
    · exact hNP x h1
    by_cases h2 : x ∈ O
    · exact hNO x h2
    exact absurd (hy0 x h1 h2) hx
  · obtain ⟨j, hj⟩ := hJ
    refine ⟨j, hy0 j (fun h ↦ hj (hNP j h)) (fun h ↦ hj (hNO j h))⟩
  · intro e he
    refine ⟨?_, zero_le_one, ?_⟩ <;> rcases Finset.mem_union.mp he with he | he
    · obtain ⟨j, hj, rfl⟩ := (hmemE₁ e).mp he
      exact (hpa j hj).1
    · simp only [E₂, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      exacts [hl₁.1, hl₂.1, hc₁.1, hc₂.1]
    · obtain ⟨j, hj, rfl⟩ := (hmemE₁ e).mp he
      exact one_le_a_of_adj (hpa j hj)
    · simp only [E₂, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      exacts [one_le_a_of_adj hl₁, one_le_a_of_adj hl₂, one_le_a_of_adj hc₁,
        one_le_a_of_adj hc₂]
  · intro e he hes
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨j, hj, rfl⟩ := (hmemE₁ _).mp he
      rcases Finset.mem_union.mp hes with hes | hes
      · obtain ⟨i, hi, h⟩ := (hmemE₁ _).mp hes
        simp only [Prod.swap_prod_mk, Prod.mk.injEq] at h
        have h1 := hpinj i (by omega) (j + 1) (by omega) h.1
        have h2 := hpinj (i + 1) (by omega) j (by omega) h.2
        omega
      · simp only [Prod.swap_prod_mk, E₂, Finset.mem_insert, Finset.mem_singleton,
          Prod.mk.injEq] at hes
        rcases hes with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · exact h1₁ j (by omega) h
        · exact h1₂ j (by omega) h
        · exact h2₁ j (by omega) h
        · exact h2₂ j (by omega) h
    · simp only [E₂, Finset.mem_insert, Finset.mem_singleton] at he
      rcases Finset.mem_union.mp hes with hes | hes
      · rcases he with rfl | rfl | rfl | rfl <;>
        · obtain ⟨i, hi, h⟩ := (hmemE₁ _).mp hes
          simp only [Prod.swap_prod_mk, Prod.mk.injEq] at h
          first
            | exact h1₁ i (by omega) h.1 | exact h1₂ i (by omega) h.1
            | exact h2₁ i (by omega) h.1 | exact h2₂ i (by omega) h.1
      · simp only [E₂, Finset.mem_insert, Finset.mem_singleton] at hes
        rcases he with rfl | rfl | rfl | rfl <;>
        · simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hes
          rcases hes with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
          first
            | exact h1₁ 0 (by omega) h.symm | exact h1₂ 0 (by omega) h.symm
            | exact h1₁ n le_rfl h.symm | exact h1₂ n le_rfl h.symm
            | exact h2₁ 0 (by omega) h.symm | exact h2₂ 0 (by omega) h.symm
            | exact h2₁ n le_rfl h.symm | exact h2₂ n le_rfl h.symm
  · -- `∑ yᵢ² = 4 (n + 1) + 4 = ∑_{edges} yᵢ yⱼ`
    have hsq : ∑ x, y x ^ 2 = ∑ x ∈ Sp ∪ O, y x ^ 2 := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx ↦ ?_).symm
      simp only [Finset.mem_union, not_or] at hx
      rw [hy0 x hx.1 hx.2]
      ring
    have hsq' : ∑ x ∈ Sp ∪ O, y x ^ 2 = 4 * (n + 1) + 4 := by
      rw [Finset.sum_union hdisj]
      have e1 : ∑ x ∈ Sp, y x ^ 2 = ∑ x ∈ Sp, (4 : ℤ) :=
        Finset.sum_congr rfl fun x hx ↦ by rw [hyP x hx]; norm_num
      have e2 : ∑ x ∈ O, y x ^ 2 = ∑ x ∈ O, (1 : ℤ) :=
        Finset.sum_congr rfl fun x hx ↦ by rw [hyO x hx]; norm_num
      rw [e1, e2]
      simp [hcardP, hcardO]
      ring
    have hE1 : ∑ e ∈ E₁, (1 : ℤ) * y e.1 * y e.2 = 4 * n := by
      rw [hE₁, Finset.sum_image]
      · rw [Finset.sum_congr rfl fun j hj ↦ by
          rw [hyp j (by simp at hj; omega), hyp (j + 1) (by simp at hj; omega)]]
        simp
        ring
      · intro i hi j hj h
        simp only [Finset.coe_range, Set.mem_Iio] at hi hj
        simp only [Prod.mk.injEq] at h
        exact hpinj i (by omega) j (by omega) h.1
    have hE2 : ∑ e ∈ E₂, (1 : ℤ) * y e.1 * y e.2 = 8 := by
      have hne1 : (p 0, l₁) ∉ ({(p 0, l₂), (p n, c₁), (p n, c₂)} : Finset (ι × ι)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
        exact ⟨fun h ↦ hl h.2, fun h ↦ h3₁₁ h.2.symm, fun h ↦ h3₂₁ h.2.symm⟩
      have hne2 : (p 0, l₂) ∉ ({(p n, c₁), (p n, c₂)} : Finset (ι × ι)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
        exact ⟨fun h ↦ h3₁₂ h.2.symm, fun h ↦ h3₂₂ h.2.symm⟩
      have hne3 : (p n, c₁) ≠ (p n, c₂) := fun h ↦ hc (Prod.mk.inj h).2
      rw [hE₂, Finset.sum_insert hne1, Finset.sum_insert hne2, Finset.sum_pair hne3]
      simp only [hyp 0 (by omega), hyp n le_rfl, hyl₁, hyl₂, hyc₁, hyc₂]
      norm_num
    rw [hsq, hsq', Finset.sum_union hE₁₂, hE1, hE2]
    ring_nf
    omega

end Tests

section Bound

variable {T} {P : ι → Prop}

/-- The neighbours of `x` in the graph of `(-2)`-indices. -/
noncomputable def nbrs (P : ι → Prop) (x : ι) : Finset ι := by
  classical exact Finset.univ.filter ((T.indexGraph P).Adj x)

lemma mem_nbrs {x y : ι} : y ∈ T.nbrs P x ↔ (T.indexGraph P).Adj x y := by
  classical
  simp [nbrs]

/-- For a `(-2)`-index `x`: `2 mₓ = ∑_{y ∼ x} m_y + ∑_{j} aₓⱼ mⱼ`, the last sum over the indices `j`
which are not `(-2)`-indices. -/
lemma two_mul_m_eq [DecidablePred P] (hP : ∀ i, P i → T.a i i = -2) (hJ : ∃ j, ¬ P j)
    {x : ι} (hx : P x) :
    2 * T.m x = ∑ y ∈ T.nbrs P x, T.m y +
      ∑ j, if P j then 0 else T.a x j * T.m j := by
  classical
  have h0 := T.sum_mul_eq_zero x
  have hterm : ∀ k, T.a x k * T.m k = (if k = x then -2 * T.m x else 0) +
      (if (T.indexGraph P).Adj x k then T.m k else 0) +
      (if P k then 0 else T.a x k * T.m k) := by
    intro k
    by_cases hkx : k = x
    · subst hkx
      simp [hx, hP _ hx]
    · by_cases hk : P k
      · by_cases hadj : (T.indexGraph P).Adj x k
        · simp [hkx, hadj, hk, a_eq_one_of_adj hP hJ hadj]
        · have : T.a x k = 0 := by
            by_contra hne
            exact hadj ⟨Ne.symm hkx, hx, hk, hne⟩
          simp [hkx, hadj, hk, this]
      · have : ¬ (T.indexGraph P).Adj x k := fun h ↦ hk h.2.2.1
        simp [hkx, this, hk]
  rw [Finset.sum_congr rfl fun k _ ↦ hterm k, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ x] at h0
  simp only [Finset.mem_univ, ↓reduceIte] at h0
  have : ∑ k, (if (T.indexGraph P).Adj x k then T.m k else 0) = ∑ y ∈ T.nbrs P x, T.m y := by
    rw [nbrs, Finset.sum_filter]
  linarith

/-- Every connected component of the graph of `(-2)`-indices contains an index meeting a
non-`(-2)`-index (`T` is connected). -/
lemma exists_reachable_attached (hJ : ∃ j, ¬ P j) {i : ι}
    (hi : P i) :
    ∃ s, (T.indexGraph P).Reachable i s ∧ ∃ j, ¬ P j ∧ T.a s j ≠ 0 := by
  obtain ⟨j₀, hj₀⟩ := hJ
  obtain ⟨s, hs, k, hk, hsk⟩ := T.connected {x | (T.indexGraph P).Reachable i x}
    ⟨i, SimpleGraph.Reachable.refl i⟩ (fun h ↦ hj₀ (of_reachable hi
      (show j₀ ∈ {x | (T.indexGraph P).Reachable i x} from h ▸ Set.mem_univ j₀)))
  refine ⟨s, hs, k, fun hkN ↦ hk ?_, hsk⟩
  have hsN := of_reachable hi hs
  have hsk' : s ≠ k := fun h ↦ hk (h ▸ hs)
  exact hs.trans (SimpleGraph.Adj.reachable (G := (T.indexGraph P)) ⟨hsk', hsN, hkN, hsk⟩)

/-- The maximum principle: let `u ≥ 1` on the component `W` of the `(-2)`-index `i₀` with
`∑_{y ∼ x} u_y ≤ 2 uₓ` for `x ∈ W`, and let `B` bound `mₓ` at every `x ∈ W` meeting a
non-`(-2)`-index. Then `mₓ ≤ B uₓ` on `W`. -/
lemma m_le_of_superharmonic (hP : ∀ i, P i → T.a i i = -2)
    (hJ : ∃ j, ¬ P j) {i₀ : ι}
    (hi₀ : P i₀) (u : ι → ℤ)
    (hu1 : ∀ x, (T.indexGraph P).Reachable i₀ x → 1 ≤ u x)
    (hu : ∀ x, (T.indexGraph P).Reachable i₀ x → ∑ y ∈ T.nbrs P x, u y ≤ 2 * u x) (B : ℤ)
    (hB : ∀ x j, (T.indexGraph P).Reachable i₀ x → ¬ P j → T.a x j ≠ 0 →
      T.m x ≤ B) :
    ∀ x, (T.indexGraph P).Reachable i₀ x → T.m x ≤ B * u x := by
  classical
  set W := Finset.univ.filter ((T.indexGraph P).Reachable i₀)
  have hmemW : ∀ x, x ∈ W ↔ (T.indexGraph P).Reachable i₀ x := fun x ↦ by simp [W]
  have hW : W.Nonempty := ⟨i₀, (hmemW i₀).mpr (SimpleGraph.Reachable.refl i₀)⟩
  set q : ι → ℚ := fun x ↦ (T.m x : ℚ) / (u x : ℚ)
  obtain ⟨z, hzW, hzmax⟩ := W.exists_max_image q hW
  set r := q z
  have hupos : ∀ x ∈ W, (0 : ℚ) < u x := fun x hx ↦ by
    have := hu1 x ((hmemW x).mp hx)
    exact_mod_cast (show (0 : ℤ) < u x by omega)
  have hle : ∀ x ∈ W, (T.m x : ℚ) ≤ r * u x := fun x hx ↦ by
    have := hzmax x hx
    simp only [q] at this
    rwa [div_le_iff₀ (hupos x hx)] at this
  -- some maximizer meets a non-`(-2)`-index
  have key : ∃ z' ∈ W, q z' = r ∧ ∃ j, ¬ P j ∧ T.a z' j ≠ 0 := by
    by_contra! hcon
    set Z := W.filter fun x ↦ q x = r
    -- `Z` is closed under adjacency
    have hclosed : ∀ x ∈ Z, ∀ y, (T.indexGraph P).Adj x y → y ∈ Z := by
      intro x hx y hxy
      simp only [Z, Finset.mem_filter] at hx
      have hxN : P x := of_reachable hi₀ ((hmemW x).mp hx.1)
      have hb : ∀ j, ¬ P j → T.a x j = 0 := fun j hj ↦
        hcon x hx.1 hx.2 j hj
      have h2m := two_mul_m_eq hP hJ hxN
      have hb0 : (∑ j, if P j then 0 else T.a x j * T.m j) = 0 :=
        Finset.sum_eq_zero fun j _ ↦ by
          split_ifs with hj
          · rfl
          · rw [hb j hj, zero_mul]
      rw [hb0, add_zero] at h2m
      have hnW : ∀ y ∈ T.nbrs P x, y ∈ W := fun y hy ↦
        (hmemW y).mpr (((hmemW x).mp hx.1).trans (mem_nbrs.mp hy).reachable)
      have hxr : (T.m x : ℚ) = r * u x := by
        have := hx.2
        simp only [q] at this
        rw [← this, div_mul_cancel₀ _ (hupos x hx.1).ne']
      -- `∑_{y ∼ x} (r u_y - m_y) ≤ 0` with nonnegative terms
      have hsum : ∑ y ∈ T.nbrs P x, (r * u y - T.m y) ≤ 0 := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        have h1 : (∑ y ∈ T.nbrs P x, (u y : ℚ)) ≤ 2 * u x := by
          exact_mod_cast hu x ((hmemW x).mp hx.1)
        have h2 : (2 : ℚ) * T.m x = ∑ y ∈ T.nbrs P x, (T.m y : ℚ) := by exact_mod_cast h2m
        have hr0 : 0 ≤ r := by
          have := hupos x hx.1
          have hm := T.m_pos x
          have : (0 : ℚ) < T.m x := by exact_mod_cast hm
          nlinarith
        have := mul_le_mul_of_nonneg_left h1 hr0
        rw [← h2, hxr] at *
        nlinarith
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun y hy ↦
        sub_nonneg.mpr (hle y (hnW y hy))).mp (le_antisymm hsum (Finset.sum_nonneg fun y hy ↦
          sub_nonneg.mpr (hle y (hnW y hy)))) y (mem_nbrs.mpr hxy)
      simp only [Z, Finset.mem_filter]
      refine ⟨hnW y (mem_nbrs.mpr hxy), ?_⟩
      simp only [q]
      rw [div_eq_iff (hupos y (hnW y (mem_nbrs.mpr hxy))).ne']
      linarith
    have hzZ : z ∈ Z := by simp [Z, hzW, r]
    -- hence `Z = W`
    have hwalk : ∀ (a b : ι), (T.indexGraph P).Walk a b → a ∈ Z → b ∈ Z := by
      intro a b w
      induction w with
      | nil => exact id
      | cons hab _ ih => exact fun ha ↦ ih (hclosed _ ha _ hab)
    have hZW : ∀ x, (T.indexGraph P).Reachable z x → x ∈ Z := fun x ⟨w⟩ ↦ hwalk z x w hzZ
    -- apply connectedness of `T` to `W`
    obtain ⟨s, hs, k, hk, hsk⟩ := exists_reachable_attached hJ hi₀
    have hsZ : s ∈ Z := hZW s (((hmemW z).mp hzW).symm.trans hs)
    simp only [Z, Finset.mem_filter] at hsZ
    exact hsk (hcon s hsZ.1 hsZ.2 k hk)
  obtain ⟨z', hz'W, hz'r, j, hj, hz'j⟩ := key
  have hmB : T.m z' ≤ B := hB z' j ((hmemW z').mp hz'W) hj hz'j
  have hrB : r ≤ B := by
    rw [← hz'r]
    simp only [q]
    rw [div_le_iff₀ (hupos z' hz'W)]
    have h1 : (1 : ℚ) ≤ u z' := by exact_mod_cast hu1 z' ((hmemW z').mp hz'W)
    have h2 : (T.m z' : ℚ) ≤ B := by exact_mod_cast hmB
    have h3 : (0 : ℚ) < T.m z' := by exact_mod_cast T.m_pos z'
    nlinarith
  intro x hx
  have h1 := hle x ((hmemW x).mpr hx)
  have h2 : r * u x ≤ B * u x := mul_le_mul_of_nonneg_right hrB (hupos x ((hmemW x).mpr hx)).le
  exact_mod_cast h1.trans h2

/-- Along an edge of the graph of `(-2)`-indices the multiplicity at most doubles (Stacks, Tag
0C9U). -/
lemma m_le_two_mul_of_adj (hP : ∀ i, P i → T.a i i = -2) (hJ : ∃ j, ¬ P j) {x y : ι}
    (hxy : (T.indexGraph P).Adj x y) : T.m y ≤ 2 * T.m x := by
  have := (T.mul_le_of_pos hxy.1.symm (by rw [a_eq_one_of_adj hP hJ hxy.symm]; norm_num)).1
  rw [a_eq_one_of_adj hP hJ hxy.symm, hP x hxy.2.1] at this
  linarith

lemma m_le_pow_dist (hP : ∀ i, P i → T.a i i = -2) (hJ : ∃ j, ¬ P j) {s x : ι}
    (hr : (T.indexGraph P).Reachable s x) :
    T.m x ≤ 2 ^ (T.indexGraph P).dist s x * T.m s := by
  obtain ⟨p, hp0, hpn, -, hpa⟩ := exists_path s _ x hr rfl
  have : ∀ j ≤ (T.indexGraph P).dist s x, T.m (p j) ≤ 2 ^ j * T.m s := by
    intro j
    induction j with
    | zero => intro _; simp [hp0]
    | succ j ih =>
      intro hj
      have h1 := m_le_two_mul_of_adj hP hJ (hpa j (by omega))
      have h2 := ih (by omega)
      rw [pow_succ]
      linarith
  simpa [hpn] using this _ le_rfl

end Bound

section General

variable {T} {P : ι → Prop} (hP : ∀ i, P i → T.a i i = -2) (hJ : ∃ j, ¬ P j)
include hP hJ

/-- The bound on multiplicities, in general form: let `P` be a set of indices with `aᵢᵢ = -2` for
`i ∈ P`, not containing every index, and let `B ≥ 0` bound `mₓ` at every `x` of the component of
`i` in the graph of `P` (`NumericalType.indexGraph`) which meets an index outside `P`. Then
`mᵢ ≤ 2⁸ B`. -/
theorem m_le_of_attached_le (B : ℤ) (hB0 : 0 ≤ B) {i : ι} (hi : P i)
    (hB : ∀ x j, (T.indexGraph P).Reachable i x → ¬ P j → T.a x j ≠ 0 → T.m x ≤ B) :
    T.m i ≤ 2 ^ 8 * B := by
  classical
  by_cases hA : ∀ x, (T.indexGraph P).Reachable i x → (T.nbrs P x).card ≤ 2
  · -- all degrees `≤ 2`: the maximum principle with `u = 1`
    have := m_le_of_superharmonic hP hJ hi (fun _ ↦ 1) (fun _ _ ↦ le_rfl) (fun x hx ↦ by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hA x hx) B hB i (SimpleGraph.Reachable.refl i)
    have h256 : (1 : ℤ) ≤ 2 ^ 8 := by norm_num
    nlinarith
  push Not at hA
  obtain ⟨v, hv, hv3⟩ := hA
  have hv3' : (T.nbrs P v).card = 3 :=
    le_antisymm (card_le_three_of_adj hP hJ v _ fun y hy ↦ mem_nbrs.mp hy) hv3
  by_cases hB1 : ∃ l₁ l₂, (T.indexGraph P).Adj v l₁ ∧ (T.indexGraph P).Adj v l₂ ∧ l₁ ≠ l₂ ∧
      (∀ y, (T.indexGraph P).Adj l₁ y → y = v) ∧ (∀ y, (T.indexGraph P).Adj l₂ y → y = v)
  · -- `D`-type: `v` has two leaf neighbours
    obtain ⟨l₁, l₂, hl₁, hl₂, hl, hleaf₁, hleaf₂⟩ := hB1
    -- `v` is the only vertex with three neighbours (no `D̃`)
    have huniq : ∀ w, (T.indexGraph P).Reachable i w → w ≠ v → (T.nbrs P w).card ≤ 2 := by
      intro w hw hwv
      by_contra! hw3
      have hvw : (T.indexGraph P).Reachable v w := hv.symm.trans hw
      have hn : 1 ≤ (T.indexGraph P).dist v w := Nat.pos_of_ne_zero
        (SimpleGraph.dist_ne_zero_iff_ne_and_reachable.mpr ⟨Ne.symm hwv, hvw⟩)
      obtain ⟨p, hp0, hpn, hpd, hpa⟩ := exists_path v _ w hvw rfl
      generalize (T.indexGraph P).dist v w = n at hn hpn hpd hpa
      have hcard : 1 < ((T.nbrs P w).erase (p (n - 1))).card := by
        have := Finset.pred_card_le_card_erase (s := T.nbrs P w) (a := p (n - 1))
        omega
      obtain ⟨c₁, hc₁, c₂, hc₂, hc⟩ := Finset.one_lt_card.mp hcard
      rw [Finset.mem_erase, mem_nbrs] at hc₁ hc₂
      rw [← hp0] at hl₁ hl₂ hleaf₁ hleaf₂ hpd
      rw [← hpn] at hc₁ hc₂
      exact not_Dtilde hP hJ n hn p hpd hpa hl₁ hl₂ hl hleaf₁ hleaf₂ hc₁.2 hc₂.2 hc hc₁.1 hc₂.1
    set u : ι → ℤ := fun x ↦ if x = l₁ ∨ x = l₂ then 1 else 2 with hu
    have hule : ∀ y, u y ≤ 2 := fun y ↦ by simp only [u]; split_ifs <;> norm_num
    have hvl : ¬ (v = l₁ ∨ v = l₂) := by
      rintro (e | e)
      · exact hl₁.ne e
      · exact hl₂.ne e
    have hu1 : ∀ x, (T.indexGraph P).Reachable i x → 1 ≤ u x := fun x _ ↦ by
      simp only [u]
      split_ifs <;> norm_num
    have hus : ∀ x, (T.indexGraph P).Reachable i x → ∑ y ∈ T.nbrs P x, u y ≤ 2 * u x := by
      intro x hx
      by_cases hxl : x = l₁ ∨ x = l₂
      · have hnb : T.nbrs P x = {v} := by
          ext y
          rw [mem_nbrs, Finset.mem_singleton]
          constructor
          · intro hy
            rcases hxl with rfl | rfl
            exacts [hleaf₁ y hy, hleaf₂ y hy]
          · rintro rfl
            rcases hxl with rfl | rfl
            exacts [hl₁.symm, hl₂.symm]
        rw [hnb, Finset.sum_singleton]
        simp only [u, hvl, hxl, ↓reduceIte]
        norm_num
      · by_cases hxv : x = v
        · subst hxv
          have hl₁m : l₁ ∈ T.nbrs P x := mem_nbrs.mpr hl₁
          have hl₂m : l₂ ∈ (T.nbrs P x).erase l₁ :=
            Finset.mem_erase.mpr ⟨Ne.symm hl, mem_nbrs.mpr hl₂⟩
          rw [← Finset.add_sum_erase _ _ hl₁m, ← Finset.add_sum_erase _ _ hl₂m]
          have hcard : (((T.nbrs P x).erase l₁).erase l₂).card = 1 := by
            rw [Finset.card_erase_of_mem hl₂m, Finset.card_erase_of_mem hl₁m, hv3']
          have hrest : ∑ y ∈ ((T.nbrs P x).erase l₁).erase l₂, u y ≤
              (((T.nbrs P x).erase l₁).erase l₂).card • (2 : ℤ) :=
            Finset.sum_le_card_nsmul _ _ _ fun y _ ↦ hule y
          rw [hcard] at hrest
          simp only [u, true_or, or_true, ↓reduceIte, hvl] at hrest ⊢
          norm_num at hrest ⊢
          linarith
        · have hx2 := huniq x hx hxv
          have hsum : ∑ y ∈ T.nbrs P x, u y ≤ (T.nbrs P x).card • (2 : ℤ) :=
            Finset.sum_le_card_nsmul _ _ _ fun y _ ↦ hule y
          simp only [u, hxl, ↓reduceIte, nsmul_eq_mul] at hsum ⊢
          have : ((T.nbrs P x).card : ℤ) ≤ 2 := by exact_mod_cast hx2
          nlinarith
    have := m_le_of_superharmonic hP hJ hi u hu1 hus B hB i (SimpleGraph.Reachable.refl i)
    have hui := hule i
    have h256 : (2 : ℤ) ≤ 2 ^ 8 := by norm_num
    nlinarith
  · -- otherwise every vertex is within distance `4` of `v` (no `Ẽ₈`)
    push Not at hB1
    have hdist : ∀ x, (T.indexGraph P).Reachable v x → (T.indexGraph P).dist v x ≤ 4 := by
      intro x hx
      by_contra! hfar
      obtain ⟨p, hp0, hpn, hpd, hpa⟩ := exists_path v _ x hx rfl
      have hp1 : p 1 ∈ T.nbrs P v := mem_nbrs.mpr (hp0 ▸ hpa 0 (by omega))
      have hcard : 1 < ((T.nbrs P v).erase (p 1)).card := by
        rw [Finset.card_erase_of_mem hp1, hv3']
        norm_num
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
      rw [Finset.mem_erase, mem_nbrs] at ha hb
      have hnl : (∃ a', (T.indexGraph P).Adj a a' ∧ a' ≠ v) ∨
          (∃ b', (T.indexGraph P).Adj b b' ∧ b' ≠ v) := by
        by_contra! hcon
        obtain ⟨y, hy, hyv⟩ := hB1 a b ha.2 hb.2 hab (fun y hy ↦ hcon.1 y hy)
        exact hyv (hcon.2 y hy)
      rcases hnl with ⟨a', ha', ha'v⟩ | ⟨b', hb', hb'v⟩
      · exact not_E8 hP hJ p hp0 (fun j hj ↦ hpd j (by omega)) (fun j hj ↦ hpa j (by omega)) hb.2
          ha.2 ha' ha'v hab hb.1 ha.1
      · exact not_E8 hP hJ p hp0 (fun j hj ↦ hpd j (by omega)) (fun j hj ↦ hpa j (by omega)) ha.2
          hb.2 hb' hb'v (Ne.symm hab) ha.1 hb.1
    obtain ⟨s, hs, j, hj, hsj⟩ := exists_reachable_attached hJ hi
    have hms : T.m s ≤ B := hB s j hs hj hsj
    have hd : (T.indexGraph P).dist s i ≤ 8 := by
      have hsv : (T.indexGraph P).Reachable s v := hs.symm.trans hv
      have h1 := hsv.dist_triangle_left i
      have h2 : (T.indexGraph P).dist s v ≤ 4 := by
        rw [SimpleGraph.dist_comm]
        exact hdist s (hv.symm.trans hs)
      have h3 := hdist i hv.symm
      omega
    have h1 := m_le_pow_dist hP hJ hs.symm
    have h2 : (2 : ℤ) ^ (T.indexGraph P).dist s i ≤ 2 ^ 8 :=
      pow_le_pow_right₀ (by norm_num) hd
    have hm := T.m_pos s
    calc T.m i ≤ 2 ^ (T.indexGraph P).dist s i * T.m s := h1
      _ ≤ 2 ^ 8 * T.m s := mul_le_mul_of_nonneg_right h2 hm.le
      _ ≤ 2 ^ 8 * B := mul_le_mul_of_nonneg_left hms (by norm_num)


end General

section Main

/-- If `g ≥ 2`, some index is not a `(-2)`-index. -/
lemma exists_not_isMinusTwoIndex (hg : 2 ≤ T.genus) : ∃ j, ¬ T.IsMinusTwoIndex j := by
  by_contra! hall
  have h2 := T.two_mul_genus
  have : ∑ i, T.contrib i = 0 := Finset.sum_eq_zero fun i _ ↦ by
    simp [contrib, (hall i).1, (hall i).2]
  omega

variable {T} (hT : T.IsMinimal) (h : 1 < Fintype.card ι) (hg : 2 ≤ T.genus)
include hT h hg

/-- The heart of Stacks, Tag 0C9W (with weights `1`): in a minimal numerical type of genus `g ≥ 2`
with `n > 1`, every `(-2)`-index `i` has `mᵢ ≤ 2⁸ (6g - 6)`. -/
theorem m_le_of_isMinusTwoIndex {i : ι} (hi : T.IsMinusTwoIndex i) :
    T.m i ≤ 2 ^ 8 * (6 * T.genus - 6) := by
  refine m_le_of_attached_le (fun j hj ↦ hj.2) (T.exists_not_isMinusTwoIndex hg) _
    (by omega) hi fun x j hx hj hxj ↦ ?_
  have hxN := of_reachable hi hx
  have hxj' : x ≠ j := fun e ↦ hj (e ▸ hxN)
  have h1 := T.mul_le_six_mul hT h hj x
  have ha : 1 ≤ T.a x j := by
    have := T.nonneg x j hxj'
    omega
  have hm := T.m_pos x
  nlinarith

/-- Stacks, Tag 0C9W (with weights `1`, and the constant `2⁹ (6g - 6)` instead of `768 g`): in a
minimal numerical type of genus `g ≥ 2` with `n > 1`, `mᵢ |aᵢⱼ| ≤ 2⁹ (6g - 6)` for all `i, j`. -/
theorem mul_abs_le (i j : ι) : T.m i * |T.a i j| ≤ 2 ^ 9 * (6 * T.genus - 6) := by
  have hB0 : 0 ≤ 6 * T.genus - 6 := by omega
  have hmi := T.m_pos i
  -- the diagonal bound `mₖ |aₖₖ| ≤ 2⁹ (6g - 6)`
  have hdiag : ∀ k, T.m k * -T.a k k ≤ 2 ^ 9 * (6 * T.genus - 6) := by
    intro k
    by_cases hk : T.IsMinusTwoIndex k
    · rw [hk.2]
      have := m_le_of_isMinusTwoIndex hT h hg hk
      linarith
    · have := T.mul_neg_diag_le hT h hk
      linarith
  by_cases hij : i = j
  · subst hij
    rw [abs_of_neg (T.diag_neg h i)]
    exact hdiag i
  rcases (T.nonneg i j hij).lt_or_eq with hpos | h0
  · rw [abs_of_pos hpos]
    exact (T.mul_le_of_pos hij hpos).1.trans (hdiag j)
  · rw [← h0, abs_zero, mul_zero]
    positivity

/-- Part of Stacks, Tag 0C9X, for a minimal numerical type with weights `1`, `n > 1` and genus
`g ≥ 2`: for a prime `ℓ > 2⁹ (6g - 6)`, `|Pic(T)[ℓ]| ≤ ℓ^{g_top}`, i.e.
`dim_{𝔽_ℓ} Pic(T)[ℓ] ≤ g_top`. Deviations from Tag 0C9X: only `dim ≤ g_top` is proved (Stacks
also has `g_top ≤ g`, Tag 0C7C, not proved here, and the bound `dim ≤ g` for every numerical
type); the threshold is `ℓ > 2⁹ (6g - 6)`, stronger than Stacks' `ℓ > 768 g`. -/
theorem card_torsionBy_pic_le_of_lt [LinearOrder ι] [Nonempty ι] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : 2 ^ 9 * (6 * T.genus - 6) < ℓ) :
    Nat.card (Submodule.torsionBy ℤ T.Pic (ℓ : ℤ)) ≤ ℓ ^ T.topGenus.toNat := by
  refine T.card_torsionBy_pic_le ℓ (fun i hdvd ↦ ?_) (fun i j hij hdvd ↦ ?_)
  · have h1 := T.mul_abs_le hT h hg i i
    have hmi := T.m_pos i
    have ha : 1 ≤ |T.a i i| := by
      have := T.diag_neg h i
      rw [abs_of_neg this]
      omega
    have : T.m i ≤ T.m i * |T.a i i| := by nlinarith
    have := Int.le_of_dvd hmi hdvd
    omega
  · have h1 := T.mul_abs_le hT h hg i j
    have hmi := T.m_pos i
    have habs : 0 < |T.a i j| := abs_pos.mpr hij
    have : |T.a i j| ≤ T.m i * |T.a i j| := by nlinarith
    have := Int.le_of_dvd habs ((dvd_abs _ _).mpr hdvd)
    omega

end Main

section GenusOne

variable {T} (hT : T.IsMinimal) (h : 1 < Fintype.card ι) (hg : T.genus = 1)
include hT h hg

/-- In a minimal numerical type of genus `1` with `n > 1`, every index is a `(-2)`-index (all the
contributions to the genus vanish, Stacks, Tag 0C7D). -/
lemma isMinusTwoIndex_of_genus_eq_one (i : ι) : T.IsMinusTwoIndex i := by
  have h2 := T.two_mul_genus
  have hsum : ∑ j, T.contrib j = 0 := by omega
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ T.contrib_nonneg hT h j).mp hsum i
    (Finset.mem_univ i)
  exact T.isMinusTwoIndex_of_contrib_eq_zero h h0

variable {i₀ : ι} (hi₀ : T.m i₀ = 1)
include hi₀

/-- A genus-one analogue of Stacks, Tag 0C9W: in a minimal numerical type of genus `1` with
`n > 1` and an index `i₀` of multiplicity `1` (the case of a model with a rational point, Stacks,
Tag 0CE8), every multiplicity is at most `2⁹`. (Stacks instead classifies the minimal numerical
types of genus `1`, Tag 0C8T.) -/
theorem m_le_of_genus_eq_one (i : ι) : T.m i ≤ 2 ^ 9 := by
  classical
  by_cases hi : i = i₀
  · subst hi
    rw [hi₀]
    norm_num
  have hP : ∀ j, j ≠ i₀ → T.a j j = -2 := fun j _ ↦
    (isMinusTwoIndex_of_genus_eq_one hT h hg j).2
  have := m_le_of_attached_le (P := fun j ↦ j ≠ i₀) hP ⟨i₀, fun h ↦ h rfl⟩ 2 (by norm_num) hi
    fun x j hx hj hxj ↦ by
      have hxi : x ≠ i₀ := of_reachable (P := fun j ↦ j ≠ i₀) hi hx
      have hj' : j = i₀ := not_not.mp hj
      subst hj'
      have hpos : 0 < T.a x j := lt_of_le_of_ne (T.nonneg x j hxi) (Ne.symm hxj)
      have h1 := (T.mul_le_of_pos hxi hpos).1
      rw [hi₀, (isMinusTwoIndex_of_genus_eq_one hT h hg j).2] at h1
      have hm := T.m_pos x
      nlinarith
  linarith

/-- A genus-one analogue of Stacks, Tag 0C9W: under the hypotheses of `m_le_of_genus_eq_one`,
`mᵢ |aᵢⱼ| ≤ 2¹⁰` for all `i, j`. -/
theorem mul_abs_le_of_genus_eq_one (i j : ι) : T.m i * |T.a i j| ≤ 2 ^ 10 := by
  have hmi := T.m_pos i
  have hdiag : ∀ k, T.m k * -T.a k k ≤ 2 ^ 10 := fun k ↦ by
    rw [(isMinusTwoIndex_of_genus_eq_one hT h hg k).2]
    have := m_le_of_genus_eq_one hT h hg hi₀ k
    linarith
  by_cases hij : i = j
  · subst hij
    rw [abs_of_neg (T.diag_neg h i)]
    exact hdiag i
  rcases (T.nonneg i j hij).lt_or_eq with hpos | h0
  · rw [abs_of_pos hpos]
    exact (T.mul_le_of_pos hij hpos).1.trans (hdiag j)
  · rw [← h0, abs_zero, mul_zero]
    positivity

/-- A genus-one analogue of Stacks, Tag 0C9X: under the hypotheses of `m_le_of_genus_eq_one`, for a
prime `ℓ > 2¹⁰`, `|Pic(T)[ℓ]| ≤ ℓ^{g_top}`. -/
theorem card_torsionBy_pic_le_of_genus_eq_one [LinearOrder ι] [Nonempty ι] (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓ : 2 ^ 10 < ℓ) :
    Nat.card (Submodule.torsionBy ℤ T.Pic (ℓ : ℤ)) ≤ ℓ ^ T.topGenus.toNat := by
  refine T.card_torsionBy_pic_le ℓ (fun i hdvd ↦ ?_) (fun i j hij hdvd ↦ ?_)
  · have h1 := mul_abs_le_of_genus_eq_one hT h hg hi₀ i i
    have hmi := T.m_pos i
    have ha : 1 ≤ |T.a i i| := by
      have := T.diag_neg h i
      rw [abs_of_neg this]
      omega
    have : T.m i ≤ T.m i * |T.a i i| := by nlinarith
    have := Int.le_of_dvd hmi hdvd
    omega
  · have h1 := mul_abs_le_of_genus_eq_one hT h hg hi₀ i j
    have hmi := T.m_pos i
    have habs : 0 < |T.a i j| := abs_pos.mpr hij
    have : |T.a i j| ≤ T.m i * |T.a i j| := by nlinarith
    have := Int.le_of_dvd habs ((dvd_abs _ _).mpr hdvd)
    omega

end GenusOne

section OneComponent

variable {T}

/-- If `n = 1`, the Picard group `ℤⁿ / A ℤⁿ = ℤ` of a numerical type has no `ℓ`-torsion. -/
theorem card_torsionBy_pic_le_one_of_card_eq_one (h : Fintype.card ι = 1) (ℓ : ℕ)
    [Fact ℓ.Prime] : Nat.card (Submodule.torsionBy ℤ T.Pic (ℓ : ℤ)) ≤ 1 := by
  classical
  have hsub : ∀ i j : ι, i = j := fun i j ↦ Fintype.card_le_one_iff.mp h.le i j
  have ha : T.a = 0 := by
    ext i j
    rw [hsub j i, T.diag_eq_zero_of_card_eq_one h i]
    rfl
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have key : ∀ c : Submodule.torsionBy ℤ T.Pic (ℓ : ℤ), c = 0 := fun c ↦ by
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ c.1
    have hc := (Submodule.mem_torsionBy_iff _ _).mp c.2
    rw [← hv, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hc
    obtain ⟨w, hw⟩ := hc
    rw [ha, Matrix.mulVecLin_apply, Matrix.zero_mulVec] at hw
    have hv0 : v = 0 := smul_right_injective (ι → ℤ) hℓ0 (by
      simp only [smul_zero]
      exact hw.symm)
    apply Subtype.ext
    rw [← hv, hv0, Submodule.Quotient.mk_zero]
    rfl
  have : Subsingleton (Submodule.torsionBy ℤ T.Pic (ℓ : ℤ)) :=
    ⟨fun c d ↦ by rw [key c, key d]⟩
  exact (Nat.card_of_subsingleton (0 : Submodule.torsionBy ℤ T.Pic (ℓ : ℤ))).le

/-- Part of Stacks, Tag 0C9X, for every minimal numerical type with weights `1` and genus
`g ≥ 2` (`n = 1` included): for a prime `ℓ > 2⁹ (6g - 6)`, `|Pic(T)[ℓ]| ≤ ℓ^{g_top}`. Deviations
from Tag 0C9X: only `dim_{𝔽_ℓ} Pic(T)[ℓ] ≤ g_top` is proved (Stacks also has `g_top ≤ g`, Tag 0C7C,
not proved here, and the bound `dim ≤ g` for every numerical type); the threshold is
`ℓ > 2⁹ (6g - 6)`, stronger than Stacks' `ℓ > 768 g`. -/
theorem card_torsionBy_pic_le_of_isMinimal [LinearOrder ι] [Nonempty ι] (hT : T.IsMinimal)
    (hg : 2 ≤ T.genus) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 2 ^ 9 * (6 * T.genus - 6) < ℓ) :
    Nat.card (Submodule.torsionBy ℤ T.Pic (ℓ : ℤ)) ≤ ℓ ^ T.topGenus.toNat := by
  rcases Nat.lt_or_ge 1 (Fintype.card ι) with h | h
  · exact card_torsionBy_pic_le_of_lt hT h hg ℓ hℓ
  · have h1 : Fintype.card ι = 1 := le_antisymm h Fintype.card_pos
    exact (card_torsionBy_pic_le_one_of_card_eq_one h1 ℓ).trans (Nat.one_le_pow _ _
      (Fact.out : ℓ.Prime).pos)

/-- Stacks, Tag 0C9W (with weights `1`, and the constant `2⁹ (6g - 6)` instead of `768 g`), for
every minimal numerical type of genus `g ≥ 2`, `n = 1` included (there `a₁₁ = 0`):
`mᵢ |aᵢⱼ| ≤ 2⁹ (6g - 6)` for all `i, j`. -/
theorem mul_abs_le_of_isMinimal (hT : T.IsMinimal) (hg : 2 ≤ T.genus) (i j : ι) :
    T.m i * |T.a i j| ≤ 2 ^ 9 * (6 * T.genus - 6) := by
  rcases Nat.lt_or_ge 1 (Fintype.card ι) with h | h
  · exact T.mul_abs_le hT h hg i j
  · have h1 : Fintype.card ι = 1 := le_antisymm h (Fintype.card_pos_iff.mpr ⟨i⟩)
    have hji : j = i := Fintype.card_le_one_iff.mp h1.le j i
    rw [hji, T.diag_eq_zero_of_card_eq_one h1 i, abs_zero, mul_zero]
    omega

end OneComponent

end NumericalType

end AlgebraicGeometry
