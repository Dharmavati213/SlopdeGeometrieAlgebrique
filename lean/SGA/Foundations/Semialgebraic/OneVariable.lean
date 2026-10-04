/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Semialgebraic.Definable
import SGA.Foundations.Semialgebraic.Line

/-!
# Semialgebraic subsets of `ℝ` and semialgebraic functions of one variable

`Real.IsSemialgebraicSet A`: `A ⊆ ℝ` is semialgebraic; `Real.IsSemialgebraicFun f`: the graph of
`f : ℝ → ℝ` is semialgebraic. A semialgebraic subset of `ℝ` is a finite union of points and open
intervals (`Real.IsSemialgebraicSet.exists_finset`); in particular an infinite one contains an
open interval (`Real.IsSemialgebraicSet.exists_Ioo_subset_of_infinite`), and near each point it is
on each side either everything or nothing (`Real.IsSemialgebraicSet.eventually_right`,
`Real.IsSemialgebraicSet.eventually_left`): this *o-minimality* is all that the theory of
semialgebraic functions of one variable uses.

For first-order definitions involving `f`, `Real.IsSemialgebraicFun.subst` substitutes the value
`f (v i)` into a coordinate `k` of `ℝ^ι`: `{v | v[k ↦ f (v i)] ∈ S}` is semialgebraic if `S` is.

## References

* [L. van den Dries, *Tame topology and o-minimal structures*, Chapter 1][vdD]
* [J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, §2.1][BCR]
-/

open Set hiding ofPred_and ofPred_or ofPred_exists ofPred_forall
open MvPolynomial

variable {ι : Type*}

/-! ### Coordinate conditions -/

namespace IsSemialgebraic

lemma ofPred_coord_lt_coord (i j : ι) : IsSemialgebraic {v : ι → ℝ | v i < v j} := by
  simpa using IsSemialgebraic.lt (X i) (X j)

lemma ofPred_coord_le_coord (i j : ι) : IsSemialgebraic {v : ι → ℝ | v i ≤ v j} := by
  simpa using IsSemialgebraic.le (X i) (X j)

lemma ofPred_coord_eq_coord (i j : ι) : IsSemialgebraic {v : ι → ℝ | v i = v j} := by
  simpa using IsSemialgebraic.eq (X i) (X j)

lemma ofPred_const_lt_coord (a : ℝ) (i : ι) : IsSemialgebraic {v : ι → ℝ | a < v i} := by
  simpa using IsSemialgebraic.lt (C a) (X i)

lemma ofPred_coord_lt_const (i : ι) (a : ℝ) : IsSemialgebraic {v : ι → ℝ | v i < a} := by
  simpa using IsSemialgebraic.lt (X i) (C a)

lemma ofPred_coord_eq_const (i : ι) (a : ℝ) : IsSemialgebraic {v : ι → ℝ | v i = a} := by
  simpa using IsSemialgebraic.eq (X i) (C a)

lemma ofPred_coord_mem_Ioo (i : ι) (a b : ℝ) : IsSemialgebraic {v : ι → ℝ | v i ∈ Ioo a b} :=
  (ofPred_const_lt_coord a i).inter (ofPred_coord_lt_const i b)

end IsSemialgebraic

namespace Real

/-! ### Semialgebraic subsets of `ℝ` -/

/-- A subset of `ℝ` is *semialgebraic* if it is semialgebraic as a subset of `ℝ¹`. -/
def IsSemialgebraicSet (A : Set ℝ) : Prop := IsSemialgebraic {v : Unit → ℝ | v () ∈ A}

namespace IsSemialgebraicSet

variable {A B : Set ℝ}

/-- `A ⊆ ℝ` is semialgebraic iff the set of `v ∈ ℝ^ι` with `v i ∈ A` is. -/
lemma iff_coord (i : ι) : IsSemialgebraicSet A ↔ IsSemialgebraic {v : ι → ℝ | v i ∈ A} :=
  ⟨fun h ↦ h.preimage_comp (fun _ : Unit ↦ i), fun h ↦ h.preimage_comp (fun _ : ι ↦ ())⟩

lemma coord (hA : IsSemialgebraicSet A) (i : ι) : IsSemialgebraic {v : ι → ℝ | v i ∈ A} :=
  (iff_coord i).mp hA

lemma of_coord (i : ι) (h : IsSemialgebraic {v : ι → ℝ | v i ∈ A}) : IsSemialgebraicSet A :=
  (iff_coord i).mpr h

lemma inter (hA : IsSemialgebraicSet A) (hB : IsSemialgebraicSet B) :
    IsSemialgebraicSet (A ∩ B) :=
  IsSemialgebraic.inter hA hB

lemma union (hA : IsSemialgebraicSet A) (hB : IsSemialgebraicSet B) :
    IsSemialgebraicSet (A ∪ B) :=
  IsSemialgebraic.union hA hB

lemma compl (hA : IsSemialgebraicSet A) : IsSemialgebraicSet Aᶜ :=
  IsSemialgebraic.compl hA

/-- The preimage of a semialgebraic subset of `ℝ` under `x ↦ -x` is semialgebraic. -/
lemma preimage_neg (hA : IsSemialgebraicSet A) : IsSemialgebraicSet ((fun x ↦ -x) ⁻¹' A) := by
  unfold IsSemialgebraicSet at hA ⊢
  convert IsSemialgebraic.preimage_polynomialMap (fun _ : Unit ↦ -X ()) hA using 1
  ext v
  simp

/-- A semialgebraic subset of `ℝ` is a finite union of points and intervals: membership is
constant on the intervals `[t, t']` avoiding a finite set `Z`. -/
theorem exists_finset (hA : IsSemialgebraicSet A) :
    ∃ Z : Finset ℝ, ∀ t t', t ≤ t' → (∀ z ∈ Z, z ∉ Icc t t') → (t ∈ A ↔ t' ∈ A) := by
  obtain ⟨Z, hZ⟩ := IsSemialgebraic.exists_finset_mem_iff_line hA 0 1
  refine ⟨Z, fun t t' htt' h ↦ ?_⟩
  have := hZ t t' htt' h
  simpa using this

/-- An infinite semialgebraic subset of `ℝ` contains an open interval. -/
theorem exists_Ioo_subset_of_infinite (hA : IsSemialgebraicSet A) (hinf : A.Infinite) :
    ∃ a b, a < b ∧ Ioo a b ⊆ A := by
  obtain ⟨Z, hZ⟩ := hA.exists_finset
  obtain ⟨t, htA, htZ⟩ := (hinf.sdiff Z.finite_toSet).nonempty
  obtain ⟨δ, hδ, hδZ⟩ := Metric.isOpen_iff.mp Z.finite_toSet.isClosed.isOpen_compl t htZ
  refine ⟨t - δ, t + δ, by linarith, fun s hs ↦ ?_⟩
  have hball (u : ℝ) (hu : u ∈ Icc (min s t) (max s t)) : u ∈ Metric.ball t δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have h1 := hu.1; have h2 := hu.2
    rw [min_le_iff] at h1; rw [le_max_iff] at h2
    constructor
    · rcases h1 with h1 | h1 <;> linarith [hs.1]
    · rcases h2 with h2 | h2 <;> linarith [hs.2]
  have hiff := hZ (min s t) (max s t) min_le_max fun z hz hzI ↦ hδZ (hball z hzI) hz
  rcases le_total s t with h | h
  · rw [min_eq_left h, max_eq_right h] at hiff
    exact hiff.mpr htA
  · rw [min_eq_right h, max_eq_left h] at hiff
    exact hiff.mp htA

/-- Just to the right of a point, a semialgebraic subset of `ℝ` is everything or nothing. -/
theorem eventually_right (hA : IsSemialgebraicSet A) (x : ℝ) :
    ∃ δ > 0, Ioo x (x + δ) ⊆ A ∨ Disjoint (Ioo x (x + δ)) A := by
  obtain ⟨δ, hδ, h⟩ := IsSemialgebraic.exists_pos_line hA 0 1 x
  refine ⟨δ, hδ, h.imp (fun h t ht ↦ by simpa using h t ht) fun h ↦ ?_⟩
  exact disjoint_left.mpr fun t ht htA ↦ h t ht (by simpa using htA)

/-- Just to the left of a point, a semialgebraic subset of `ℝ` is everything or nothing. -/
theorem eventually_left (hA : IsSemialgebraicSet A) (x : ℝ) :
    ∃ δ > 0, Ioo (x - δ) x ⊆ A ∨ Disjoint (Ioo (x - δ) x) A := by
  obtain ⟨δ, hδ, h⟩ := IsSemialgebraic.exists_pos_line hA (fun _ ↦ x) (fun _ ↦ -1) 0
  refine ⟨δ, hδ, h.imp (fun h t ht ↦ ?_) fun h ↦ ?_⟩
  · have := h (x - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa [sub_eq_add_neg] using this
  · refine disjoint_left.mpr fun t ht htA ↦ h (x - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ ?_
    simpa [sub_eq_add_neg] using htA

end IsSemialgebraicSet

lemma isSemialgebraicSet_Ioo (a b : ℝ) : IsSemialgebraicSet (Ioo a b) :=
  .of_coord () (IsSemialgebraic.ofPred_coord_mem_Ioo () a b)

lemma isSemialgebraicSet_Ioi (a : ℝ) : IsSemialgebraicSet (Ioi a) :=
  .of_coord () (IsSemialgebraic.ofPred_const_lt_coord a ())

lemma isSemialgebraicSet_Iio (a : ℝ) : IsSemialgebraicSet (Iio a) :=
  .of_coord () (IsSemialgebraic.ofPred_coord_lt_const () a)

lemma isSemialgebraicSet_singleton (a : ℝ) : IsSemialgebraicSet {a} :=
  .of_coord () (IsSemialgebraic.ofPred_coord_eq_const () a)

/-! ### Semialgebraic functions of one variable -/

/-- A function `f : ℝ → ℝ` is *semialgebraic* if its graph is a semialgebraic subset of `ℝ²`. -/
def IsSemialgebraicFun (f : ℝ → ℝ) : Prop := IsSemialgebraic {v : Fin 2 → ℝ | f (v 0) = v 1}

namespace IsSemialgebraicFun

variable {f : ℝ → ℝ}

/-- `x ↦ -f x` is semialgebraic. -/
lemma neg (hf : IsSemialgebraicFun f) : IsSemialgebraicFun fun x ↦ -f x := by
  unfold IsSemialgebraicFun at hf ⊢
  refine (congrArg IsSemialgebraic ?_).mpr (IsSemialgebraic.preimage_polynomialMap ![X 0, -X 1] hf)
  ext v
  simp [neg_eq_iff_eq_neg]

/-- `x ↦ f (-x)` is semialgebraic. -/
lemma comp_neg (hf : IsSemialgebraicFun f) : IsSemialgebraicFun fun x ↦ f (-x) := by
  unfold IsSemialgebraicFun at hf ⊢
  refine (congrArg IsSemialgebraic ?_).mpr (IsSemialgebraic.preimage_polynomialMap ![-X 0, X 1] hf)
  ext v
  simp

/-- The graph of a semialgebraic function, in coordinates `i`, `j` of `ℝ^ι`. -/
lemma graph (hf : IsSemialgebraicFun f) (i j : ι) :
    IsSemialgebraic {v : ι → ℝ | f (v i) = v j} :=
  hf.preimage_comp ![i, j]

/-- Substituting the value of a semialgebraic function: `{v | v[k ↦ f (v i)] ∈ S}` is semialgebraic
if `S` is, for `i ≠ k`. -/
theorem subst [DecidableEq ι] (hf : IsSemialgebraicFun f) {S : Set (ι → ℝ)}
    (hS : IsSemialgebraic S) {i k : ι} (hik : i ≠ k) :
    IsSemialgebraic {v : ι → ℝ | Function.update v k (f (v i)) ∈ S} := by
  convert (hS.inter (hf.graph i k)).exists_update k using 1
  ext v
  simp only [mem_ofPred_eq, mem_inter_iff, Function.update_self, Function.update_of_ne hik]
  exact ⟨fun h ↦ ⟨_, h, rfl⟩, fun ⟨t, h, ht⟩ ↦ ht ▸ h⟩

/-- The preimage of a semialgebraic subset of `ℝ` under a semialgebraic function is
semialgebraic. -/
theorem preimage (hf : IsSemialgebraicFun f) {A : Set ℝ} (hA : IsSemialgebraicSet A) :
    IsSemialgebraicSet (f ⁻¹' A) := by
  refine IsSemialgebraicSet.of_coord (0 : Fin 2) ?_
  convert hf.subst (hA.coord (1 : Fin 2)) (show (0 : Fin 2) ≠ 1 by decide) using 1
  ext v
  simp

/-- The image of a semialgebraic subset of `ℝ` under a semialgebraic function is
semialgebraic. -/
theorem image (hf : IsSemialgebraicFun f) {A : Set ℝ} (hA : IsSemialgebraicSet A) :
    IsSemialgebraicSet (f '' A) := by
  refine IsSemialgebraicSet.of_coord (1 : Fin 2) ?_
  convert ((hA.coord (0 : Fin 2)).inter hf).exists_update (0 : Fin 2) using 1
  ext v
  simp only [mem_image, mem_ofPred_eq, mem_inter_iff, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]

end IsSemialgebraicFun

end Real
