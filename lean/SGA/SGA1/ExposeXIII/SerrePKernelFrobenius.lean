/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.RingTheory.Discriminant
import SGA.SGA1.ExposeI.Discriminant
import SGA.SGA1.ExposeXIII.SerrePKernelCounting

/-!
# Frobenius on a finite étale `k[T]`-algebra multiplies degrees by `p`

An input of Serre's degree count (`SGA.SGA1.ExposeXIII.SerrePKernelCounting`), used for Serre's
theorem on `p`-group kernels in Raynaud's proof of XIII.2.13. In characteristic `p`:

* `trace_pow_char`: `tr(Mᵖ) = tr(M)ᵖ` for matrices over any commutative ring (from
  `charpoly_pow_char`: the characteristic polynomial of `Mᵖ` is that of `M` with coefficients
  raised to the `p`-th power);
* `discr_pow_char`: the discriminant of the `p`-th powers of a basis is the `p`-th power of the
  discriminant, so the matrix of the `p`-th powers of a basis is invertible when the discriminant
  is a unit (`isUnit_det_frobMatrix`), e.g. for finite étale algebras (I.4.10,
  `SGA.SGA1.ExposeI.etale_iff_isUnit_discr`);
* `exists_deg_pow_char_bounds`, `exists_deg_pow_char_bounds_pi`: for a finite free `k[T]`-algebra
  with unit discriminant, `p deg x - c₀ ≤ deg xᵖ ≤ p deg x + c₂` in the coordinates of a basis.
-/

universe u

namespace SGA.SGA1.ExposeXIII

namespace SerrePKernel

open Polynomial Matrix Module

section CharpolyFrobenius

variable {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R] (p : ℕ)
  [hp : Fact p.Prime] [CharP R p]

/-- In characteristic `p`, the characteristic polynomial of `Mᵖ` is that of `M` with its
coefficients raised to the `p`-th power. -/
theorem charpoly_pow_char (M : Matrix n n R) :
    (M ^ p).charpoly = M.charpoly.map (frobenius R p) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [Matrix.charpoly, Matrix.det_isEmpty]
  apply expand_injective hp.out.pos
  rw [← map_expand, map_frobenius_expand]
  unfold charpoly
  rw [AlgHom.map_det, ← coe_detMonoidHom, ← (detMonoidHom : Matrix n n R[X] →* R[X]).map_pow]
  apply congr_arg det
  refine matPolyEquiv.injective ?_
  rw [map_pow, matPolyEquiv_charmatrix, sub_pow_char_of_commute p (commute_X (C M)), ← C_pow]
  exact (id (matPolyEquiv_eq_X_pow_sub_C p M) :)

/-- In characteristic `p`, `tr(Mᵖ) = tr(M)ᵖ`. -/
theorem trace_pow_char (M : Matrix n n R) : trace (M ^ p) = trace M ^ p := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [Matrix.trace, zero_pow hp.out.ne_zero]
  rw [trace_eq_neg_charpoly_coeff, trace_eq_neg_charpoly_coeff, charpoly_pow_char, coeff_map,
    frobenius_def, neg_pow, neg_one_pow_char R p, neg_one_mul]

end CharpolyFrobenius

section Discriminant

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) [hp : Fact p.Prime]
  [CharP A p] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- In characteristic `p`, the trace of `xᵖ` is the `p`-th power of the trace of `x`. -/
theorem trace_pow_char_of_basis [Finite ι] (b : Basis ι A B) (x : B) :
    Algebra.trace A B (x ^ p) = Algebra.trace A B x ^ p := by
  classical
  have := Fintype.ofFinite ι
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace b, map_pow, trace_pow_char]

/-- In characteristic `p`, the discriminant of the `p`-th powers of a basis is the `p`-th power of
its discriminant. -/
theorem discr_pow_char (b : Basis ι A B) :
    Algebra.discr A (fun i ↦ b i ^ p) = Algebra.discr A b ^ p := by
  rw [Algebra.discr_def, Algebra.discr_def, ← frobenius_def, RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, frobenius_def]
  rw [← mul_pow, trace_pow_char_of_basis p b]

/-- The matrix of the `p`-th powers of a basis in that basis. -/
noncomputable def frobMatrix (b : Basis ι A B) : Matrix ι ι A :=
  Matrix.of fun i j ↦ b.repr (b i ^ p) j

omit hp [CharP A p] [DecidableEq ι] in
lemma frobMatrix_mulVec (b : Basis ι A B) :
    (frobMatrix p b).map (algebraMap A B) *ᵥ b = fun i ↦ b i ^ p := by
  ext i
  rw [mulVec, dotProduct]
  conv_rhs => rw [← b.sum_repr (b i ^ p)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [frobMatrix, Algebra.smul_def]

/-- If `B` is étale over `A`, the matrix of the `p`-th powers of a basis is invertible. -/
theorem isUnit_det_frobMatrix (b : Basis ι A B) (hd : IsUnit (Algebra.discr A b)) :
    IsUnit (frobMatrix p b).det := by
  have h := Algebra.discr_of_matrix_mulVec b (frobMatrix p b)
  rw [frobMatrix_mulVec, discr_pow_char] at h
  have h2 : IsUnit ((frobMatrix p b).det ^ 2 * Algebra.discr A b) := h ▸ hd.pow p
  exact (isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_left h2)

end Discriminant

lemma exists_le_of_finite {α : Type*} [Finite α] (f : α → ℕ) : ∃ c, ∀ a, f a ≤ c :=
  have := Fintype.ofFinite α
  ⟨Finset.univ.sup f, fun a ↦ Finset.le_sup (Finset.mem_univ a)⟩

section Degree

variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] {B : Type*} [CommRing B]
  [CharP B p] [Algebra k[X] B] {I : Type*} [Fintype I] [DecidableEq I] (b : Basis I k[X] B)

omit [CharP k p] [DecidableEq I] in
/-- The coordinates of `xᵖ`: `(xᵖ)ⱼ = ∑ᵢ xᵢᵖ Cᵢⱼ` with `C = frobMatrix p b`. -/
lemma repr_pow_char (x : B) (j : I) :
    b.repr (x ^ p) j = ∑ i, (b.repr x i) ^ p * frobMatrix p b i j := by
  conv_lhs => rw [← b.sum_repr x]
  rw [sum_pow_char, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_pow, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rfl

/-- If `B` is finite étale over `k[T]` (its discriminant is a unit), the Frobenius `x ↦ xᵖ`
multiplies degrees by `p`, up to bounded errors. -/
theorem exists_deg_pow_char_bounds (hd : IsUnit (Algebra.discr k[X] b)) :
    ∃ c₀ c₂ : ℕ, ∀ x : B, p * deg b x ≤ deg b (x ^ p) + c₀ ∧ deg b (x ^ p) ≤ p * deg b x + c₂ := by
  obtain ⟨D, hCD⟩ : ∃ D : Matrix I I k[X], frobMatrix p b * D = 1 :=
    ⟨_, Matrix.mul_nonsing_inv _ (isUnit_det_frobMatrix p b hd)⟩
  obtain ⟨c₀, hc₀⟩ := exists_le_of_finite fun ij : I × I ↦ (D ij.1 ij.2).natDegree
  obtain ⟨c₂, hc₂⟩ := exists_le_of_finite fun ij : I × I ↦ (frobMatrix p b ij.1 ij.2).natDegree
  refine ⟨c₀, c₂, fun x ↦ ⟨?_, ?_⟩⟩
  · rcases isEmpty_or_nonempty I with hI | hI
    · simp [deg]
    obtain ⟨i, hi⟩ := exists_natDegree_repr_eq b x
    rw [← hi]
    have hv : (b.repr x i) ^ p = ∑ j, b.repr (x ^ p) j * D j i := by
      have h1 : (fun j ↦ b.repr (x ^ p) j) = (fun i ↦ (b.repr x i) ^ p) ᵥ* frobMatrix p b := by
        ext j
        rw [repr_pow_char, vecMul, dotProduct]
      have h2 : (fun j ↦ b.repr (x ^ p) j) ᵥ* D = fun i ↦ (b.repr x i) ^ p := by
        rw [h1, vecMul_vecMul, hCD, vecMul_one]
      have := congrFun h2 i
      rw [vecMul, dotProduct] at this
      exact this.symm
    have h3 := congrArg natDegree hv
    rw [natDegree_pow] at h3
    rw [h3]
    exact natDegree_sum_le_of_forall_le _ _ fun j _ ↦ natDegree_mul_le.trans
      (Nat.add_le_add (natDegree_repr_le_deg b _ j) (hc₀ (j, i)))
  · rw [deg_le_iff]
    intro j
    rw [repr_pow_char]
    exact natDegree_sum_le_of_forall_le _ _ fun i _ ↦ natDegree_mul_le.trans
      (Nat.add_le_add (natDegree_pow_le.trans (Nat.mul_le_mul_left p
        (natDegree_repr_le_deg b x i))) (hc₂ (i, j)))

omit [CharP k p] [DecidableEq I] in
lemma deg_pi_apply_le {ι : Type*} [Fintype ι] (w : ι → B) (i : ι) :
    deg b (w i) ≤ deg (Pi.basis fun _ : ι ↦ b) w := by
  rw [deg_le_iff]
  intro j
  have := natDegree_repr_le_deg (Pi.basis fun _ : ι ↦ b) w ⟨i, j⟩
  rwa [Pi.basis_repr] at this

omit [CharP k p] [DecidableEq I] in
lemma deg_pi_le_iff {ι : Type*} [Fintype ι] {w : ι → B} {E : ℕ} :
    deg (Pi.basis fun _ : ι ↦ b) w ≤ E ↔ ∀ i, deg b (w i) ≤ E := by
  refine ⟨fun h i ↦ (deg_pi_apply_le b w i).trans h, fun h ↦ (deg_le_iff _).mpr fun ⟨i, j⟩ ↦ ?_⟩
  rw [Pi.basis_repr]
  exact (natDegree_repr_le_deg b (w i) j).trans (h i)

/-- The degree bounds for the coordinatewise Frobenius on `Bᶥ`. -/
theorem exists_deg_pow_char_bounds_pi (hd : IsUnit (Algebra.discr k[X] b)) {ι : Type*}
    [Fintype ι] : ∃ c₀ c₂ : ℕ, ∀ w : ι → B,
      p * deg (Pi.basis fun _ : ι ↦ b) w ≤ deg (Pi.basis fun _ : ι ↦ b) (fun i ↦ w i ^ p) + c₀ ∧
      deg (Pi.basis fun _ : ι ↦ b) (fun i ↦ w i ^ p) ≤ p * deg (Pi.basis fun _ : ι ↦ b) w + c₂ := by
  obtain ⟨c₀, c₂, h⟩ := exists_deg_pow_char_bounds p b hd
  refine ⟨c₀, c₂, fun w ↦ ⟨?_, ?_⟩⟩
  · rcases isEmpty_or_nonempty ι with hι | hι
    · have : deg (Pi.basis fun _ : ι ↦ b) w = 0 :=
        Nat.le_zero.mp ((deg_pi_le_iff b).mpr fun i ↦ (IsEmpty.false i).elim)
      rw [this, mul_zero]
      exact Nat.zero_le _
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
        fun i ↦ deg b (w i)
      have hw : deg (Pi.basis fun _ : ι ↦ b) w = deg b (w i) :=
        le_antisymm ((deg_pi_le_iff b).mpr fun i' ↦ hi ▸
          Finset.le_sup (f := fun i ↦ deg b (w i)) (Finset.mem_univ i'))
          (deg_pi_apply_le b w i)
      rw [hw]
      exact (h (w i)).1.trans (Nat.add_le_add_right
        (deg_pi_apply_le b (fun i ↦ w i ^ p) i) _)
  · rw [deg_pi_le_iff]
    intro i
    exact (h (w i)).2.trans (Nat.add_le_add_right (Nat.mul_le_mul_left p
      (deg_pi_apply_le b w i)) _)

end Degree

end SerrePKernel

end SGA.SGA1.ExposeXIII
