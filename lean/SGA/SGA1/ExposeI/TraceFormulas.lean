/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.Trace.Basic
import SGA.SGA1.ExposeI.StandardEtale

/-!
# SGA 1, Exposé I, I.9.6–I.9.8: Euler's trace formulas

Let `K` be a ring, `F ∈ K[t]` monic of degree `n`, `L = K[t]/(F)` and `u` the class of `t`.
Let `φ : L → K` be the coefficient of `u^(n-1)` in the basis `1, u, …, u^(n-1)` (`lastCoeff`).
Then `Tr_{L/K}(y) = φ(F'(u) y)` for every `y ∈ L` (`trace_eq_lastCoeff_mul`); no separability
is needed. When `F` is separable, `F'(u)` is a unit and this gives Euler's formulas I.9.6:
`Tr_{L/K}(uⁱ/F'(u)) = 0` for `i < n - 1` and `= 1` for `i = n - 1`; then I.9.7 (the
determinant `(-1)^(n(n-1)/2)`) and I.9.8 (the trace dual of `A[u]` is spanned by the
`uⁱ/F'(u)`).

The proof is the classical one with a dual basis: write `F(t) = (t - u) ∑ bᵢ tⁱ` in `L[t]`
(`quotientByRoot`); the map `z ↦ ∑ φ(z bᵢ) uⁱ` commutes with multiplication by `u` (because
`F(u) = 0`) and fixes `1`, so it is the identity (`sum_lastCoeff_mul_root_pow`). Hence the
`bᵢ` are `φ`-dual to the `uⁱ`, and `Tr(y) = ∑ φ(y uⁱ bᵢ) = φ(y ∑ bᵢ uⁱ) = φ(y F'(u))`.

In I.9.8 SGA takes `A ⊆ K` without saying that `F` must have coefficients in `A` (as it does in
its application I.9.9); this hypothesis is needed.
-/

universe u

open Polynomial

namespace SGA.SGA1.ExposeI

variable {K : Type*} [CommRing K] {F : K[X]}

/-- The coefficient of `u^(n-1)` in the basis `1, u, …, u^(n-1)` of `K[t]/(F)`, `F` monic of
degree `n`. -/
noncomputable def lastCoeff (hF : F.Monic) : AdjoinRoot F →ₗ[K] K :=
  (lcoeff K (F.natDegree - 1)).comp (AdjoinRoot.modByMonicHom hF)

lemma lastCoeff_root_pow (hF : F.Monic) {e : ℕ} (he : e < F.natDegree) :
    lastCoeff hF (AdjoinRoot.root F ^ e) = if e = F.natDegree - 1 then 1 else 0 := by
  nontriviality K
  rw [lastCoeff, LinearMap.comp_apply, ← AdjoinRoot.mk_X, ← map_pow,
    AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hF).mpr, lcoeff_apply, coeff_X_pow]
  · simp [eq_comm]
  · rw [degree_X_pow, degree_eq_natDegree hF.ne_zero]; exact_mod_cast he

/-- The quotient `F(t) / (t - u)` in `L[t]`, `L = K[t]/(F)`. -/
noncomputable abbrev quotientByRoot (F : K[X]) : (AdjoinRoot F)[X] :=
  F.map (algebraMap K (AdjoinRoot F)) /ₘ (X - C (AdjoinRoot.root F))

lemma X_sub_C_mul_quotientByRoot (F : K[X]) :
    (X - C (AdjoinRoot.root F)) * quotientByRoot F = F.map (algebraMap K (AdjoinRoot F)) := by
  rw [mul_divByMonic_eq_iff_isRoot, AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.isRoot_root F

/-- `F'(u) = (F(t) / (t - u))(u)`. -/
lemma eval_quotientByRoot (F : K[X]) :
    (quotientByRoot F).eval (AdjoinRoot.root F) = aeval (AdjoinRoot.root F) (derivative F) := by
  have h := congrArg (fun p ↦ (derivative p).eval (AdjoinRoot.root F))
    (X_sub_C_mul_quotientByRoot F)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero,
    derivative_map, eval_map_algebraMap] at h
  exact h

lemma coeff_quotientByRoot (hF : F.Monic) [Nontrivial (AdjoinRoot F)] (i : ℕ) :
    (quotientByRoot F).coeff i = ∑ j ∈ Finset.Icc (i + 1) F.natDegree,
      AdjoinRoot.root F ^ (j - (i + 1)) * algebraMap K (AdjoinRoot F) (F.coeff j) := by
  rw [coeff_divByMonic_X_sub_C, hF.natDegree_map]
  simp only [coeff_map]

lemma coeff_quotientByRoot_rec (F : K[X]) (i : ℕ) :
    (quotientByRoot F).coeff i = algebraMap K (AdjoinRoot F) (F.coeff (i + 1)) +
      AdjoinRoot.root F * (quotientByRoot F).coeff (i + 1) := by
  rw [coeff_divByMonic_X_sub_C_rec, coeff_map]

lemma root_mul_coeff_quotientByRoot_zero (F : K[X]) :
    AdjoinRoot.root F * (quotientByRoot F).coeff 0 = -algebraMap K (AdjoinRoot F) (F.coeff 0) := by
  have h := congrArg (coeff · 0) (X_sub_C_mul_quotientByRoot F)
  simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_mul,
    coeff_map] at h
  rw [← h, neg_neg]

lemma natDegree_pos_of_nontrivial (hF : F.Monic) [Nontrivial (AdjoinRoot F)] :
    0 < F.natDegree := by
  by_contra h
  have hF1 : F = 1 := hF.natDegree_eq_zero.mp (by omega)
  have : (1 : AdjoinRoot F) = 0 := by
    rw [← map_one (AdjoinRoot.mk F), AdjoinRoot.mk_eq_zero, hF1]
  exact one_ne_zero this

/-- `φ(bᵢ) = δ_{i,0}` for the coefficients `bᵢ` of `F(t)/(t - u)`. -/
lemma lastCoeff_coeff_quotientByRoot (hF : F.Monic) [Nontrivial (AdjoinRoot F)] (i : ℕ) :
    lastCoeff hF ((quotientByRoot F).coeff i) = if i = 0 then 1 else 0 := by
  have hn := natDegree_pos_of_nontrivial hF
  rw [coeff_quotientByRoot hF, map_sum]
  have h (j : ℕ) (hj : j ∈ Finset.Icc (i + 1) F.natDegree) :
      lastCoeff hF (AdjoinRoot.root F ^ (j - (i + 1)) *
        algebraMap K (AdjoinRoot F) (F.coeff j)) = if j = F.natDegree ∧ i = 0 then 1 else 0 := by
    rw [Finset.mem_Icc] at hj
    rw [mul_comm, ← Algebra.smul_def, map_smul, lastCoeff_root_pow hF (by omega), smul_eq_mul]
    by_cases hji : j = F.natDegree ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := hji
      simp [hF.coeff_natDegree]
    · simp only [show j - (i + 1) ≠ F.natDegree - 1 by omega, hji, ite_false, mul_zero]
  rw [Finset.sum_congr rfl h]
  by_cases hi : i = 0
  · subst hi
    simp only [and_true, ite_true]
    rw [Finset.sum_ite_eq']
    simp [show 1 ≤ F.natDegree from hn]
  · simp [hi]

/-- The dual basis: for `F` monic, every `z ∈ L = K[t]/(F)` is `∑ φ(z bᵢ) uⁱ`, where the `bᵢ`
are the coefficients of `F(t)/(t - u)`. The map `z ↦ ∑ φ(z bᵢ) uⁱ` commutes with
multiplication by `u` (because `F(u) = 0`) and fixes `1`. -/
theorem sum_lastCoeff_mul_root_pow (hF : F.Monic) (z : AdjoinRoot F) :
    ∑ i ∈ Finset.range F.natDegree, algebraMap K (AdjoinRoot F)
      (lastCoeff hF (z * (quotientByRoot F).coeff i)) * AdjoinRoot.root F ^ i = z := by
  nontriviality AdjoinRoot F
  set u := AdjoinRoot.root F
  set b := fun i ↦ (quotientByRoot F).coeff i
  set φ := lastCoeff hF
  set alg := algebraMap K (AdjoinRoot F)
  obtain ⟨m, hm⟩ : ∃ m, F.natDegree = m + 1 :=
    ⟨F.natDegree - 1, by have := natDegree_pos_of_nontrivial hF; omega⟩
  let Ψ : AdjoinRoot F → AdjoinRoot F := fun z ↦
    ∑ i ∈ Finset.range F.natDegree, alg (φ (z * b i)) * u ^ i
  change Ψ z = z
  -- `b_m = 1` and `u^(m+1) = -∑ aᵢ uⁱ`
  have hbm : b m = 1 := by
    simp only [b, coeff_quotientByRoot hF, hm, Finset.Icc_self, Finset.sum_singleton,
      Nat.sub_self, pow_zero, one_mul]
    rw [← hm, hF.coeff_natDegree, map_one]
  have hum : u ^ (m + 1) = -(alg (F.coeff 0) +
      ∑ i ∈ Finset.range m, alg (F.coeff (i + 1)) * u ^ (i + 1)) := by
    have h := AdjoinRoot.aeval_eq (f := F) F
    rw [AdjoinRoot.mk_self, aeval_eq_sum_range, hm, Finset.sum_range_succ, ← hm,
      hF.coeff_natDegree, one_smul, hm, Finset.sum_range_succ'] at h
    simp only [Algebra.smul_def, pow_zero, mul_one] at h
    rw [eq_neg_iff_add_eq_zero]
    linear_combination h
  -- `Ψ` commutes with multiplication by `u`
  have hcomm (z : AdjoinRoot F) : Ψ (u * z) = u * Ψ z := by
    have h1 (i : ℕ) : φ (u * z * b (i + 1)) = φ (z * b i) - F.coeff (i + 1) * φ z := by
      have : u * z * b (i + 1) = z * b i - F.coeff (i + 1) • z := by
        rw [show b i = _ from coeff_quotientByRoot_rec F i, Algebra.smul_def]
        ring
      rw [this, map_sub, map_smul, smul_eq_mul]
    have h0 : φ (u * z * b 0) = -(F.coeff 0 * φ z) := by
      have : u * z * b 0 = -(F.coeff 0 • z) := by
        rw [mul_comm u z, mul_assoc, show u * b 0 = _ from root_mul_coeff_quotientByRoot_zero F,
          Algebra.smul_def]
        ring
      rw [this, map_neg, map_smul, smul_eq_mul]
    have lhs : Ψ (u * z) = ∑ i ∈ Finset.range m,
        (alg (φ (z * b i)) - alg (F.coeff (i + 1)) * alg (φ z)) * u ^ (i + 1) -
          alg (F.coeff 0) * alg (φ z) := by
      simp only [Ψ]
      rw [hm, Finset.sum_range_succ']
      simp only [h1, h0, map_sub, map_mul, map_neg, pow_zero, mul_one]
      ring
    have rhs : u * Ψ z = ∑ i ∈ Finset.range m, alg (φ (z * b i)) * u ^ (i + 1) +
        alg (φ z) * u ^ (m + 1) := by
      simp only [Ψ]
      rw [hm, Finset.sum_range_succ, hbm, mul_one, mul_add, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ ↦ by ring
      · ring
    have e : ∑ i ∈ Finset.range m, alg (F.coeff (i + 1)) * alg (φ z) * u ^ (i + 1) =
        alg (φ z) * ∑ i ∈ Finset.range m, alg (F.coeff (i + 1)) * u ^ (i + 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [lhs, rhs, hum]
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e]
    ring
  -- hence `Ψ` fixes every polynomial in `u`
  have hb (i : ℕ) : φ (b i) = if i = 0 then 1 else 0 := lastCoeff_coeff_quotientByRoot hF i
  have hone : Ψ 1 = 1 := by
    simp only [Ψ, one_mul]
    rw [Finset.sum_eq_single 0 (fun i _ hi ↦ by simp [hb, hi])
      (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h)]
    simp [hb]
  have hlin (a : K) (z : AdjoinRoot F) : Ψ (alg a * z) = alg a * Ψ z := by
    simp only [Ψ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have : alg a * z * b i = a • (z * b i) := by rw [Algebra.smul_def]; ring
    rw [this, map_smul, smul_eq_mul, map_mul]
    ring
  have hadd (z w : AdjoinRoot F) : Ψ (z + w) = Ψ z + Ψ w := by
    simp only [Ψ, add_mul, map_add, ← Finset.sum_add_distrib]
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    induction p using Polynomial.induction_on with
    | C a =>
      have : AdjoinRoot.mk F (C a) = alg a * 1 := by
        rw [AdjoinRoot.mk_C, mul_one]
        rfl
      rw [this, hlin, hone]
    | add p q hp hq => rw [map_add, hadd, hp, hq]
    | monomial n a ih =>
      have : C a * X ^ (n + 1) = X * (C a * X ^ n) := by ring
      rw [this, map_mul, AdjoinRoot.mk_X, hcomm, ih]

/-- For `F` monic, `Tr_{L/K}(y) = φ(F'(u) y)` for every `y ∈ L = K[t]/(F)`, where `φ` is the
coefficient of `u^(n-1)`. (No separability is needed.) -/
theorem trace_eq_lastCoeff_mul (hF : F.Monic) (y : AdjoinRoot F) :
    Algebra.trace K (AdjoinRoot F) y =
      lastCoeff hF (aeval (AdjoinRoot.root F) (derivative F) * y) := by
  classical
  rcases subsingleton_or_nontrivial (AdjoinRoot F) with h | h
  · rw [Subsingleton.elim y 0, mul_zero, map_zero, map_zero]
  let bs : Module.Basis (Fin F.natDegree) K (AdjoinRoot F) := AdjoinRoot.powerBasisAux' hF
  have hpb (j : Fin F.natDegree) : bs j = AdjoinRoot.root F ^ (j : ℕ) :=
    (AdjoinRoot.powerBasis' hF).basis_eq_pow j
  have hrepr (z : AdjoinRoot F) (i : Fin F.natDegree) :
      bs.repr z i = lastCoeff hF (z * (quotientByRoot F).coeff i) := by
    conv_lhs => rw [← sum_lastCoeff_mul_root_pow hF z]
    rw [Finset.sum_range (fun i ↦ algebraMap K (AdjoinRoot F)
      (lastCoeff hF (z * (quotientByRoot F).coeff i)) * AdjoinRoot.root F ^ i)]
    simp_rw [← Algebra.smul_def, ← hpb, bs.repr_sum_self]
  have hdeg : (quotientByRoot F).natDegree < F.natDegree := by
    rw [natDegree_divByMonic _ (monic_X_sub_C _), hF.natDegree_map, natDegree_X_sub_C]
    have := natDegree_pos_of_nontrivial hF
    omega
  rw [Algebra.trace_eq_matrix_trace bs, Matrix.trace]
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hrepr]
  rw [mul_comm, ← eval_quotientByRoot, eval_eq_sum_range' hdeg, Finset.mul_sum, map_sum,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hpb]
  ring_nf

/-- The reversal `i ↦ n - 1 - i` of `Fin n` has sign `(-1)^(n(n-1)/2)`. -/
theorem sign_revPerm (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) = (-1) ^ (n * (n - 1) / 2) := by
  induction n with
  | zero => rw [Subsingleton.elim (Fin.revPerm : Equiv.Perm (Fin 0)) 1, map_one]; rfl
  | succ n ih =>
    have h : (Fin.revPerm : Equiv.Perm (Fin (n + 1))) =
        (finRotate (n + 1))⁻¹ * Equiv.Perm.decomposeFin.symm (0, Fin.revPerm) := by
      refine Equiv.ext fun k ↦ Fin.cases ?_ (fun x ↦ ?_) k
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_zero, eq_comm,
          Equiv.Perm.inv_eq_iff_eq, Fin.revPerm_apply, Fin.rev_zero, finRotate_last]
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
          Equiv.refl_apply, eq_comm, Equiv.Perm.inv_eq_iff_eq, Fin.revPerm_apply,
          Fin.revPerm_apply, Fin.rev_succ,
          finRotate_apply, Fin.coeSucc_eq_succ]
    rw [h, map_mul, map_inv, Equiv.Perm.decomposeFin.symm_sign, ih, sign_finRotate]
    rw [← Finset.sum_range_id, ← Finset.sum_range_id, Finset.sum_range_succ, pow_add,
      Nat.add_sub_cancel, ← inv_pow, inv_neg_one, mul_comm]
    simp only [↓reduceIte, one_mul]

/-- For `F` separable, `F'(u)` is a unit of `L = K[t]/(F)` (I.7.4). -/
theorem isUnit_aeval_root_derivative (hs : F.Separable) :
    IsUnit (aeval (AdjoinRoot.root F) (derivative F)) := by
  rw [AdjoinRoot.aeval_eq, isUnit_mk_iff_isCoprime]
  exact hs

/-- I.9.6 (Euler's formulas): let `K` be a ring, `F ∈ K[t]` monic of degree `n`, `L = K[t]/(F)`,
`u` the class of `t`, and let `v = F'(u)⁻¹` (which exists when `F` is separable,
`isUnit_aeval_root_derivative`). Then `Tr_{L/K}(uⁱ v) = 0` for `0 ≤ i < n - 1` and
`Tr_{L/K}(u^(n-1) v) = 1`. -/
theorem trace_root_pow_mul_eq_ite (hF : F.Monic) {v : AdjoinRoot F}
    (hv : aeval (AdjoinRoot.root F) (derivative F) * v = 1) {i : ℕ} (hi : i < F.natDegree) :
    Algebra.trace K (AdjoinRoot F) (AdjoinRoot.root F ^ i * v) =
      if i = F.natDegree - 1 then 1 else 0 := by
  rw [trace_eq_lastCoeff_mul hF, mul_left_comm, hv, mul_one, lastCoeff_root_pow hF hi]

/-- I.9.7: in the situation of I.9.6, the matrix `(Tr_{L/K}(uʲ uⁱ v))_{0 ≤ i, j < n}` has
determinant `(-1)^(n(n-1)/2)`; in particular it is invertible in every subring of `K`. -/
theorem det_trace_root_pow_mul (hF : F.Monic) {v : AdjoinRoot F}
    (hv : aeval (AdjoinRoot.root F) (derivative F) * v = 1) :
    (Matrix.of fun i j : Fin F.natDegree ↦ Algebra.trace K (AdjoinRoot F)
      (AdjoinRoot.root F ^ (j : ℕ) * AdjoinRoot.root F ^ (i : ℕ) * v)).det =
      (-1) ^ (F.natDegree * (F.natDegree - 1) / 2) := by
  set n := F.natDegree
  set M := Matrix.of fun i j : Fin n ↦ Algebra.trace K (AdjoinRoot F)
    (AdjoinRoot.root F ^ (j : ℕ) * AdjoinRoot.root F ^ (i : ℕ) * v)
  have hM' : (M.submatrix id Fin.revPerm).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ ?_]
    · refine Finset.prod_eq_one fun i _ ↦ ?_
      have := i.isLt
      simp only [Matrix.submatrix_apply, _root_.id, M, Matrix.of_apply, Fin.revPerm_apply,
        Fin.val_rev, ← pow_add]
      rw [trace_root_pow_mul_eq_ite hF hv (by omega), ite_eq_left (by omega)]
    · intro i j hij
      have := j.isLt
      simp only [Matrix.submatrix_apply, _root_.id, M, Matrix.of_apply, Fin.revPerm_apply,
        Fin.val_rev, ← pow_add]
      have : (i : ℕ) < j := hij
      rw [trace_root_pow_mul_eq_ite hF hv (by omega), ite_eq_right (by omega)]
  rw [Matrix.det_permute', sign_revPerm] at hM'
  push_cast at hM'
  calc M.det = (-1) ^ (n * (n - 1) / 2) * ((-1) ^ (n * (n - 1) / 2) * M.det) := by
        rw [← mul_assoc, ← mul_pow]; simp
    _ = (-1) ^ (n * (n - 1) / 2) := by rw [hM', mul_one]

section Dual

variable {A : Type*} [CommRing A] [Algebra A K]

/-- I.9.8: let `A → K` be a ring map, `F ∈ K[t]` monic of degree `n` with coefficients in `A`,
`L = K[t]/(F)`, `u` the class of `t` and `v = F'(u)⁻¹` (it exists if `F` is separable). An
element `x ∈ L` satisfies `Tr_{L/K}(x uⁱ) ∈ A` for all `i < n`, i.e. `x` lies in the trace dual
of `V = A[u] = ∑ A uⁱ`, iff `x` is an `A`-linear combination of the `uⁱ v`. (SGA takes `A ⊆ K`
and does not say that `F` should have coefficients in `A`, but this is needed: it fails for
`F = t² + t/2` over `ℤ ⊆ ℚ`.) The `uⁱ v` are `A`-linearly independent if `A → K` is injective
(`linearIndependent_root_pow_mul`). -/
theorem forall_trace_mul_root_pow_mem_iff (hF : F.Monic) (hA : F ∈ lifts (algebraMap A K))
    {v : AdjoinRoot F} (hv : aeval (AdjoinRoot.root F) (derivative F) * v = 1)
    (x : AdjoinRoot F) :
    (∀ i < F.natDegree, Algebra.trace K (AdjoinRoot F) (x * AdjoinRoot.root F ^ i) ∈
        Set.range (algebraMap A K)) ↔
      x ∈ Submodule.span A
        (Set.range fun i : Fin F.natDegree ↦ AdjoinRoot.root F ^ (i : ℕ) * v) := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · have := Module.subsingleton K (AdjoinRoot F)
    exact iff_of_true (fun _ _ ↦ ⟨0, Subsingleton.elim _ _⟩)
      (by rw [Subsingleton.elim x 0]; exact zero_mem _)
  set u := AdjoinRoot.root F
  obtain ⟨G, hGF, -, hG⟩ := lifts_and_natDegree_eq_and_monic hA hF
  -- `φ(uᵉ) ∈ A` for all `e`
  have hφ (e : ℕ) : lastCoeff hF (u ^ e) ∈ Set.range (algebraMap A K) := by
    have : X ^ e %ₘ F = (X ^ e %ₘ G).map (algebraMap A K) := by
      rw [map_modByMonic _ hG, Polynomial.map_pow, map_X, hGF]
    rw [show u ^ e = AdjoinRoot.mk F (X ^ e) by rw [map_pow, AdjoinRoot.mk_X], lastCoeff,
      LinearMap.comp_apply, AdjoinRoot.modByMonicHom_mk, this, lcoeff_apply, coeff_map]
    exact ⟨_, rfl⟩
  have hcoeff (j : ℕ) : F.coeff j ∈ Set.range (algebraMap A K) :=
    (lifts_iff_coeff_lifts F).mp hA j
  constructor
  · intro hx
    -- the coordinates of `z = F'(u) x` are `φ(z bᵢ) = Tr(x bᵢ)`, and `bᵢ ∈ A[u]`
    have hb (i : ℕ) : Algebra.trace K _ (x * (quotientByRoot F).coeff i) ∈
        Set.range (algebraMap A K) := by
      rcases subsingleton_or_nontrivial (AdjoinRoot F) with hL | hL
      · rw [Subsingleton.elim (x * _) 0, map_zero]
        exact ⟨0, map_zero _⟩
      rw [coeff_quotientByRoot hF, Finset.mul_sum, map_sum, ← RingHom.coe_range]
      refine Subring.sum_mem _ fun j hj ↦ ?_
      rw [Finset.mem_Icc] at hj
      obtain ⟨a, ha⟩ := hcoeff j
      obtain ⟨c, hc⟩ := hx (j - (i + 1)) (by omega)
      rw [← ha, mul_comm (u ^ _), ← mul_assoc, mul_comm x, mul_assoc, ← Algebra.smul_def,
        map_smul, smul_eq_mul]
      exact ⟨a * c, by rw [map_mul, hc]⟩
    choose c hc using hb
    have hz : x = ∑ i : Fin F.natDegree, c i • (u ^ (i : ℕ) * v) := by
      have := sum_lastCoeff_mul_root_pow hF (aeval u (derivative F) * x)
      rw [Finset.sum_range] at this
      calc x = aeval u (derivative F) * x * v := by
            rw [mul_right_comm, hv, one_mul]
        _ = _ := by
          rw [← this, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hci : algebraMap A K (c i) =
              lastCoeff hF (aeval u (derivative F) * x * (quotientByRoot F).coeff i) := by
            rw [hc i, trace_eq_lastCoeff_mul hF, mul_assoc]
          rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A K, hci]
          ring
    rw [hz]
    exact sum_mem fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hx i hi
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [trace_eq_lastCoeff_mul hF]
      have : aeval u (derivative F) * (u ^ (j : ℕ) * v * u ^ i) = u ^ ((j : ℕ) + i) := by
        rw [pow_add]
        linear_combination (u ^ (j : ℕ) * u ^ i) * hv
      rw [this]
      exact hφ _
    | zero => exact ⟨0, by simp⟩
    | add y w _ _ hy hw =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hw
      exact ⟨a + b, by rw [add_mul, map_add, map_add, ha, hb]⟩
    | smul a y _ hy =>
      obtain ⟨b, hb⟩ := hy
      refine ⟨a * b, ?_⟩
      rw [smul_mul_assoc, ← algebraMap_smul K a, map_smul, smul_eq_mul, ← hb, map_mul]

/-- I.9.8, the basis: if `A → K` is injective and `F'(u) v = 1`, the `uⁱ v` (`i < n`) are
`A`-linearly independent. -/
theorem linearIndependent_root_pow_mul (hF : F.Monic) {v : AdjoinRoot F}
    (hv : aeval (AdjoinRoot.root F) (derivative F) * v = 1)
    (hA : Function.Injective (algebraMap A K)) :
    LinearIndependent A fun i : Fin F.natDegree ↦ AdjoinRoot.root F ^ (i : ℕ) * v := by
  have hK : LinearIndependent K fun i : Fin F.natDegree ↦ AdjoinRoot.root F ^ (i : ℕ) * v := by
    let bs : Module.Basis (Fin F.natDegree) K (AdjoinRoot F) := AdjoinRoot.powerBasisAux' hF
    have hpb (j : Fin F.natDegree) : bs j = AdjoinRoot.root F ^ (j : ℕ) :=
      (AdjoinRoot.powerBasis' hF).basis_eq_pow j
    have := bs.linearIndependent.map' (LinearMap.mulRight K v) (by
      rw [LinearMap.ker_eq_bot']
      intro y hy
      have : y * v * aeval (AdjoinRoot.root F) (derivative F) = 0 := by
        rw [show y * v = 0 from hy, zero_mul]
      rwa [mul_assoc, mul_comm v, hv, mul_one] at this)
    have hfun : (⇑(LinearMap.mulRight K v) ∘ ⇑bs) =
        fun i : Fin F.natDegree ↦ AdjoinRoot.root F ^ (i : ℕ) * v := by
      funext i
      simp [hpb]
    exact hfun ▸ this
  refine hK.restrict_scalars ?_
  simpa [Algebra.smul_def] using hA

end Dual


end SGA.SGA1.ExposeI
