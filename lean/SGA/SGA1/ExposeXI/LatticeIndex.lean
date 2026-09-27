/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.AdjoinRoot

/-!
# Lattices over `k[T]` and `k[T⁻¹]` (for XI.1.1)

This file contains the linear algebra behind the proof that `ℙ¹` over an algebraically closed
field is simply connected (XI.1.1): a vector bundle on `ℙ¹` is described by two lattices, over
`k[T]` and over `k[T⁻¹]`, in a free `k[T, T⁻¹]`-module, and its global sections are the
intersection of the two lattices. The Riemann–Roch inequality `h⁰ ≥ rank + degree` for such a
pair of lattices is `le_finrank_sections`; SGA uses the genus formula instead.

* `finrank_quotient_range_eq_natDegree_det`: for a square matrix `h` over `k[X]` with nonzero
  determinant, `k[X]ⁿ / h k[X]ⁿ` has dimension `deg (det h)` over `k` (Smith normal form).
* `le_finrank_inf_range`: the vectors of degree `≤ m` in `h k[X]ⁿ` form a space of dimension at
  least `(m + 1) n - deg (det h)`.
* `le_finrank_sections`: if `b, b'` are two bases of a free `k[T, T⁻¹]`-module `W` with
  `det (b.toMatrix b')² ∈ k`, then the elements of `W` whose `b`-coordinates lie in `k[T]` and
  whose `b'`-coordinates lie in `k[T⁻¹]` form a finite-dimensional `k`-space of dimension at
  least the rank of `W`.
-/

open Polynomial Module

namespace SGA.SGA1.ExposeXI

section Index

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The dimension of `k[X]ⁿ / h k[X]ⁿ` over `k` is the degree of `det h` (by the Smith normal
form of `h`). -/
theorem finrank_quotient_range_eq_natDegree_det (h : Matrix ι ι k[X]) (hdet : h.det ≠ 0) :
    FiniteDimensional k ((ι → k[X]) ⧸ LinearMap.range h.mulVecLin) ∧
      finrank k ((ι → k[X]) ⧸ LinearMap.range h.mulVecLin) = h.det.natDegree := by
  set N := LinearMap.range h.mulVecLin
  have hinj : Function.Injective h.mulVecLin := Matrix.mulVec_injective_of_det_ne_zero hdet
  let e₀ : (ι → k[X]) ≃ₗ[k[X]] N := LinearEquiv.ofInjective _ hinj
  have hrank : finrank k[X] N = finrank k[X] (ι → k[X]) := e₀.symm.finrank_eq
  let b := Pi.basisFun k[X] ι
  let a := Submodule.smithNormalFormCoeffs b hrank
  let b' := Submodule.smithNormalFormTopBasis b hrank
  let ab := Submodule.smithNormalFormBotBasis b hrank
  have ab_eq := Submodule.smithNormalFormBotBasis_def b hrank
  have ha0 : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrank
  let e' : (ι → k[X]) ≃ₗ[k[X]] N := b'.equiv ab (Equiv.refl _)
  let f : (ι → k[X]) →ₗ[k[X]] (ι → k[X]) := N.subtype.comp (e' : (ι → k[X]) →ₗ[k[X]] N)
  have hf : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _)) (b' i) : ι → k[X]) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdetf : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, hf, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hassoc : Associated h.det (∏ i, a i) := by
    rw [← hdetf, ← LinearMap.det_toLin' h]
    have : Matrix.toLin' h = N.subtype.comp (e₀ : (ι → k[X]) →ₗ[k[X]] N) := by
      ext x : 1
      rfl
    rw [this]
    exact LinearMap.associated_det_comp_equiv _ _ _
  have hfd : ∀ i, FiniteDimensional k
      (k[X] ⧸ Ideal.span ({Submodule.smithNormalFormCoeffs b hrank i} : Set k[X])) := fun i ↦
    PowerBasis.finite (AdjoinRoot.powerBasis (ha0 i))
  have hfin : FiniteDimensional k ((ι → k[X]) ⧸ N) :=
    Module.Finite.equiv ((N.quotientEquivPiSpan b hrank).restrictScalars k).symm
  refine ⟨hfin, ?_⟩
  rw [Submodule.finrank_quotient_eq_sum k b hrank,
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc),
    natDegree_prod _ _ fun i _ ↦ ha0 i]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact (AdjoinRoot.powerBasis (ha0 i)).finrank.trans (AdjoinRoot.powerBasis_dim (ha0 i))

variable (k ι) in
/-- The vectors of polynomials of degree `< n`. -/
noncomputable def vecDegreeLT (n : ℕ) : Submodule k (ι → k[X]) :=
  Submodule.pi Set.univ fun _ ↦ degreeLT k n

omit [Fintype ι] [DecidableEq ι] in
lemma mem_vecDegreeLT {n : ℕ} {w : ι → k[X]} :
    w ∈ vecDegreeLT k ι n ↔ ∀ i, w i ∈ degreeLT k n := by
  simp [vecDegreeLT, Submodule.mem_pi]

/-- The vectors of polynomials of degree `< n` form a space of dimension `n · |ι|`. -/
noncomputable def vecDegreeLTEquiv (n : ℕ) : vecDegreeLT k ι n ≃ₗ[k] (ι → Fin n → k) :=
  { toFun w i := degreeLTEquiv k n ⟨w.1 i, mem_vecDegreeLT.1 w.2 i⟩
    invFun v := ⟨fun i ↦ ((degreeLTEquiv k n).symm (v i)).1,
      mem_vecDegreeLT.2 fun i ↦ ((degreeLTEquiv k n).symm (v i)).2⟩
    map_add' w w' := by
      funext i
      exact (degreeLTEquiv k n).map_add ⟨w.1 i, _⟩ ⟨w'.1 i, _⟩
    map_smul' c w := by
      funext i
      exact (degreeLTEquiv k n).map_smul c ⟨w.1 i, _⟩
    left_inv w := by
      ext i : 2
      simp
    right_inv v := by
      funext i
      simp }

omit [Fintype ι] [DecidableEq ι] in
instance [Finite ι] (n : ℕ) : FiniteDimensional k (vecDegreeLT k ι n) :=
  have := Fintype.ofFinite ι
  Module.Finite.equiv (vecDegreeLTEquiv n).symm

omit [DecidableEq ι] in
lemma finrank_vecDegreeLT (n : ℕ) : finrank k (vecDegreeLT k ι n) = Fintype.card ι * n := by
  rw [(vecDegreeLTEquiv n).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- The vectors of degree `< n` in `h k[X]ⁿ` form a space of dimension at least
`n |ι| - deg (det h)`. -/
theorem le_finrank_inf_range (h : Matrix ι ι k[X]) (hdet : h.det ≠ 0) (n : ℕ) :
    FiniteDimensional k ↥(vecDegreeLT k ι n ⊓ (LinearMap.range h.mulVecLin).restrictScalars k) ∧
      Fintype.card ι * n ≤
        finrank k ↥(vecDegreeLT k ι n ⊓ (LinearMap.range h.mulVecLin).restrictScalars k) +
          h.det.natDegree := by
  set R := LinearMap.range h.mulVecLin
  set Z := vecDegreeLT k ι n ⊓ R.restrictScalars k
  obtain ⟨hQ, hQrank⟩ := finrank_quotient_range_eq_natDegree_det h hdet
  have hZ : FiniteDimensional k Z := Submodule.finiteDimensional_of_le inf_le_left
  refine ⟨hZ, ?_⟩
  let κ : vecDegreeLT k ι n →ₗ[k] (ι → k[X]) ⧸ R :=
    (R.mkQ.restrictScalars k).comp (vecDegreeLT k ι n).subtype
  let eK : LinearMap.ker κ ≃ₗ[k] Z :=
    { toFun w := ⟨w.1.1, w.1.2, (Submodule.Quotient.mk_eq_zero R).1 w.2⟩
      invFun z := ⟨⟨z.1, z.2.1⟩, (Submodule.Quotient.mk_eq_zero R).2 z.2.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl }
  have hrn := LinearMap.finrank_range_add_finrank_ker κ
  rw [finrank_vecDegreeLT, eK.finrank_eq] at hrn
  have hle : finrank k (LinearMap.range κ) ≤ h.det.natDegree :=
    hQrank ▸ Submodule.finrank_le _
  omega

end Index

section Laurent

open LaurentPolynomial

variable (k : Type*) [Field k]

/-- The inclusion `k[T⁻¹] ⊆ k[T, T⁻¹]`, `X ↦ T⁻¹`. -/
noncomputable def toLaurentInv : k[X] →ₐ[k] k[T;T⁻¹] :=
  (invert : k[T;T⁻¹] ≃ₐ[k] k[T;T⁻¹]).toAlgHom.comp toLaurentAlg

variable {k}

lemma toLaurentInv_apply (p : k[X]) : toLaurentInv k p = invert (toLaurent p) := rfl

lemma toLaurentInv_injective : Function.Injective (toLaurentInv k) :=
  invert.injective.comp Polynomial.toLaurent_injective

/-- `Tᵐ p(T⁻¹)` is a polynomial in `T` if and only if `deg p ≤ m`. -/
lemma T_mul_toLaurentInv_mem_range_iff (m : ℕ) (p : k[X]) :
    T m * toLaurentInv k p ∈ Set.range (toLaurent : k[X] → k[T;T⁻¹]) ↔
      p ∈ degreeLT k (m + 1) := by
  rw [mem_degreeLT, toLaurentInv_apply]
  by_cases hp : p = 0
  · simp only [hp, map_zero, mul_zero, Polynomial.degree_zero]
    exact ⟨fun _ ↦ WithBot.bot_lt_coe _, fun _ ↦ ⟨0, map_zero _⟩⟩
  have hinv : invert (toLaurent p) = toLaurent p.reverse * T (-(p.natDegree : ℤ)) := by
    rw [toLaurent_reverse, mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one]
  rw [degree_eq_natDegree hp, Nat.cast_lt, hinv]
  constructor
  · rintro ⟨q, hq⟩
    by_contra hlt
    obtain ⟨j, hj⟩ : ∃ j, p.natDegree = m + (j + 1) := ⟨p.natDegree - m - 1, by omega⟩
    have h1 : toLaurent p.reverse = toLaurent (q * X ^ (j + 1)) := by
      rw [map_mul, hq, toLaurent_X_pow, mul_comm (T (m : ℤ)), mul_assoc, mul_assoc, ← T_add,
        ← T_add, hj]
      simp
    have h2 := congrArg (fun r : k[X] ↦ r.coeff 0) (Polynomial.toLaurent_injective h1)
    simp only [coeff_zero_reverse, pow_succ, ← mul_assoc, mul_coeff_zero, coeff_X_zero,
      mul_zero] at h2
    exact hp (leadingCoeff_eq_zero.1 h2)
  · intro hlt
    refine ⟨p.reverse * X ^ (m - p.natDegree), ?_⟩
    rw [map_mul, toLaurent_X_pow, mul_comm (T (m : ℤ)), mul_assoc, ← T_add,
      Nat.cast_sub (by omega)]
    ring_nf

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [AddCommGroup W]
  [Module k[T;T⁻¹] W] [Module k W] [IsScalarTower k k[T;T⁻¹] W]

variable (k) in
/-- `k[T]`, as a `k`-subspace of `k[T, T⁻¹]`. -/
noncomputable abbrev polyPart : Submodule k k[T;T⁻¹] :=
  LinearMap.range (toLaurentAlg : k[X] →ₐ[k] k[T;T⁻¹]).toLinearMap

variable (k) in
/-- `k[T⁻¹]`, as a `k`-subspace of `k[T, T⁻¹]`. -/
noncomputable abbrev invPolyPart : Submodule k k[T;T⁻¹] :=
  LinearMap.range (toLaurentInv k).toLinearMap

/-- The global sections of the vector bundle on `ℙ¹` given by two bases `b, b'` of a free
`k[T, T⁻¹]`-module `W`: the elements whose `b`-coordinates lie in `k[T]` and whose
`b'`-coordinates lie in `k[T⁻¹]`. -/
noncomputable def latticeSections (b b' : Basis ι k[T;T⁻¹] W) : Submodule k W :=
  (Submodule.pi Set.univ fun _ ↦ polyPart k).comap (b.equivFun.toLinearMap.restrictScalars k) ⊓
    (Submodule.pi Set.univ fun _ ↦ invPolyPart k).comap
      (b'.equivFun.toLinearMap.restrictScalars k)

omit [DecidableEq ι] in
lemma mem_latticeSections {b b' : Basis ι k[T;T⁻¹] W} {w : W} :
    w ∈ latticeSections b b' ↔ (∀ i, b.repr w i ∈ Set.range (toLaurent : k[X] → k[T;T⁻¹])) ∧
      ∀ i, b'.repr w i ∈ Set.range (toLaurentInv k) := by
  simp [latticeSections, Submodule.mem_pi, toLaurentAlg_apply]

/-- A Laurent polynomial becomes a polynomial in `T⁻¹` after multiplication by `T⁻ᵐ`, `m ≫ 0`. -/
lemma exists_T_neg_mul_mem (f : k[T;T⁻¹]) :
    ∃ n : ℕ, ∀ m ≥ n, T (-(m : ℤ)) * f ∈ Set.range (toLaurentInv k) := by
  obtain ⟨n, f', hf'⟩ := exists_T_pow (invert f)
  refine ⟨n, fun m hm ↦ ⟨f' * X ^ (m - n), ?_⟩⟩
  rw [map_mul, toLaurentInv_apply, toLaurentInv_apply, hf', toLaurent_X_pow, map_mul, invert_T,
    invert_T, involutive_invert f, mul_assoc, ← T_add, mul_comm, Nat.cast_sub hm]
  congr 2
  ring

/-- The Riemann–Roch inequality for a vector bundle of degree `-δ/2` on `ℙ¹`: if `b, b'` are bases
of a free `k[T, T⁻¹]`-module `W` whose change of basis matrix has square determinant
`c⁻¹ f(T⁻¹)` with `f` a polynomial of degree `δ`, then the global sections
(`latticeSections b b'`) form a finite-dimensional `k`-space of dimension at least
`rank W - δ/2`. -/
theorem le_finrank_latticeSections_of_det_sq (b b' : Basis ι k[T;T⁻¹] W) (c : k) (hc0 : c ≠ 0)
    (f : k[X]) (hc : (b.toMatrix b').det ^ 2 * LaurentPolynomial.C c = toLaurentInv k f) :
    FiniteDimensional k (latticeSections b b') ∧
      2 * Fintype.card ι ≤ 2 * finrank k (latticeSections b b') + f.natDegree := by
  set M := b.toMatrix b'
  -- Write `M = Tᵐ H(T⁻¹)` with `H` a matrix of polynomials.
  have hex : ∀ i j, ∃ n : ℕ, ∀ m ≥ n, T (-(m : ℤ)) * M i j ∈ Set.range (toLaurentInv k) :=
    fun i j ↦ exists_T_neg_mul_mem _
  choose n hn using hex
  set m := ∑ i, ∑ j, n i j
  have hm : ∀ i j, T (-(m : ℤ)) * M i j ∈ Set.range (toLaurentInv k) := fun i j ↦
    hn i j m ((Finset.single_le_sum (f := fun j ↦ n i j) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i ↦ ∑ j, n i j)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)))
  choose h' hh' using hm
  let H : Matrix ι ι k[X] := Matrix.of h'
  have hMH : ∀ i j, M i j = T m * toLaurentInv k (H i j) := by
    intro i j
    change M i j = T m * toLaurentInv k (h' i j)
    rw [hh', ← mul_assoc, ← T_add, add_neg_cancel, T_zero, one_mul]
  -- The determinant of `H` has degree `m |ι|`.
  have hdetM : M.det ≠ 0 := by
    have := congrArg Matrix.det (Basis.toMatrix_mul_toMatrix_flip b b')
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hHmap : (toLaurentInv k).mapMatrix H = (T (-(m : ℤ)) : k[T;T⁻¹]) • M := by
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, H,
      Matrix.of_apply, hh']
  have hdetH : toLaurentInv k H.det = (T (-(m : ℤ)) : k[T;T⁻¹]) ^ Fintype.card ι * M.det := by
    rw [AlgHom.map_det, hHmap, Matrix.det_smul]
  have hH0 : H.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hdetH
    exact mul_ne_zero (pow_ne_zero _ (isUnit_T _).ne_zero) hdetM hdetH.symm
  have hsq : H.det ^ 2 * Polynomial.C c = f * X ^ (2 * (m * Fintype.card ι)) := by
    apply toLaurentInv_injective
    rw [map_mul, map_pow, hdetH, mul_pow, mul_assoc, map_mul, ← hc, map_pow,
      toLaurentInv_apply (Polynomial.C c), toLaurentInv_apply X, toLaurent_C, toLaurent_X,
      invert_C, invert_T, ← pow_mul, T_pow, T_pow]
    rw [mul_comm (T _), mul_assoc, mul_assoc]
    congr 3
    push_cast
    ring
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hsq
    exact mul_ne_zero (pow_ne_zero 2 hH0) (Polynomial.C_ne_zero.mpr hc0) hsq
  have hdeg : 2 * H.det.natDegree = 2 * (m * Fintype.card ι) + f.natDegree := by
    have := congrArg Polynomial.natDegree hsq
    rw [natDegree_mul (pow_ne_zero 2 hH0) (Polynomial.C_ne_zero.mpr hc0), natDegree_C,
      natDegree_pow, natDegree_mul hf0 (pow_ne_zero _ X_ne_zero), natDegree_X_pow] at this
    omega
  -- The sections are `Ψ` of the vectors `u` with `deg (H u) ≤ m`.
  let Ψ : (ι → k[X]) →ₗ[k] W :=
    (b'.equivFun.symm.toLinearMap.restrictScalars k).comp ((toLaurentInv k).toLinearMap.compLeft ι)
  have hΨ' : ∀ u i, b'.repr (Ψ u) i = toLaurentInv k (u i) := by
    intro u i
    rw [← b'.equivFun_apply]
    change b'.equivFun (b'.equivFun.symm _) i = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hΨ : ∀ u i, b.repr (Ψ u) i = T m * toLaurentInv k ((H.mulVec u) i) := by
    intro u i
    rw [← Basis.toMatrix_mulVec_repr (b := b') (b' := b) (Ψ u)]
    simp only [Matrix.mulVec, dotProduct, hΨ', map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← mul_assoc, ← hMH]
  have hΨinj : Function.Injective Ψ := by
    intro u v huv
    funext i
    have := congrArg (fun w ↦ b'.repr w i) huv
    simp only [hΨ'] at this
    exact toLaurentInv_injective this
  let Z₀ := (vecDegreeLT k ι (m + 1)).comap (H.mulVecLin.restrictScalars k)
  have hΓ : latticeSections b b' = Z₀.map Ψ := by
    ext w
    rw [mem_latticeSections]
    constructor
    · rintro ⟨h₀, h₁⟩
      choose u hu using h₁
      have hw : Ψ u = w := b'.repr.injective (Finsupp.ext fun i ↦ by rw [hΨ', hu])
      refine ⟨u, ?_, hw⟩
      change H.mulVec u ∈ vecDegreeLT k ι (m + 1)
      rw [mem_vecDegreeLT]
      intro i
      rw [← T_mul_toLaurentInv_mem_range_iff, ← hΨ, hw]
      exact h₀ i
    · rintro ⟨u, hu, rfl⟩
      change H.mulVec u ∈ vecDegreeLT k ι (m + 1) at hu
      rw [mem_vecDegreeLT] at hu
      refine ⟨fun i ↦ ?_, fun i ↦ ⟨u i, (hΨ' u i).symm⟩⟩
      rw [hΨ]
      exact (T_mul_toLaurentInv_mem_range_iff m _).2 (hu i)
  have hZ : Z₀.map (H.mulVecLin.restrictScalars k) =
      vecDegreeLT k ι (m + 1) ⊓ (LinearMap.range H.mulVecLin).restrictScalars k := by
    rw [Submodule.map_comap_eq, LinearMap.range_restrictScalars, inf_comm]
  have hHinj : Function.Injective (H.mulVecLin.restrictScalars k) :=
    Matrix.mulVec_injective_of_det_ne_zero hH0
  let e₁ : latticeSections b b' ≃ₗ[k] Z₀ :=
    (LinearEquiv.ofEq _ _ hΓ).trans (Submodule.equivMapOfInjective Ψ hΨinj Z₀).symm
  let e₂ : Z₀ ≃ₗ[k] ↥(vecDegreeLT k ι (m + 1) ⊓
      (LinearMap.range H.mulVecLin).restrictScalars k) :=
    (Submodule.equivMapOfInjective _ hHinj Z₀).trans (LinearEquiv.ofEq _ _ hZ)
  obtain ⟨hfin, hle⟩ := le_finrank_inf_range H hH0 (m + 1)
  have : FiniteDimensional k (latticeSections b b') := Module.Finite.equiv (e₁.trans e₂).symm
  refine ⟨this, ?_⟩
  rw [(e₁.trans e₂).finrank_eq]
  nlinarith

/-- The Riemann–Roch inequality for a vector bundle of degree `0` on `ℙ¹`: if `b, b'` are bases
of a free `k[T, T⁻¹]`-module `W` whose change of basis matrix has constant square determinant,
then the global sections (`latticeSections b b'`) form a finite-dimensional `k`-space of
dimension at least the rank of `W`. -/
theorem le_finrank_latticeSections (b b' : Basis ι k[T;T⁻¹] W) (c : k)
    (hc : (b.toMatrix b').det ^ 2 = LaurentPolynomial.C c) :
    FiniteDimensional k (latticeSections b b') ∧
      Fintype.card ι ≤ finrank k (latticeSections b b') := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hdetM : (b.toMatrix b').det ≠ 0 := by
      have := congrArg Matrix.det (Basis.toMatrix_mul_toMatrix_flip b b')
      rw [Matrix.det_mul, Matrix.det_one] at this
      exact left_ne_zero_of_mul_eq_one this
    rw [map_zero] at hc
    exact hdetM (pow_eq_zero_iff two_ne_zero |>.1 hc)
  obtain ⟨h, hle⟩ := le_finrank_latticeSections_of_det_sq b b' c⁻¹ (inv_ne_zero hc0) 1 (by
    rw [hc, ← map_mul, mul_inv_cancel₀ hc0, map_one, map_one])
  exact ⟨h, by simp at hle; omega⟩

end Laurent

end SGA.SGA1.ExposeXI
