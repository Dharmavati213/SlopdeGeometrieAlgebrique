/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.UnitaryCoordinates
import SGA.Foundations.Hodge.ExteriorAlgebraPairs
import SGA.Foundations.Hodge.KahlerPower
import SGA.Foundations.Hodge.Integration
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Positivity of `i^{p²} θ ∧ θ̄ ∧ ωᵐ` for forms of type `(p, 0)`

Let `E` be a complex vector space of dimension `n`, `κ` a positive real `(1, 1)`-form on `E`
(`Hodge.IsPositiveForm`; e.g. the value of a Kähler form at a point) and `θ` a form of type
`(p, 0)`, with `p + m = n`. Then the top-degree form `i^{p²} θ ⋏ θ̄ ⋏ κᵐ` is a nonnegative multiple
of the volume form, and a positive one if `θ ≠ 0`.

We evaluate on the real frame `(w₀, …, w_{n-1}, i w₀, …, i w_{n-1})` of a complex basis `w`
(`Hodge.basisFrame w`). In the order `(x₀, …, x_{n-1}, y₀, …, y_{n-1})` the standard orientation
`x₀ ∧ y₀ ∧ ⋯ ∧ x_{n-1} ∧ y_{n-1}` of a complex vector space takes the value
`(-1)^(n choose 2)` on this frame, whence the sign in:

* `Hodge.IsPositiveForm.wedge_conj_wedgePow_apply_basisFrame`: in a unitary frame `u` of `κ`,
  `(θ ⋏ θ̄ ⋏ κᵐ)(u-frame) = (i/2)ᵐ m! (-1)^(p choose 2) (∑_J |θ(u_J)|²) (-1)^(n choose 2) (-2i)ⁿ`;
* `Hodge.IsPositiveForm.wedge_conj_wedgePow_nonneg`: for every complex basis `w`,
  `(-1)^(n choose 2) i^{p²} (θ ⋏ θ̄ ⋏ κᵐ)(w-frame) ≥ 0` (in the order of `ℂ`: real and `≥ 0`);
* `Hodge.IsPositiveForm.wedge_conj_wedgePow_pos`: it is `> 0` if `θ ≠ 0`.

The degree of `θ ⋏ θ̄ ⋏ κᵐ` is `(p + p) + 2m`, which equals `n + n` only propositionally; the
frame is composed with the cast `Fin ((p + p) + 2m) ≃ Fin (n + n)`.

The proof computes in mathlib's exterior algebra of `1`-forms (`ContinuousAlternatingMap.toForms`):
`κ = (i/2) ∑ⱼ ζⱼ ∧ ζ̄ⱼ` in a unitary frame (`Hodge.IsPositiveForm.eq_sum_of_unitary`),
`θ = ∑_J θ(u_J) ζ_J` (`Hodge.IsOfType.eq_sum_detForm`), and the product is evaluated by
`ExteriorAlgebra.sum_mul_sum_mul_pow_sum_pairCenter`.

Reference: D. Huybrechts, *Complex geometry*, §1.2 (Hodge–Riemann bilinear relations, in the
special case of `(p, 0)`-forms, which are primitive); C. Voisin, *Hodge theory and complex
algebraic geometry I*, §6.3.
-/

noncomputable section

open ComplexConjugate ContinuousAlternatingMap ExteriorAlgebra
open scoped ComplexOrder

namespace ContinuousAlternatingMap

variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedField 𝕜]
  [NormedAlgebra ℝ 𝕜]

/-- Reading `toForms` in two equal degrees. -/
lemma toForms_congr_degree (x : ExteriorAlgebra 𝕜 (E →L[ℝ] 𝕜)) {l l' : ℕ} (h : l = l') :
    toForms E 𝕜 x l' = (toForms E 𝕜 x l).domDomCongr (finCongr h) := by
  subst h
  simp

lemma toForms_ι_mul_ι (a b : E →L[ℝ] 𝕜) :
    toForms E 𝕜 (ι 𝕜 a * ι 𝕜 b) 2 = detForm ![a, b] := by
  have : ι 𝕜 a * ι 𝕜 b = ιMulti 𝕜 2 ![a, b] := by
    simp [Matrix.vecTail]
  rw [this, toForms_ιMulti_self]

lemma toForms_ιMulti_mul_ιMulti {a b : ℕ} (φ : Fin a → E →L[ℝ] 𝕜) (ψ : Fin b → E →L[ℝ] 𝕜) :
    toForms E 𝕜 (ιMulti 𝕜 a φ * ιMulti 𝕜 b ψ) (a + b) = detForm (Fin.append φ ψ) := by
  rw [ιMulti_mul_ιMulti, toForms_ιMulti_self]

end ContinuousAlternatingMap

namespace Hodge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {n : ℕ}

omit [FiniteDimensional ℂ E] in
lemma conjForm_finsetSum {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → E [⋀^Fin k]→L[ℝ] ℂ) :
    conjForm (∑ i ∈ s, f i) = ∑ i ∈ s, conjForm (f i) := by
  have h := _root_.map_sum (conjFormCLM E k) f s
  simp only [conjFormCLM_apply] at h
  exact h

/-! ### Scalars -/

/-- `i^{p²} (-1)^(p choose 2) (-i)ᵖ = 1`. -/
lemma I_pow_sq_mul_neg_one_pow_choose_mul (p : ℕ) :
    Complex.I ^ (p ^ 2) * (-1) ^ p.choose 2 * (-Complex.I) ^ p = 1 := by
  induction p with
  | zero => simp
  | succ p ih =>
    have e1 : (p + 1) ^ 2 = p ^ 2 + 2 * p + 1 := by ring
    rw [e1, Nat.choose_succ_succ, Nat.choose_one_right, pow_add, pow_add, pow_mul,
      Complex.I_sq, pow_succ (-Complex.I), pow_add (-1 : ℂ)]
    calc Complex.I ^ p ^ 2 * (-1) ^ p * Complex.I ^ 1 * ((-1) ^ p * (-1) ^ p.choose 2) *
          ((-Complex.I) ^ p * -Complex.I)
        = (Complex.I ^ (p ^ 2) * (-1) ^ p.choose 2 * (-Complex.I) ^ p) *
            (((-1) ^ p) ^ 2 * (-(Complex.I * Complex.I))) := by ring
      _ = 1 := by
        rw [ih, ← pow_mul, mul_comm p 2, pow_mul, neg_one_sq, one_pow, Complex.I_mul_I]
        ring

/-- `(i/2)ᵐ (-2i)ᵐ = 1`. -/
lemma I_div_two_pow_mul_neg_two_I_pow (m : ℕ) :
    (Complex.I / 2) ^ m * (-2 * Complex.I) ^ m = 1 := by
  rw [← mul_pow]
  have : Complex.I / 2 * (-2 * Complex.I) = 1 := by
    field_simp
    rw [Complex.I_sq, neg_neg]
  rw [this, one_pow]

/-! ### The top degree element `∏ⱼ ζⱼ ∧ ζ̄ⱼ` -/

variable (u : Module.Basis (Fin n) ℂ E)

/-- `ζ₀ ∧ ⋯ ∧ ζ_{n-1} ∧ ζ̄₀ ∧ ⋯ ∧ ζ̄_{n-1}` takes the value `(-2i)ⁿ` on the frame
`(u₀, …, u_{n-1}, i u₀, …, i u_{n-1})`. -/
lemma detForm_append_coordForm_basisFrame :
    detForm (Fin.append (coordForm u) (conjCoordForm u)) (basisFrame u) =
      (-2 * Complex.I) ^ n := by
  rw [detForm_apply_eq_det, ← Matrix.det_reindex_self finSumFinEquiv.symm]
  have hM : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (Matrix.of fun i j ↦ Fin.append (coordForm u) (conjCoordForm u) j (basisFrame u i)) =
      Matrix.fromBlocks 1 1 (Complex.I • 1) (-Complex.I • 1) := by
    ext (k | k) (l | l) <;>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.of_apply, basisFrame,
        Fin.append_left, Fin.append_right, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, coordForm_apply,
        conjCoordForm_apply, coord_basis, coord_I_basis, Matrix.smul_apply, Matrix.one_apply] <;>
      split_ifs <;> simp_all
  rw [hM, Matrix.det_fromBlocks_one₁₁, Matrix.mul_one, ← sub_smul, Matrix.det_smul,
    Matrix.det_one, mul_one, Fintype.card_fin]
  ring_nf

/-- The value of `∏ⱼ ζⱼ ∧ ζ̄ⱼ` on the frame `(u₀, …, u_{n-1}, i u₀, …, i u_{n-1})`. -/
lemma toForms_prod_pairCenter_basisFrame :
    toForms E ℂ ((∏ j, pairCenter ℂ (coordForm u) (conjCoordForm u) j :
      Subalgebra.center ℂ _) : ExteriorAlgebra ℂ (E →L[ℝ] ℂ)) (n + n) (basisFrame u) =
      (-1) ^ n.choose 2 * (-2 * Complex.I) ^ n := by
  have h := ιMulti_mul_ιMulti_eq_prod_pairCenter (R := ℂ) (coordForm u) (conjCoordForm u) id
  simp only [Function.comp_id, id] at h
  have h' : ((∏ j, pairCenter ℂ (coordForm u) (conjCoordForm u) j :
      Subalgebra.center ℂ _) : ExteriorAlgebra ℂ (E →L[ℝ] ℂ)) =
      ((-1 : ℂ) ^ n.choose 2) • (ιMulti ℂ n (coordForm u) * ιMulti ℂ n (conjCoordForm u)) := by
    rw [h, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  rw [h', map_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    toForms_ιMulti_mul_ιMulti, detForm_append_coordForm_basisFrame, smul_eq_mul]

/-! ### The computation in a unitary frame -/

/-- **`θ ⋏ θ̄ ⋏ κᵐ` in a unitary frame.** For a positive `(1, 1)`-form `κ` with unitary frame `u`
and a form `θ` of type `(p, 0)`, `p + m = n`:
`(θ ⋏ θ̄ ⋏ κᵐ)(u-frame)` equals
`(i/2)ᵐ m! (-1)^(p choose 2) (∑_J θ(u_J) θ(u_J)‾) (-1)^(n choose 2) (-2i)ⁿ`. -/
theorem IsPositiveForm.wedge_conj_wedgePow_apply_basisFrame {κ : E [⋀^Fin 2]→L[ℝ] ℂ}
    (hκ : IsPositiveForm κ)
    (hu : ∀ j k, κ ![u j, Complex.I • u k] = (if j = k then 1 else 0) ∧ κ ![u j, u k] = 0)
    {p m : ℕ} (hpm : p + m = n) {θ : E [⋀^Fin p]→L[ℝ] ℂ} (hθ : IsOfType p 0 θ)
    (h : (p + p) + 2 * m = n + n) :
    ((θ ⋏ conjForm θ) ⋏ wedgePow κ m) (fun i ↦ basisFrame u (finCongr h i)) =
      (Complex.I / 2) ^ m * ((m.factorial : ℂ) * (-1) ^ p.choose 2 *
        ∑ J : Set.powersetCard (Fin n) p, θ (basisOf u J) * conj (θ (basisOf u J))) *
          ((-1) ^ n.choose 2 * (-2 * Complex.I) ^ n) := by
  set a := coordForm u
  set b := conjCoordForm u
  set e := fun J : Set.powersetCard (Fin n) p ↦
    (Set.powersetCard.ofFinEmbEquiv.symm J : Fin p → Fin n)
  set Θ : ExteriorAlgebra ℂ (E →L[ℝ] ℂ) := ∑ J, θ (basisOf u J) • ιMulti ℂ p (a ∘ e J)
  set Θ' : ExteriorAlgebra ℂ (E →L[ℝ] ℂ) := ∑ J, conj (θ (basisOf u J)) • ιMulti ℂ p (b ∘ e J)
  set P : Subalgebra.center ℂ (ExteriorAlgebra ℂ (E →L[ℝ] ℂ)) := ∑ j, pairCenter ℂ a b j
  set K : ExteriorAlgebra ℂ (E →L[ℝ] ℂ) := (Complex.I / 2) • (P : ExteriorAlgebra ℂ _)
  have hΘmem : Θ ∈ ⋀[ℂ]^p (E →L[ℝ] ℂ) :=
    Submodule.sum_mem _ fun J _ ↦ Submodule.smul_mem _ _ (ιMulti_mem_exteriorPower _)
  have hΘ'mem : Θ' ∈ ⋀[ℂ]^p (E →L[ℝ] ℂ) :=
    Submodule.sum_mem _ fun J _ ↦ Submodule.smul_mem _ _ (ιMulti_mem_exteriorPower _)
  have hKmem : K ∈ ⋀[ℂ]^2 (E →L[ℝ] ℂ) := by
    refine Submodule.smul_mem _ _ ?_
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Submodule.sum_mem _ fun j _ ↦ ι_mul_ι_mem_exteriorPower _ _
  have hΘ : toForms E ℂ Θ p = θ := by
    rw [hθ.eq_sum_detForm u]
    simp only [Θ, _root_.map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, toForms_ιMulti_self]
    rfl
  have hΘ' : toForms E ℂ Θ' p = conjForm θ := by
    conv_rhs => rw [hθ.eq_sum_detForm u]
    simp only [Θ', _root_.map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, toForms_ιMulti_self,
      conjForm_finsetSum, conjForm_smul, conjForm_detForm_coordFormsOf]
    rfl
  have hK : toForms E ℂ K 2 = κ := by
    rw [hκ.eq_sum_of_unitary u hu]
    simp only [K, P, map_smul, Pi.smul_apply, AddSubmonoidClass.coe_finsetSum, _root_.map_sum,
      Finset.sum_apply, coe_pairCenter, toForms_ι_mul_ι]
    rfl
  have hKm : ∀ k : ℕ, toForms E ℂ (K ^ k) (2 * k) = wedgePow κ k := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, wedgePow_zero]
      have : (1 : ExteriorAlgebra ℂ (E →L[ℝ] ℂ)) = ιMulti ℂ 0 (Fin.elim0) := by simp
      rw [this, toForms_ιMulti_self]
      ext v
      simp [detForm_apply]
    | succ k ih =>
      rw [pow_succ, wedgePow_succ, ← ih, ← hK]
      exact toForms_mul (pow_mem_exteriorPower hKmem k) hKmem
  have hprod : toForms E ℂ (Θ * Θ' * K ^ m) ((p + p) + 2 * m) =
      (θ ⋏ conjForm θ) ⋏ wedgePow κ m := by
    rw [toForms_mul (mul_mem_exteriorPower hΘmem hΘ'mem) (pow_mem_exteriorPower hKmem m),
      toForms_mul hΘmem hΘ'mem, hΘ, hΘ', hKm]
  have hcomp : Θ * Θ' * K ^ m = ((Complex.I / 2) ^ m * ((m.factorial : ℂ) * (-1) ^ p.choose 2 *
      ∑ J, θ (basisOf u J) * conj (θ (basisOf u J)))) •
        ((∏ j, pairCenter ℂ a b j : Subalgebra.center ℂ _) : ExteriorAlgebra ℂ _) := by
    rw [smul_pow, mul_smul_comm, ← SubmonoidClass.coe_pow,
      sum_mul_sum_mul_pow_sum_pairCenter a b hpm, smul_smul]
  rw [← hprod, hcomp, map_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    toForms_congr_degree _ h.symm, domDomCongr_apply]
  congr 1
  convert toForms_prod_pairCenter_basisFrame u using 2
  ext i
  simp

/-! ### Positivity in any complex frame -/

/-- The value of `(-1)^(n choose 2) i^{p²} θ ⋏ θ̄ ⋏ κᵐ` on the frame of any complex basis `w`:
`|det_ℂ (u ↦ w)|² 2ᵖ m! ∑_J |θ(u_J)|²` for a unitary frame `u` of `κ`. -/
theorem IsPositiveForm.wedge_conj_wedgePow_apply_eq {κ : E [⋀^Fin 2]→L[ℝ] ℂ}
    (hκ : IsPositiveForm κ) {p m : ℕ} (hpm : p + m = Module.finrank ℂ E)
    {θ : E [⋀^Fin p]→L[ℝ] ℂ} (hθ : IsOfType p 0 θ)
    (w : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E)
    (h : (p + p) + 2 * m = Module.finrank ℂ E + Module.finrank ℂ E) :
    ∃ (u : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E) (d : ℂ), d ≠ 0 ∧
      ((-1) ^ (Module.finrank ℂ E).choose 2 * Complex.I ^ (p ^ 2)) *
          ((θ ⋏ conjForm θ) ⋏ wedgePow κ m) (fun i ↦ basisFrame w (finCongr h i)) =
        ((Complex.normSq d * 2 ^ p * m.factorial *
          ∑ J : Set.powersetCard (Fin (Module.finrank ℂ E)) p,
            Complex.normSq (θ (basisOf u J)) : ℝ) : ℂ) := by
  obtain ⟨u, hu⟩ := hκ.exists_unitary_basis
  have hk : Module.finrank ℝ E = (p + p) + 2 * m := by
    rw [finrank_real_of_complex]
    omega
  let A : E →L[ℂ] E := (u.equiv w (Equiv.refl _)).toContinuousLinearEquiv
  have hframe : (fun i ↦ basisFrame w (finCongr h i)) =
      (A.restrictScalars ℝ : E →L[ℝ] E) ∘ fun i ↦ basisFrame u (finCongr h i) := by
    ext i
    rw [basisFrame_map u w]
    rfl
  refine ⟨u, LinearMap.det (A : E →ₗ[ℂ] E), ?_, ?_⟩
  · exact (LinearEquiv.isUnit_det' (u.equiv w (Equiv.refl _))).ne_zero
  rw [hframe, ContinuousAlternatingMap.map_comp_eq_det_mul hk,
    ContinuousLinearMap.det_restrictScalars_eq_normSq,
    hκ.wedge_conj_wedgePow_apply_basisFrame u hu hpm hθ h]
  have hS : ∑ J : Set.powersetCard (Fin (Module.finrank ℂ E)) p,
      θ (basisOf u J) * conj (θ (basisOf u J)) =
      ((∑ J : Set.powersetCard (Fin (Module.finrank ℂ E)) p,
        Complex.normSq (θ (basisOf u J)) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun J _ ↦ Complex.mul_conj _
  rw [hS]
  have e1 : (-2 * Complex.I) ^ Module.finrank ℂ E =
      2 ^ p * (-Complex.I) ^ p * (-2 * Complex.I) ^ m := by
    rw [← hpm, pow_add, show -2 * Complex.I = 2 * -Complex.I by ring, mul_pow]
  rw [e1]
  have e2 := I_pow_sq_mul_neg_one_pow_choose_mul p
  have e3 := I_div_two_pow_mul_neg_two_I_pow m
  have e4 : ((-1 : ℂ) ^ (Module.finrank ℂ E).choose 2) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  push_cast
  linear_combination (((Complex.normSq (LinearMap.det (A : E →ₗ[ℂ] E)) : ℂ) * 2 ^ p *
      (m.factorial : ℂ) * ∑ J : Set.powersetCard (Fin (Module.finrank ℂ E)) p,
        (Complex.normSq (θ (basisOf u J)) : ℂ))) *
    (((-1 : ℂ) ^ (Module.finrank ℂ E).choose 2) ^ 2 * (Complex.I ^ (p ^ 2) * (-1) ^ p.choose 2 *
      (-Complex.I) ^ p) * e3 + ((-1 : ℂ) ^ (Module.finrank ℂ E).choose 2) ^ 2 * e2 + e4)

/-- **Positivity of `i^{p²} θ ∧ θ̄ ∧ κᵐ`** (Hodge–Riemann for `(p, 0)`-forms): for a positive
real `(1, 1)`-form `κ` on `E` (`n = dim_ℂ E`), a form `θ` of type `(p, 0)` with `p + m = n`, and
any complex basis `w` of `E`, the number
`(-1)^(n choose 2) i^{p²} (θ ⋏ θ̄ ⋏ κᵐ)(w₀, …, w_{n-1}, iw₀, …, iw_{n-1})` is real and `≥ 0`. -/
theorem IsPositiveForm.wedge_conj_wedgePow_nonneg {κ : E [⋀^Fin 2]→L[ℝ] ℂ}
    (hκ : IsPositiveForm κ) {p m : ℕ} (hpm : p + m = Module.finrank ℂ E)
    {θ : E [⋀^Fin p]→L[ℝ] ℂ} (hθ : IsOfType p 0 θ)
    (w : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E)
    (h : (p + p) + 2 * m = Module.finrank ℂ E + Module.finrank ℂ E) :
    0 ≤ ((-1) ^ (Module.finrank ℂ E).choose 2 * Complex.I ^ (p ^ 2)) *
      ((θ ⋏ conjForm θ) ⋏ wedgePow κ m) (fun i ↦ basisFrame w (finCongr h i)) := by
  obtain ⟨u, d, -, hval⟩ := hκ.wedge_conj_wedgePow_apply_eq hpm hθ w h
  rw [hval]
  exact Complex.zero_le_real.2 (mul_nonneg (mul_nonneg (mul_nonneg (Complex.normSq_nonneg _)
    (by positivity)) (by positivity)) (Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _))

/-- **Strict positivity of `i^{p²} θ ∧ θ̄ ∧ κᵐ`** for `θ ≠ 0` (see
`Hodge.IsPositiveForm.wedge_conj_wedgePow_nonneg`). -/
theorem IsPositiveForm.wedge_conj_wedgePow_pos {κ : E [⋀^Fin 2]→L[ℝ] ℂ}
    (hκ : IsPositiveForm κ) {p m : ℕ} (hpm : p + m = Module.finrank ℂ E)
    {θ : E [⋀^Fin p]→L[ℝ] ℂ} (hθ : IsOfType p 0 θ) (hθ0 : θ ≠ 0)
    (w : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E)
    (h : (p + p) + 2 * m = Module.finrank ℂ E + Module.finrank ℂ E) :
    0 < ((-1) ^ (Module.finrank ℂ E).choose 2 * Complex.I ^ (p ^ 2)) *
      ((θ ⋏ conjForm θ) ⋏ wedgePow κ m) (fun i ↦ basisFrame w (finCongr h i)) := by
  obtain ⟨u, d, hd, hval⟩ := hκ.wedge_conj_wedgePow_apply_eq hpm hθ w h
  rw [hval]
  refine Complex.zero_lt_real.2 (mul_pos (mul_pos (mul_pos (Complex.normSq_pos.2 hd)
    (by positivity)) (by positivity)) ?_)
  -- some coefficient `θ (u_J)` is nonzero
  obtain ⟨J, hJ⟩ : ∃ J, θ (basisOf u J) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hθ0
    rw [hθ.eq_sum_detForm u]
    simp [hall]
  exact Finset.sum_pos' (fun J _ ↦ Complex.normSq_nonneg _)
    ⟨J, Finset.mem_univ _, Complex.normSq_pos.2 hJ⟩

end Hodge
