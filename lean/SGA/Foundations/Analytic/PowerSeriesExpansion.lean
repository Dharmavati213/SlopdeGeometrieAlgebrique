/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ConvergentPowerSeries
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Power series expansions of analytic functions of several variables

Let `𝕜` be a complete nontrivially normed field and `σ` a finite type. A convergent power series
`f = ∑ aₐ Xᵅ ∈ 𝕜{X}` defines, on a polydisc around `0`, the function
`tsumEval f z = ∑ aₐ zᵅ`, which is analytic at `0` in the sense of Fréchet power series
(`hasFPowerSeriesOnBall_tsumEval`). Conversely every function `𝕜^σ → 𝕜` analytic at `0` is,
near `0`, the sum of a unique convergent power series (`exists_convergent_eventuallyEq`,
`eq_of_tsumEval_eventuallyEq`). Sums and products of series correspond to sums and products
of functions.

The passage between the two languages goes through the formal multilinear series
`toFormalMultilinearSeries f`, whose `m`-th term is `∑_{|α| = m} aₐ ∏ⱼ vⱼ(e_α j)` for a choice
of tuples `e_α` with multi-index `α`, and through `ofFormalMultilinearSeries p`, which reads off
the coefficients of a multilinear series on the standard basis.
-/

open scoped NNReal ENNReal Topology
open Finset Filter

noncomputable section

namespace MvPowerSeries

variable {σ : Type*}

/-! ### Multi-indices of tuples -/

section MultiIndex

/-- The multi-index `α` of a tuple `e : Fin m → σ`: `αᵢ` is the number of `j` with `e j = i`. -/
def multiIndex {m : ℕ} (e : Fin m → σ) : σ →₀ ℕ :=
  ∑ j, Finsupp.single (e j) 1

lemma multiIndex_succ {m : ℕ} (e : Fin (m + 1) → σ) :
    multiIndex e = Finsupp.single (e 0) 1 + multiIndex (fun j ↦ e j.succ) := by
  simp [multiIndex, Fin.sum_univ_succ]

@[simp] lemma multiIndex_zero (e : Fin 0 → σ) : multiIndex e = 0 := by
  simp [multiIndex]

@[simp] lemma degree_multiIndex {m : ℕ} (e : Fin m → σ) : (multiIndex e).degree = m := by
  simp [multiIndex, map_sum, Finsupp.degree_single]

lemma monomialEval_multiIndex {M : Type*} [CommMonoid M] (z : σ → M) {m : ℕ} (e : Fin m → σ) :
    monomialEval z (multiIndex e) = ∏ j, z (e j) := by
  induction m with
  | zero => simp
  | succ m ih => rw [multiIndex_succ, monomialEval_add, ih, monomialEval_single, pow_one,
      Fin.prod_univ_succ]

lemma exists_multiIndex_eq (α : σ →₀ ℕ) {m : ℕ} (h : α.degree = m) :
    ∃ e : Fin m → σ, multiIndex e = α := by
  induction m generalizing α with
  | zero => exact ⟨Fin.elim0, by rw [multiIndex_zero, eq_comm, ← Finsupp.degree_eq_zero_iff, h]⟩
  | succ m ih =>
    have hα : α ≠ 0 := by rintro rfl; simp at h
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra! H
      exact hα (Finsupp.ext H)
    have hle : Finsupp.single i 1 ≤ α := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.mpr hi
    have hdeg : (α - Finsupp.single i 1).degree = m := by
      have := congr_arg Finsupp.degree (tsub_add_cancel_of_le hle)
      rw [map_add, Finsupp.degree_single, h] at this
      omega
    obtain ⟨e, he⟩ := ih _ hdeg
    refine ⟨Fin.cons i e, ?_⟩
    rw [multiIndex_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [he, add_comm, tsub_add_cancel_of_le hle]

/-- A tuple with multi-index `α`. -/
def tupleOf (α : σ →₀ ℕ) {m : ℕ} (h : α.degree = m) : Fin m → σ :=
  (exists_multiIndex_eq α h).choose

@[simp] lemma multiIndex_tupleOf (α : σ →₀ ℕ) {m : ℕ} (h : α.degree = m) :
    multiIndex (tupleOf α h) = α :=
  (exists_multiIndex_eq α h).choose_spec

variable [Fintype σ]

open Classical in
/-- The (finite) set of multi-indices of total degree `m`. -/
def degreeFinset (σ : Type*) [Fintype σ] (m : ℕ) : Finset (σ →₀ ℕ) :=
  univ.image (multiIndex (σ := σ) (m := m))

@[simp] lemma mem_degreeFinset {m : ℕ} {α : σ →₀ ℕ} : α ∈ degreeFinset σ m ↔ α.degree = m := by
  classical
  simp only [degreeFinset, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨e, rfl⟩
    exact degree_multiIndex e
  · exact fun h ↦ exists_multiIndex_eq α h

lemma coe_degreeFinset (m : ℕ) :
    (degreeFinset σ m : Set (σ →₀ ℕ)) = Finsupp.degree ⁻¹' {m} := by
  ext α
  simp

/-- Summing over tuples is summing over multi-indices and then over the tuples with that
multi-index. -/
lemma sum_tuples_eq [DecidableEq σ] {M : Type*} [AddCommMonoid M] (m : ℕ) (F : (Fin m → σ) → M) :
    ∑ e, F e = ∑ α ∈ degreeFinset σ m, ∑ e with multiIndex e = α, F e := by
  classical
  refine (sum_fiberwise_of_maps_to (fun e _ ↦ ?_) F).symm
  simp

lemma sum_card_fiber [DecidableEq σ] (m : ℕ) :
    ∑ α ∈ degreeFinset σ m, #{e : Fin m → σ | multiIndex e = α} = Fintype.card σ ^ m := by
  have h := sum_tuples_eq (σ := σ) (M := ℕ) m fun _ ↦ 1
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul,
    mul_one] at h
  exact h.symm

end MultiIndex

/-! ### The formal multilinear series of a power series -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section Multilinear

/-- The continuous multilinear map `(v₁, …, vₘ) ↦ ∏ⱼ vⱼ(e j)` on `(σ → 𝕜)ᵐ`. -/
def monomialMultilinear {m : ℕ} (e : Fin m → σ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin m ↦ σ → 𝕜) 𝕜 :=
  (ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin m) 𝕜).compContinuousLinearMap
    fun j ↦ ContinuousLinearMap.proj (e j)

@[simp] lemma monomialMultilinear_apply {m : ℕ} (e : Fin m → σ) (v : Fin m → σ → 𝕜) :
    monomialMultilinear e v = ∏ j, v j (e j) := by
  simp [monomialMultilinear]

variable [Fintype σ]

lemma norm_monomialMultilinear_le {m : ℕ} (e : Fin m → σ) :
    ‖monomialMultilinear (𝕜 := 𝕜) e‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun v ↦ ?_
  rw [monomialMultilinear_apply, norm_prod, one_mul]
  exact prod_le_prod (fun _ _ ↦ norm_nonneg _) fun j _ ↦ norm_le_pi_norm (v j) (e j)

/-- The formal multilinear series of a power series: its `m`-th term is the homogeneous part of
degree `m`, `(v₁, …, vₘ) ↦ ∑_{|α| = m} aₐ ∏ⱼ vⱼ(e_α j)`. -/
def toFormalMultilinearSeries (f : MvPowerSeries σ 𝕜) :
    FormalMultilinearSeries 𝕜 (σ → 𝕜) 𝕜 := fun m ↦
  ∑ α ∈ (degreeFinset σ m).attach,
    coeff α.1 f • monomialMultilinear (tupleOf α.1 (mem_degreeFinset.mp α.2))

lemma toFormalMultilinearSeries_apply_const (f : MvPowerSeries σ 𝕜) (m : ℕ) (y : σ → 𝕜) :
    toFormalMultilinearSeries f m (fun _ ↦ y) =
      ∑ α ∈ degreeFinset σ m, coeff α f * monomialEval y α := by
  rw [toFormalMultilinearSeries, _root_.sum_apply]
  simp only [smul_apply, monomialMultilinear_apply, smul_eq_mul]
  rw [← sum_attach (degreeFinset σ m) (fun α ↦ coeff α f * monomialEval y α)]
  refine sum_congr rfl fun α _ ↦ ?_
  rw [← monomialEval_multiIndex, multiIndex_tupleOf]

lemma norm_toFormalMultilinearSeries_le (f : MvPowerSeries σ 𝕜) (m : ℕ) :
    ‖toFormalMultilinearSeries f m‖ ≤ ∑ α ∈ degreeFinset σ m, ‖coeff α f‖ := by
  rw [toFormalMultilinearSeries, ← sum_attach (degreeFinset σ m) (fun α ↦ ‖coeff α f‖)]
  refine (norm_sum_le _ _).trans (sum_le_sum fun α _ ↦ ?_)
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_monomialMultilinear_le _)

end Multilinear

/-! ### Evaluation of power series -/

section Eval

/-- The value `∑ aₐ zᵅ` of a power series at `z` (meaningful when the series converges
absolutely, e.g. when `‖zᵢ‖ ≤ ρᵢ` for a polyradius `ρ` with `‖f‖_ρ < ∞`). -/
def tsumEval (f : MvPowerSeries σ 𝕜) (z : σ → 𝕜) : 𝕜 :=
  ∑' α, coeff α f * monomialEval z α

variable {f g : MvPowerSeries σ 𝕜} {ρ : σ → ℝ≥0} {z : σ → 𝕜}

lemma summable_norm_coeff_mul_monomialEval (hf : weightedNorm ρ f ≠ ⊤)
    (hz : ∀ i, ‖z i‖₊ ≤ ρ i) : Summable fun α ↦ ‖coeff α f * monomialEval z α‖ := by
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun α ↦ ?_)
    (NNReal.summable_coe.mpr (summable_of_weightedNorm_ne_top ρ hf))
  rw [← coe_nnnorm, NNReal.coe_le_coe, nnnorm_mul, norm_monomialEval]
  gcongr
  exact monomialEval_le_monomialEval hz α

lemma tsumEval_neg : tsumEval (-f) z = -tsumEval f z := by
  simp [tsumEval, tsum_neg]

lemma tsumEval_smul (c : 𝕜) : tsumEval (c • f) z = c * tsumEval f z := by
  simp [tsumEval, mul_assoc, tsum_mul_left]

@[simp] lemma tsumEval_C (c : 𝕜) : tsumEval (C (σ := σ) c) z = c := by
  classical
  rw [tsumEval, tsum_eq_single 0]
  · simp
  · intro α hα
    simp [coeff_C, hα]

@[simp] lemma tsumEval_one : tsumEval (1 : MvPowerSeries σ 𝕜) z = 1 := by
  simpa using tsumEval_C (σ := σ) (z := z) (1 : 𝕜)

@[simp] lemma tsumEval_monomial (α : σ →₀ ℕ) (c : 𝕜) :
    tsumEval (monomial α c) z = c * monomialEval z α := by
  classical
  rw [tsumEval, tsum_eq_single α]
  · simp
  · intro β hβ
    simp [coeff_monomial, hβ]

@[simp] lemma tsumEval_X (i : σ) : tsumEval (X i : MvPowerSeries σ 𝕜) z = z i := by
  change tsumEval (monomial (Finsupp.single i 1) 1) z = z i
  rw [tsumEval_monomial, monomialEval_single, pow_one, one_mul]

variable [CompleteSpace 𝕜]

lemma hasSum_tsumEval (hf : weightedNorm ρ f ≠ ⊤) (hz : ∀ i, ‖z i‖₊ ≤ ρ i) :
    HasSum (fun α ↦ coeff α f * monomialEval z α) (tsumEval f z) :=
  (summable_norm_coeff_mul_monomialEval hf hz).of_norm.hasSum

lemma tsumEval_add (hf : weightedNorm ρ f ≠ ⊤) (hg : weightedNorm ρ g ≠ ⊤)
    (hz : ∀ i, ‖z i‖₊ ≤ ρ i) : tsumEval (f + g) z = tsumEval f z + tsumEval g z := by
  have h₁ := (summable_norm_coeff_mul_monomialEval hf hz).of_norm
  have h₂ := (summable_norm_coeff_mul_monomialEval hg hz).of_norm
  rw [tsumEval, tsumEval, tsumEval, ← h₁.tsum_add h₂]
  simp only [map_add, add_mul]

lemma tsumEval_sub (hf : weightedNorm ρ f ≠ ⊤) (hg : weightedNorm ρ g ≠ ⊤)
    (hz : ∀ i, ‖z i‖₊ ≤ ρ i) : tsumEval (f - g) z = tsumEval f z - tsumEval g z := by
  rw [sub_eq_add_neg, tsumEval_add hf (by rwa [weightedNorm_neg]) hz, tsumEval_neg,
    sub_eq_add_neg]

lemma tsumEval_mul (hf : weightedNorm ρ f ≠ ⊤) (hg : weightedNorm ρ g ≠ ⊤)
    (hz : ∀ i, ‖z i‖₊ ≤ ρ i) : tsumEval (f * g) z = tsumEval f z * tsumEval g z := by
  classical
  have h₁ := summable_norm_coeff_mul_monomialEval hf hz
  have h₂ := summable_norm_coeff_mul_monomialEval hg hz
  have h₃ := summable_mul_of_summable_norm (f := fun α ↦ coeff α f * monomialEval z α)
    (g := fun α ↦ coeff α g * monomialEval z α) h₁ h₂
  rw [tsumEval, tsumEval, tsumEval, Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (A := σ →₀ ℕ) (f := fun α ↦ coeff α f * monomialEval z α)
    (g := fun α ↦ coeff α g * monomialEval z α) h₁.of_norm h₂.of_norm h₃]
  refine tsum_congr fun γ ↦ ?_
  rw [coeff_mul, sum_mul]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [← mem_antidiagonal.mp hp, monomialEval_add]
  ring

end Eval

/-! ### Convergent power series are analytic -/

section Analytic

variable [Fintype σ] [CompleteSpace 𝕜] {f : MvPowerSeries σ 𝕜}

omit [CompleteSpace 𝕜] in
lemma nnnorm_apply_le_of_mem_eball {r : ℝ≥0} {y : σ → 𝕜} (hy : y ∈ Metric.eball (0 : σ → 𝕜) r)
    (i : σ) : ‖y i‖₊ ≤ r := by
  rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_coe] at hy
  exact (nnnorm_le_pi_nnnorm y i).trans hy.le

/-- A convergent power series is the power series expansion of its sum on a ball around `0`. -/
theorem hasFPowerSeriesOnBall_tsumEval {r : ℝ≥0} (hr : 0 < r)
    (hf : weightedNorm (fun _ ↦ r) f ≠ ⊤) :
    HasFPowerSeriesOnBall (tsumEval f) (toFormalMultilinearSeries f) 0 r where
  r_le := by
    refine (toFormalMultilinearSeries f).le_radius_of_bound
      (weightedNorm (fun _ ↦ r) f).toReal fun m ↦ ?_
    have hs := NNReal.summable_coe.mpr (summable_of_weightedNorm_ne_top _ hf)
    calc ‖toFormalMultilinearSeries f m‖ * (r : ℝ) ^ m
        ≤ (∑ α ∈ degreeFinset σ m, ‖coeff α f‖) * (r : ℝ) ^ m := by
          gcongr
          exact norm_toFormalMultilinearSeries_le f m
      _ = ∑ α ∈ degreeFinset σ m,
          ((‖coeff α f‖₊ * monomialEval (fun _ ↦ r) α : ℝ≥0) : ℝ) := by
          rw [sum_mul]
          refine sum_congr rfl fun α hα ↦ ?_
          rw [monomialEval_const, mem_degreeFinset.mp hα]
          simp
      _ ≤ ∑' α, ((‖coeff α f‖₊ * monomialEval (fun _ ↦ r) α : ℝ≥0) : ℝ) :=
          hs.sum_le_tsum _ fun _ _ ↦ NNReal.coe_nonneg _
      _ = (weightedNorm (fun _ ↦ r) f).toReal := by
          rw [weightedNorm_eq_tsum _ hf, ENNReal.coe_toReal, NNReal.coe_tsum]
  r_pos := ENNReal.coe_pos.mpr hr
  hasSum {y} hy := by
    have hs := (hasSum_tsumEval hf (nnnorm_apply_le_of_mem_eball hy)).tsum_fiberwise
      Finsupp.degree
    rw [zero_add]
    convert hs using 2 with m
    rw [toFormalMultilinearSeries_apply_const, ← coe_degreeFinset,
      Finset.tsum_subtype' (degreeFinset σ m) (fun α ↦ coeff α f * monomialEval y α)]

theorem analyticAt_tsumEval (hf : f ∈ convergent σ 𝕜) : AnalyticAt 𝕜 (tsumEval f) 0 := by
  obtain ⟨r, hr, hfr⟩ := exists_weightedNorm_const_ne_top hf
  exact (hasFPowerSeriesOnBall_tsumEval hr hfr).analyticAt

end Analytic

section Finite

variable [Finite σ] {f : MvPowerSeries σ 𝕜}

/-- Near `0`, a convergent power series converges absolutely. -/
lemma eventually_nnnorm_le (hf : f ∈ convergent σ 𝕜) :
    ∃ r : ℝ≥0, 0 < r ∧ weightedNorm (fun _ ↦ r) f ≠ ⊤ ∧
      ∀ᶠ z in 𝓝 (0 : σ → 𝕜), ∀ i, ‖z i‖₊ ≤ r := by
  have := Fintype.ofFinite σ
  obtain ⟨r, hr, hfr⟩ := exists_weightedNorm_const_ne_top hf
  refine ⟨r, hr, hfr, ?_⟩
  filter_upwards [Metric.eball_mem_nhds (0 : σ → 𝕜) (ENNReal.coe_pos.mpr hr)] with z hz
  exact nnnorm_apply_le_of_mem_eball hz

variable [CompleteSpace 𝕜]

/-- Near `0`, evaluation of convergent power series is a ring homomorphism. -/
lemma eventually_tsumEval_add_mul {f g : MvPowerSeries σ 𝕜} (hf : f ∈ convergent σ 𝕜)
    (hg : g ∈ convergent σ 𝕜) :
    ∀ᶠ z in 𝓝 (0 : σ → 𝕜), tsumEval (f + g) z = tsumEval f z + tsumEval g z ∧
      tsumEval (f * g) z = tsumEval f z * tsumEval g z := by
  obtain ⟨r, hr, hfr, h₁⟩ := eventually_nnnorm_le hf
  obtain ⟨s, hs, hgs, h₂⟩ := eventually_nnnorm_le hg
  have hf' := ne_top_of_le_ne_top hfr (weightedNorm_mono (fun _ ↦ min_le_left r s) f)
  have hg' := ne_top_of_le_ne_top hgs (weightedNorm_mono (fun _ ↦ min_le_right r s) g)
  filter_upwards [h₁, h₂] with z hz₁ hz₂
  have hz : ∀ i, ‖z i‖₊ ≤ min r s := fun i ↦ le_min (hz₁ i) (hz₂ i)
  exact ⟨tsumEval_add hf' hg' hz, tsumEval_mul hf' hg' hz⟩

/-- **Identity theorem for power series**: a convergent power series whose sum vanishes near `0`
is zero. -/
theorem eq_zero_of_tsumEval_eventuallyEq_zero (hf : f ∈ convergent σ 𝕜)
    (h : tsumEval f =ᶠ[𝓝 0] 0) : f = 0 := by
  classical
  have := Fintype.ofFinite σ
  obtain ⟨r, hr, hfr⟩ := exists_weightedNorm_const_ne_top hf
  have hp : HasFPowerSeriesAt 0 (toFormalMultilinearSeries f) 0 :=
    (hasFPowerSeriesOnBall_tsumEval hr hfr).hasFPowerSeriesAt.congr h
  ext α
  have key : ∀ y : σ → 𝕜,
      ∑ β ∈ degreeFinset σ α.degree, coeff β f * monomialEval y β = 0 := fun y ↦ by
    rw [← toFormalMultilinearSeries_apply_const]
    exact hp.apply_eq_zero _ y
  let P : MvPolynomial σ 𝕜 :=
    ∑ β ∈ degreeFinset σ α.degree, MvPolynomial.monomial β (coeff β f)
  have hP : P = 0 := MvPolynomial.funext fun y ↦ by
    simp only [P, map_sum, MvPolynomial.eval_monomial, map_zero]
    exact key y
  have := congr_arg (MvPolynomial.coeff α) hP
  simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero,
    sum_ite_eq', mem_degreeFinset, ite_true] at this
  simpa using this

theorem eq_of_tsumEval_eventuallyEq {f g : MvPowerSeries σ 𝕜} (hf : f ∈ convergent σ 𝕜)
    (hg : g ∈ convergent σ 𝕜) (h : tsumEval f =ᶠ[𝓝 0] tsumEval g) : f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_tsumEval_eventuallyEq_zero (sub_mem hf hg) ?_
  obtain ⟨r, hr, hfr, h₁⟩ := eventually_nnnorm_le hf
  obtain ⟨s, hs, hgs, h₂⟩ := eventually_nnnorm_le hg
  have hf' := ne_top_of_le_ne_top hfr (weightedNorm_mono (fun _ ↦ min_le_left r s) f)
  have hg' := ne_top_of_le_ne_top hgs (weightedNorm_mono (fun _ ↦ min_le_right r s) g)
  filter_upwards [h, h₁, h₂] with z hz hz₁ hz₂
  rw [tsumEval_sub hf' hg' fun i ↦ le_min (hz₁ i) (hz₂ i), hz, sub_self, Pi.zero_apply]

end Finite

/-! ### Analytic functions are sums of convergent power series -/

section OfFormalMultilinearSeries

variable [Fintype σ] [DecidableEq σ]

/-- The coefficients of a formal multilinear series on `𝕜^σ` in the monomial basis: the
coefficient of `Xᵅ` is `∑ p_{|α|}(e_{e 1}, …, e_{e |α|})` over the tuples `e` with multi-index
`α`. -/
def ofFormalMultilinearSeries (p : FormalMultilinearSeries 𝕜 (σ → 𝕜) 𝕜) :
    MvPowerSeries σ 𝕜 := fun α ↦
  ∑ e : Fin α.degree → σ with multiIndex e = α, p α.degree fun j ↦ Pi.single (e j) 1

lemma coeff_ofFormalMultilinearSeries (p : FormalMultilinearSeries 𝕜 (σ → 𝕜) 𝕜)
    (α : σ →₀ ℕ) : coeff α (ofFormalMultilinearSeries p) =
      ∑ e : Fin α.degree → σ with multiIndex e = α, p α.degree fun j ↦ Pi.single (e j) 1 :=
  rfl

lemma apply_const_eq_sum_coeff (p : FormalMultilinearSeries 𝕜 (σ → 𝕜) 𝕜) (m : ℕ)
    (y : σ → 𝕜) : p m (fun _ ↦ y) =
      ∑ α ∈ degreeFinset σ m, coeff α (ofFormalMultilinearSeries p) * monomialEval y α := by
  have hy : y = ∑ i, y i • (Pi.single i 1 : σ → 𝕜) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hy, (p m).map_sum_finset]
  simp only [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  rw [← hy, Fintype.piFinset_univ, sum_tuples_eq]
  refine sum_congr rfl fun α hα ↦ ?_
  obtain rfl := mem_degreeFinset.mp hα
  rw [coeff_ofFormalMultilinearSeries, sum_mul]
  refine sum_congr rfl fun e he ↦ ?_
  have : monomialEval y α = ∏ i, y (e i) := by
    rw [← monomialEval_multiIndex, (mem_filter.mp he).2]
  rw [this, mul_comm]

lemma nnnorm_coeff_ofFormalMultilinearSeries_le (p : FormalMultilinearSeries 𝕜 (σ → 𝕜) 𝕜)
    (α : σ →₀ ℕ) : ‖coeff α (ofFormalMultilinearSeries p)‖₊ ≤
      #{e : Fin α.degree → σ | multiIndex e = α} * ‖p α.degree‖₊ := by
  rw [coeff_ofFormalMultilinearSeries]
  refine (nnnorm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun e _ ↦ ((p α.degree).le_opNNNorm _).trans (le_of_eq ?_)
  simp [Pi.nnnorm_single]

lemma weightedNorm_ofFormalMultilinearSeries_ne_top (p : FormalMultilinearSeries 𝕜 (σ → 𝕜) 𝕜)
    {s : ℝ≥0} (hs : ((Fintype.card σ * s : ℝ≥0) : ℝ≥0∞) < p.radius) :
    weightedNorm (fun _ ↦ s) (ofFormalMultilinearSeries p) ≠ ⊤ := by
  have hsum := p.summable_nnnorm_mul_pow hs
  refine ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := ∑' m, ‖p m‖₊ * (Fintype.card σ * s) ^ m))
    ?_
  rw [weightedNorm, ← ENNReal.tsum_fiberwise _ Finsupp.degree, ENNReal.coe_tsum hsum]
  refine ENNReal.tsum_le_tsum fun m ↦ ?_
  rw [← coe_degreeFinset, Finset.tsum_subtype' (degreeFinset σ m)
    (fun α ↦ ((‖coeff α (ofFormalMultilinearSeries p)‖₊ * monomialEval (fun _ ↦ s) α : ℝ≥0) :
      ℝ≥0∞)), ← ENNReal.ofNNReal_finsetSum, ENNReal.coe_le_coe]
  calc ∑ α ∈ degreeFinset σ m, ‖coeff α (ofFormalMultilinearSeries p)‖₊ *
        monomialEval (fun _ ↦ s) α
      ≤ ∑ α ∈ degreeFinset σ m, #{e : Fin m → σ | multiIndex e = α} * ‖p m‖₊ * s ^ m := by
        refine sum_le_sum fun α hα ↦ ?_
        obtain rfl := mem_degreeFinset.mp hα
        rw [monomialEval_const]
        gcongr
        exact nnnorm_coeff_ofFormalMultilinearSeries_le p α
    _ = ‖p m‖₊ * (Fintype.card σ * s) ^ m := by
        rw [← sum_mul, ← sum_mul, ← Nat.cast_sum, sum_card_fiber, mul_pow]
        push_cast
        ring

omit [DecidableEq σ] in
/-- **Power series expansion**: a function analytic at `0` is, near `0`, the sum of a convergent
power series. -/
theorem exists_convergent_eventuallyEq [CompleteSpace 𝕜] {F : (σ → 𝕜) → 𝕜}
    (hF : AnalyticAt 𝕜 F 0) :
    ∃ f ∈ convergent σ 𝕜, F =ᶠ[𝓝 0] tsumEval f := by
  classical
  obtain ⟨p, r, hp⟩ := hF
  obtain ⟨t, ht₀, htr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have ht : 0 < t := ENNReal.coe_pos.mp ht₀
  set s : ℝ≥0 := t / (Fintype.card σ + 1) with hs_def
  have hs : 0 < s := div_pos ht (by positivity)
  have hts : (Fintype.card σ + 1) * s = t := mul_div_cancel₀ t (by positivity)
  have hst : (Fintype.card σ * s : ℝ≥0) < t :=
    hts ▸ mul_lt_mul_of_pos_right (lt_add_one _) hs
  have hsr : ((Fintype.card σ * s : ℝ≥0) : ℝ≥0∞) < p.radius :=
    (ENNReal.coe_lt_coe.mpr hst).trans (htr.trans_le hp.r_le)
  have hfin := weightedNorm_ofFormalMultilinearSeries_ne_top p hsr
  refine ⟨ofFormalMultilinearSeries p, ⟨fun _ ↦ s, fun _ ↦ hs, hfin⟩, ?_⟩
  have hs_le : (s : ℝ≥0∞) ≤ t := ENNReal.coe_le_coe.mpr (hts ▸ le_mul_of_one_le_left
    (by positivity) (by simp))
  filter_upwards [Metric.eball_mem_nhds (0 : σ → 𝕜) (ENNReal.coe_pos.mpr hs)] with y hy
  have hy' : y ∈ Metric.eball (0 : σ → 𝕜) r :=
    Metric.eball_subset_eball (hs_le.trans htr.le) hy
  have h₁ := hp.hasSum hy'
  rw [zero_add] at h₁
  have h₂ := (hasSum_tsumEval hfin (nnnorm_apply_le_of_mem_eball hy)).tsum_fiberwise
    Finsupp.degree
  refine h₁.unique ?_
  convert h₂ using 2 with m
  rw [apply_const_eq_sum_coeff, ← coe_degreeFinset, Finset.tsum_subtype' (degreeFinset σ m)
    (fun α ↦ coeff α (ofFormalMultilinearSeries p) * monomialEval y α)]

end OfFormalMultilinearSeries

end MvPowerSeries
