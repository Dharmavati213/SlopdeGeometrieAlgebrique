/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Analytic.WeierstrassDivision
import SGA.Foundations.Analytic.Substitution
import SGA.Foundations.Analytic.Stalk
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# The ring of convergent power series is noetherian

Let `𝕜` be a complete nontrivially normed field. We view `𝕜{z, y} = 𝕜{Option τ}` as an algebra
over `𝕜{z} = 𝕜{τ}` (by renaming the variables `z`). If `g` is regular of order `b` in `y`, the
Weierstrass division theorem shows that `𝕜{z, y}/(g)` is generated over `𝕜{z}` by
`1, y, …, y^(b-1)` (`module_finite_quotient`). Every non-zero series becomes regular in `y`
after a linear change of coordinates, which gives **Rückert's basis theorem**: `𝕜{z₁, …, zₙ}` is
noetherian ([Grauert–Remmert, *Analytische Stellenalgebren*, I §3]; [Gunning–Rossi, II.B]).
-/

open scoped NNReal ENNReal Topology
open Finset Filter

noncomputable section

namespace MvPowerSeries

variable {τ : Type*}

/-! ### `𝕜{z, y}` as an algebra over `𝕜{z}` -/

section Rename

variable {𝕜 : Type*} [NormedField 𝕜]

/-- The inclusion of the variables `z` into `(z, y)`. -/
abbrev someEmb : τ ↪ Option τ := Function.Embedding.some

lemma coeff_rename_some {R : Type*} [CommSemiring R] (h : MvPowerSeries τ R)
    (β : Option τ →₀ ℕ) :
    coeff β (rename someEmb h) = if β none = 0 then coeff β.some h else 0 := by
  split_ifs with hβ
  · have : β = Finsupp.embDomain someEmb β.some := by
      ext o
      cases o with
      | none => simp [hβ, Finsupp.embDomain_of_notMem_range]
      | some i =>
        rw [show (some i : Option τ) = someEmb i from rfl, Finsupp.embDomain_apply_self]
        rfl
    conv_lhs => rw [this]
    exact coeff_embDomain_rename _ _ _
  · refine coeff_rename_eq_zero _ _ ?_
    rintro ⟨x, rfl⟩
    apply hβ
    rw [← Finsupp.embDomain_eq_mapDomain]
    exact Finsupp.embDomain_of_notMem_range _ _ _ (by simp)

lemma weightedNorm_rename_some (ρ : Option τ → ℝ≥0) (f : MvPowerSeries τ 𝕜) :
    weightedNorm ρ (rename someEmb f) = weightedNorm (fun i ↦ ρ (some i)) f := by
  rw [weightedNorm, weightedNorm, ← (Finsupp.embDomain_injective someEmb).tsum_eq]
  · refine tsum_congr fun x ↦ ?_
    rw [coeff_embDomain_rename, monomialEval, Finsupp.prod_embDomain]
    rfl
  · intro β hβ
    by_contra h
    apply hβ
    dsimp only
    rw [coeff_rename_eq_zero, nnnorm_zero, zero_mul, ENNReal.coe_zero]
    rintro ⟨x, rfl⟩
    exact h ⟨x, Finsupp.embDomain_eq_mapDomain _ _⟩

/-- The coefficient of `y^j` of a power series in `(z, y)`, as a power series in `z`. -/
def yCoeff (j : ℕ) (f : MvPowerSeries (Option τ) 𝕜) : MvPowerSeries τ 𝕜 :=
  PowerSeries.coeff j (optionEquivLeft τ 𝕜 f)

lemma coeff_yCoeff (j : ℕ) (f : MvPowerSeries (Option τ) 𝕜) (x : τ →₀ ℕ) :
    coeff x (yCoeff j f) = coeff (x.optionElim j) f :=
  coeff_coeff_optionEquivLeft f j x

lemma weightedNorm_yCoeff_le (ρ : Option τ → ℝ≥0) (j : ℕ) (f : MvPowerSeries (Option τ) 𝕜) :
    (ρ none : ℝ≥0∞) ^ j * weightedNorm (fun i ↦ ρ (some i)) (yCoeff j f) ≤ weightedNorm ρ f := by
  rw [weightedNorm, ← ENNReal.tsum_mul_left]
  refine le_trans (le_of_eq (tsum_congr fun x ↦ ?_)) (ENNReal.tsum_comp_le_tsum_of_injective
    (f := fun x : τ →₀ ℕ ↦ x.optionElim j) (fun x y h ↦ by
      simpa using congr_arg Finsupp.some h)
    fun β ↦ ((‖coeff β f‖₊ * monomialEval ρ β : ℝ≥0) : ℝ≥0∞))
  rw [coeff_yCoeff, monomialEval_option, Finsupp.optionElim_apply_none, Finsupp.some_optionElim,
    ← ENNReal.coe_pow, ← ENNReal.coe_mul]
  congr 1
  ring

lemma coeff_X_none_pow_mul_rename_some (j : ℕ) (h : MvPowerSeries τ 𝕜) (α : Option τ →₀ ℕ) :
    coeff α (X none ^ j * rename someEmb h) = if α none = j then coeff α.some h else 0 := by
  classical
  rw [coeff_X_none_pow_mul]
  split_ifs with h₁ h₂ h₂
  · have e : (α - Finsupp.single none j).some = α.some := by
      ext i
      simp [Finsupp.some_apply]
    rw [coeff_rename_some, ite_eq_left (by simp [h₂]), e]
  · rw [coeff_rename_some, ite_eq_right (by simp; omega)]
  · omega
  · rfl

/-- A power series of degree `< b` in `y` is a polynomial in `y` with coefficients in the power
series in `z`. -/
lemma IsLow.eq_sum {b : ℕ} {r : MvPowerSeries (Option τ) 𝕜} (hr : IsLow b r) :
    r = ∑ j ∈ range b, X none ^ j * rename someEmb (yCoeff j r) := by
  classical
  ext α
  rw [map_sum]
  simp_rw [coeff_X_none_pow_mul_rename_some]
  rw [sum_ite_eq]
  split_ifs with h
  · rw [coeff_yCoeff, Finsupp.optionElim_some]
  · exact hr α (by simpa using h)

end Rename

section Algebra

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

lemma rename_some_mem_convergent {f : MvPowerSeries τ 𝕜} (hf : f ∈ convergent τ 𝕜) :
    rename someEmb f ∈ convergent (Option τ) 𝕜 := by
  obtain ⟨ρ, hρ, hfin⟩ := hf
  refine ⟨fun o ↦ o.elim 1 ρ, fun o ↦ ?_, ?_⟩
  · cases o with
    | none => exact one_pos
    | some i => exact hρ i
  · rwa [weightedNorm_rename_some]

lemma yCoeff_mem_convergent (j : ℕ) {f : MvPowerSeries (Option τ) 𝕜}
    (hf : f ∈ convergent (Option τ) 𝕜) : yCoeff j f ∈ convergent τ 𝕜 := by
  obtain ⟨ρ, hρ, hfin⟩ := hf
  refine ⟨fun i ↦ ρ (some i), fun i ↦ hρ _, ?_⟩
  have h := weightedNorm_yCoeff_le ρ j f
  have hj : (ρ none : ℝ≥0∞) ^ j ≠ 0 := pow_ne_zero _ (by simp [(hρ none).ne'])
  intro htop
  rw [htop, ENNReal.mul_top hj] at h
  exact hfin (top_le_iff.mp h)

/-- The inclusion `𝕜{z} → 𝕜{z, y}`. -/
def renameSomeHom : convergent τ 𝕜 →ₐ[𝕜] convergent (Option τ) 𝕜 :=
  ((rename someEmb).comp (convergent τ 𝕜).val).codRestrict _ fun f ↦
    rename_some_mem_convergent f.2

@[simp] lemma coe_renameSomeHom (f : convergent τ 𝕜) :
    (renameSomeHom f : MvPowerSeries (Option τ) 𝕜) = rename someEmb f.1 := rfl

instance : Algebra (convergent τ 𝕜) (convergent (Option τ) 𝕜) :=
  (renameSomeHom (τ := τ) (𝕜 := 𝕜)).toRingHom.toAlgebra

lemma algebraMap_convergent_option (f : convergent τ 𝕜) :
    algebraMap (convergent τ 𝕜) (convergent (Option τ) 𝕜) f = renameSomeHom f := rfl

variable [CompleteSpace 𝕜]

/-- If `g ∈ 𝕜{z, y}` is regular of order `b` in `y`, then `𝕜{z, y}/(g)` is a finite
`𝕜{z}`-module, generated by `1, y, …, y^(b-1)`. -/
theorem module_finite_quotient {b : ℕ} (g : convergent (Option τ) 𝕜)
    (hreg : IsRegularOfOrder b g.1) :
    Module.Finite (convergent τ 𝕜) (convergent (Option τ) 𝕜 ⧸ Ideal.span {g}) := by
  classical
  let y : convergent (Option τ) 𝕜 := ⟨X none, X_mem_convergent none⟩
  refine ⟨⟨(range b).image fun j ↦ Ideal.Quotient.mk (Ideal.span {g}) (y ^ j), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨q, hq, r, hr, hlow, heq⟩ := exists_weierstrassDiv g.2 hreg f.2
  have hf : f = g * ⟨q, hq⟩ + ⟨r, hr⟩ := Subtype.ext heq
  have hr' : (⟨r, hr⟩ : convergent (Option τ) 𝕜) = ∑ j ∈ range b,
      algebraMap (convergent τ 𝕜) (convergent (Option τ) 𝕜)
        ⟨yCoeff j r, yCoeff_mem_convergent j hr⟩ * y ^ j := by
    apply Subtype.ext
    change r = _
    conv_lhs => rw [hlow.eq_sum]
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
      algebraMap_convergent_option, coe_renameSomeHom]
    exact sum_congr rfl fun j _ ↦ mul_comm _ _
  have h0 : Ideal.Quotient.mk (Ideal.span {g}) (g * ⟨q, hq⟩) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))
  rw [hf, map_add, h0, zero_add, hr', map_sum]
  refine Submodule.sum_mem _ fun j hj ↦ ?_
  rw [map_mul, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp only [coe_image, Set.mem_image, mem_coe]
  exact ⟨j, hj, rfl⟩

end Algebra

/-! ### Restriction to lines -/

section Lines

variable {σ : Type*} [Fintype σ] {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The restriction of a power series to the line `t ↦ t v`, as a power series in one variable
`t`: its coefficient of `tᵐ` is `∑_{|α| = m} aₐ vᵅ`. -/
def lineSeries (g : MvPowerSeries σ 𝕜) (v : σ → 𝕜) : MvPowerSeries Unit 𝕜 :=
  fun x ↦ ∑ α ∈ degreeFinset σ (x ()), coeff α g * monomialEval v α

lemma coeff_lineSeries (g : MvPowerSeries σ 𝕜) (v : σ → 𝕜) (x : Unit →₀ ℕ) :
    coeff x (lineSeries g v) = ∑ α ∈ degreeFinset σ (x ()), coeff α g * monomialEval v α := rfl

/-- Multi-indices in one variable are natural numbers. -/
def unitFinsuppEquiv : (Unit →₀ ℕ) ≃ ℕ where
  toFun x := x ()
  invFun m := Finsupp.single () m
  left_inv x := (eq_single_unit x).symm
  right_inv m := by simp

lemma nnnorm_monomialEval_le (v : σ → 𝕜) (α : σ →₀ ℕ) :
    ‖monomialEval v α‖₊ ≤ ‖v‖₊ ^ α.degree := by
  rw [norm_monomialEval, ← monomialEval_const]
  exact monomialEval_le_monomialEval (fun i ↦ nnnorm_le_pi_nnnorm v i) α

lemma weightedNorm_lineSeries_le {g : MvPowerSeries σ 𝕜} {r s : ℝ≥0} (v : σ → 𝕜)
    (hs : s * ‖v‖₊ ≤ r) :
    weightedNorm (fun _ ↦ s) (lineSeries g v) ≤ weightedNorm (fun _ ↦ r) g := by
  rw [weightedNorm, ← unitFinsuppEquiv.symm.tsum_eq, weightedNorm,
    ← ENNReal.tsum_fiberwise _ Finsupp.degree]
  refine ENNReal.tsum_le_tsum fun m ↦ ?_
  rw [← coe_degreeFinset, Finset.tsum_subtype' (degreeFinset σ m)
    (fun α ↦ ((‖coeff α g‖₊ * monomialEval (fun _ ↦ r) α : ℝ≥0) : ℝ≥0∞)),
    ← ENNReal.ofNNReal_finsetSum, ENNReal.coe_le_coe]
  change ‖∑ α ∈ degreeFinset σ ((Finsupp.single () m) ()), coeff α g * monomialEval v α‖₊ *
    monomialEval (fun _ ↦ s) (Finsupp.single () m) ≤ _
  rw [Finsupp.single_eq_same, monomialEval_single]
  refine (mul_le_mul_left (nnnorm_sum_le _ _) _).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun α hα ↦ ?_
  rw [mem_degreeFinset] at hα
  rw [nnnorm_mul, monomialEval_const, hα, mul_assoc]
  gcongr
  calc ‖monomialEval v α‖₊ * s ^ m ≤ ‖v‖₊ ^ m * s ^ m := by
        gcongr
        exact hα ▸ nnnorm_monomialEval_le v α
    _ = (s * ‖v‖₊) ^ m := by ring
    _ ≤ r ^ m := by gcongr

lemma lineSeries_mem_convergent {g : MvPowerSeries σ 𝕜} (hg : g ∈ convergent σ 𝕜) (v : σ → 𝕜) :
    lineSeries g v ∈ convergent Unit 𝕜 := by
  obtain ⟨r, hr, hfin⟩ := exists_weightedNorm_const_ne_top hg
  refine ⟨fun _ ↦ r / (‖v‖₊ + 1), fun _ ↦ div_pos hr (by positivity),
    ne_top_of_le_ne_top hfin (weightedNorm_lineSeries_le v ?_)⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  gcongr
  exact le_add_of_nonneg_right zero_le

/-- Along the line `t ↦ t v`, a series sums to the sum of its line restriction. -/
lemma tsumEval_lineSeries [CompleteSpace 𝕜] {g : MvPowerSeries σ 𝕜} {r : ℝ≥0}
    (hg : weightedNorm (fun _ ↦ r) g ≠ ⊤) (v : σ → 𝕜) {t : Unit → 𝕜}
    (ht : ‖t ()‖₊ * ‖v‖₊ ≤ r) : tsumEval (lineSeries g v) t = tsumEval g (t () • v) := by
  have hz : ∀ i, ‖(t () • v) i‖₊ ≤ r := fun i ↦ by
    rw [Pi.smul_apply, smul_eq_mul, nnnorm_mul]
    exact (mul_le_mul_of_nonneg_left (nnnorm_le_pi_nnnorm v i) zero_le).trans ht
  have hs := (hasSum_tsumEval hg hz).tsum_fiberwise Finsupp.degree
  rw [tsumEval, ← unitFinsuppEquiv.symm.tsum_eq]
  refine (HasSum.tsum_eq ?_)
  have key : (fun m ↦ coeff (unitFinsuppEquiv.symm m) (lineSeries g v) *
      monomialEval t (unitFinsuppEquiv.symm m)) =
      fun m ↦ ∑' b : Finsupp.degree ⁻¹' {m}, coeff b.1 g * monomialEval (t () • v) b.1 := by
    funext m
    rw [← coe_degreeFinset, Finset.tsum_subtype' (degreeFinset σ m)
      (fun α ↦ coeff α g * monomialEval (t () • v) α)]
    change (∑ α ∈ degreeFinset σ ((Finsupp.single () m) ()), coeff α g * monomialEval v α) *
      monomialEval t (Finsupp.single () m) = _
    rw [Finsupp.single_eq_same, monomialEval_single, sum_mul]
    refine sum_congr rfl fun α hα ↦ ?_
    rw [mem_degreeFinset] at hα
    rw [show t () • v = fun i ↦ t () * v i from rfl, monomialEval_const_mul, hα]
    ring
  rw [key]
  exact hs

omit [Fintype σ] in
/-- The restriction to the `y`-axis is the line restriction along `(0, …, 0, 1)`. -/
lemma restrictY_eq_lineSeries [Fintype τ] [DecidableEq τ] (h : MvPowerSeries (Option τ) 𝕜) :
    restrictY h = lineSeries h (Pi.single none 1) := by
  classical
  refine MvPowerSeries.ext fun x ↦ ?_
  rw [eq_single_unit x, coeff_restrictY, coeff_lineSeries, Finsupp.single_eq_same,
    sum_eq_single (Finsupp.single none (x ()))]
  · rw [monomialEval_single, Pi.single_eq_same, one_pow, mul_one]
  · intro α hα hne
    rw [mem_degreeFinset] at hα
    have hsome : α.some ≠ 0 := by
      intro h0
      apply hne
      rw [eq_single_none_of_some_eq_zero h0]
      congr 1
      rw [← hα]
      conv_rhs => rw [eq_single_none_of_some_eq_zero h0]
      rw [Finsupp.degree_single]
    rw [monomialEval_option]
    have : (fun i ↦ (Pi.single none (1 : 𝕜) : Option τ → 𝕜) (some i)) = fun _ ↦ 0 := by
      funext i
      simp
    rw [this, monomialEval_const, zero_pow (by rwa [ne_eq, Finsupp.degree_eq_zero_iff]),
      mul_zero, mul_zero]
  · intro h
    exact absurd (by simp) h

omit [Fintype σ] in
lemma eventually_nnnorm_mul_le {r : ℝ≥0} (hr : 0 < r) {E : Type*} [SeminormedAddCommGroup E]
    (w : E) : ∀ᶠ t in 𝓝 (0 : Unit → 𝕜), ‖t ()‖₊ * ‖w‖₊ ≤ r := by
  have hc : Continuous fun t : Unit → 𝕜 ↦ ‖t ()‖₊ * ‖w‖₊ :=
    (continuous_nnnorm.comp (continuous_apply ())).mul continuous_const
  have h0 : (fun t : Unit → 𝕜 ↦ ‖t ()‖₊ * ‖w‖₊) 0 < r := by simpa using hr
  exact (hc.tendsto 0).eventually_le_const h0

/-- For a linear change of coordinates `Φ`, the line restriction of `g ∘ Φ` along `w` is the
line restriction of `g` along `Φ w`. -/
lemma lineSeries_substAnalytic [CompleteSpace 𝕜] {υ : Type*} [Fintype υ]
    {Φ : (υ → 𝕜) → σ → 𝕜} (hΦ : AnalyticAt 𝕜 Φ 0) (hΦ0 : Φ 0 = 0)
    (hlin : ∀ (c : 𝕜) w, Φ (c • w) = c • Φ w) {g : MvPowerSeries σ 𝕜} (hg : g ∈ convergent σ 𝕜)
    (w : υ → 𝕜) : lineSeries (substAnalytic Φ g) w = lineSeries g (Φ w) := by
  refine eq_of_tsumEval_eventuallyEq
    (lineSeries_mem_convergent (substAnalytic_mem_convergent Φ g) w)
    (lineSeries_mem_convergent hg (Φ w)) ?_
  obtain ⟨r₁, hr₁, hfin₁⟩ := exists_weightedNorm_const_ne_top (substAnalytic_mem_convergent Φ g)
  obtain ⟨r₂, hr₂, hfin₂⟩ := exists_weightedNorm_const_ne_top hg
  have hline : Tendsto (fun t : Unit → 𝕜 ↦ t () • w) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun t : Unit → 𝕜 ↦ t () • w) :=
      (continuous_apply ()).smul continuous_const
    simpa using this.tendsto 0
  filter_upwards [hline.eventually (tsumEval_substAnalytic hΦ hΦ0 hg),
    eventually_nnnorm_mul_le hr₁ w, eventually_nnnorm_mul_le hr₂ (Φ w)] with t h₁ h₂ h₃
  rw [tsumEval_lineSeries hfin₁ w h₂, tsumEval_lineSeries hfin₂ (Φ w) h₃, ← h₁, hlin]

end Lines

/-! ### Linear changes of coordinates -/

section Coordinates

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

omit [CompleteSpace 𝕜] in
lemma analyticAt_apply {σ : Type*} [Fintype σ] (i : σ) (x : σ → 𝕜) :
    AnalyticAt 𝕜 (fun z : σ → 𝕜 ↦ z i) x :=
  (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ ↦ 𝕜) i).analyticAt x

/-- Renaming the variables along an equivalence `σ ≃ σ'`. -/
def convergentCongr {σ σ' : Type*} [Fintype σ] [Fintype σ'] (e : σ ≃ σ') :
    convergent σ 𝕜 ≃ₐ[𝕜] convergent σ' 𝕜 :=
  AlgEquiv.ofAlgHom
    (substAnalyticHom (φ := fun (z : σ' → 𝕜) (i : σ) ↦ z (e i))
      (AnalyticAt.pi fun i ↦ analyticAt_apply (e i) 0) rfl)
    (substAnalyticHom (φ := fun (z : σ → 𝕜) (i : σ') ↦ z (e.symm i))
      (AnalyticAt.pi fun i ↦ analyticAt_apply (e.symm i) 0) rfl)
    (AlgHom.ext fun f ↦ Subtype.ext <| by
      simp only [AlgHom.coe_comp, Function.comp_apply, substAnalyticHom_apply, AlgHom.coe_id,
        id_eq]
      rw [substAnalytic_substAnalytic (AnalyticAt.pi fun i ↦ analyticAt_apply (e.symm i) 0) rfl
        (AnalyticAt.pi fun i ↦ analyticAt_apply (e i) 0) rfl f.2]
      convert substAnalytic_id f.2
      funext z i
      simp)
    (AlgHom.ext fun f ↦ Subtype.ext <| by
      simp only [AlgHom.coe_comp, Function.comp_apply, substAnalyticHom_apply, AlgHom.coe_id,
        id_eq]
      rw [substAnalytic_substAnalytic (AnalyticAt.pi fun i ↦ analyticAt_apply (e i) 0) rfl
        (AnalyticAt.pi fun i ↦ analyticAt_apply (e.symm i) 0) rfl f.2]
      convert substAnalytic_id f.2
      funext z i
      simp)

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

omit [CompleteSpace 𝕜] [DecidableEq τ] in
/-- A non-zero series has a non-zero restriction to some line `t ↦ t v` with `v none ≠ 0`. -/
lemma exists_lineSeries_ne_zero {g : MvPowerSeries (Option τ) 𝕜} (hg : g ≠ 0) :
    ∃ v : Option τ → 𝕜, v none ≠ 0 ∧ lineSeries g v ≠ 0 := by
  classical
  obtain ⟨α₀, hα₀⟩ : ∃ α, coeff α g ≠ 0 := by
    by_contra! h
    exact hg (ext h)
  let P : MvPolynomial (Option τ) 𝕜 :=
    ∑ α ∈ degreeFinset (Option τ) α₀.degree, MvPolynomial.monomial α (coeff α g)
  have hP : P ≠ 0 := by
    intro h
    have := congr_arg (MvPolynomial.coeff α₀) h
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, sum_ite_eq',
      mem_degreeFinset, ite_true, MvPolynomial.coeff_zero] at this
    exact hα₀ this
  have hQ : P * MvPolynomial.X none ≠ 0 := mul_ne_zero hP (MvPolynomial.X_ne_zero _)
  obtain ⟨v, hv⟩ : ∃ v, MvPolynomial.eval v (P * MvPolynomial.X none) ≠ 0 := by
    by_contra! h
    exact hQ (MvPolynomial.funext fun v ↦ by simpa using h v)
  rw [map_mul, MvPolynomial.eval_X] at hv
  refine ⟨v, right_ne_zero_of_mul hv, fun hL ↦ left_ne_zero_of_mul hv ?_⟩
  have := congr_arg (coeff (Finsupp.single () α₀.degree)) hL
  rw [coeff_lineSeries, Finsupp.single_eq_same, map_zero] at this
  simpa [P, MvPolynomial.eval_monomial, map_sum, monomialEval] using this

/-- The shear `(z, y) ↦ (z + y v_z, v_y y)`, a linear map sending `(0, 1)` to `v`. -/
def shear (v z : Option τ → 𝕜) : Option τ → 𝕜 :=
  fun o ↦ o.elim (v none * z none) fun i ↦ z (some i) + v (some i) * z none

/-- The inverse of `shear v` (when `v none ≠ 0`). -/
def shearInv (v w : Option τ → 𝕜) : Option τ → 𝕜 :=
  fun o ↦ o.elim (w none / v none) fun i ↦ w (some i) - v (some i) * (w none / v none)

omit [Fintype τ] [DecidableEq τ] [CompleteSpace 𝕜] in
lemma shear_shearInv {v : Option τ → 𝕜} (hv : v none ≠ 0) (w : Option τ → 𝕜) :
    shear v (shearInv v w) = w := by
  funext o
  cases o with
  | none => simp [shear, shearInv, mul_div_cancel₀ _ hv]
  | some i => simp [shear, shearInv]

omit [Fintype τ] [DecidableEq τ] [CompleteSpace 𝕜] in
lemma shearInv_shear {v : Option τ → 𝕜} (hv : v none ≠ 0) (z : Option τ → 𝕜) :
    shearInv v (shear v z) = z := by
  funext o
  cases o with
  | none => simp [shear, shearInv, mul_div_cancel_left₀ _ hv]
  | some i => simp [shear, shearInv, mul_div_cancel_left₀ _ hv]

omit [Fintype τ] [DecidableEq τ] [CompleteSpace 𝕜] in
lemma shear_zero (v : Option τ → 𝕜) : shear v 0 = 0 := by
  funext o
  cases o <;> simp [shear]

omit [Fintype τ] [DecidableEq τ] [CompleteSpace 𝕜] in
lemma shearInv_zero (v : Option τ → 𝕜) : shearInv v 0 = 0 := by
  funext o
  cases o <;> simp [shearInv]

omit [Fintype τ] [DecidableEq τ] [CompleteSpace 𝕜] in
lemma shear_smul (v : Option τ → 𝕜) (c : 𝕜) (z : Option τ → 𝕜) :
    shear v (c • z) = c • shear v z := by
  funext o
  cases o <;> simp [shear] <;> ring

omit [Fintype τ] [CompleteSpace 𝕜] in
lemma shear_single (v : Option τ → 𝕜) : shear v (Pi.single none 1) = v := by
  funext o
  cases o <;> simp [shear]

omit [DecidableEq τ] [CompleteSpace 𝕜] in
lemma analyticAt_shear (v : Option τ → 𝕜) : AnalyticAt 𝕜 (shear v) 0 := by
  refine AnalyticAt.pi (f := fun o z ↦ shear v z o) fun o ↦ ?_
  cases o with
  | none => exact analyticAt_const.mul (analyticAt_apply none 0)
  | some i =>
    exact (analyticAt_apply (some i) 0).add (analyticAt_const.mul (analyticAt_apply none 0))

omit [DecidableEq τ] [CompleteSpace 𝕜] in
lemma analyticAt_shearInv (v : Option τ → 𝕜) : AnalyticAt 𝕜 (shearInv v) 0 := by
  refine AnalyticAt.pi (f := fun o z ↦ shearInv v z o) fun o ↦ ?_
  cases o with
  | none => exact (analyticAt_apply none 0).div_const
  | some i =>
    exact (analyticAt_apply (some i) 0).sub
      (analyticAt_const.mul (analyticAt_apply none 0).div_const)

/-- The change of coordinates `f ↦ f ∘ shear v` of `𝕜{z, y}`. -/
def shearEquiv {v : Option τ → 𝕜} (hv : v none ≠ 0) :
    convergent (Option τ) 𝕜 ≃ₐ[𝕜] convergent (Option τ) 𝕜 :=
  AlgEquiv.ofAlgHom (substAnalyticHom (analyticAt_shear v) (shear_zero v))
    (substAnalyticHom (analyticAt_shearInv v) (shearInv_zero v))
    (AlgHom.ext fun f ↦ Subtype.ext <| by
      simp only [AlgHom.coe_comp, Function.comp_apply, substAnalyticHom_apply, AlgHom.coe_id,
        id_eq]
      rw [substAnalytic_substAnalytic (analyticAt_shearInv v) (shearInv_zero v)
        (analyticAt_shear v) (shear_zero v) f.2]
      convert substAnalytic_id f.2
      funext z
      exact shearInv_shear hv z)
    (AlgHom.ext fun f ↦ Subtype.ext <| by
      simp only [AlgHom.coe_comp, Function.comp_apply, substAnalyticHom_apply, AlgHom.coe_id,
        id_eq]
      rw [substAnalytic_substAnalytic (analyticAt_shear v) (shear_zero v)
        (analyticAt_shearInv v) (shearInv_zero v) f.2]
      convert substAnalytic_id f.2
      funext z
      exact shear_shearInv hv z)

omit [DecidableEq τ] in
lemma coe_shearEquiv {v : Option τ → 𝕜} (hv : v none ≠ 0) (f : convergent (Option τ) 𝕜) :
    (shearEquiv hv f : MvPowerSeries (Option τ) 𝕜) = substAnalytic (shear v) f.1 := rfl

omit [DecidableEq τ] in
/-- After a linear change of coordinates, every non-zero convergent power series becomes
regular in `y` (of some order). -/
theorem exists_isRegularOfOrder_shearEquiv {g : convergent (Option τ) 𝕜} (hg : g ≠ 0) :
    ∃ (v : Option τ → 𝕜) (hv : v none ≠ 0) (b : ℕ),
      IsRegularOfOrder b (shearEquiv hv g : MvPowerSeries (Option τ) 𝕜) := by
  classical
  obtain ⟨v, hv, hL⟩ := exists_lineSeries_ne_zero (fun h ↦ hg (Subtype.ext h))
  have hR : restrictY (shearEquiv hv g : MvPowerSeries (Option τ) 𝕜) ≠ 0 := by
    rw [restrictY_eq_lineSeries, coe_shearEquiv, lineSeries_substAnalytic (analyticAt_shear v)
      (shear_zero v) (shear_smul v) g.2, shear_single]
    exact hL
  rw [ne_eq, restrictY_eq_zero_iff, not_forall] at hR
  refine ⟨v, hv, Nat.find hR, fun j hj ↦ ?_, Nat.find_spec hR⟩
  by_contra h
  exact Nat.find_min hR hj h

end Coordinates

/-! ### Rückert's basis theorem -/

section Noetherian

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

theorem isNoetherianRing_convergent_option {τ : Type*} [Finite τ]
    [IsNoetherianRing (convergent τ 𝕜)] : IsNoetherianRing (convergent (Option τ) 𝕜) := by
  have := Fintype.ofFinite τ
  refine ⟨fun I ↦ ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]
    exact Submodule.fg_bot
  obtain ⟨g, hgI, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨v, hv, b, hreg⟩ := exists_isRegularOfOrder_shearEquiv hg0
  set S := shearEquiv (𝕜 := 𝕜) hv
  set g' := S g
  let J : Ideal (convergent (Option τ) 𝕜) := Ideal.map (S : convergent (Option τ) 𝕜 →+* _) I
  have hg'J : g' ∈ J := Ideal.mem_map_of_mem _ hgI
  have hfin := module_finite_quotient g' hreg
  have hA : IsNoetherian (convergent τ 𝕜) (convergent (Option τ) 𝕜 ⧸ Ideal.span {g'}) :=
    inferInstance
  have hB : IsNoetherian (convergent (Option τ) 𝕜) (convergent (Option τ) 𝕜 ⧸ Ideal.span {g'}) :=
    isNoetherian_of_tower (convergent τ 𝕜) hA
  have hJ : J.FG := by
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (Ideal.span {g'}).mkQ
      (IsNoetherian.noetherian _) ?_
    rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hg'J)]
    exact Submodule.fg_span_singleton g'
  have hIJ : I = Ideal.map (S.symm : convergent (Option τ) 𝕜 →+* _) J := by
    rw [Ideal.map_map]
    convert (Ideal.map_id I).symm
    ext f
    simp
  rw [hIJ]
  exact hJ.map _

lemma isNoetherianRing_convergent_empty {σ : Type*} [IsEmpty σ] :
    IsNoetherianRing (convergent σ 𝕜) := by
  refine ⟨fun I ↦ ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]
    exact Submodule.fg_bot
  obtain ⟨f, hfI, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hunit : IsUnit f := by
    rw [isUnit_convergent_iff]
    intro h
    apply hf0
    apply Subtype.ext
    ext α
    rw [Subsingleton.elim α 0, coeff_zero_eq_constantCoeff_apply, h]
    rfl
  rw [Ideal.eq_top_of_isUnit_mem I hfI hunit]
  exact ⟨{1}, by rw [Finset.coe_singleton]; exact Ideal.span_singleton_one⟩

theorem isNoetherianRing_convergent_fin (n : ℕ) : IsNoetherianRing (convergent (Fin n) 𝕜) := by
  induction n with
  | zero => exact isNoetherianRing_convergent_empty
  | succ n ih =>
    have : IsNoetherianRing (convergent (Option (Fin n)) 𝕜) := isNoetherianRing_convergent_option
    exact isNoetherianRing_of_ringEquiv _ (convergentCongr (_root_.finSuccEquiv n).symm).toRingEquiv

/-- **Rückert's basis theorem**: the ring `𝕜{z₁, …, zₙ}` of convergent power series is
noetherian. -/
instance isNoetherianRing_convergent {σ : Type*} [Finite σ] :
    IsNoetherianRing (convergent σ 𝕜) := by
  have := Fintype.ofFinite σ
  have := isNoetherianRing_convergent_fin (𝕜 := 𝕜) (Fintype.card σ)
  exact isNoetherianRing_of_ringEquiv _ (convergentCongr (Fintype.equivFin σ).symm).toRingEquiv

end Noetherian

end MvPowerSeries
