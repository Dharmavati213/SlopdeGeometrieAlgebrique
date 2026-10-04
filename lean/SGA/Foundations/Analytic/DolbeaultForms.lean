/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.DolbeaultPartial
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The coordinate Dolbeault complex on `ℂ^σ`

A `(0, q)`-form `∑_{|I| = q} φ_I dz̄_I` on (an open subset of) `ℂ^σ` is recorded by its family of
coefficients `φ : Finset σ → (σ → ℂ) → ℂ` (for a linear order on `σ`, `dz̄_I` is the wedge product
of the `dz̄ᵢ`, `i ∈ I`, in increasing order). The operator `∂̄` becomes
`(∂̄φ)_J = ∑_{j ∈ J} (-1)^{#{i ∈ J | i < j}} ∂φ_{J ∖ {j}}/∂z̄ⱼ` (`AnalyticGeometry.dbarForm`), the
Koszul complex of the commuting operators `∂/∂z̄ⱼ` acting on smooth functions. This is the form
of the Dolbeault complex used in Hörmander's proof of the Dolbeault–Grothendieck lemma
(Hörmander, *An introduction to complex analysis in several variables*, 2.3), which works on
coefficients; it is the coordinate model of the `(0,q)`-forms of `SGA.Foundations.Hodge`.

## Main results

* `AnalyticGeometry.dbarPartial_dbarPartial_comm`: `∂²f/∂z̄ᵢ∂z̄ⱼ = ∂²f/∂z̄ⱼ∂z̄ᵢ` for `C²` functions.
* `AnalyticGeometry.dbarForm_dbarForm`: `∂̄ ∘ ∂̄ = 0` on smooth forms.
* `AnalyticGeometry.dbarForm_eq_zero_of_card_ne`: `∂̄` raises the degree by one.
* `AnalyticGeometry.dbarPartial_eq_zero_of_dbarForm_eq_zero`: if a `∂̄`-closed form only involves
  the `dz̄ⱼ` with `j ∈ A`, its coefficients are holomorphic in the variables outside `A`
  (Hörmander, proof of Theorem 2.3.3).
-/

noncomputable section

open Topology Filter Set Complex
open scoped ContDiff

namespace AnalyticGeometry

section Partial

variable {σ : Type} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
lemma dbarPartial_apply (j : σ) (f : (σ → ℂ) → ℂ) (z : σ → ℂ) :
    dbarPartial j f z = (1 / 2 : ℂ) * (fderiv ℝ f z (Pi.single j 1) +
      I * fderiv ℝ f z (Pi.single j I)) := by
  rw [dbarPartial, dbarCLM_apply]
  rfl

omit [Fintype σ] in
/-- `∂/∂z̄ⱼ` vanishes exactly when the real derivative is `ℂ`-linear in the direction `eⱼ`. -/
lemma dbarPartial_eq_zero_iff (j : σ) (f : (σ → ℂ) → ℂ) (z : σ → ℂ) :
    dbarPartial j f z = 0 ↔
      fderiv ℝ f z (Pi.single j I) = I * fderiv ℝ f z (Pi.single j 1) := by
  rw [dbarPartial_apply]
  constructor
  · intro h
    have h' : fderiv ℝ f z (Pi.single j 1) + I * fderiv ℝ f z (Pi.single j I) = 0 := by
      simpa using h
    linear_combination (-I) * h' + (fderiv ℝ f z (Pi.single j I)) * I_sq
  · intro h
    rw [h]
    ring_nf
    rw [I_sq]
    ring

/-- The real linear functional `L ↦ ∂/∂z̄ⱼ` applied to a real derivative `L`. -/
private def dbarFun (j : σ) : ((σ → ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  dbarCLM.comp ((ContinuousLinearMap.compL ℝ ℂ (σ → ℂ) ℂ).flip
    (ContinuousLinearMap.single ℝ (fun _ : σ ↦ ℂ) j))

private lemma dbarFun_apply (j : σ) (L : (σ → ℂ) →L[ℝ] ℂ) :
    dbarFun j L = (1 / 2 : ℂ) * (L (Pi.single j 1) + I * L (Pi.single j I)) := by
  simp only [dbarFun, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, dbarCLM_apply]
  rfl

private lemma dbarPartial_eq_dbarFun (j : σ) (f : (σ → ℂ) → ℂ) (z : σ → ℂ) :
    dbarPartial j f z = dbarFun j (fderiv ℝ f z) := rfl

omit [Fintype σ] in
lemma dbarPartial_sum [Finite σ] {ι : Type*} (j : σ) (s : Finset ι) {f : ι → (σ → ℂ) → ℂ}
    {z : σ → ℂ} (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    dbarPartial j (fun y ↦ ∑ i ∈ s, f i y) z = ∑ i ∈ s, dbarPartial j (f i) z := by
  have := Fintype.ofFinite σ
  simp only [dbarPartial_eq_dbarFun, fderiv_fun_sum hf, map_sum]

omit [Fintype σ] in
lemma dbarPartial_const_mul [Finite σ] (j : σ) (c : ℂ) {f : (σ → ℂ) → ℂ} {z : σ → ℂ}
    (hf : DifferentiableAt ℝ f z) :
    dbarPartial j (fun y ↦ c * f y) z = c * dbarPartial j f z := by
  have := Fintype.ofFinite σ
  have : HasFDerivAt (fun y ↦ c * f y) (c • fderiv ℝ f z) z := hf.hasFDerivAt.const_mul c
  rw [dbarPartial_apply, dbarPartial_apply, this.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype σ] in
/-- `dbarPartial_sub` with the difference written pointwise. -/
lemma dbarPartial_sub' [Finite σ] (j : σ) {f g : (σ → ℂ) → ℂ} {z : σ → ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbarPartial j (fun y ↦ f y - g y) z = dbarPartial j f z - dbarPartial j g z :=
  dbarPartial_sub hf hg

omit [Fintype σ] in
/-- `dbarPartial_add` with the sum written pointwise. -/
lemma dbarPartial_add' [Finite σ] (j : σ) {f g : (σ → ℂ) → ℂ} {z : σ → ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbarPartial j (fun y ↦ f y + g y) z = dbarPartial j f z + dbarPartial j g z :=
  dbarPartial_add hf hg

omit [Fintype σ] in
/-- `∂/∂z̄ⱼ` of a function vanishing near `z` vanishes at `z`. -/
lemma dbarPartial_eq_zero_of_eventuallyEq_zero (j : σ) {f : (σ → ℂ) → ℂ} {z : σ → ℂ}
    (h : f =ᶠ[𝓝 z] 0) : dbarPartial j f z = 0 := by
  rw [dbarPartial_congr h, dbarPartial_zero]

/-- **Mixed `∂̄`-derivatives commute** for `C²` functions. -/
lemma dbarPartial_dbarPartial_comm {f : (σ → ℂ) → ℂ} {z : σ → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (i j : σ) : dbarPartial i (dbarPartial j f) z = dbarPartial j (dbarPartial i f) z := by
  have hsymm : IsSymmSndFDerivAt ℝ f z := hf.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hk : ∀ k, HasFDerivAt (dbarPartial k f)
      ((dbarFun k).comp (fderiv ℝ (fderiv ℝ f) z)) z := fun k ↦
    (dbarFun k).hasFDerivAt.comp z hd.hasFDerivAt
  rw [dbarPartial, (hk j).fderiv, dbarPartial, (hk i).fderiv]
  change dbarFun i _ = dbarFun j _
  rw [dbarFun_apply, dbarFun_apply]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, dbarFun_apply]
  rw [hsymm (Pi.single i 1) (Pi.single j 1), hsymm (Pi.single i 1) (Pi.single j I),
    hsymm (Pi.single i I) (Pi.single j 1), hsymm (Pi.single i I) (Pi.single j I)]
  ring

end Partial

/-! ### The Koszul sign -/

section Sign

variable {σ : Type} [LinearOrder σ]

/-- The sign `(-1)^{#{i ∈ J | i < j}}` of `dz̄ⱼ ∧ dz̄_{J ∖ {j}} = ± dz̄_J`. -/
def koszulSign (j : σ) (J : Finset σ) : ℂ := (-1) ^ (J.filter (· < j)).card

lemma koszulSign_mul_self (j : σ) (J : Finset σ) : koszulSign j J * koszulSign j J = 1 := by
  rw [koszulSign, ← pow_add, ← two_mul, pow_mul]
  simp

lemma koszulSign_ne_zero (j : σ) (J : Finset σ) : koszulSign j J ≠ 0 := by
  simp [koszulSign]

lemma koszulSign_erase_self (j : σ) (J : Finset σ) : koszulSign j (J.erase j) = koszulSign j J := by
  rw [koszulSign, koszulSign, Finset.filter_erase, Finset.erase_eq_of_notMem (by simp)]

lemma koszulSign_insert_self (j : σ) (J : Finset σ) :
    koszulSign j (insert j J) = koszulSign j J := by
  rw [koszulSign, koszulSign, Finset.filter_insert]
  simp

lemma koszulSign_erase_of_lt {i j : σ} {J : Finset σ} (hij : i < j) (hi : i ∈ J) :
    koszulSign j (J.erase i) = -koszulSign j J := by
  rw [koszulSign, koszulSign, Finset.filter_erase,
    Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hi, hij⟩)]
  have hpos : 0 < (J.filter (· < j)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hij⟩⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  rw [hk, Nat.succ_sub_one, pow_succ]
  ring

lemma koszulSign_erase_of_gt {i j : σ} {J : Finset σ} (hji : j < i) :
    koszulSign j (J.erase i) = koszulSign j J := by
  have hi : i ∉ J.filter (· < j) := fun h ↦ lt_asymm hji (Finset.mem_filter.mp h).2
  rw [koszulSign, koszulSign, Finset.filter_erase, Finset.erase_eq_of_notMem hi]

/-- The sign identity behind `∂̄ ∘ ∂̄ = 0`. -/
lemma koszulSign_mul_koszulSign_erase {i j : σ} {J : Finset σ} (hij : i ≠ j) (hi : i ∈ J)
    (hj : j ∈ J) :
    koszulSign j J * koszulSign i (J.erase j) = -(koszulSign i J * koszulSign j (J.erase i)) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [koszulSign_erase_of_gt h, koszulSign_erase_of_lt h hi]
    ring
  · rw [koszulSign_erase_of_lt h hj, koszulSign_erase_of_gt h]
    ring

end Sign

/-! ### The operator `∂̄` on forms -/

section Forms

variable {σ : Type} [Fintype σ] [LinearOrder σ]

/-- `∂̄` on `(0, *)`-forms in coordinates: `(∂̄φ)_J = ∑_{j ∈ J} ± ∂φ_{J ∖ {j}}/∂z̄ⱼ`. -/
def dbarForm (φ : Finset σ → (σ → ℂ) → ℂ) (J : Finset σ) (z : σ → ℂ) : ℂ :=
  ∑ j ∈ J, koszulSign j J * dbarPartial j (φ (J.erase j)) z

/-- A form is smooth at `z` if all its coefficients are. -/
def IsSmoothFormAt (φ : Finset σ → (σ → ℂ) → ℂ) (z : σ → ℂ) : Prop :=
  ∀ I, ContDiffAt ℝ ∞ (φ I) z

omit [LinearOrder σ] in
lemma IsSmoothFormAt.differentiableAt {φ : Finset σ → (σ → ℂ) → ℂ} {z : σ → ℂ}
    (h : IsSmoothFormAt φ z) (I : Finset σ) : DifferentiableAt ℝ (φ I) z :=
  (h I).differentiableAt (by simp)

lemma IsSmoothFormAt.dbarForm {φ : Finset σ → (σ → ℂ) → ℂ} {z : σ → ℂ}
    (h : IsSmoothFormAt φ z) : IsSmoothFormAt (dbarForm φ) z := fun J ↦ by
  unfold AnalyticGeometry.dbarForm
  exact ContDiffAt.sum fun j _ ↦ contDiffAt_const.mul (contDiffAt_dbarPartial j (h _))

omit [Fintype σ] in
lemma dbarForm_sub [Finite σ] {φ ψ : Finset σ → (σ → ℂ) → ℂ} {z : σ → ℂ}
    (hφ : ∀ I, DifferentiableAt ℝ (φ I) z) (hψ : ∀ I, DifferentiableAt ℝ (ψ I) z)
    (J : Finset σ) :
    dbarForm (fun I y ↦ φ I y - ψ I y) J z = dbarForm φ J z - dbarForm ψ J z := by
  simp only [dbarForm, ← Finset.sum_sub_distrib, ← mul_sub]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [dbarPartial_sub' j (hφ _) (hψ _)]

omit [Fintype σ] in
lemma dbarForm_add [Finite σ] {φ ψ : Finset σ → (σ → ℂ) → ℂ} {z : σ → ℂ}
    (hφ : ∀ I, DifferentiableAt ℝ (φ I) z) (hψ : ∀ I, DifferentiableAt ℝ (ψ I) z)
    (J : Finset σ) :
    dbarForm (fun I y ↦ φ I y + ψ I y) J z = dbarForm φ J z + dbarForm ψ J z := by
  simp only [dbarForm, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [dbarPartial_add' j (hφ _) (hψ _)]

omit [Fintype σ] in
/-- `∂̄` is local. -/
lemma dbarForm_congr {φ ψ : Finset σ → (σ → ℂ) → ℂ} {z : σ → ℂ}
    (h : ∀ I, φ I =ᶠ[𝓝 z] ψ I) (J : Finset σ) : dbarForm φ J z = dbarForm ψ J z := by
  simp only [dbarForm]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [dbarPartial_congr (h _)]

/-- **`∂̄ ∘ ∂̄ = 0`** on forms which are smooth near `z`. -/
theorem dbarForm_dbarForm {φ : Finset σ → (σ → ℂ) → ℂ} {z : σ → ℂ} (hφ : IsSmoothFormAt φ z)
    (J : Finset σ) : dbarForm (dbarForm φ) J z = 0 := by
  -- expand the outer `∂̄ⱼ` through the inner sum
  have hdiff : ∀ (j : σ) (i : σ) (I : Finset σ),
      DifferentiableAt ℝ (fun y ↦ koszulSign i I * dbarPartial i (φ (I.erase i)) y) z :=
    fun j i I ↦ (differentiableAt_const _).mul
      ((contDiffAt_dbarPartial i (hφ _)).differentiableAt (by simp))
  have h1 : ∀ j ∈ J, dbarPartial j (dbarForm φ (J.erase j)) z =
      ∑ i ∈ J.erase j, koszulSign i (J.erase j) *
        dbarPartial j (dbarPartial i (φ ((J.erase j).erase i))) z := by
    intro j _
    change dbarPartial j (fun y ↦ ∑ i ∈ J.erase j,
      koszulSign i (J.erase j) * dbarPartial i (φ ((J.erase j).erase i)) y) z = _
    rw [dbarPartial_sum j _ fun i _ ↦ hdiff j i _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact dbarPartial_const_mul j _ ((contDiffAt_dbarPartial i (hφ _)).differentiableAt (by simp))
  -- the double sum over ordered pairs `(j, i)` of distinct elements of `J`
  set F : σ → σ → ℂ := fun j i ↦ koszulSign j J * koszulSign i (J.erase j) *
    dbarPartial j (dbarPartial i (φ ((J.erase j).erase i))) z with hF
  have hS : dbarForm (dbarForm φ) J z = ∑ j ∈ J, ∑ i ∈ J.erase j, F j i := by
    simp only [dbarForm]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [h1 j hj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hF]; ring
  -- `F` is antisymmetric
  have hanti : ∀ j ∈ J, ∀ i ∈ J.erase j, F j i = -F i j := by
    intro j hj i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have hiJ : i ∈ J := Finset.mem_of_mem_erase hi
    simp only [hF]
    rw [koszulSign_mul_koszulSign_erase hij hiJ hj, Finset.erase_right_comm,
      dbarPartial_dbarPartial_comm ((hφ _).of_le (by simp)) j i]
    ring
  -- swapping the summation order
  have hswap : ∑ j ∈ J, ∑ i ∈ J.erase j, F j i = ∑ i ∈ J, ∑ j ∈ J.erase i, F j i := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij' (fun p _ ↦ ⟨p.2, p.1⟩) (fun p _ ↦ ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨j, i⟩ h
      simp only [Finset.mem_sigma, Finset.mem_erase] at h ⊢
      exact ⟨h.2.2, h.2.1.symm, h.1⟩
    · rintro ⟨j, i⟩ h
      simp only [Finset.mem_sigma, Finset.mem_erase] at h ⊢
      exact ⟨h.2.2, h.2.1.symm, h.1⟩
    · rintro ⟨j, i⟩ _
      rfl
    · rintro ⟨j, i⟩ _
      rfl
    · rintro ⟨j, i⟩ _
      rfl
  have hneg : ∑ j ∈ J, ∑ i ∈ J.erase j, F j i = -∑ j ∈ J, ∑ i ∈ J.erase j, F j i := by
    conv_lhs => rw [hswap]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj ↦ hanti j (Finset.mem_of_mem_erase hj) i
      (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hj).symm, hi⟩)
  rw [hS]
  have h2 : (2 : ℂ) * ∑ j ∈ J, ∑ i ∈ J.erase j, F j i = 0 := by
    rw [two_mul]
    nth_rewrite 1 [hneg]
    ring
  simpa using h2

omit [Fintype σ] in
/-- `∂̄` raises the degree by one: if `φ` is of degree `q` on an open set `W`, then `∂̄φ` is of
degree `q + 1` on `W`. -/
lemma dbarForm_eq_zero_of_card_ne {φ : Finset σ → (σ → ℂ) → ℂ} {W : Set (σ → ℂ)} (hW : IsOpen W)
    {q : ℕ} (hφ : ∀ I, I.card ≠ q → ∀ z ∈ W, φ I z = 0) {J : Finset σ} (hJ : J.card ≠ q + 1)
    {z : σ → ℂ} (hz : z ∈ W) : dbarForm φ J z = 0 := by
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  have hcard : (J.erase j).card ≠ q := by
    have := Finset.card_pos.mpr ⟨j, hj⟩
    rw [Finset.card_erase_of_mem hj]
    omega
  rw [dbarPartial_eq_zero_of_eventuallyEq_zero j, mul_zero]
  filter_upwards [hW.mem_nhds hz] with y hy using hφ _ hcard y hy

omit [Fintype σ] in
/-- **Closed forms involving only some `dz̄ⱼ` have holomorphic coefficients in the other
variables** (Hörmander, proof of Theorem 2.3.3): if `∂̄g = 0` on an open set `W` and `g_J = 0`
on `W` unless `J ⊆ A`, then `∂g_J/∂z̄ₖ = 0` on `W` for `J ⊆ A` and `k ∉ A`. -/
theorem dbarPartial_eq_zero_of_dbarForm_eq_zero {g : Finset σ → (σ → ℂ) → ℂ} {W : Set (σ → ℂ)}
    (hW : IsOpen W) {A : Finset σ} (hA : ∀ J, ¬ J ⊆ A → ∀ z ∈ W, g J z = 0)
    (hg : ∀ J, ∀ z ∈ W, dbarForm g J z = 0) {J : Finset σ} (hJ : J ⊆ A) {k : σ} (hk : k ∉ A)
    {z : σ → ℂ} (hz : z ∈ W) : dbarPartial k (g J) z = 0 := by
  have hkJ : k ∉ J := fun h ↦ hk (hJ h)
  have h0 := hg (insert k J) z hz
  rw [dbarForm, Finset.sum_insert hkJ, Finset.erase_insert hkJ] at h0
  have hrest : ∑ j ∈ J, koszulSign j (insert k J) *
      dbarPartial j (g ((insert k J).erase j)) z = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hjk : j ≠ k := fun h ↦ hkJ (h ▸ hj)
    have hnot : ¬ (insert k J).erase j ⊆ A := fun h ↦
      hk (h (Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_insert_self k J⟩))
    rw [dbarPartial_eq_zero_of_eventuallyEq_zero j, mul_zero]
    filter_upwards [hW.mem_nhds hz] with y hy using hA _ hnot y hy
  rw [hrest, add_zero] at h0
  exact (mul_eq_zero.mp h0).resolve_left (koszulSign_ne_zero _ _)

end Forms

end AnalyticGeometry
