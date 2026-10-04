/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.DolbeaultForms
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# The Cauchy transform in one variable, with parameters

For `h : ℂ^σ → ℂ` and a coordinate `m`, `AnalyticGeometry.cauchyTransformIn m h` is the Cauchy
transform of `h` in the variable `zₘ`, the other variables being parameters:

  `(Tₘh)(z) = (1/π) ∫ h(z₁, …, t, …, zₙ) / (zₘ - t) dA(t)`.

If `h` is smooth on an open set `s` which is stable under changing the `m`-th coordinate, and
vanishes (on `s`) when `zₘ` is outside a fixed compact set, then `Tₘh` is smooth on `s`
(`AnalyticGeometry.contDiffAt_cauchyTransformIn`), solves `∂(Tₘh)/∂z̄ₘ = h`
(`AnalyticGeometry.dbarPartial_cauchyTransformIn_self`), and is holomorphic in every other
variable in which `h` is (`AnalyticGeometry.dbarPartial_cauchyTransformIn_of_ne`). This is
Hörmander, *An introduction to complex analysis in several variables*, Theorem 1.2.2 with
parameters, the analytic input of the Dolbeault–Grothendieck lemma (first step of the proof of
Hörmander's Theorem 2.3.3).
-/

noncomputable section

open Topology Filter Set Complex MeasureTheory
open scoped ContDiff Convolution

namespace AnalyticGeometry

variable {σ : Type} [Fintype σ] [DecidableEq σ]

section Update

omit [Fintype σ] in
lemma update_eq_add_single (z : σ → ℂ) (m : σ) (t : ℂ) :
    Function.update z m t = z + Pi.single m (t - z m) := by
  funext i
  by_cases hi : i = m
  · subst hi
    simp
  · simp [hi]

/-- `(p, t) ↦ p₍ₘ←t₎` is smooth. -/
lemma contDiff_update_prod (m : σ) :
    ContDiff ℝ ∞ fun q : (σ → ℂ) × ℂ ↦ Function.update q.1 m q.2 := by
  simp_rw [update_eq_add_single]
  exact contDiff_fst.add ((contDiff_single (F' := fun _ : σ ↦ ℂ) _ m).comp
    (contDiff_snd.sub ((contDiff_apply ℝ ℂ m).comp contDiff_fst)))

omit [Fintype σ] in
/-- `∂/∂z̄ⱼ` is the one-variable `∂/∂z̄` of the restriction to the `j`-th coordinate line. -/
lemma dbarPartial_eq_dbar_update [Finite σ] {F : (σ → ℂ) → ℂ} {z : σ → ℂ}
    (hF : DifferentiableAt ℝ F z) (j : σ) :
    dbarPartial j F z = dbar (fun t ↦ F (Function.update z j t)) (z j) := by
  have := Fintype.ofFinite σ
  have hu : HasFDerivAt (fun t ↦ Function.update z j t)
      (ContinuousLinearMap.single ℝ (fun _ : σ ↦ ℂ) j) (z j) := by
    refine (hasFDerivAt_update (𝕜 := ℝ) z (i := j) (z j)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun t ↦ funext fun i ↦ ?_
    by_cases hi : i = j
    · subst hi
      simp
    · simp [hi]
  have hcomp : HasFDerivAt (fun t ↦ F (Function.update z j t))
      ((fderiv ℝ F z).comp (ContinuousLinearMap.single ℝ (fun _ : σ ↦ ℂ) j)) (z j) := by
    have hF' : HasFDerivAt F (fderiv ℝ F z) (Function.update z j (z j)) := by
      simpa using hF.hasFDerivAt
    exact hF'.comp (z j) hu
  rw [dbar_eq_dbarCLM, hcomp.fderiv]
  rfl

end Update

/-- The Cauchy transform of `h : ℂ^σ → ℂ` in the variable `zₘ`, the other variables being
parameters: `(Tₘh)(z) = (1/π) ∫ h(z₍ₘ←t₎) / (zₘ - t) dA(t)`. -/
def cauchyTransformIn (m : σ) (h : (σ → ℂ) → ℂ) (z : σ → ℂ) : ℂ :=
  cauchyTransform (fun t ↦ h (Function.update z m t)) (z m)

omit [Fintype σ] in
lemma cauchyTransformIn_update (m : σ) (h : (σ → ℂ) → ℂ) (z : σ → ℂ) (t : ℂ) :
    cauchyTransformIn m h (Function.update z m t) =
      cauchyTransform (fun t' ↦ h (Function.update z m t')) t := by
  simp [cauchyTransformIn]

variable {m : σ} {h : (σ → ℂ) → ℂ} {s : Set (σ → ℂ)} {k : Set ℂ}

/-- The hypotheses on `h`: smooth on an open set `s` stable under changing `zₘ`, and vanishing on
`s` for `zₘ` outside the compact set `k`. -/
structure CauchyTransformInData (m : σ) (h : (σ → ℂ) → ℂ) (s : Set (σ → ℂ)) (k : Set ℂ) :
    Prop where
  isOpen : IsOpen s
  update_mem : ∀ z ∈ s, ∀ t, Function.update z m t ∈ s
  isCompact : IsCompact k
  eq_zero : ∀ z ∈ s, ∀ t ∉ k, h (Function.update z m t) = 0
  contDiffAt : ∀ z ∈ s, ContDiffAt ℝ ∞ h z

namespace CauchyTransformInData

variable (H : CauchyTransformInData m h s k)
include H

/-- The integrand as a function of the parameter and the integration variable is smooth. -/
lemma contDiffOn_uncurry :
    ContDiffOn ℝ ∞ (fun q : (σ → ℂ) × ℂ ↦ h (Function.update q.1 m q.2)) (s ×ˢ univ) :=
  fun q hq ↦ ((H.contDiffAt _ (H.update_mem _ hq.1 _)).comp q
    (contDiff_update_prod m).contDiffAt).contDiffWithinAt

lemma hasCompactSupport_slice {z : σ → ℂ} (hz : z ∈ s) :
    HasCompactSupport fun t ↦ h (Function.update z m t) :=
  HasCompactSupport.intro H.isCompact fun t ht ↦ H.eq_zero z hz t ht

lemma contDiff_slice {z : σ → ℂ} (hz : z ∈ s) :
    ContDiff ℝ ∞ fun t ↦ h (Function.update z m t) :=
  contDiff_iff_contDiffAt.mpr fun t ↦
    (H.contDiffAt _ (H.update_mem z hz t)).comp t (contDiff_update ∞ z m).contDiffAt

end CauchyTransformInData

variable (H : CauchyTransformInData m h s k)
include H

/-- **The Cauchy transform with parameters is smooth.** -/
theorem contDiffOn_cauchyTransformIn : ContDiffOn ℝ ∞ (cauchyTransformIn m h) s := by
  have := contDiffOn_convolution_left_with_param_comp (μ := volume) (n := ⊤)
    (ContinuousLinearMap.mul ℝ ℂ) (v := fun z : σ → ℂ ↦ z m)
    ((contDiff_apply ℝ ℂ m).contDiffOn) (g := fun p t ↦ h (Function.update p m t))
    H.isOpen H.isCompact (fun p t hp ht ↦ H.eq_zero p hp t ht) locallyIntegrable_cauchyKernel
    H.contDiffOn_uncurry
  exact this

theorem contDiffAt_cauchyTransformIn {z : σ → ℂ} (hz : z ∈ s) :
    ContDiffAt ℝ ∞ (cauchyTransformIn m h) z :=
  (contDiffOn_cauchyTransformIn H).contDiffAt (H.isOpen.mem_nhds hz)

/-- **`Tₘ` solves `∂u/∂z̄ₘ = h`.** -/
theorem dbarPartial_cauchyTransformIn_self {z : σ → ℂ} (hz : z ∈ s) :
    dbarPartial m (cauchyTransformIn m h) z = h z := by
  rw [dbarPartial_eq_dbar_update ((contDiffAt_cauchyTransformIn H hz).differentiableAt
    (by simp)) m]
  simp_rw [cauchyTransformIn_update]
  rw [dbar_cauchyTransform (H.hasCompactSupport_slice hz) ((H.contDiff_slice hz).of_le (by simp)),
    Function.update_eq_self]

/-- **`Tₘ` preserves holomorphy in the other variables**: if `∂h/∂z̄ₖ = 0` on `s` for some
`k ≠ m`, then `∂(Tₘh)/∂z̄ₖ = 0` on `s`. -/
theorem dbarPartial_cauchyTransformIn_of_ne {k' : σ} (hk : k' ≠ m)
    (hh : ∀ y ∈ s, dbarPartial k' h y = 0) {z : σ → ℂ} (hz : z ∈ s) :
    dbarPartial k' (cauchyTransformIn m h) z = 0 := by
  set L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ).flip
  set g : (σ → ℂ) → ℂ → ℂ := fun p t ↦ h (Function.update p m t)
  have hg1 : ContDiffOn ℝ 1 ↿g (s ×ˢ univ) := H.contDiffOn_uncurry.of_le (by simp)
  have hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0 := fun p x hp hx ↦ H.eq_zero p hp x hx
  -- the transform as a convolution with the parameter on the right
  set Φ : (σ → ℂ) × ℂ → ℂ := fun q ↦ (cauchyKernel ⋆[L, volume] g q.1) q.2
  have hΦ : cauchyTransformIn m h = fun z ↦ Φ (z, z m) := by
    funext z
    simp only [Φ, L, cauchyTransformIn, cauchyTransform, convolution_flip]
    rfl
  have hD := hasFDerivAt_convolution_right_with_param L H.isOpen H.isCompact hgs
    locallyIntegrable_cauchyKernel hg1 (z, z m) hz
  set D := (cauchyKernel ⋆[L.precompR ((σ → ℂ) × ℂ), volume]
    fun x ↦ fderiv ℝ ↿g (z, x)) (z m)
  have hpair : HasFDerivAt (fun z : σ → ℂ ↦ (z, z m))
      ((ContinuousLinearMap.id ℝ (σ → ℂ)).prod (ContinuousLinearMap.proj m)) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_apply m z)
  have hF : HasFDerivAt (cauchyTransformIn m h)
      (D.comp ((ContinuousLinearMap.id ℝ (σ → ℂ)).prod (ContinuousLinearMap.proj m))) z := by
    rw [hΦ]
    exact hD.comp z hpair
  -- the derivative of the integrand in a direction `(v, 0)`
  have hgcont : Continuous fun x ↦ fderiv ℝ ↿g (z, x) := by
    have := hg1.continuousOn_fderiv_of_isOpen (H.isOpen.prod isOpen_univ) le_rfl
    exact this.comp_continuous (continuous_const.prodMk continuous_id) fun x ↦ ⟨hz, mem_univ x⟩
  have hgcs : HasCompactSupport fun x ↦ fderiv ℝ ↿g (z, x) := by
    refine HasCompactSupport.intro H.isCompact fun x hx ↦ ?_
    refine (hasFDerivAt_zero_of_eventually_const 0 ?_).fderiv
    have M : s ×ˢ kᶜ ∈ 𝓝 (z, x) :=
      (H.isOpen.prod H.isCompact.isClosed.isOpen_compl).mem_nhds ⟨hz, hx⟩
    filter_upwards [M] with q hq using hgs q.1 q.2 hq.1 hq.2
  have hDapply : ∀ v : σ → ℂ, D (v, 0) =
      (cauchyKernel ⋆[L, volume] fun x ↦ fderiv ℝ ↿g (z, x) (v, 0)) (z m) := fun v ↦
    convolution_precompR_apply L locallyIntegrable_cauchyKernel hgcs hgcont (z m) (v, 0)
  -- in the directions `eₖ`, `i eₖ`, the integrand is `ℂ`-linear
  have hgder : ∀ x (v : σ → ℂ), v m = 0 →
      fderiv ℝ ↿g (z, x) (v, 0) = fderiv ℝ h (Function.update z m x) v := by
    intro x v hv
    have hup : HasFDerivAt (fun q : (σ → ℂ) × ℂ ↦ Function.update q.1 m q.2)
        (fderiv ℝ (fun q : (σ → ℂ) × ℂ ↦ Function.update q.1 m q.2) (z, x)) (z, x) :=
      ((contDiff_update_prod m).differentiable (by simp) _).hasFDerivAt
    have hh' : HasFDerivAt h (fderiv ℝ h (Function.update z m x)) (Function.update z m x) :=
      ((H.contDiffAt _ (H.update_mem z hz x)).differentiableAt (by simp)).hasFDerivAt
    have hcomp := hh'.comp (z, x) hup
    change fderiv ℝ (h ∘ fun q : (σ → ℂ) × ℂ ↦ Function.update q.1 m q.2) (z, x) (v, 0) = _
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
    congr 1
    -- the derivative of `(p, t) ↦ p₍ₘ←t₎` in the direction `(v, 0)` with `vₘ = 0` is `v`
    have hlin : (fun q : (σ → ℂ) × ℂ ↦ Function.update q.1 m q.2) =
        fun q ↦ q.1 + (Pi.single m (q.2 - q.1 m) : σ → ℂ) := by
      funext q
      exact update_eq_add_single q.1 m q.2
    have hd : HasFDerivAt (fun q : (σ → ℂ) × ℂ ↦ q.1 + (Pi.single m (q.2 - q.1 m) : σ → ℂ))
        ((ContinuousLinearMap.fst ℝ (σ → ℂ) ℂ) +
          (ContinuousLinearMap.single ℝ (fun _ : σ ↦ ℂ) m).comp
            ((ContinuousLinearMap.snd ℝ (σ → ℂ) ℂ) -
              (ContinuousLinearMap.proj m).comp (ContinuousLinearMap.fst ℝ (σ → ℂ) ℂ))) (z, x) :=
      ((ContinuousLinearMap.fst ℝ (σ → ℂ) ℂ) +
          (ContinuousLinearMap.single ℝ (fun _ : σ ↦ ℂ) m).comp
            ((ContinuousLinearMap.snd ℝ (σ → ℂ) ℂ) -
              (ContinuousLinearMap.proj m).comp
                (ContinuousLinearMap.fst ℝ (σ → ℂ) ℂ))).hasFDerivAt.congr_of_eventuallyEq
        (Eventually.of_forall fun q ↦ by simp [Pi.single_sub])
    rw [hlin, hd.fderiv]
    simp [hv]
  have hlinear : ∀ x, fderiv ℝ ↿g (z, x) (Pi.single k' I, 0) =
      I * fderiv ℝ ↿g (z, x) (Pi.single k' 1, 0) := by
    intro x
    rw [hgder x _ (by simp [hk.symm]), hgder x _ (by simp [hk.symm])]
    exact (dbarPartial_eq_zero_iff k' h _).mp (hh _ (H.update_mem z hz x))
  -- conclusion
  rw [dbarPartial_eq_zero_iff, hF.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.proj_apply]
  rw [Pi.single_eq_of_ne hk.symm, Pi.single_eq_of_ne hk.symm, hDapply, hDapply]
  simp_rw [hlinear]
  simp only [convolution_def, L, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

end AnalyticGeometry
