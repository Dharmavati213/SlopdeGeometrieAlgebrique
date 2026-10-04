/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.RungeParam
import SGA.Foundations.Analytic.RungeLaurent

/-!
# The Laurent splitting with holomorphic parameters

Fix a coordinate `j` of `ℂ^σ`. For `f : ℂ^σ → ℂ` define, with the other coordinates as parameters,

* the **nonnegative Laurent part** `laurentPlus j R f z = (2πi)⁻¹ ∮_{|ζ|=R} f(z₍ⱼ←ζ₎)/(ζ - zⱼ) dζ`;
* the **negative Laurent part** `laurentMinus j r f z = -(2πi)⁻¹ ∮_{|ζ|=r} f(z₍ⱼ←ζ₎)/(ζ - zⱼ) dζ`,
  and its expression in the coordinate `w = 1/zⱼ` at infinity,
  `laurentMinusInv j r f z = (2πi)⁻¹ ∮_{|ζ|=r} zⱼ (1 - zⱼ ζ)⁻¹ f(z₍ⱼ←ζ₎) dζ`
  (`AnalyticGeometry.laurentMinus_update_inv`).

Main results:

* analyticity in all variables: `AnalyticGeometry.analyticAt_laurentPlus` (where `|zⱼ| ≠ R`),
  `AnalyticGeometry.analyticAt_laurentMinusInv` (where `|zⱼ| r < 1`, including `zⱼ = 0`, where it
  vanishes: `AnalyticGeometry.laurentMinusInv_of_eq_zero`);
* the splitting `f = f₊ + f₋` on an annulus in `zⱼ`
  (`AnalyticGeometry.eq_laurentPlus_add_laurentMinus`) and independence of the radii
  (`AnalyticGeometry.laurentPlus_eq_of_le`, `AnalyticGeometry.laurentMinusInv_eq_of_le`);
* **the global splitting** (`AnalyticGeometry.exists_laurent_splitting`): if `U ⊆ ℂ^σ` is open
  and stable under changing `zⱼ`, and `f` is analytic on `U ∩ {zⱼ ≠ 0}`, then
  `f(z) = g(z) + h(z₍ⱼ←zⱼ⁻¹₎)` on `U ∩ {zⱼ ≠ 0}` with `g`, `h` analytic on all of `U` and
  `h = 0` on `{zⱼ = 0}`. For `U = ℂ^σ` this is the Laurent splitting on `ℂ* × ℂ^{σ ∖ j}` used to
  compute the cohomology of `𝒪(d)` on `ℙⁿ` by the standard affine cover (Serre, *Géométrie
  algébrique et géométrie analytique*, §3, no. 13, footnote 4; Cartan's seminar 1951/52).

Reference: Ahlfors, *Complex analysis*, 5.1.3; Gunning–Rossi, *Analytic functions of several
complex variables*, I.A (holomorphy of integrals with parameters).
-/

noncomputable section

open Complex Set Metric Filter Topology
open scoped Real

namespace AnalyticGeometry

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The nonnegative Laurent part in `zⱼ`, on the circle `|ζ| = R`:
`(2πi)⁻¹ ∮_{|ζ| = R} (ζ - zⱼ)⁻¹ f(z₍ⱼ←ζ₎) dζ`. -/
def laurentPlus (j : σ) (R : ℝ) (f : (σ → ℂ) → ℂ) (z : σ → ℂ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ ζ in C(0, R), (ζ - z j)⁻¹ * f (Function.update z j ζ)

/-- The negative Laurent part in `zⱼ`, on the circle `|ζ| = r`:
`-(2πi)⁻¹ ∮_{|ζ| = r} (ζ - zⱼ)⁻¹ f(z₍ⱼ←ζ₎) dζ`. -/
def laurentMinus (j : σ) (r : ℝ) (f : (σ → ℂ) → ℂ) (z : σ → ℂ) : ℂ :=
  -((2 * π * I)⁻¹ * ∮ ζ in C(0, r), (ζ - z j)⁻¹ * f (Function.update z j ζ))

/-- The negative Laurent part in the coordinate `w = zⱼ` at infinity:
`(2πi)⁻¹ ∮_{|ζ| = r} zⱼ (1 - zⱼ ζ)⁻¹ f(z₍ⱼ←ζ₎) dζ` (`laurentMinus_update_inv`). -/
def laurentMinusInv (j : σ) (r : ℝ) (f : (σ → ℂ) → ℂ) (z : σ → ℂ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ ζ in C(0, r), z j * (1 - z j * ζ)⁻¹ * f (Function.update z j ζ)

omit [DecidableEq σ] in
/-- `p ↦ p.1 j` is analytic on `ℂ^σ × ℂ`. -/
private lemma analyticAt_fst_apply (j : σ) (p : (σ → ℂ) × ℂ) :
    AnalyticAt ℂ (fun p : (σ → ℂ) × ℂ ↦ p.1 j) p :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ↦ ℂ) j).analyticAt _).comp analyticAt_fst

private lemma analyticAt_comp_update {f : (σ → ℂ) → ℂ} {j : σ} {p : (σ → ℂ) × ℂ}
    (hf : AnalyticAt ℂ f (Function.update p.1 j p.2)) :
    AnalyticAt ℂ (fun p : (σ → ℂ) × ℂ ↦ f (Function.update p.1 j p.2)) p :=
  AnalyticAt.comp (g := f) (f := fun p : (σ → ℂ) × ℂ ↦ Function.update p.1 j p.2) hf
    (analyticAt_update_prod j p)

/-- The nonnegative Laurent part is analytic at `z₀` if `|z₀ⱼ| ≠ |R|` and `f` is analytic along
the circle `{z₀₍ⱼ←ζ₎ : |ζ| = |R|}`. -/
theorem analyticAt_laurentPlus {j : σ} {R : ℝ} {f : (σ → ℂ) → ℂ} {z₀ : σ → ℂ}
    (hz : ‖z₀ j‖ ≠ |R|) (hf : ∀ ζ ∈ sphere (0 : ℂ) |R|, AnalyticAt ℂ f (Function.update z₀ j ζ)) :
    AnalyticAt ℂ (laurentPlus j R f) z₀ := by
  refine analyticAt_const.mul (analyticAt_circleIntegral_param fun ζ hζ ↦ ?_)
  have hne : ζ - z₀ j ≠ 0 := fun h ↦ hz (by
    rw [← sub_eq_zero.mp h]
    exact mem_sphere_zero_iff_norm.mp hζ)
  exact ((analyticAt_snd.sub (analyticAt_fst_apply j _)).inv hne).mul
    (analyticAt_comp_update (hf ζ hζ))

/-- The negative Laurent part is analytic at `z₀` if `|z₀ⱼ| ≠ |r|` and `f` is analytic along the
circle `{z₀₍ⱼ←ζ₎ : |ζ| = |r|}`. -/
theorem analyticAt_laurentMinus {j : σ} {r : ℝ} {f : (σ → ℂ) → ℂ} {z₀ : σ → ℂ}
    (hz : ‖z₀ j‖ ≠ |r|) (hf : ∀ ζ ∈ sphere (0 : ℂ) |r|, AnalyticAt ℂ f (Function.update z₀ j ζ)) :
    AnalyticAt ℂ (laurentMinus j r f) z₀ :=
  (analyticAt_laurentPlus hz hf).neg

/-- The negative Laurent part in the coordinate at infinity is analytic at `z₀` if
`|z₀ⱼ| |r| < 1` and `f` is analytic along the circle `{z₀₍ⱼ←ζ₎ : |ζ| = |r|}`. -/
theorem analyticAt_laurentMinusInv {j : σ} {r : ℝ} {f : (σ → ℂ) → ℂ} {z₀ : σ → ℂ}
    (hz : ‖z₀ j‖ * |r| < 1)
    (hf : ∀ ζ ∈ sphere (0 : ℂ) |r|, AnalyticAt ℂ f (Function.update z₀ j ζ)) :
    AnalyticAt ℂ (laurentMinusInv j r f) z₀ := by
  refine analyticAt_const.mul (analyticAt_circleIntegral_param fun ζ hζ ↦ ?_)
  have hne : 1 - z₀ j * ζ ≠ 0 := by
    intro h
    have h1 : z₀ j * ζ = 1 := (sub_eq_zero.mp h).symm
    have h2 : ‖z₀ j * ζ‖ = ‖z₀ j‖ * |r| := by
      rw [norm_mul, mem_sphere_zero_iff_norm.mp hζ]
    rw [h1, norm_one] at h2
    linarith
  exact ((analyticAt_fst_apply j _).mul ((analyticAt_const.sub
    ((analyticAt_fst_apply j _).mul analyticAt_snd)).inv hne)).mul
    (analyticAt_comp_update (hf ζ hζ))

omit [Fintype σ] in
@[simp] lemma laurentMinusInv_of_eq_zero {j : σ} {r : ℝ} {f : (σ → ℂ) → ℂ} {z : σ → ℂ}
    (hz : z j = 0) : laurentMinusInv j r f z = 0 := by
  simp [laurentMinusInv, hz, circleIntegral]

omit [Fintype σ] in
/-- `laurentMinusInv` is `laurentMinus` read in the coordinate `w = 1/zⱼ`. -/
theorem laurentMinus_update_inv {j : σ} {r : ℝ} {f : (σ → ℂ) → ℂ} {z : σ → ℂ} (hz : z j ≠ 0) :
    laurentMinus j r f (Function.update z j (z j)⁻¹) = laurentMinusInv j r f z := by
  have hpt : ∀ ζ : ℂ, -((ζ - (z j)⁻¹)⁻¹ * f (Function.update z j ζ)) =
      z j * (1 - z j * ζ)⁻¹ * f (Function.update z j ζ) := fun ζ ↦ by
    by_cases h1 : 1 - z j * ζ = 0
    · have h2 : ζ - (z j)⁻¹ = 0 := by
        have : ζ = (z j)⁻¹ := by
          field_simp
          linear_combination -h1
        rw [this, sub_self]
      rw [h1, h2]
      simp
    · have h2 : ζ - (z j)⁻¹ = -(1 - z j * ζ) / z j := by
        field_simp
        ring
      rw [h2]
      field_simp
  simp only [laurentMinus, laurentMinusInv, Function.update_self, Function.update_idem]
  rw [← mul_neg]
  congr 1
  rw [neg_eq_neg_one_mul, ← circleIntegral.integral_const_mul]
  congr 1
  funext ζ
  rw [← hpt ζ]
  ring

/-- **The Laurent splitting on an annulus**: if `0 ≤ r`, `r < |zⱼ| < R` (or `|zⱼ| < R` and
`r = 0`), and `f` is analytic at `z₍ⱼ←ζ₎` for `r ≤ |ζ| ≤ R`, then
`f(z) = laurentPlus j R f z + laurentMinus j r f z`. -/
theorem eq_laurentPlus_add_laurentMinus {j : σ} {r R : ℝ} {f : (σ → ℂ) → ℂ} {z : σ → ℂ}
    (hr : 0 ≤ r) (hrz : r = 0 ∨ r < ‖z j‖) (hzR : ‖z j‖ < R)
    (hf : ∀ ζ ∈ closedAnnulus r R, AnalyticAt ℂ f (Function.update z j ζ)) :
    f z = laurentPlus j R f z + laurentMinus j r f z := by
  have hF : ∀ ζ ∈ closedAnnulus r R, DifferentiableAt ℂ (fun ζ ↦ f (Function.update z j ζ)) ζ :=
    fun ζ hζ ↦ ((hf ζ hζ).comp (analyticAt_update_right z j ζ)).differentiableAt
  have h := circleIntegral_sub_circleIntegral_eq hr hF hzR hrz
  have h2π : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  simp only [Function.update_eq_self] at h
  rw [laurentPlus, laurentMinus, ← sub_eq_add_neg, ← mul_sub, h, ← mul_assoc,
    inv_mul_cancel₀ h2π, one_mul]

/-- **Independence of the radius** for the nonnegative part: if `0 < R ≤ R'`, `|zⱼ| < R` and `f` is
analytic at `z₍ⱼ←ζ₎` for `R ≤ |ζ| ≤ R'`, then `laurentPlus j R f z = laurentPlus j R' f z`. -/
theorem laurentPlus_eq_of_le {j : σ} {R R' : ℝ} {f : (σ → ℂ) → ℂ} {z : σ → ℂ} (hR : 0 < R)
    (hRR' : R ≤ R') (hz : ‖z j‖ < R)
    (hf : ∀ ζ ∈ closedAnnulus R R', AnalyticAt ℂ f (Function.update z j ζ)) :
    laurentPlus j R f z = laurentPlus j R' f z := by
  have hd : ∀ ζ ∈ closedAnnulus R R',
      DifferentiableAt ℂ (fun ζ ↦ (ζ - z j)⁻¹ * f (Function.update z j ζ)) ζ := fun ζ hζ ↦ by
    have hne : ζ - z j ≠ 0 := fun h ↦ by
      have := hζ.1
      rw [sub_eq_zero.mp h] at this
      linarith
    have h1 : DifferentiableAt ℂ (fun ζ : ℂ ↦ (ζ - z j)⁻¹) ζ :=
      ((differentiableAt_id (x := ζ)).sub_const (z j)).inv hne
    exact h1.mul ((hf ζ hζ).comp (analyticAt_update_right z j ζ)).differentiableAt
  have h := circleIntegral_eq_of_differentiable_on_annulus_off_countable hR hRR' countable_empty
    (fun ζ hζ ↦ (hd ζ ⟨by simpa using hζ.2, mem_closedBall_zero_iff.mp hζ.1⟩).continuousAt
      |>.continuousWithinAt)
    (fun ζ hζ ↦ hd ζ ⟨(not_le.mp (by simpa using hζ.1.2)).le, (mem_ball_zero_iff.mp hζ.1.1).le⟩)
  rw [laurentPlus, laurentPlus, h]

/-- **Independence of the radius** for the negative part at infinity: if `0 < r ≤ r'`,
`|zⱼ| r' < 1` and `f` is analytic at `z₍ⱼ←ζ₎` for `r ≤ |ζ| ≤ r'`, then
`laurentMinusInv j r f z = laurentMinusInv j r' f z`. -/
theorem laurentMinusInv_eq_of_le {j : σ} {r r' : ℝ} {f : (σ → ℂ) → ℂ} {z : σ → ℂ} (hr : 0 < r)
    (hrr' : r ≤ r') (hz : ‖z j‖ * r' < 1)
    (hf : ∀ ζ ∈ closedAnnulus r r', AnalyticAt ℂ f (Function.update z j ζ)) :
    laurentMinusInv j r f z = laurentMinusInv j r' f z := by
  have hd : ∀ ζ ∈ closedAnnulus r r', DifferentiableAt ℂ
      (fun ζ ↦ z j * (1 - z j * ζ)⁻¹ * f (Function.update z j ζ)) ζ := fun ζ hζ ↦ by
    have hne : 1 - z j * ζ ≠ 0 := fun h ↦ by
      have h1 : z j * ζ = 1 := (sub_eq_zero.mp h).symm
      have h2 : ‖z j * ζ‖ ≤ ‖z j‖ * r' := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hζ.2 (norm_nonneg _)
      rw [h1, norm_one] at h2
      linarith
    have h1 : DifferentiableAt ℂ (fun ζ : ℂ ↦ 1 - z j * ζ) ζ :=
      (differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)
    exact ((differentiableAt_const (z j)).mul (h1.inv hne)).mul
      ((hf ζ hζ).comp (analyticAt_update_right z j ζ)).differentiableAt
  have h := circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrr' countable_empty
    (fun ζ hζ ↦ (hd ζ ⟨by simpa using hζ.2, mem_closedBall_zero_iff.mp hζ.1⟩).continuousAt
      |>.continuousWithinAt)
    (fun ζ hζ ↦ hd ζ ⟨(not_le.mp (by simpa using hζ.1.2)).le, (mem_ball_zero_iff.mp hζ.1.1).le⟩)
  rw [laurentMinusInv, laurentMinusInv, h]

/-! ### The Laurent projectors -/

/-- **The Laurent projector** `Pⱼ`: the nonnegative Laurent part in `zⱼ`, computed on the circle
`|ζ| = |zⱼ| + 1`, i.e. `laurentPlus j (‖z j‖ + 1) f z`. -/
def laurentProj (j : σ) (f : (σ → ℂ) → ℂ) (z : σ → ℂ) : ℂ :=
  laurentPlus j (‖z j‖ + 1) f z

/-- The complementary negative Laurent part in `zⱼ`, written in the coordinate `w = 1/zⱼ` at
infinity and computed on the circle `|ζ| = (|wⱼ| + 1)⁻¹`, i.e.
`laurentMinusInv j (‖z j‖ + 1)⁻¹ f z`. -/
def laurentProjInv (j : σ) (f : (σ → ℂ) → ℂ) (z : σ → ℂ) : ℂ :=
  laurentMinusInv j (‖z j‖ + 1)⁻¹ f z

omit [Fintype σ] in
@[simp] lemma laurentProjInv_of_eq_zero {j : σ} {f : (σ → ℂ) → ℂ} {z : σ → ℂ} (hz : z j = 0) :
    laurentProjInv j f z = 0 :=
  laurentMinusInv_of_eq_zero hz

section Projector

variable {j : σ} {U : Set (σ → ℂ)} {f : (σ → ℂ) → ℂ}

/-- `f` is analytic along every punctured coordinate line through `U`. -/
private lemma analyticAt_update_of_ne_zero (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U)
    (hf : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ f z) {z : σ → ℂ} (hz : z ∈ U) {ζ : ℂ} (hζ : ζ ≠ 0) :
    AnalyticAt ℂ f (Function.update z j ζ) :=
  hf _ (hUj z hz ζ) (by simpa using hζ)

private lemma analyticAt_update_of_mem_closedAnnulus
    (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U) (hf : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ f z)
    {z : σ → ℂ} (hz : z ∈ U) {a b : ℝ} (ha : 0 < a) {ζ : ℂ} (hζ : ζ ∈ closedAnnulus a b) :
    AnalyticAt ℂ f (Function.update z j ζ) :=
  analyticAt_update_of_ne_zero hUj hf hz fun h ↦ by
    have := hζ.1
    rw [h, norm_zero] at this
    linarith

/-- **The Laurent projector is analytic on `U`**, including where `zⱼ = 0`: here `U` is open and
stable under changing `zⱼ`, and `f` is analytic at every point of `U` with `zⱼ ≠ 0`. -/
theorem analyticAt_laurentProj (hU : IsOpen U) (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U)
    (hf : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ f z) {z₀ : σ → ℂ} (hz₀ : z₀ ∈ U) :
    AnalyticAt ℂ (laurentProj j f) z₀ := by
  have hcont : Continuous fun z : σ → ℂ ↦ ‖z j‖ := (continuous_apply j).norm
  -- `Pⱼ f` agrees near `z₀` with the nonnegative part on the fixed circle `|ζ| = |z₀ⱼ| + 1`
  set R₀ : ℝ := ‖z₀ j‖ + 1
  have hR₀ : 0 < R₀ := by positivity
  have hev : laurentProj j f =ᶠ[𝓝 z₀] laurentPlus j R₀ f := by
    have hlt : ∀ᶠ z in 𝓝 z₀, ‖z j‖ < R₀ :=
      hcont.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
    filter_upwards [hlt, hU.mem_nhds hz₀] with z hz hzU
    simp only [laurentProj]
    rcases le_total (‖z j‖ + 1) R₀ with hle | hle
    · exact laurentPlus_eq_of_le (by positivity) hle (lt_add_one _)
        fun ζ hζ ↦ analyticAt_update_of_mem_closedAnnulus hUj hf hzU (by positivity) hζ
    · exact (laurentPlus_eq_of_le hR₀ hle hz
        fun ζ hζ ↦ analyticAt_update_of_mem_closedAnnulus hUj hf hzU hR₀ hζ).symm
  have hne : ∀ ζ ∈ sphere (0 : ℂ) |R₀|, ζ ≠ 0 := by
    rintro ζ hζ rfl
    rw [mem_sphere_zero_iff_norm, norm_zero, abs_of_pos hR₀] at hζ
    exact hR₀.ne hζ
  refine (analyticAt_laurentPlus ?_ fun ζ hζ ↦
    analyticAt_update_of_ne_zero hUj hf hz₀ (hne ζ hζ)).congr hev.symm
  rw [abs_of_pos hR₀]
  exact (lt_add_one _).ne

/-- **The complementary projector is analytic on `U`**, including where `zⱼ = 0` (where it
vanishes, `laurentProjInv_of_eq_zero`); hypotheses as in `analyticAt_laurentProj`. -/
theorem analyticAt_laurentProjInv (hU : IsOpen U)
    (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U) (hf : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ f z)
    {z₀ : σ → ℂ} (hz₀ : z₀ ∈ U) : AnalyticAt ℂ (laurentProjInv j f) z₀ := by
  have hcont : Continuous fun z : σ → ℂ ↦ ‖z j‖ := (continuous_apply j).norm
  -- it agrees near `z₀` with the negative part on the fixed circle `|ζ| = (|z₀ⱼ| + 1)⁻¹`
  set r₀ : ℝ := (‖z₀ j‖ + 1)⁻¹
  have hr₀ : 0 < r₀ := by positivity
  have hlt1 : ∀ z : σ → ℂ, ‖z j‖ * (‖z j‖ + 1)⁻¹ < 1 := fun z ↦ by
    rw [← div_eq_mul_inv, div_lt_one (by positivity)]
    exact lt_add_one _
  have hev : laurentProjInv j f =ᶠ[𝓝 z₀] laurentMinusInv j r₀ f := by
    have hlt : ∀ᶠ z in 𝓝 z₀, ‖z j‖ < ‖z₀ j‖ + 1 :=
      hcont.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
    filter_upwards [hlt, hU.mem_nhds hz₀] with z hz hzU
    simp only [laurentProjInv]
    have hz' : ‖z j‖ * r₀ < 1 := by
      rw [← div_eq_mul_inv, div_lt_one (by positivity)]
      exact hz
    rcases le_total (‖z j‖ + 1)⁻¹ r₀ with hle | hle
    · exact laurentMinusInv_eq_of_le (by positivity) hle hz'
        fun ζ hζ ↦ analyticAt_update_of_mem_closedAnnulus hUj hf hzU (by positivity) hζ
    · exact (laurentMinusInv_eq_of_le hr₀ hle (hlt1 z)
        fun ζ hζ ↦ analyticAt_update_of_mem_closedAnnulus hUj hf hzU hr₀ hζ).symm
  have hne : ∀ ζ ∈ sphere (0 : ℂ) |r₀|, ζ ≠ 0 := by
    rintro ζ hζ rfl
    rw [mem_sphere_zero_iff_norm, norm_zero, abs_of_pos hr₀] at hζ
    exact hr₀.ne hζ
  refine (analyticAt_laurentMinusInv ?_ fun ζ hζ ↦
    analyticAt_update_of_ne_zero hUj hf hz₀ (hne ζ hζ)).congr hev.symm
  rw [abs_of_pos hr₀]
  exact hlt1 z₀

/-- **The Laurent splitting by the projectors**: if `U` is stable under changing `zⱼ` and `f` is
analytic at every point of `U` with `zⱼ ≠ 0`, then
`f(z) = Pⱼ f(z) + laurentProjInv j f (z₍ⱼ←zⱼ⁻¹₎)` for `z ∈ U` with `zⱼ ≠ 0`. -/
theorem eq_laurentProj_add_laurentProjInv (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U)
    (hf : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ f z) {z : σ → ℂ} (hz : z ∈ U) (hzj : z j ≠ 0) :
    f z = laurentProj j f z + laurentProjInv j f (Function.update z j (z j)⁻¹) := by
  -- the splitting on the annulus `r < |zⱼ| < |zⱼ| + 1`
  have hzpos : 0 < ‖z j‖ := norm_pos_iff.mpr hzj
  set z' : σ → ℂ := Function.update z j (z j)⁻¹ with hz'def
  have hz'j : z' j = (z j)⁻¹ := by simp [hz'def]
  have hz'z : Function.update z' j (z' j)⁻¹ = z := by
    rw [hz'j, inv_inv, hz'def, Function.update_idem, Function.update_eq_self]
  set r : ℝ := (‖z' j‖ + 1)⁻¹ with hrdef
  have hr : 0 < r := by positivity
  have hrz : r < ‖z j‖ := by
    rw [hrdef, hz'j, norm_inv]
    rw [inv_lt_comm₀ (by positivity) hzpos]
    exact lt_add_one _
  have hsplit := eq_laurentPlus_add_laurentMinus (j := j) (f := f) (z := z) hr.le (Or.inr hrz)
    (lt_add_one ‖z j‖) fun ζ hζ ↦ analyticAt_update_of_mem_closedAnnulus hUj hf hz hr hζ
  have hminus : laurentMinus j r f z = laurentProjInv j f z' := by
    have := laurentMinus_update_inv (j := j) (r := r) (f := f) (z := z') (by
      rw [hz'j]
      exact inv_ne_zero hzj)
    rw [hz'z] at this
    rw [this]
    rfl
  rw [hsplit, hminus]
  rfl

end Projector

/-- **The Laurent splitting with holomorphic parameters**: let `U ⊆ ℂ^σ` be open and stable under
changing the coordinate `zⱼ`, and let `f` be analytic at every point of `U` with `zⱼ ≠ 0`. Then
there are `g`, `h` analytic at every point of `U` (including `zⱼ = 0`), with `h = 0` where
`zⱼ = 0`, such that `f(z) = g(z) + h(z₍ⱼ←zⱼ⁻¹₎)` for `z ∈ U` with `zⱼ ≠ 0`. One can take
`g = laurentProj j f`, `h = laurentProjInv j f` (`eq_laurentProj_add_laurentProjInv`); the
splitting is unique (`AnalyticGeometry.laurent_splitting_unique`, `RungeLaurentProjector.lean`). -/
theorem exists_laurent_splitting {j : σ} {U : Set (σ → ℂ)} (hU : IsOpen U)
    (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U) {f : (σ → ℂ) → ℂ}
    (hf : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ f z) :
    ∃ g h : (σ → ℂ) → ℂ, (∀ z ∈ U, AnalyticAt ℂ g z) ∧ (∀ z ∈ U, AnalyticAt ℂ h z) ∧
      (∀ z, z j = 0 → h z = 0) ∧
      ∀ z ∈ U, z j ≠ 0 → f z = g z + h (Function.update z j (z j)⁻¹) :=
  ⟨laurentProj j f, laurentProjInv j f, fun _ hz ↦ analyticAt_laurentProj hU hUj hf hz,
    fun _ hz ↦ analyticAt_laurentProjInv hU hUj hf hz, fun _ hz ↦ laurentProjInv_of_eq_zero hz,
    fun _ hz hzj ↦ eq_laurentProj_add_laurentProjInv hUj hf hz hzj⟩

end AnalyticGeometry
