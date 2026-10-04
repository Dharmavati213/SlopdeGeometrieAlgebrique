/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Moving finitely many points of `ℂ`: local triviality of `ℂ` minus moving points

Let `s : B → (Fin r → ℂ)` be continuous, and `b₀ ∈ B` with the points `s b₀ i` pairwise at distance
`≥ ρ > 0`. For `b` with `∑ᵢ ‖s b i - s b₀ i‖ < ρ / 2` (`isotopyNhd s b₀ ρ`, an open neighbourhood
of `b₀`), the map `x ↦ x + ∑ᵢ tent(x - s b₀ i) (s b i - s b₀ i)` (`famIsotopy`, with
`tent z = max 0 (1 - ‖z‖ / ρ)`) is a homeomorphism of `ℂ` sending `s b₀ i` to `s b i`: it is the
identity plus a `1/2`-Lipschitz map (`isotopy_injective`, `isotopy_surjective` by the contraction
mapping principle). Its inverse depends continuously on `(b, y)` (`norm_famIsotopyInv_sub_le`), so
the family `{(b, x) | x ∉ {s b i}}` is trivial over `isotopyNhd s b₀ ρ` (`isotopyTriv`).

This is the local triviality of the family of punctured lines used in the proof of XII.5.1 in
higher dimension (`SGA.SGA1.ExposeXII.RiemannHigher`); it is elementary (no Ehresmann theorem).
-/
noncomputable section

open Topology Set Metric

namespace SGA.SGA1.ExposeXII.RiemannHigher

/-- A tent function on `ℂ`: `1` at `0`, `0` outside the ball of radius `ρ`, `1/ρ`-Lipschitz. -/
def tent (ρ : ℝ) (z : ℂ) : ℝ := max 0 (1 - ‖z‖ / ρ)

section Tent

variable {ρ : ℝ}

lemma tent_nonneg (z : ℂ) : 0 ≤ tent ρ z := le_max_left _ _

lemma tent_le_one (hρ : 0 < ρ) (z : ℂ) : tent ρ z ≤ 1 :=
  max_le zero_le_one (sub_le_self _ (div_nonneg (norm_nonneg z) hρ.le))

lemma tent_zero : tent ρ 0 = 1 := by
  simp [tent]

lemma tent_eq_zero_of_le {z : ℂ} (hρ : 0 < ρ) (h : ρ ≤ ‖z‖) : tent ρ z = 0 := by
  refine max_eq_left ?_
  rw [sub_nonpos, le_div_iff₀ hρ, one_mul]
  exact h

lemma abs_tent_sub_le (hρ : 0 < ρ) (z w : ℂ) : |tent ρ z - tent ρ w| ≤ ‖z - w‖ / ρ := by
  have h : |(1 - ‖z‖ / ρ) - (1 - ‖w‖ / ρ)| ≤ ‖z - w‖ / ρ := by
    rw [sub_sub_sub_cancel_left, ← sub_div, abs_div, abs_of_pos hρ]
    gcongr
    rw [abs_sub_comm]
    exact abs_norm_sub_norm_le z w
  simp only [tent]
  rw [max_comm 0, max_comm 0]
  exact (abs_max_sub_max_le_abs _ _ 0).trans h

lemma continuous_tent : Continuous (tent ρ) := by
  unfold tent
  fun_prop

end Tent

section Displacement

variable {r : ℕ} (ρ : ℝ) (a δ : Fin r → ℂ)

/-- The displacement `x ↦ ∑ᵢ tent(x - aᵢ) δᵢ`, moving `aᵢ` by `δᵢ` when the `aᵢ` are `ρ`-apart. -/
def displacement (x : ℂ) : ℂ := ∑ i, (tent ρ (x - a i) : ℂ) * δ i

/-- The isotopy `x ↦ x + ∑ᵢ tent(x - aᵢ) δᵢ`. -/
def isotopy (x : ℂ) : ℂ := x + displacement ρ a δ x

variable {ρ a δ}

lemma continuous_displacement : Continuous (displacement ρ a δ) := by
  unfold displacement
  have := continuous_tent (ρ := ρ)
  fun_prop

lemma norm_displacement_sub_le (hρ : 0 < ρ) (x y : ℂ) :
    ‖displacement ρ a δ x - displacement ρ a δ y‖ ≤ (∑ i, ‖δ i‖) / ρ * ‖x - y‖ := by
  unfold displacement
  rw [← Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc |tent ρ (x - a i) - tent ρ (y - a i)| * ‖δ i‖
      ≤ ‖x - y‖ / ρ * ‖δ i‖ := by
        gcongr
        simpa using abs_tent_sub_le hρ (x - a i) (y - a i)
    _ = ‖δ i‖ * ρ⁻¹ * ‖x - y‖ := by ring

lemma norm_displacement_sub_displacement_le (hρ : 0 < ρ) (δ' : Fin r → ℂ) (x : ℂ) :
    ‖displacement ρ a δ x - displacement ρ a δ' x‖ ≤ ∑ i, ‖δ i - δ' i‖ := by
  unfold displacement
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tent_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (tent_le_one hρ _)

lemma isotopy_apply_of_sep (hρ : 0 < ρ) (hsep : ∀ i j, i ≠ j → ρ ≤ ‖a i - a j‖) (i : Fin r) :
    isotopy ρ a δ (a i) = a i + δ i := by
  unfold isotopy displacement
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [tent_eq_zero_of_le hρ (hsep i j hj.symm),
    Complex.ofReal_zero, zero_mul]) (by simp), sub_self, tent_zero, Complex.ofReal_one,
    one_mul]

lemma norm_sub_le_two_mul_norm_isotopy_sub (hρ : 0 < ρ) (hδ : ∑ i, ‖δ i‖ ≤ ρ / 2) (x y : ℂ) :
    ‖x - y‖ ≤ 2 * ‖isotopy ρ a δ x - isotopy ρ a δ y‖ := by
  have hL : (∑ i, ‖δ i‖) / ρ ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ]
    linarith
  have h1 := norm_displacement_sub_le (a := a) (δ := δ) hρ x y
  have h2 : x - y = (isotopy ρ a δ x - isotopy ρ a δ y) -
      (displacement ρ a δ x - displacement ρ a δ y) := by
    unfold isotopy
    ring
  have h3 : ‖x - y‖ ≤ ‖isotopy ρ a δ x - isotopy ρ a δ y‖ +
      ‖displacement ρ a δ x - displacement ρ a δ y‖ := by
    conv_lhs => rw [h2]
    exact norm_sub_le _ _
  nlinarith [norm_nonneg (x - y)]

lemma isotopy_injective (hρ : 0 < ρ) (hδ : ∑ i, ‖δ i‖ ≤ ρ / 2) :
    Function.Injective (isotopy ρ a δ) := fun x y h ↦ by
  have := norm_sub_le_two_mul_norm_isotopy_sub (a := a) hρ hδ x y
  rw [h, sub_self, norm_zero, mul_zero] at this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

lemma isotopy_surjective (hρ : 0 < ρ) (hδ : ∑ i, ‖δ i‖ ≤ ρ / 2) :
    Function.Surjective (isotopy ρ a δ) := fun y ↦ by
  have hL : (∑ i, ‖δ i‖) / ρ ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ]
    linarith
  let K : NNReal := ⟨1 / 2, by norm_num⟩
  have hc : ContractingWith K (fun x ↦ y - displacement ρ a δ x) := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; change (1 / 2 : ℝ) < 1; norm_num,
      LipschitzWith.of_dist_le_mul fun x x' ↦ ?_⟩
    rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_left, norm_sub_rev]
    calc ‖displacement ρ a δ x - displacement ρ a δ x'‖
        ≤ (∑ i, ‖δ i‖) / ρ * ‖x - x'‖ := norm_displacement_sub_le hρ x x'
      _ ≤ 1 / 2 * ‖x - x'‖ := by gcongr
  refine ⟨ContractingWith.fixedPoint _ hc, ?_⟩
  have hfix := ContractingWith.fixedPoint_isFixedPt (f := fun x ↦ y - displacement ρ a δ x) hc
  unfold isotopy
  conv_rhs => rw [← sub_add_cancel y (displacement ρ a δ (ContractingWith.fixedPoint _ hc))]
  rw [hfix.eq, add_comm]

end Displacement

section Family

variable {B : Type*} {r : ℕ} (s : B → Fin r → ℂ) (b₀ : B) (ρ : ℝ)

/-- The parameters `b` whose points `s b` are within total distance `ρ / 2` of `s b₀`. -/
def isotopyNhd : Set B := {b | ∑ i, ‖s b i - s b₀ i‖ < ρ / 2}

/-- The isotopy of `ℂ` moving the points `s b₀` to `s b`. -/
def famIsotopy (b : B) : ℂ → ℂ := isotopy ρ (s b₀) (s b - s b₀)

/-- The inverse of `famIsotopy` (meaningful for `b ∈ isotopyNhd s b₀ ρ`). -/
def famIsotopyInv (b : B) (y : ℂ) : ℂ := Function.invFun (famIsotopy s b₀ ρ b) y

variable {s b₀ ρ}

lemma isOpen_isotopyNhd [TopologicalSpace B] (hs : Continuous s) : IsOpen (isotopyNhd s b₀ ρ) :=
  isOpen_lt (by fun_prop) continuous_const

lemma mem_isotopyNhd (hρ : 0 < ρ) : b₀ ∈ isotopyNhd s b₀ ρ := by
  simp [isotopyNhd, hρ]

lemma sum_le_of_mem_isotopyNhd {b : B} (hb : b ∈ isotopyNhd s b₀ ρ) :
    ∑ i, ‖(s b - s b₀) i‖ ≤ ρ / 2 :=
  le_of_lt hb

lemma famIsotopy_bijective (hρ : 0 < ρ) {b : B} (hb : b ∈ isotopyNhd s b₀ ρ) :
    Function.Bijective (famIsotopy s b₀ ρ b) :=
  ⟨isotopy_injective hρ (sum_le_of_mem_isotopyNhd hb),
    isotopy_surjective hρ (sum_le_of_mem_isotopyNhd hb)⟩

lemma famIsotopy_apply (hρ : 0 < ρ) (hsep : ∀ i j, i ≠ j → ρ ≤ ‖s b₀ i - s b₀ j‖) (b : B)
    (i : Fin r) : famIsotopy s b₀ ρ b (s b₀ i) = s b i := by
  rw [famIsotopy, isotopy_apply_of_sep hρ hsep, Pi.sub_apply, add_sub_cancel]

lemma famIsotopy_self (x : ℂ) : famIsotopy s b₀ ρ b₀ x = x := by
  simp [famIsotopy, isotopy, displacement]

lemma famIsotopy_famIsotopyInv (hρ : 0 < ρ) {b : B} (hb : b ∈ isotopyNhd s b₀ ρ) (y : ℂ) :
    famIsotopy s b₀ ρ b (famIsotopyInv s b₀ ρ b y) = y :=
  Function.invFun_eq ((famIsotopy_bijective hρ hb).2 y)

lemma famIsotopyInv_famIsotopy (hρ : 0 < ρ) {b : B} (hb : b ∈ isotopyNhd s b₀ ρ) (x : ℂ) :
    famIsotopyInv s b₀ ρ b (famIsotopy s b₀ ρ b x) = x :=
  Function.leftInverse_invFun (famIsotopy_bijective hρ hb).1 x

lemma norm_famIsotopyInv_sub_le (hρ : 0 < ρ) {b b' : B} (hb : b ∈ isotopyNhd s b₀ ρ)
    (hb' : b' ∈ isotopyNhd s b₀ ρ) (y y' : ℂ) :
    ‖famIsotopyInv s b₀ ρ b y - famIsotopyInv s b₀ ρ b' y'‖ ≤
      2 * (‖y - y'‖ + ∑ i, ‖s b i - s b' i‖) := by
  set x := famIsotopyInv s b₀ ρ b y
  set x' := famIsotopyInv s b₀ ρ b' y'
  have hy : x + displacement ρ (s b₀) (s b - s b₀) x = y := famIsotopy_famIsotopyInv hρ hb y
  have hy' : x' + displacement ρ (s b₀) (s b' - s b₀) x' = y' :=
    famIsotopy_famIsotopyInv hρ hb' y'
  have hL : (∑ i, ‖(s b - s b₀) i‖) / ρ ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ]
    linarith [sum_le_of_mem_isotopyNhd hb]
  have h1 := norm_displacement_sub_le (a := s b₀) (δ := s b - s b₀) hρ x x'
  have h2 := norm_displacement_sub_displacement_le (a := s b₀) (δ := s b - s b₀) hρ
    (s b' - s b₀) x'
  have h3 : ∑ i, ‖(s b - s b₀) i - (s b' - s b₀) i‖ = ∑ i, ‖s b i - s b' i‖ := by
    simp only [Pi.sub_apply, sub_sub_sub_cancel_right]
  have h4 : x - x' = (y - y') - (displacement ρ (s b₀) (s b - s b₀) x -
      displacement ρ (s b₀) (s b - s b₀) x') - (displacement ρ (s b₀) (s b - s b₀) x' -
      displacement ρ (s b₀) (s b' - s b₀) x') := by
    rw [← hy, ← hy']
    ring
  have h5 : ‖x - x'‖ ≤ ‖y - y'‖ + 1 / 2 * ‖x - x'‖ + ∑ i, ‖s b i - s b' i‖ := by
    refine (congrArg norm h4).le.trans ((norm_sub_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add le_rfl ?_)) (h2.trans h3.le)))
    exact h1.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  linarith

lemma continuous_famIsotopy [TopologicalSpace B] (hs : Continuous s) :
    Continuous fun p : B × ℂ ↦ famIsotopy s b₀ ρ p.1 p.2 := by
  unfold famIsotopy isotopy displacement
  have := continuous_tent (ρ := ρ)
  fun_prop

variable (s) in
/-- `ℂ` minus the points `s b`, for `b` in `U`, as a family over `U`. -/
abbrev PuncturedTotal (U : Set B) : Type _ := {p : B × ℂ // p.1 ∈ U ∧ ∀ i, p.2 ≠ s p.1 i}

variable (s) in
/-- `ℂ` minus the points `s b₀`. -/
abbrev PuncturedFibre (b₀ : B) : Type _ := {x : ℂ // ∀ i, x ≠ s b₀ i}

lemma continuousOn_famIsotopyInv' [TopologicalSpace B] {U : Set B}
    (hU : U ⊆ isotopyNhd s b₀ ρ) (hs : ContinuousOn s U) (hρ : 0 < ρ) :
    ContinuousOn (fun p : B × ℂ ↦ famIsotopyInv s b₀ ρ p.1 p.2) (U ×ˢ univ) := by
  intro p hp
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun q hq ↦
      norm_famIsotopyInv_sub_le hρ (hU hq.1) (hU hp.1) q.2 p.2) ?_
  have hsp : ContinuousWithinAt (fun q : B × ℂ ↦ s q.1) (U ×ˢ univ) p :=
    (hs p.1 hp.1).comp continuousWithinAt_fst fun q hq ↦ hq.1
  have : ContinuousWithinAt (fun q : B × ℂ ↦ 2 * (‖q.2 - p.2‖ + ∑ i, ‖s q.1 i - s p.1 i‖))
      (U ×ˢ univ) p := by
    have h₁ : Continuous fun q : B × ℂ ↦ ‖q.2 - p.2‖ := by fun_prop
    refine continuousWithinAt_const.mul (h₁.continuousWithinAt.add
      (tendsto_finsetSum _ fun i _ ↦ ?_))
    exact ((continuous_apply i).continuousAt.comp_continuousWithinAt hsp |>.sub
      continuousWithinAt_const).norm
  simpa using this.tendsto

lemma continuousOn_famIsotopyInv [TopologicalSpace B] (hs : Continuous s) (hρ : 0 < ρ) :
    ContinuousOn (fun p : B × ℂ ↦ famIsotopyInv s b₀ ρ p.1 p.2)
      (isotopyNhd s b₀ ρ ×ˢ univ) :=
  continuousOn_famIsotopyInv' subset_rfl hs.continuousOn hρ

lemma continuousOn_famIsotopy [TopologicalSpace B] {U : Set B} (hs : ContinuousOn s U) :
    ContinuousOn (fun p : B × ℂ ↦ famIsotopy s b₀ ρ p.1 p.2) (U ×ˢ univ) := by
  unfold famIsotopy isotopy displacement
  have := continuous_tent (ρ := ρ)
  have hs' : ContinuousOn (fun p : B × ℂ ↦ s p.1) (U ×ˢ univ) :=
    hs.comp continuousOn_fst fun q hq ↦ hq.1
  refine continuousOn_snd.add (continuousOn_finsetSum _ fun i _ ↦ ?_)
  refine (Complex.continuous_ofReal.comp_continuousOn ((continuous_tent).comp_continuousOn
    (continuousOn_snd.sub continuousOn_const))).mul ?_
  exact ((continuous_apply i).comp_continuousOn hs').sub continuousOn_const

variable (s) in
/-- `ℂ` minus the points `s b (ι k)`, for `b` in `U`: only some of the moving points are removed. -/
abbrev PuncturedTotalAlong {m : ℕ} (ι : Fin m → Fin r) (U : Set B) : Type _ :=
  {p : B × ℂ // p.1 ∈ U ∧ ∀ k, p.2 ≠ s p.1 (ι k)}

variable (s) in
/-- `ℂ` minus the points `s b₀ (ι k)`. -/
abbrev PuncturedFibreAlong {m : ℕ} (ι : Fin m → Fin r) (b₀ : B) : Type _ :=
  {x : ℂ // ∀ k, x ≠ s b₀ (ι k)}

/-- The isotopies `famIsotopy` trivialize `ℂ` minus the points `s b (ι k)` over any
`U ⊆ isotopyNhd s b₀ ρ` on which `s` is continuous, if all the points `s b₀ i` are `ρ`-apart; the
other moving points `s b i` are carried along (`famIsotopy_apply`). -/
def isotopyTrivAlong [TopologicalSpace B] {m : ℕ} (ι : Fin m → Fin r) {U : Set B}
    (hU : U ⊆ isotopyNhd s b₀ ρ) (hs : ContinuousOn s U) (hρ : 0 < ρ)
    (hsep : ∀ i j, i ≠ j → ρ ≤ ‖s b₀ i - s b₀ j‖) :
    PuncturedTotalAlong s ι U ≃ₜ U × PuncturedFibreAlong s ι b₀ where
  toFun p := (⟨p.1.1, p.2.1⟩, ⟨famIsotopyInv s b₀ ρ p.1.1 p.1.2, fun k h ↦ p.2.2 k (by
    rw [← famIsotopy_famIsotopyInv hρ (hU p.2.1) p.1.2, h, famIsotopy_apply hρ hsep])⟩)
  invFun q := ⟨(q.1.1, famIsotopy s b₀ ρ q.1.1 q.2.1), q.1.2, fun k h ↦ q.2.2 k
    ((famIsotopy_bijective hρ (hU q.1.2)).1 (h.trans (famIsotopy_apply hρ hsep _ (ι k)).symm))⟩
  left_inv p := Subtype.ext (Prod.ext rfl (famIsotopy_famIsotopyInv hρ (hU p.2.1) p.1.2))
  right_inv q := Prod.ext rfl (Subtype.ext (famIsotopyInv_famIsotopy hρ (hU q.1.2) q.2.1))
  continuous_toFun := by
    have h1 : Continuous fun p : PuncturedTotalAlong s ι U ↦ p.1 := continuous_subtype_val
    refine (h1.fst.subtype_mk _).prodMk (Continuous.subtype_mk ?_ _)
    exact (continuousOn_famIsotopyInv' hU hs hρ).comp_continuous h1 fun p ↦ ⟨p.2.1, trivial⟩
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine (continuous_subtype_val.comp continuous_fst).prodMk ?_
    exact (continuousOn_famIsotopy hs).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)) fun q ↦ ⟨q.1.2, trivial⟩

lemma isotopyTrivAlong_apply_snd [TopologicalSpace B] {m : ℕ} (ι : Fin m → Fin r) {U : Set B}
    (hU : U ⊆ isotopyNhd s b₀ ρ) (hs : ContinuousOn s U) (hρ : 0 < ρ)
    (hsep : ∀ i j, i ≠ j → ρ ≤ ‖s b₀ i - s b₀ j‖) (p : PuncturedTotalAlong s ι U) :
    ((isotopyTrivAlong ι hU hs hρ hsep p).2 : ℂ) = famIsotopyInv s b₀ ρ p.1.1 p.1.2 := rfl

/-- `isotopyTriv` over any `U ⊆ isotopyNhd s b₀ ρ` on which `s` is continuous
(`isotopyTrivAlong` removing all the moving points). -/
def isotopyTrivOn [TopologicalSpace B] {U : Set B} (hU : U ⊆ isotopyNhd s b₀ ρ)
    (hs : ContinuousOn s U) (hρ : 0 < ρ) (hsep : ∀ i j, i ≠ j → ρ ≤ ‖s b₀ i - s b₀ j‖) :
    PuncturedTotal s U ≃ₜ U × PuncturedFibre s b₀ :=
  isotopyTrivAlong id hU hs hρ hsep

/-- Local triviality of `ℂ` minus moving points: over `isotopyNhd s b₀ ρ`, the family of the
`ℂ ∖ {s b}` is trivial, through the isotopies `famIsotopy`, if the points `s b₀ i` are `ρ`-apart
and `s` is continuous (`isotopyTrivOn` for `U = isotopyNhd s b₀ ρ`). -/
def isotopyTriv [TopologicalSpace B] (hs : Continuous s) (hρ : 0 < ρ)
    (hsep : ∀ i j, i ≠ j → ρ ≤ ‖s b₀ i - s b₀ j‖) :
    PuncturedTotal s (isotopyNhd s b₀ ρ) ≃ₜ isotopyNhd s b₀ ρ × PuncturedFibre s b₀ :=
  isotopyTrivOn subset_rfl hs.continuousOn hρ hsep

lemma isotopyTriv_fst [TopologicalSpace B] (hs : Continuous s) (hρ : 0 < ρ)
    (hsep : ∀ i j, i ≠ j → ρ ≤ ‖s b₀ i - s b₀ j‖) (p : PuncturedTotal s (isotopyNhd s b₀ ρ)) :
    ((isotopyTriv hs hρ hsep p).1 : B) = p.1.1 := rfl

lemma isotopyTriv_symm_apply [TopologicalSpace B] (hs : Continuous s) (hρ : 0 < ρ)
    (hsep : ∀ i j, i ≠ j → ρ ≤ ‖s b₀ i - s b₀ j‖)
    (q : isotopyNhd s b₀ ρ × PuncturedFibre s b₀) :
    ((isotopyTriv hs hρ hsep).symm q).1 = (q.1.1, famIsotopy s b₀ ρ q.1.1 q.2.1) := rfl

end Family

end SGA.SGA1.ExposeXII.RiemannHigher
