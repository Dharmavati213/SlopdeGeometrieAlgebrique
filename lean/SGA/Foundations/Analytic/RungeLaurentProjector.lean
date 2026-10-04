/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.RungeLaurentSplitting
import Mathlib.Analysis.Complex.Liouville

/-!
# The Laurent projectors: uniqueness, idempotence, commutation, homogeneity

Fix a coordinate `j` of `ℂ^σ`, an open set `U ⊆ ℂ^σ` stable under changing `zⱼ`, and `f`
analytic on `U ∩ {zⱼ ≠ 0}`. The Laurent splitting `f(z) = Pⱼf(z) + Rⱼf(z₍ⱼ←zⱼ⁻¹₎)`
(`AnalyticGeometry.laurentProj`, `AnalyticGeometry.laurentProjInv`,
`AnalyticGeometry.eq_laurentProj_add_laurentProjInv`), with `Pⱼf`, `Rⱼf` analytic on `U` and
`Rⱼf = 0` on `{zⱼ = 0}`, is **unique** (`AnalyticGeometry.laurent_splitting_unique`, Liouville's
theorem on each coordinate line). Consequently:

* `AnalyticGeometry.laurentProj_eq_of_splitting`: any such splitting is the projector's;
* `AnalyticGeometry.laurentProj_eq_self`: `Pⱼf = f` and `Rⱼf = 0` if `f` is analytic on all of
  `U`; hence `Pⱼ ∘ Pⱼ = Pⱼ` (`AnalyticGeometry.laurentProj_laurentProj`);
* linearity: `AnalyticGeometry.laurentProj_add`, `AnalyticGeometry.laurentProj_const_mul`;
* **commutation** `PᵢPⱼ = PⱼPᵢ` for `i ≠ j` (`AnalyticGeometry.laurentProj_comm`), for `f`
  analytic on `U ∩ {zᵢ ≠ 0} ∩ {zⱼ ≠ 0}`, `U` stable under changing `zᵢ` and `zⱼ`;
* **homogeneity**: if `U` is stable under `z ↦ cz` and `f(cz) = cᵈ f(z)`, then
  `Pⱼf(cz) = cᵈ Pⱼf(z)` (`AnalyticGeometry.laurentProj_smul`).

These are the analytic inputs of the computation of the cohomology of `𝒪(d)` on `ℙⁿ` by the
standard affine cover, where the analytic Čech complex is decomposed by the commuting projectors
`Pⱼ` according to the signs of the Laurent exponents (Serre, *Géométrie algébrique et géométrie
analytique*, §3, no. 13; Cartan's seminar 1951/52).

Reference: Ahlfors, *Complex analysis*, 5.1.3 (Laurent series), 4.2.3 (Liouville).
-/

noncomputable section

open Complex Set Metric Filter Topology
open scoped Real

namespace AnalyticGeometry

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ### Uniqueness of the splitting -/

/-- **Uniqueness of the Laurent splitting**: let `U` be stable under changing `zⱼ`, let `g`, `h`
be analytic on `U` with `h = 0` on `U ∩ {zⱼ = 0}`, and `g(z) + h(z₍ⱼ←zⱼ⁻¹₎) = 0` on
`U ∩ {zⱼ ≠ 0}`. Then `g = h = 0` on `U`. -/
theorem laurent_splitting_unique {j : σ} {U : Set (σ → ℂ)}
    (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U) {g h : (σ → ℂ) → ℂ}
    (hg : ∀ z ∈ U, AnalyticAt ℂ g z) (hh : ∀ z ∈ U, AnalyticAt ℂ h z)
    (hh0 : ∀ z ∈ U, z j = 0 → h z = 0)
    (hgh : ∀ z ∈ U, z j ≠ 0 → g z + h (Function.update z j (z j)⁻¹) = 0) {z : σ → ℂ}
    (hz : z ∈ U) : g z = 0 ∧ h z = 0 := by
  -- the restrictions to the coordinate line through `z`
  set φ : ℂ → ℂ := fun t ↦ g (Function.update z j t) with hφdef
  set ψ : ℂ → ℂ := fun t ↦ h (Function.update z j t) with hψdef
  have hφ : Differentiable ℂ φ := fun t ↦
    ((hg _ (hUj z hz t)).comp (analyticAt_update_right z j t)).differentiableAt
  have hψ : Differentiable ℂ ψ := fun t ↦
    ((hh _ (hUj z hz t)).comp (analyticAt_update_right z j t)).differentiableAt
  have hrel : ∀ t : ℂ, t ≠ 0 → φ t + ψ t⁻¹ = 0 := fun t ht ↦ by
    have := hgh _ (hUj z hz t) (by simpa using ht)
    simpa [hφdef, hψdef, Function.update_idem] using this
  -- `φ` is bounded, hence constant
  obtain ⟨Cφ, hCφ⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hφ.continuous.continuousOn
  obtain ⟨Cψ, hCψ⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hψ.continuous.continuousOn
  have hbound : ∀ t, ‖φ t‖ ≤ max Cφ Cψ := fun t ↦ by
    by_cases ht : ‖t‖ ≤ 1
    · exact (hCφ t (mem_closedBall_zero_iff.mpr ht)).trans (le_max_left _ _)
    · have ht0 : t ≠ 0 := fun h ↦ ht (by simp [h])
      have hinv : ‖t⁻¹‖ ≤ 1 := by
        rw [norm_inv]
        exact inv_le_one_of_one_le₀ (not_le.mp ht).le
      rw [eq_neg_of_add_eq_zero_left (hrel t ht0), norm_neg]
      exact (hCψ _ (mem_closedBall_zero_iff.mpr hinv)).trans (le_max_right _ _)
  have hconst : ∀ t, φ t = φ 0 := fun t ↦
    hφ.apply_eq_apply_of_bounded (isBounded_iff_forall_norm_le.mpr
      ⟨max Cφ Cψ, by rintro _ ⟨s, rfl⟩; exact hbound s⟩) t 0
  -- `ψ = -φ(0)` off `0`, so `φ(0) = -ψ(0) = 0` by continuity
  have hψc : ∀ w : ℂ, w ≠ 0 → ψ w = -φ 0 := fun w hw ↦ by
    have := hrel w⁻¹ (inv_ne_zero hw)
    rw [inv_inv, hconst] at this
    linear_combination this
  have hψ0 : ψ 0 = 0 := hh0 _ (hUj z hz 0) (by simp)
  have hlim1 : Tendsto ψ (𝓝[≠] 0) (𝓝 (ψ 0)) :=
    hψ.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto ψ (𝓝[≠] 0) (𝓝 (-φ 0)) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun w hw ↦ (hψc w hw).symm)
  have hφ0 : φ 0 = 0 := by
    have := tendsto_nhds_unique hlim1 hlim2
    rw [hψ0] at this
    exact neg_eq_zero.mp this.symm
  refine ⟨?_, ?_⟩
  · have h1 := hconst (z j)
    rw [hφ0] at h1
    simpa [hφdef, Function.update_eq_self] using h1
  · by_cases hzj : z j = 0
    · exact hh0 z hz hzj
    · have h1 := hψc (z j) hzj
      rw [hφ0, neg_zero] at h1
      simpa [hψdef, Function.update_eq_self] using h1

/-! ### Consequences for the projectors -/

section Projector

variable {j : σ} {U : Set (σ → ℂ)} {f : (σ → ℂ) → ℂ}

/-- **Characterization of the Laurent projectors**: if `f = g + h(·₍ⱼ←·ⱼ⁻¹₎)` on `U ∩ {zⱼ ≠ 0}`
with `g`, `h` analytic on `U` and `h = 0` on `U ∩ {zⱼ = 0}`, then `g = Pⱼf` and
`h = laurentProjInv j f` on `U`. Here `U` is open and stable under changing `zⱼ`, and `f` is
analytic on `U ∩ {zⱼ ≠ 0}`. -/
theorem laurentProj_eq_of_splitting (hU : IsOpen U)
    (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U) (hf : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ f z)
    {g h : (σ → ℂ) → ℂ} (hg : ∀ z ∈ U, AnalyticAt ℂ g z) (hh : ∀ z ∈ U, AnalyticAt ℂ h z)
    (hh0 : ∀ z ∈ U, z j = 0 → h z = 0)
    (hfgh : ∀ z ∈ U, z j ≠ 0 → f z = g z + h (Function.update z j (z j)⁻¹)) {z : σ → ℂ}
    (hz : z ∈ U) : laurentProj j f z = g z ∧ laurentProjInv j f z = h z := by
  have := laurent_splitting_unique (g := fun z ↦ laurentProj j f z - g z)
    (h := fun z ↦ laurentProjInv j f z - h z) hUj
    (fun z hz ↦ (analyticAt_laurentProj hU hUj hf hz).sub (hg z hz))
    (fun z hz ↦ (analyticAt_laurentProjInv hU hUj hf hz).sub (hh z hz))
    (fun z hz hzj ↦ by simp [laurentProjInv_of_eq_zero hzj, hh0 z hz hzj])
    (fun z hz hzj ↦ by
      have h1 := eq_laurentProj_add_laurentProjInv hUj hf hz hzj
      have h2 := hfgh z hz hzj
      linear_combination h2 - h1) hz
  exact ⟨sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩

/-- **`Pⱼ` fixes functions analytic across `zⱼ = 0`**: if `f` is analytic on all of `U` (open,
stable under changing `zⱼ`), then `Pⱼf = f` and `laurentProjInv j f = 0` on `U`. -/
theorem laurentProj_eq_self (hU : IsOpen U) (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U)
    (hf : ∀ z ∈ U, AnalyticAt ℂ f z) {z : σ → ℂ} (hz : z ∈ U) :
    laurentProj j f z = f z ∧ laurentProjInv j f z = 0 :=
  laurentProj_eq_of_splitting (h := fun _ ↦ 0) hU hUj (fun z hz _ ↦ hf z hz) hf
    (fun _ _ ↦ analyticAt_const) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ (add_zero _).symm) hz

/-- **`Pⱼ` is idempotent**: `Pⱼ(Pⱼf) = Pⱼf` on `U` (open, stable under changing `zⱼ`), for `f`
analytic on `U ∩ {zⱼ ≠ 0}`. -/
theorem laurentProj_laurentProj (hU : IsOpen U) (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U)
    (hf : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ f z) {z : σ → ℂ} (hz : z ∈ U) :
    laurentProj j (laurentProj j f) z = laurentProj j f z :=
  (laurentProj_eq_self hU hUj (fun _ hy ↦ analyticAt_laurentProj hU hUj hf hy) hz).1

/-- `Pⱼ` kills the negative part: `Pⱼ(f - Pⱼf) = 0` on `U`. -/
theorem laurentProj_sub_laurentProj (hU : IsOpen U)
    (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U) (hf : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ f z)
    {z : σ → ℂ} (hz : z ∈ U) : laurentProj j (fun y ↦ f y - laurentProj j f y) z = 0 :=
  (laurentProj_eq_of_splitting (g := fun _ ↦ 0) (h := laurentProjInv j f) hU hUj
    (fun y hy hyj ↦ (hf y hy hyj).sub (analyticAt_laurentProj hU hUj hf hy))
    (fun _ _ ↦ analyticAt_const) (fun _ hy ↦ analyticAt_laurentProjInv hU hUj hf hy)
    (fun _ _ hyj ↦ laurentProjInv_of_eq_zero hyj)
    (fun y hy hyj ↦ by
      simp only [Pi.sub_apply]
      rw [eq_laurentProj_add_laurentProjInv hUj hf hy hyj]
      ring) hz).1

/-- **`Pⱼ` is additive** on functions analytic on `U ∩ {zⱼ ≠ 0}`. -/
theorem laurentProj_add (hU : IsOpen U) (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U)
    {f g : (σ → ℂ) → ℂ} (hf : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ f z)
    (hg : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ g z) {z : σ → ℂ} (hz : z ∈ U) :
    laurentProj j (fun y ↦ f y + g y) z = laurentProj j f z + laurentProj j g z :=
  (laurentProj_eq_of_splitting (g := fun y ↦ laurentProj j f y + laurentProj j g y)
    (h := fun y ↦ laurentProjInv j f y + laurentProjInv j g y) hU hUj
    (fun y hy hyj ↦ (hf y hy hyj).add (hg y hy hyj))
    (fun _ hy ↦ (analyticAt_laurentProj hU hUj hf hy).add (analyticAt_laurentProj hU hUj hg hy))
    (fun _ hy ↦ (analyticAt_laurentProjInv hU hUj hf hy).add
      (analyticAt_laurentProjInv hU hUj hg hy))
    (fun _ _ hyj ↦ by simp [laurentProjInv_of_eq_zero hyj])
    (fun y hy hyj ↦ by
      simp only [Pi.add_apply]
      rw [eq_laurentProj_add_laurentProjInv hUj hf hy hyj,
        eq_laurentProj_add_laurentProjInv hUj hg hy hyj]
      ring) hz).1

/-- **`Pⱼ` is `ℂ`-linear**: `Pⱼ(af) = a Pⱼf`. -/
theorem laurentProj_const_mul (hU : IsOpen U) (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U)
    (hf : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ f z) (a : ℂ) {z : σ → ℂ} (hz : z ∈ U) :
    laurentProj j (fun y ↦ a * f y) z = a * laurentProj j f z :=
  (laurentProj_eq_of_splitting (g := fun y ↦ a * laurentProj j f y)
    (h := fun y ↦ a * laurentProjInv j f y) hU hUj
    (fun y hy hyj ↦ analyticAt_const.mul (hf y hy hyj))
    (fun _ hy ↦ analyticAt_const.mul (analyticAt_laurentProj hU hUj hf hy))
    (fun _ hy ↦ analyticAt_const.mul (analyticAt_laurentProjInv hU hUj hf hy))
    (fun _ _ hyj ↦ by simp [laurentProjInv_of_eq_zero hyj])
    (fun y hy hyj ↦ by
      simp only [Pi.mul_apply]
      rw [eq_laurentProj_add_laurentProjInv hUj hf hy hyj]
      ring) hz).1

end Projector

/-! ### Commutation -/

section Comm

variable {U : Set (σ → ℂ)}

omit [Fintype σ] in
private lemma update_inv_update_comm {i j : σ} (hij : i ≠ j) (z : σ → ℂ) (ζ : ℂ) :
    Function.update (Function.update z i ζ) j ((Function.update z i ζ) j)⁻¹ =
      Function.update (Function.update z j (z j)⁻¹) i ζ := by
  rw [Function.update_of_ne hij.symm, Function.update_comm hij]

omit [Fintype σ] in
/-- `Pᵢ` of a function of `z₍ⱼ←zⱼ⁻¹₎` (`i ≠ j`) is computed at `z₍ⱼ←zⱼ⁻¹₎`. -/
private lemma laurentProj_comp_update_inv {i j : σ} (hij : i ≠ j) (h : (σ → ℂ) → ℂ)
    (z : σ → ℂ) :
    laurentProj i (fun y ↦ h (Function.update y j (y j)⁻¹)) z =
      laurentProj i h (Function.update z j (z j)⁻¹) := by
  simp only [laurentProj, laurentPlus, Function.update_of_ne hij]
  congr 2
  funext ζ
  rw [update_inv_update_comm hij]

omit [Fintype σ] in
/-- `Pᵢh` vanishes on `{zⱼ = 0}` if `h` does (`i ≠ j`). -/
private lemma laurentProj_eq_zero_of_eq_zero {i j : σ} (hij : i ≠ j) {h : (σ → ℂ) → ℂ}
    (hh0 : ∀ z, z j = 0 → h z = 0) {z : σ → ℂ} (hz : z j = 0) : laurentProj i h z = 0 := by
  have : ∀ ζ : ℂ, (ζ - z i)⁻¹ * h (Function.update z i ζ) = 0 := fun ζ ↦ by
    rw [hh0 _ (by rwa [Function.update_of_ne hij.symm]), mul_zero]
  simp only [laurentProj, laurentPlus, this]
  simp [circleIntegral]

/-- **The Laurent projectors commute**: for `i ≠ j`, `U` open and stable under changing `zᵢ` and
`zⱼ`, and `f` analytic at every point of `U` with `zᵢ ≠ 0` and `zⱼ ≠ 0`,
`Pᵢ(Pⱼf) = Pⱼ(Pᵢf)` on `U`. -/
theorem laurentProj_comm {i j : σ} (hij : i ≠ j) (hU : IsOpen U)
    (hUi : ∀ z ∈ U, ∀ t, Function.update z i t ∈ U)
    (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U) {f : (σ → ℂ) → ℂ}
    (hf : ∀ z ∈ U, z i ≠ 0 → z j ≠ 0 → AnalyticAt ℂ f z) {z : σ → ℂ} (hz : z ∈ U) :
    laurentProj i (laurentProj j f) z = laurentProj j (laurentProj i f) z := by
  -- the opens `U ∩ {zᵢ ≠ 0}` (stable in `j`) and `U ∩ {zⱼ ≠ 0}` (stable in `i`)
  set Ui : Set (σ → ℂ) := U ∩ {y | y i ≠ 0}
  set Uj : Set (σ → ℂ) := U ∩ {y | y j ≠ 0}
  have hUio : IsOpen Ui := hU.inter (isOpen_ne_fun (continuous_apply i) continuous_const)
  have hUjo : IsOpen Uj := hU.inter (isOpen_ne_fun (continuous_apply j) continuous_const)
  have hUij : ∀ y ∈ Ui, ∀ t, Function.update y j t ∈ Ui := fun y hy t ↦
    ⟨hUj y hy.1 t, by simpa [Function.update_of_ne hij] using hy.2⟩
  have hUji : ∀ y ∈ Uj, ∀ t, Function.update y i t ∈ Uj := fun y hy t ↦
    ⟨hUi y hy.1 t, by simpa [Function.update_of_ne hij.symm] using hy.2⟩
  have hfi : ∀ y ∈ Ui, y j ≠ 0 → AnalyticAt ℂ f y := fun y hy hyj ↦ hf y hy.1 hy.2 hyj
  have hfj : ∀ y ∈ Uj, y i ≠ 0 → AnalyticAt ℂ f y := fun y hy hyi ↦ hf y hy.1 hyi hy.2
  -- the splitting in `zⱼ` on `U ∩ {zᵢ ≠ 0}`
  set g := laurentProj j f
  set h := laurentProjInv j f
  have hg : ∀ y ∈ Ui, AnalyticAt ℂ g y := fun y hy ↦ analyticAt_laurentProj hUio hUij hfi hy
  have hh : ∀ y ∈ Ui, AnalyticAt ℂ h y := fun y hy ↦ analyticAt_laurentProjInv hUio hUij hfi hy
  have hg' : ∀ y ∈ U, y i ≠ 0 → AnalyticAt ℂ g y := fun y hy hyi ↦ hg y ⟨hy, hyi⟩
  have hh' : ∀ y ∈ U, y i ≠ 0 → AnalyticAt ℂ h y := fun y hy hyi ↦ hh y ⟨hy, hyi⟩
  -- `Pᵢf = Pᵢg + (Pᵢh)(·₍ⱼ←·ⱼ⁻¹₎)` on `U ∩ {zⱼ ≠ 0}`
  have hsplit : ∀ y ∈ U, y j ≠ 0 →
      laurentProj i f y = laurentProj i g y + laurentProj i h (Function.update y j (y j)⁻¹) := by
    intro y hy hyj
    rw [← laurentProj_comp_update_inv hij]
    set R : ℝ := ‖y i‖ + 1
    have hR : 0 < R := by positivity
    have hsph : ∀ ζ ∈ sphere (0 : ℂ) R, ζ ≠ 0 ∧ ζ - y i ≠ 0 := fun ζ hζ ↦ by
      rw [mem_sphere_zero_iff_norm] at hζ
      refine ⟨fun h0 ↦ by rw [h0, norm_zero] at hζ; linarith, fun h0 ↦ ?_⟩
      rw [sub_eq_zero.mp h0] at hζ
      linarith
    have hmem : ∀ ζ ∈ sphere (0 : ℂ) R, Function.update y i ζ ∈ Ui := fun ζ hζ ↦
      ⟨hUi y hy ζ, by simpa using (hsph ζ hζ).1⟩
    have hyU' : ∀ ζ ∈ sphere (0 : ℂ) R,
        Function.update (Function.update y i ζ) j ((Function.update y i ζ) j)⁻¹ ∈ Ui :=
      fun ζ hζ ↦ hUij _ (hmem ζ hζ) _
    have hcg : ContinuousOn (fun ζ ↦ (ζ - y i)⁻¹ * g (Function.update y i ζ)) (sphere 0 R) :=
      fun ζ hζ ↦ ((continuousAt_id.sub continuousAt_const).inv₀ (hsph ζ hζ).2 |>.mul
        ((hg _ (hmem ζ hζ)).continuousAt.comp
          (continuous_const.update i continuous_id).continuousAt)).continuousWithinAt
    have hch : ContinuousOn (fun ζ ↦ (ζ - y i)⁻¹ * h (Function.update
        (Function.update y i ζ) j ((Function.update y i ζ) j)⁻¹)) (sphere 0 R) := by
      intro ζ hζ
      have hcont : Continuous fun ζ : ℂ ↦
          Function.update (Function.update y i ζ) j ((Function.update y i ζ) j)⁻¹ := by
        simp_rw [update_inv_update_comm hij]
        exact continuous_const.update i continuous_id
      exact ((continuousAt_id.sub continuousAt_const).inv₀ (hsph ζ hζ).2 |>.mul
        (ContinuousAt.comp (g := h) (f := fun ζ : ℂ ↦ Function.update (Function.update y i ζ) j
          ((Function.update y i ζ) j)⁻¹) (hh _ (hyU' ζ hζ)).continuousAt
          hcont.continuousAt)).continuousWithinAt
    have e1 : laurentProj i f y = (2 * π * I)⁻¹ *
        ∮ ζ in C(0, R), (ζ - y i)⁻¹ * f (Function.update y i ζ) := rfl
    have e2 : laurentProj i g y = (2 * π * I)⁻¹ *
        ∮ ζ in C(0, R), (ζ - y i)⁻¹ * g (Function.update y i ζ) := rfl
    have e3 : laurentProj i (fun y ↦ h (Function.update y j (y j)⁻¹)) y = (2 * π * I)⁻¹ *
        ∮ ζ in C(0, R), (ζ - y i)⁻¹ *
          h (Function.update (Function.update y i ζ) j ((Function.update y i ζ) j)⁻¹) := rfl
    rw [e1, e2, e3, ← mul_add,
      ← circleIntegral.integral_add (hcg.circleIntegrable hR.le) (hch.circleIntegrable hR.le)]
    congr 1
    refine circleIntegral.integral_congr hR.le fun ζ hζ ↦ ?_
    simp only [← mul_add]
    congr 1
    have hyj' : (Function.update y i ζ) j ≠ 0 := by rwa [Function.update_of_ne hij.symm]
    exact eq_laurentProj_add_laurentProjInv hUij hfi (hmem ζ hζ) hyj'
  -- uniqueness of the splitting of `Pᵢf` in `zⱼ`
  have hPif : ∀ y ∈ U, y j ≠ 0 → AnalyticAt ℂ (laurentProj i f) y := fun y hy hyj ↦
    analyticAt_laurentProj hUjo hUji hfj ⟨hy, hyj⟩
  exact (laurentProj_eq_of_splitting hU hUj hPif
    (fun y hy ↦ analyticAt_laurentProj hU hUi hg' hy)
    (fun y hy ↦ analyticAt_laurentProj hU hUi hh' hy)
    (fun y _ hyj ↦ laurentProj_eq_zero_of_eq_zero hij (fun _ h0 ↦ laurentProjInv_of_eq_zero h0)
      hyj) hsplit hz).1.symm

end Comm

/-! ### Homogeneity -/

/-- **The Laurent projector preserves homogeneity**: let `U` be open, stable under changing `zⱼ`
and under `z ↦ cz` (`c ≠ 0`), and let `f` be analytic on `U ∩ {zⱼ ≠ 0}` with
`f(cz) = cᵈ f(z)` there (`d ∈ ℤ`). Then `Pⱼf(cz) = cᵈ Pⱼf(z)` on `U`. -/
theorem laurentProj_smul {j : σ} {U : Set (σ → ℂ)} (hU : IsOpen U)
    (hUj : ∀ z ∈ U, ∀ t, Function.update z j t ∈ U) {f : (σ → ℂ) → ℂ}
    (hf : ∀ z ∈ U, z j ≠ 0 → AnalyticAt ℂ f z) {c : ℂ} (hc : c ≠ 0)
    (hUc : ∀ z ∈ U, c • z ∈ U) {d : ℤ} (hfd : ∀ z ∈ U, z j ≠ 0 → f (c • z) = c ^ d * f z)
    {z : σ → ℂ} (hz : z ∈ U) : laurentProj j f (c • z) = c ^ d * laurentProj j f z := by
  have hcd : c ^ d ≠ 0 := zpow_ne_zero d hc
  -- the rescaled splitting
  set T : (σ → ℂ) → σ → ℂ := fun w ↦ Function.update (c • w) j (w j / c)
  have hT : ∀ w, AnalyticAt ℂ T w := fun w ↦ by
    have h0 : AnalyticAt ℂ (fun w : σ → ℂ ↦ c • w) w :=
      (analyticAt_id (𝕜 := ℂ) (z := w)).const_smul (c := c)
    have h1 : AnalyticAt ℂ (fun w : σ → ℂ ↦ (c • w, w j / c)) w :=
      h0.prod (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ↦ ℂ) j).analyticAt w).div_const
        (c := c))
    exact AnalyticAt.comp (g := fun p : (σ → ℂ) × ℂ ↦ Function.update p.1 j p.2)
      (f := fun w : σ → ℂ ↦ (c • w, w j / c)) (analyticAt_update_prod j _) h1
  have hTU : ∀ w ∈ U, T w ∈ U := fun w hw ↦ hUj _ (hUc w hw) _
  have hTinv : ∀ y : σ → ℂ, T (Function.update y j (y j)⁻¹) =
      Function.update (c • y) j ((c • y) j)⁻¹ := fun y ↦ by
    simp only [T, Function.update_self, Pi.smul_apply, smul_eq_mul]
    rw [show c • Function.update y j (y j)⁻¹ = Function.update (c • y) j (c * (y j)⁻¹) by
      rw [← smul_eq_mul, ← Function.update_smul]]
    rw [Function.update_idem]
    congr 1
    rw [mul_inv]
    ring
  have hscale : ∀ y ∈ U, AnalyticAt ℂ (fun y : σ → ℂ ↦ c • y) y := fun y _ ↦
    (analyticAt_id (𝕜 := ℂ) (z := y)).const_smul (c := c)
  have key := laurentProj_eq_of_splitting (j := j) (f := f)
    (g := fun y ↦ (c ^ d)⁻¹ * laurentProj j f (c • y))
    (h := fun w ↦ (c ^ d)⁻¹ * laurentProjInv j f (T w)) hU hUj hf
    (fun y hy ↦ analyticAt_const.mul
      ((analyticAt_laurentProj hU hUj hf (hUc y hy)).comp (hscale y hy)))
    (fun w hw ↦ analyticAt_const.mul
      ((analyticAt_laurentProjInv hU hUj hf (hTU w hw)).comp (hT w)))
    (fun w _ hwj ↦ by
      have : (T w) j = 0 := by simp [T, hwj]
      simp [laurentProjInv_of_eq_zero this])
    (fun y hy hyj ↦ by
      have hcy : (c • y) j ≠ 0 := by simpa using mul_ne_zero hc hyj
      have h1 := eq_laurentProj_add_laurentProjInv hUj hf (hUc y hy) hcy
      have h2 := hfd y hy hyj
      rw [hTinv y]
      rw [h1] at h2
      rw [← mul_add, h2, ← mul_assoc, inv_mul_cancel₀ hcd, one_mul]) hz
  rw [key.1, ← mul_assoc, mul_inv_cancel₀ hcd, one_mul]

end AnalyticGeometry
