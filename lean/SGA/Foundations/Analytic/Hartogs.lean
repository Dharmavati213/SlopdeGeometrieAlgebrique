/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.RungeLaurentProjector
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous holomorphic functions and Hartogs extension across the origin

Let `σ` be a finite type.

* **Homogeneous entire functions are polynomials**: if `f : ℂ^σ → ℂ` is analytic everywhere and
  `f(cz) = cⁿ f(z)` for all `c ≠ 0` (`n : ℕ`), then `f` is a homogeneous polynomial of degree `n`
  (`AnalyticGeometry.exists_isHomogeneous_eq_of_homogeneous`):
  `f(z) = (1/n!) Dⁿf(0)(z, …, z)`, expanded in the coordinates. If `f` is continuous at `0` and
  homogeneous of negative degree `d < 0`, then `f = 0`
  (`AnalyticGeometry.eq_zero_of_homogeneous_neg`).
* **Hartogs extension across the origin** (`AnalyticGeometry.exists_analyticAt_extension`): if
  `σ` has two distinct elements, every function analytic on `ℂ^σ ∖ {0}` agrees there with an
  entire function, namely its nonnegative Laurent part in one coordinate
  (`AnalyticGeometry.laurentProj`).
* Consequently a function analytic on `ℂ^σ ∖ {0}` (`#σ ≥ 2`) and homogeneous of degree `n ≥ 0`
  is a homogeneous polynomial of degree `n` there
  (`AnalyticGeometry.exists_isHomogeneous_eq_of_compl_zero`), and of negative degree it is `0`
  (`AnalyticGeometry.eq_zero_of_compl_zero_of_neg`). This is the `H⁰` case of the comparison of
  the cohomology of `𝒪(d)` on `ℙⁿ` with that of `𝒪(d)^an` (`n ≥ 1`).

Reference: Hörmander, *An introduction to complex analysis in several variables*, Theorem 2.3.2
(Hartogs); Serre, *Géométrie algébrique et géométrie analytique*, §3, no. 13; Gunning–Rossi,
*Analytic functions of several complex variables*, I.C.
-/

noncomputable section

open Complex Set Metric Filter Topology
open scoped ContDiff

namespace AnalyticGeometry

variable {σ : Type} [Fintype σ]

/-! ### Homogeneous functions -/

omit [Fintype σ] in
/-- **Homogeneous functions of negative degree vanish**: if `f` is continuous at `0` and
`f(cz) = cᵈ f(z)` for all `c ≠ 0` and all `z`, with `d < 0`, then `f = 0`. -/
theorem eq_zero_of_homogeneous_neg {f : (σ → ℂ) → ℂ} (hf : ContinuousAt f 0) {d : ℤ}
    (hd : d < 0) (hfd : ∀ c : ℂ, c ≠ 0 → ∀ z, f (c • z) = c ^ d * f z) (z : σ → ℂ) :
    f z = 0 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, -d = (m + 1 : ℕ) := ⟨(-d - 1).toNat, by omega⟩
  -- `f(z) = c^{m+1} f(cz)` for `c ≠ 0`
  have hrel : ∀ c : ℂ, c ≠ 0 → f z = c ^ (m + 1) * f (c • z) := fun c hc ↦ by
    rw [hfd c hc z, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ hc]
    have : ((m + 1 : ℕ) : ℤ) + d = 0 := by omega
    rw [this, zpow_zero, one_mul]
  -- let `c → 0`
  have hlim : Tendsto (fun c : ℂ ↦ c ^ (m + 1) * f (c • z)) (𝓝[≠] 0) (𝓝 (0 ^ (m + 1) * f 0)) := by
    have h1 : Tendsto (fun c : ℂ ↦ c • z) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℂ))).smul_const z
    exact ((continuous_pow _).tendsto 0).mul (hf.tendsto.comp h1) |>.mono_left nhdsWithin_le_nhds
  have hconst : Tendsto (fun c : ℂ ↦ c ^ (m + 1) * f (c • z)) (𝓝[≠] 0) (𝓝 (f z)) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun c hc ↦ hrel c hc)
  have := tendsto_nhds_unique hconst hlim
  rw [this]
  simp

/-- **Taylor's formula for homogeneous entire functions**: if `f` is analytic everywhere and
`f(cz) = cⁿ f(z)` for `c ≠ 0`, then `f(z) = (1/n!) Dⁿf(0)(z, …, z)`. -/
theorem eq_iteratedFDeriv_of_homogeneous {f : (σ → ℂ) → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    {n : ℕ} (hfd : ∀ c : ℂ, c ≠ 0 → ∀ z, f (c • z) = c ^ n * f z) (z : σ → ℂ) :
    f z = (n.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ n f 0 fun _ ↦ z := by
  have hcd : ContDiff ℂ ∞ f := AnalyticOnNhd.contDiff fun z _ ↦ hf z
  set L : ℂ →L[ℂ] (σ → ℂ) := ContinuousLinearMap.toSpanSingleton ℂ z
  have hL : ∀ t, L t = t • z := fun t ↦ rfl
  -- `t ↦ f(tz)` is `t ↦ tⁿ f(z)`
  have hφ : f ∘ L = fun t ↦ t ^ n * f z := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ))
      (hcd.continuous.comp L.continuous) (by fun_prop) fun t ht ↦ ?_
    simp only [Function.comp_apply, hL]
    exact hfd t ht z
  have hder : iteratedDeriv n (f ∘ L) 0 = iteratedFDeriv ℂ n f 0 fun _ ↦ z := by
    rw [iteratedDeriv_eq_iteratedFDeriv,
      L.iteratedFDeriv_comp_right hcd 0 (by exact_mod_cast le_top)]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, hL]
  have hpow : iteratedDeriv n (f ∘ L) 0 = n.factorial * f z := by
    rw [hφ, iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero]
    simp
  rw [← hder, hpow, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero),
    one_mul]

/-- The polynomial `∑_{r : Fin n → σ} A(e_{r₁}, …, e_{rₙ}) X_{r₁} ⋯ X_{rₙ}` of a multilinear map
`A` on `(ℂ^σ)ⁿ`, whose evaluation at `z` is `A(z, …, z)`. -/
def multilinearPoly [DecidableEq σ] {n : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ σ → ℂ) ℂ) : MvPolynomial σ ℂ :=
  ∑ r : Fin n → σ,
    MvPolynomial.C (A fun i ↦ Pi.single (r i) 1) * ∏ i, MvPolynomial.X (r i)

lemma isHomogeneous_multilinearPoly [DecidableEq σ] {n : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ σ → ℂ) ℂ) :
    (multilinearPoly A).IsHomogeneous n := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun r _ ↦ ?_
  have hprod := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i ↦ MvPolynomial.X (R := ℂ) (r i)) (fun _ ↦ 1)
    (fun i _ ↦ MvPolynomial.isHomogeneous_X ℂ (r i))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hprod
  exact hprod.C_mul _

lemma eval_multilinearPoly [DecidableEq σ] {n : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ σ → ℂ) ℂ) (z : σ → ℂ) :
    MvPolynomial.eval z (multilinearPoly A) = A fun _ ↦ z := by
  have hz : z = ∑ j, z j • (Pi.single j 1 : σ → ℂ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hz]
  rw [A.map_sum]
  simp only [A.map_smul_univ, smul_eq_mul, multilinearPoly, map_sum, map_mul,
    MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  ring

/-- **Homogeneous entire functions are homogeneous polynomials**: if `f` is analytic at every
point of `ℂ^σ` and `f(cz) = cⁿ f(z)` for all `c ≠ 0` and all `z`, then `f` is (the evaluation
of) a homogeneous polynomial of degree `n`. -/
theorem exists_isHomogeneous_eq_of_homogeneous {f : (σ → ℂ) → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    {n : ℕ} (hfd : ∀ c : ℂ, c ≠ 0 → ∀ z, f (c • z) = c ^ n * f z) :
    ∃ P : MvPolynomial σ ℂ, P.IsHomogeneous n ∧ ∀ z, f z = MvPolynomial.eval z P := by
  classical
  refine ⟨MvPolynomial.C (n.factorial : ℂ)⁻¹ * multilinearPoly (iteratedFDeriv ℂ n f 0),
    (isHomogeneous_multilinearPoly _).C_mul _, fun z ↦ ?_⟩
  rw [map_mul, MvPolynomial.eval_C, eval_multilinearPoly,
    eq_iteratedFDeriv_of_homogeneous hf hfd]

/-! ### Hartogs extension across the origin -/

/-- **Hartogs extension across the origin**: if `σ` has two distinct elements and `f` is
analytic at every point of `ℂ^σ ∖ {0}`, then some entire function agrees with `f` on
`ℂ^σ ∖ {0}`. -/
theorem exists_analyticAt_extension (hσ : ∃ i j : σ, i ≠ j) {f : (σ → ℂ) → ℂ}
    (hf : ∀ z, z ≠ 0 → AnalyticAt ℂ f z) :
    ∃ F : (σ → ℂ) → ℂ, (∀ z, AnalyticAt ℂ F z) ∧ ∀ z, z ≠ 0 → F z = f z := by
  classical
  obtain ⟨i, j, hij⟩ := hσ
  have hstab : ∀ z ∈ (univ : Set (σ → ℂ)), ∀ t, Function.update z j t ∈ univ :=
    fun _ _ _ ↦ mem_univ _
  have hfj : ∀ z ∈ (univ : Set (σ → ℂ)), z j ≠ 0 → AnalyticAt ℂ f z := fun z _ hzj ↦
    hf z fun h ↦ hzj (by simp [h])
  refine ⟨laurentProj j f, fun z ↦ analyticAt_laurentProj isOpen_univ hstab hfj (mem_univ z),
    fun z hz ↦ ?_⟩
  -- the open set where some coordinate other than `zⱼ` is nonzero
  set U' : Set (σ → ℂ) := {y | Function.update y j 0 ≠ 0}
  have hU'o : IsOpen U' :=
    isOpen_ne_fun (continuous_id.update j continuous_const) continuous_const
  have hU'j : ∀ y ∈ U', ∀ t, Function.update y j t ∈ U' := fun y hy t ↦ by
    simpa [U', Function.update_idem] using hy
  have hfU' : ∀ y ∈ U', AnalyticAt ℂ f y := fun y hy ↦ hf y fun h ↦ hy (by simp [h])
  have heq : ∀ y ∈ U', laurentProj j f y = f y := fun y hy ↦
    (laurentProj_eq_self hU'o hU'j hfU' hy).1
  by_cases hzU : z ∈ U'
  · exact heq z hzU
  -- otherwise approximate `z` by points of `U'` moving the coordinate `zᵢ`
  have hFc : ContinuousAt (laurentProj j f) z :=
    (analyticAt_laurentProj isOpen_univ hstab hfj (mem_univ z)).continuousAt
  have hfc : ContinuousAt f z := (hf z hz).continuousAt
  have hzi : z i = 0 := by
    have := congrFun (not_not.mp hzU) i
    simpa [Function.update_of_ne hij] using this
  have hpath : Tendsto (fun ε : ℂ ↦ Function.update z i ε) (𝓝[≠] 0) (𝓝 z) := by
    have hc : Continuous fun ε : ℂ ↦ Function.update z i ε :=
      continuous_const.update i continuous_id
    have : Tendsto (fun ε : ℂ ↦ Function.update z i ε) (𝓝 (z i)) (𝓝 z) := by
      simpa using hc.tendsto (z i)
    rw [hzi] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : (fun ε : ℂ ↦ laurentProj j f (Function.update z i ε)) =ᶠ[𝓝[≠] 0]
      fun ε ↦ f (Function.update z i ε) := by
    refine eventually_nhdsWithin_of_forall fun ε hε ↦ heq _ ?_
    intro h
    have := congrFun h i
    rw [Function.update_of_ne hij, Function.update_self, Pi.zero_apply] at this
    exact hε this
  exact tendsto_nhds_unique ((hFc.tendsto.comp hpath).congr' hev) (hfc.tendsto.comp hpath)

/-- **Homogeneous holomorphic functions on `ℂ^σ ∖ {0}` are polynomials** (`#σ ≥ 2`): if `f` is
analytic on `ℂ^σ ∖ {0}` and `f(cz) = cⁿ f(z)` for `c ≠ 0`, `z ≠ 0`, then `f` agrees on
`ℂ^σ ∖ {0}` with a homogeneous polynomial of degree `n`. -/
theorem exists_isHomogeneous_eq_of_compl_zero (hσ : ∃ i j : σ, i ≠ j) {f : (σ → ℂ) → ℂ}
    (hf : ∀ z, z ≠ 0 → AnalyticAt ℂ f z) {n : ℕ}
    (hfd : ∀ c : ℂ, c ≠ 0 → ∀ z, z ≠ 0 → f (c • z) = c ^ n * f z) :
    ∃ P : MvPolynomial σ ℂ, P.IsHomogeneous n ∧ ∀ z, z ≠ 0 → f z = MvPolynomial.eval z P := by
  classical
  obtain ⟨F, hF, hFf⟩ := exists_analyticAt_extension hσ hf
  obtain ⟨i, -, -⟩ := hσ
  have hFd : ∀ c : ℂ, c ≠ 0 → ∀ z, F (c • z) = c ^ n * F z := by
    intro c hc z
    by_cases hz : z = 0
    · -- by continuity along `ε eᵢ → 0`
      subst hz
      have hpath : Tendsto (fun ε : ℂ ↦ ε • (Pi.single i 1 : σ → ℂ)) (𝓝[≠] 0) (𝓝 0) := by
        have hc : Continuous fun ε : ℂ ↦ ε • (Pi.single i 1 : σ → ℂ) :=
          continuous_id.smul continuous_const
        have := (hc.tendsto (0 : ℂ)).mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
        simpa using this
      have hne : ∀ ε : ℂ, ε ≠ 0 → ε • (Pi.single i 1 : σ → ℂ) ≠ 0 := fun ε hε h ↦ by
        have := congrFun h i
        simp [hε] at this
      have h1 : Tendsto (fun ε : ℂ ↦ F (c • ε • (Pi.single i 1 : σ → ℂ))) (𝓝[≠] 0)
          (𝓝 (F (c • 0))) := by
        have := ((hF (c • 0)).continuousAt.tendsto).comp
          (((continuous_const_smul c).tendsto 0).comp hpath)
        simpa [Function.comp_def] using this
      have h2 : Tendsto (fun ε : ℂ ↦ F (c • ε • (Pi.single i 1 : σ → ℂ))) (𝓝[≠] 0)
          (𝓝 (c ^ n * F 0)) := by
        refine (((hF 0).continuousAt.tendsto.comp hpath).const_mul (c ^ n)).congr' ?_
        refine eventually_nhdsWithin_of_forall fun ε hε ↦ ?_
        simp only [Function.comp_apply]
        rw [hFf _ (smul_ne_zero hc (hne ε hε)), hFf _ (hne ε hε), hfd c hc _ (hne ε hε)]
      exact tendsto_nhds_unique h1 h2
    · rw [hFf _ (smul_ne_zero hc hz), hFf z hz, hfd c hc z hz]
  obtain ⟨P, hP, hPF⟩ := exists_isHomogeneous_eq_of_homogeneous hF hFd
  exact ⟨P, hP, fun z hz ↦ by rw [← hFf z hz, hPF]⟩

/-- **Homogeneous holomorphic functions of negative degree on `ℂ^σ ∖ {0}` vanish**
(`#σ ≥ 2`). -/
theorem eq_zero_of_compl_zero_of_neg (hσ : ∃ i j : σ, i ≠ j) {f : (σ → ℂ) → ℂ}
    (hf : ∀ z, z ≠ 0 → AnalyticAt ℂ f z) {d : ℤ} (hd : d < 0)
    (hfd : ∀ c : ℂ, c ≠ 0 → ∀ z, z ≠ 0 → f (c • z) = c ^ d * f z) {z : σ → ℂ} (hz : z ≠ 0) :
    f z = 0 := by
  obtain ⟨F, hF, hFf⟩ := exists_analyticAt_extension hσ hf
  -- `F` is homogeneous off `0`; this suffices for the argument of `eq_zero_of_homogeneous_neg`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, -d = (m + 1 : ℕ) := ⟨(-d - 1).toNat, by omega⟩
  have hrel : ∀ c : ℂ, c ≠ 0 → F z = c ^ (m + 1) * F (c • z) := fun c hc ↦ by
    rw [hFf _ (smul_ne_zero hc hz), hFf z hz, hfd c hc z hz, ← mul_assoc, ← zpow_natCast,
      ← zpow_add₀ hc]
    have : ((m + 1 : ℕ) : ℤ) + d = 0 := by omega
    rw [this, zpow_zero, one_mul]
  have hlim : Tendsto (fun c : ℂ ↦ c ^ (m + 1) * F (c • z)) (𝓝[≠] 0)
      (𝓝 (0 ^ (m + 1) * F 0)) := by
    have h1 : Tendsto (fun c : ℂ ↦ c • z) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℂ))).smul_const z
    exact ((continuous_pow _).tendsto 0).mul ((hF 0).continuousAt.tendsto.comp h1)
      |>.mono_left nhdsWithin_le_nhds
  have hconst : Tendsto (fun c : ℂ ↦ c ^ (m + 1) * F (c • z)) (𝓝[≠] 0) (𝓝 (F z)) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun c hc ↦ hrel c hc)
  have := tendsto_nhds_unique hconst hlim
  rw [← hFf z hz, this]
  simp

end AnalyticGeometry
