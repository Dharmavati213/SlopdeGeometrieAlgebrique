/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Osgood

/-!
# Weierstrass's theorem in several variables

A locally uniform limit of analytic functions on an open set `U ⊆ ℂ^σ` (`σ` finite) is analytic
on `U` (`AnalyticGeometry.analyticAt_of_tendstoLocallyUniformlyOn`). The limit is continuous,
and holomorphic in each variable separately by the one-variable theorem
(`TendstoLocallyUniformlyOn.differentiableOn`, applied on the coordinate lines); Osgood's lemma
(`AnalyticGeometry.analyticAt_of_continuousOn_of_separately`) concludes. The same holds for
uniform limits on compact subsets (`AnalyticGeometry.analyticAt_of_tendstoUniformlyOn_isCompact`)
and for series converging locally uniformly.

Reference: Hörmander, *An introduction to complex analysis in several variables*, Corollary
2.2.4; Gunning–Rossi, *Analytic functions of several complex variables*, I.A.
-/

noncomputable section

open Set Filter Topology

namespace AnalyticGeometry

variable {σ : Type} [Fintype σ] {ι : Type*} {l : Filter ι} [l.NeBot]
  {F : ι → (σ → ℂ) → ℂ} {f : (σ → ℂ) → ℂ} {U : Set (σ → ℂ)}

/-- **Weierstrass's theorem in several variables**: if analytic functions `Fₙ` on the open set
`U ⊆ ℂ^σ` converge locally uniformly on `U` to `f`, then `f` is analytic on `U`. -/
theorem analyticAt_of_tendstoLocallyUniformlyOn (hU : IsOpen U)
    (hF : ∀ᶠ n in l, ∀ z ∈ U, AnalyticAt ℂ (F n) z) (hlim : TendstoLocallyUniformlyOn F f l U)
    {z : σ → ℂ} (hz : z ∈ U) : AnalyticAt ℂ f z := by
  classical
  have hcont : ContinuousOn f U := hlim.continuousOn
    (hF.frequently.mono fun n hn y hy ↦ (hn y hy).continuousAt.continuousWithinAt)
  refine analyticAt_of_continuousOn_of_separately hU hcont (fun y hy j ↦ ?_) hz
  -- the coordinate line through `y` in the direction `j`
  set L : Set ℂ := {t | Function.update y j t ∈ U}
  have hcL : Continuous fun t : ℂ ↦ Function.update y j t :=
    continuous_const.update j continuous_id
  have hL : IsOpen L := hU.preimage hcL
  have hyL : y j ∈ L := by simp [L, hy]
  have hlimL : TendstoLocallyUniformlyOn (fun n ↦ F n ∘ fun t ↦ Function.update y j t)
      (f ∘ fun t ↦ Function.update y j t) l L :=
    hlim.comp _ (fun t ht ↦ ht) hcL.continuousOn
  have hFL : ∀ᶠ n in l, DifferentiableOn ℂ (F n ∘ fun t ↦ Function.update y j t) L :=
    hF.mono fun n hn t ht ↦
      ((hn _ ht).differentiableAt.comp t (hasFDerivAt_update y t).differentiableAt
        ).differentiableWithinAt
  exact (hlimL.differentiableOn hFL hL).differentiableAt (hL.mem_nhds hyL)

/-- **Weierstrass's theorem, compact form**: if analytic functions `Fₙ` on the open set `U`
converge to `f` uniformly on every compact subset of `U`, then `f` is analytic on `U`. -/
theorem analyticAt_of_tendstoUniformlyOn_isCompact (hU : IsOpen U)
    (hF : ∀ᶠ n in l, ∀ z ∈ U, AnalyticAt ℂ (F n) z)
    (hlim : ∀ K ⊆ U, IsCompact K → TendstoUniformlyOn F f l K) {z : σ → ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ f z :=
  analyticAt_of_tendstoLocallyUniformlyOn hU hF
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr hlim) hz

/-- **Locally uniformly convergent series of analytic functions are analytic**: if
`∑ₙ uₙ` converges locally uniformly on the open set `U ⊆ ℂ^σ` (as finite partial sums) to `f`
and every `uₙ` is analytic on `U`, then `f` is analytic on `U`. -/
theorem analyticAt_of_tendstoLocallyUniformlyOn_sum {u : ℕ → (σ → ℂ) → ℂ} (hU : IsOpen U)
    (hu : ∀ n, ∀ z ∈ U, AnalyticAt ℂ (u n) z)
    (hlim : TendstoLocallyUniformlyOn (fun N z ↦ ∑ n ∈ Finset.range N, u n z) f atTop U)
    {z : σ → ℂ} (hz : z ∈ U) : AnalyticAt ℂ f z :=
  analyticAt_of_tendstoLocallyUniformlyOn hU
    (Eventually.of_forall fun _ y hy ↦ Finset.analyticAt_fun_sum _ fun n _ ↦ hu n y hy) hlim hz

end AnalyticGeometry
