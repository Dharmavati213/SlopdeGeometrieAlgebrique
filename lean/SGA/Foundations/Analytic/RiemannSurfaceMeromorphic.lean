/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.RiemannSurfaceRefinement
import Mathlib.Analysis.Meromorphic.Order

/-!
# Meromorphic functions with a single pole on a compact Riemann surface

**Theorem** (Forster, *Lectures on Riemann surfaces*, 14.9 and 14.13). Let `M` be a compact Riemann
surface and `y ∈ M`. Then there is a meromorphic function on `M` whose only pole is at `y`:
`f` is holomorphic on `M ∖ {y}` and, in the chart at `y`, meromorphic at `y` of negative order
(`AnalyticGeometry.exists_meromorphic_single_pole`).

Proof. Cover `M` by finitely many disc charts such that `y` lies in the first disc only, and not
in the closure of the others (`exists_discChart_cover`). The bounded holomorphic `1`-cocycles on
this cover modulo coboundaries form a finite-dimensional space (`DiscChart.cofg_range_cechδ`:
Forster's finiteness criterion `cofg_range_cechδ`, whose hypothesis is the `∂̄`-step
`DiscChart.exists_eq_cechRestrict_add_cechδ`). The principal parts `(z - z(y))^{-(k+1)}`,
`k ≤ N`, give cocycles; for `N` larger than that dimension a nontrivial linear combination is a
coboundary `δη`, and the combination of principal parts minus `η` glues to the required function.

This is the analytic heart of the Riemann existence theorem for curves
(`SGA.SGA1.ExposeXII.CompactRiemannSurfaceMeromorphicStatement`).
-/

noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff BoundedContinuousFunction

namespace AnalyticGeometry

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- A finite cover of a compact Riemann surface by disc charts, adapted to a point `y`: the
discs of relative radius `s` cover `M`, the chart indexed by `none` is centred at `y`, and `y`
does not lie in the closed disc of any other chart. -/
theorem exists_discChart_cover [T2Space M] [CompactSpace M] (y : M) {s : ℝ} (hs : 0 < s) :
    ∃ (ι : Type u) (_ : Fintype ι) (D : Option ι → DiscChart M), (D none).center = y ∧
      (∀ x, ∃ i, x ∈ (D i).disc s) ∧
      ∀ i : ι, y ∉ (D (some i)).chart.symm '' closedBall (D (some i)).c (D (some i)).radius := by
  classical
  obtain ⟨D₀, hD₀, -⟩ := DiscChart.exists_image_closedBall_subset y univ_mem
  set K : Set M := (D₀.disc s)ᶜ
  have hK : IsCompact K := (D₀.isOpen_disc s).isClosed_compl.isCompact
  have hyK : ∀ q ∈ K, q ≠ y := fun q hq h => hq (h ▸ hD₀ ▸ D₀.center_mem_disc hs)
  choose Dq hDq using fun q : K => DiscChart.exists_image_closedBall_subset (q : M)
    (isOpen_compl_singleton.mem_nhds (hyK q q.2))
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun q : K => (Dq q).disc s)
    (fun q => (Dq q).isOpen_disc s) (fun q hq => mem_iUnion.mpr ⟨⟨q, hq⟩, by
      simpa [(hDq ⟨q, hq⟩).1] using (Dq ⟨q, hq⟩).center_mem_disc hs⟩)
  refine ⟨t, inferInstance, fun o => o.elim D₀ fun q => Dq q, hD₀, fun x => ?_, fun i hy => ?_⟩
  · by_cases hx : x ∈ D₀.disc s
    · exact ⟨none, hx⟩
    · obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (ht hx)
      exact ⟨some ⟨q, hq⟩, hxq⟩
  · exact (hDq i).2 hy rfl

-- `[Fintype ι]` gives the normed structure on the cochain spaces used in the proof (see
-- `AnalyticGeometry.cofg_range_cechδ`).
set_option linter.unusedFintypeInType false in
/-- **Finiteness of `H¹(M, 𝒪)`** (Forster 14.9), in the form used here: for finitely many disc
charts on a compact Riemann surface whose discs of relative radius `s` cover `M`, the bounded
holomorphic `1`-cocycles on these discs modulo coboundaries form a finite-dimensional space. -/
theorem DiscChart.cofg_range_cechδ [IsManifold 𝓘(ℂ) ω M] [T2Space M] [CompactSpace M]
    {ι : Type*} [Fintype ι] (D : ι → DiscChart M) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hcov : ∀ x : M, ∃ i, x ∈ (D i).disc s) :
    (LinearMap.range (cechδ (fun i => (D i).disc s) :
      Cech0 (fun i => (D i).disc s) →ₗ[ℂ] cocycles (fun i => (D i).disc s))).CoFG := by
  set s' := (s + 1) / 2
  have hss' : s < s' := by simp only [s']; linarith
  have hs' : s' < 1 := by simp only [s']; linarith
  refine AnalyticGeometry.cofg_range_cechδ (U' := fun i => (D i).disc s')
    (fun i => (D i).isOpen_disc s) (fun i => (D i).isOpen_disc s')
    (fun i => (D i).isCompact_closure_disc hs1.le)
    (fun i => (D i).closure_disc_subset_disc hss' hs'.le) fun ζ => ?_
  exact DiscChart.exists_eq_cechRestrict_add_cechδ D hs hss' hs' hcov ζ

private lemma inv_pow_succ_eq {w : ℂ} (hw : w ≠ 0) {a b : ℕ} (hab : a ≤ b) :
    (w⁻¹) ^ (a + 1) = (w ^ (b + 1))⁻¹ * w ^ (b - a) := by
  rw [show b + 1 = (b - a) + (a + 1) by omega, pow_add w (b - a) (a + 1), mul_inv,
    mul_comm (w ^ (b - a))⁻¹,
    mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hw), mul_one, inv_pow]

/-- A finite sum of principal parts `∑ₖ gₖ (z - c)^{-(k+1)}`, not all zero, minus a function
analytic at `c`, is meromorphic at `c` of negative order. -/
theorem meromorphicAt_and_order_neg_of_principalParts {n : ℕ} (g : Fin n → ℂ)
    (hg : ∃ k, g k ≠ 0) {c : ℂ} {H f : ℂ → ℂ} (hH : AnalyticAt ℂ H c)
    (hf : ∀ᶠ z in 𝓝 c, f z = ∑ k, g k * ((z - c)⁻¹) ^ ((k : ℕ) + 1) - H z) :
    MeromorphicAt f c ∧ meromorphicOrderAt f c < 0 := by
  classical
  obtain ⟨k0, hk0⟩ := hg
  set S := Finset.univ.filter fun k : Fin n => g k ≠ 0
  have hSne : S.Nonempty := ⟨k0, by simp [S, hk0]⟩
  set K := S.max' hSne
  have hK : g K ≠ 0 := by simpa [S] using S.max'_mem hSne
  have hKmax : ∀ k, g k ≠ 0 → (k : ℕ) ≤ K := fun k hk => S.le_max' k (by simp [S, hk])
  let G : ℂ → ℂ := fun z =>
    ∑ k, g k * (z - c) ^ ((K : ℕ) - (k : ℕ)) - (z - c) ^ ((K : ℕ) + 1) * H z
  have hGa : AnalyticAt ℂ G c :=
    (Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul
      ((analyticAt_id.sub analyticAt_const).pow _)).sub
      (((analyticAt_id.sub analyticAt_const).pow _).mul hH)
  have hGc : G c = g K := by
    simp only [G, sub_self, zero_pow (Nat.succ_ne_zero _), zero_mul, sub_zero]
    rw [Finset.sum_eq_single K]
    · simp
    · intro k _ hkK
      by_cases hgk : g k = 0
      · simp [hgk]
      · have hlt : (k : ℕ) < K := lt_of_le_of_ne (hKmax k hgk) (fun h => hkK (Fin.ext h))
        rw [zero_pow (by omega), mul_zero]
    · simp
  have hrep : ∀ᶠ z in 𝓝[≠] c, f z = (z - c) ^ (-((K : ℕ) + 1 : ℤ)) • G z := by
    filter_upwards [nhdsWithin_le_nhds hf, self_mem_nhdsWithin] with z hz hzc
    have hw : z - c ≠ 0 := sub_ne_zero.mpr hzc
    rw [hz, smul_eq_mul, zpow_neg,
      show ((K : ℕ) + 1 : ℤ) = (((K : ℕ) + 1 : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
    simp only [G, mul_sub, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hgk : g k = 0
      · simp [hgk]
      · rw [inv_pow_succ_eq hw (hKmax k hgk)]
        ring
    · rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hw), one_mul]
  have hmero : MeromorphicAt f c :=
    (((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow _).mul hGa.meromorphicAt).congr
      (hrep.mono fun z hz => hz.symm)
  refine ⟨hmero, ?_⟩
  rw [(meromorphicOrderAt_eq_int_iff hmero).mpr ⟨G, hGa, hGc ▸ hK, hrep⟩]
  exact_mod_cast (by omega : (-((K : ℕ) + 1 : ℤ)) < 0)

lemma Cech1.eval_sum {ι : Type*} {U : ι → Set M} {κ : Type*} (t : Finset κ) (ζ : κ → Cech1 U)
    (i j : ι) (x : M) :
    Cech1.eval U (∑ k ∈ t, ζ k) i j x = ∑ k ∈ t, Cech1.eval U (ζ k) i j x := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Cech1.eval_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Cech1.eval_add, ih]

/-- **Meromorphic functions with a single pole** (Forster, *Lectures on Riemann surfaces*, 14.13,
from the finiteness theorem 14.9): on a compact Riemann surface `M`, for every point `y` there is
a function `f : M → ℂ` which is holomorphic on `M ∖ {y}` and, in the chart at `y`, meromorphic at
`y` of negative order. -/
theorem exists_meromorphic_single_pole [IsManifold 𝓘(ℂ) ω M] [T2Space M] [CompactSpace M]
    (y : M) :
    ∃ f : M → ℂ, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f {y}ᶜ ∧
      MeromorphicAt (f ∘ (extChartAt 𝓘(ℂ) y).symm) (extChartAt 𝓘(ℂ) y y) ∧
      meromorphicOrderAt (f ∘ (extChartAt 𝓘(ℂ) y).symm) (extChartAt 𝓘(ℂ) y y) < 0 := by
  classical
  set s : ℝ := 1 / 2 with hsdef
  obtain ⟨ι, _, D, hD0, hcov, hy⟩ := exists_discChart_cover y (s := s) (by norm_num)
  set U : Option ι → Set M := fun i => (D i).disc s with hUdef
  have hU : ∀ i, IsOpen (U i) := fun i => (D i).isOpen_disc s
  set φ := extChartAt 𝓘(ℂ) y with hφdef
  set c := φ y with hcdef
  have hDφ : (D none).chart = φ := by
    change extChartAt 𝓘(ℂ) (D none).center = extChartAt 𝓘(ℂ) y
    rw [hD0]
  have hUsrc : U none ⊆ φ.source := hDφ ▸ (D none).disc_subset_source s
  -- `y` is not in the closure of the other discs
  have hycl : ∀ i, y ∉ closure (U (some i)) := fun i h =>
    hy i (image_mono (closedBall_subset_closedBall
      (by simp only [hsdef]; nlinarith [(D (some i)).radius_pos]))
      ((D (some i)).closure_disc_subset_image (by norm_num) h))
  have hyU : ∀ i, y ∉ U (some i) := fun i h => hycl i (subset_closure h)
  -- a disc around `c` in the chart avoids the other discs
  obtain ⟨ε, hε, hεU⟩ : ∃ ε > 0, ∀ x ∈ φ.source, ‖φ x - c‖ < ε → ∀ i, x ∉ U (some i) := by
    have hN : (⋃ i, closure (U (some i)))ᶜ ∈ 𝓝 y :=
      (isClosed_iUnion_of_finite fun i => isClosed_closure).isOpen_compl.mem_nhds
        (by simpa using hycl)
    have hN' : φ.symm ⁻¹' (⋃ i, closure (U (some i)))ᶜ ∈ 𝓝 c :=
      (continuousAt_extChartAt_symm (I := 𝓘(ℂ)) y).preimage_mem_nhds
        (by rwa [extChartAt_to_inv])
    obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.mp hN'
    refine ⟨ε, hε, fun x hx hxε i hxi => ?_⟩
    have h := hεN (mem_ball_iff_norm.mpr hxε)
    rw [mem_preimage, φ.left_inv hx] at h
    exact h (mem_iUnion.mpr ⟨i, subset_closure hxi⟩)
  -- functions of the chart coordinate, holomorphic away from `c`
  have hcomp : ∀ R : ℂ → ℂ, (∀ z ≠ c, DifferentiableAt ℂ R z) →
      ∀ x ∈ φ.source, x ≠ y → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (R ∘ φ) x := by
    intro R hR x hx hxy
    have hxs : x ∈ (chartAt ℂ y).source := by rwa [← extChartAt_source (I := 𝓘(ℂ))]
    rw [mdifferentiableAt_iff_differentiableAt_chart hxs]
    have hne : φ x ≠ c := fun h => hxy (φ.injOn hx (mem_extChartAt_source y) h)
    refine (hR _ hne).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_extChartAt_target y).mem_nhds (φ.map_source hx)] with z hz
    exact congrArg R (φ.right_inv hz)
  -- the principal parts
  set Q : ℕ → ℂ → ℂ := fun k z => ((z - c)⁻¹) ^ (k + 1) with hQdef
  have hQd : ∀ k, ∀ z ≠ c, DifferentiableAt ℂ (Q k) z := fun k z hz =>
    ((differentiableAt_id.sub_const c).inv (sub_ne_zero.mpr hz)).pow _
  set mOf : ℕ → Option ι → M → ℂ := fun k o x => o.elim (Q k (φ x)) fun _ => 0 with hmOf
  have hsrcy : ∀ i, ∀ x ∈ U none ∩ U (some i), x ∈ φ.source ∧ x ≠ y := fun i x hx =>
    ⟨hUsrc hx.1, fun h => hyU i (h ▸ hx.2)⟩
  have hQbd : ∀ k i, ∀ x ∈ U none ∩ U (some i), ‖Q k (φ x)‖ ≤ ε⁻¹ ^ (k + 1) := by
    intro k i x hx
    have hge : ε ≤ ‖φ x - c‖ := by
      by_contra hlt
      exact hεU x (hUsrc hx.1) (not_le.mp hlt) i hx.2
    simp only [hQdef, norm_pow, norm_inv]
    gcongr
  have hmhol : ∀ k i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (fun x => mOf k j x - mOf k i x)
      (U i ∩ U j) := by
    intro k i j
    rcases i with _ | i <;> rcases j with _ | j
    · exact (mdifferentiableOn_const (c := (0 : ℂ))).congr fun x _ => by simp [hmOf]
    · intro x hx
      have h := (hcomp (Q k) (hQd k) x (hsrcy j x hx).1 (hsrcy j x hx).2).neg
      exact (h.congr_of_eventuallyEq (Eventually.of_forall fun x' => by
        simp [hmOf])).mdifferentiableWithinAt
    · intro x hx
      have h := hcomp (Q k) (hQd k) x (hsrcy i x ⟨hx.2, hx.1⟩).1 (hsrcy i x ⟨hx.2, hx.1⟩).2
      exact (h.congr_of_eventuallyEq (Eventually.of_forall fun x' => by
        simp [hmOf])).mdifferentiableWithinAt
    · exact (mdifferentiableOn_const (c := (0 : ℂ))).congr fun x _ => by simp [hmOf]
  have hmbd : ∀ k i j, ∃ C, ∀ x ∈ U i ∩ U j, ‖mOf k j x - mOf k i x‖ ≤ C := by
    intro k i j
    rcases i with _ | i <;> rcases j with _ | j
    · exact ⟨0, fun x _ => by simp [hmOf]⟩
    · exact ⟨ε⁻¹ ^ (k + 1), fun x hx => by simpa [hmOf] using hQbd k j x hx⟩
    · exact ⟨ε⁻¹ ^ (k + 1), fun x hx => by simpa [hmOf] using hQbd k i x ⟨hx.2, hx.1⟩⟩
    · exact ⟨0, fun x _ => by simp [hmOf]⟩
  set cc : ℕ → Cech1 U := fun k i j =>
    boundedHolomorphic.mk (fun x => mOf k j x - mOf k i x) (hmhol k i j) (hmbd k i j) with hccdef
  have hcc : ∀ k i j, ∀ x ∈ U i ∩ U j, Cech1.eval U (cc k) i j x = mOf k j x - mOf k i x :=
    fun k i j x hx => boundedHolomorphic.extendByZero_mk _ _ _ hx
  have hcc_coc : ∀ k, cc k ∈ cocycles U := fun k i j l x hx => by
    rw [hcc k i l x ⟨hx.1.1, hx.2⟩, hcc k i j x hx.1, hcc k j l x ⟨hx.1.2, hx.2⟩]
    ring
  -- linear dependence modulo coboundaries
  have hfin := DiscChart.cofg_range_cechδ D (by norm_num) (by norm_num) hcov
  set B := LinearMap.range (cechδ U : Cech0 U →ₗ[ℂ] cocycles U)
  set N := Module.finrank ℂ (cocycles U ⧸ B)
  have hdep : ¬ LinearIndependent ℂ
      (fun k : Fin (N + 1) => B.mkQ (⟨cc k, hcc_coc k⟩ : cocycles U)) := fun hli => by
    have := hli.fintype_card_le_finrank
    simp [N] at this
  obtain ⟨g, hg, k0, hk0⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hmem : ∑ k : Fin (N + 1), g k • (⟨cc k, hcc_coc k⟩ : cocycles U) ∈ B := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hg
    exact map_smul _ _ _
  obtain ⟨η, hη⟩ := LinearMap.mem_range.mp hmem
  -- the evaluation identity `ηⱼ - ηᵢ = ∑ₖ gₖ (mₖⱼ - mₖᵢ)`
  set e : Option ι → M → ℂ := fun i =>
    extendByZero ((η i : boundedHolomorphic (U i)) : U i →ᵇ ℂ) with hedef
  have hδ : ∀ i j, ∀ x ∈ U i ∩ U j,
      e j x - e i x = ∑ k : Fin (N + 1), g k * (mOf k j x - mOf k i x) := by
    intro i j x hx
    have h := congr_arg (fun ζ : cocycles U => Cech1.eval U (ζ : Cech1 U) i j x) hη
    rw [show (((cechδ U : Cech0 U →ₗ[ℂ] cocycles U) η : cocycles U) : Cech1 U) = cechδ₁ U η
      from rfl, cechδ₁_eval U η i j hx, Submodule.coe_sum, Cech1.eval_sum] at h
    rw [h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Cech1.eval_smul, hcc k i j x hx]
  -- the glued function
  set Mf : Option ι → M → ℂ := fun i x => ∑ k : Fin (N + 1), g k * mOf k i x with hMf
  have hglue : ∀ i j, ∀ x ∈ U i ∩ U j, Mf i x - e i x = Mf j x - e j x := by
    intro i j x hx
    have h := hδ i j x hx
    simp only [hMf, mul_sub, Finset.sum_sub_distrib] at h ⊢
    linear_combination h
  set F : M → ℂ := fun x => Mf (hcov x).choose x - e (hcov x).choose x with hFdef
  have hF : ∀ i, ∀ x ∈ U i, F x = Mf i x - e i x := fun i x hx =>
    hglue _ _ x ⟨(hcov x).choose_spec, hx⟩
  -- `Mf none` is a function of the chart coordinate
  set R : ℂ → ℂ := fun z => ∑ k : Fin (N + 1), g k * Q k z with hRdef
  have hMnone : Mf none = R ∘ φ := rfl
  have hRd : ∀ z ≠ c, DifferentiableAt ℂ R z := fun z hz =>
    DifferentiableAt.fun_sum fun k _ => (hQd k z hz).const_mul _
  refine ⟨F, ?_, ?_⟩
  · -- holomorphy away from `y`
    intro x (hx : x ≠ y)
    obtain ⟨i, hi⟩ := hcov x
    have hev : F =ᶠ[𝓝 x] fun x' => Mf i x' - e i x' := by
      filter_upwards [(hU i).mem_nhds hi] with x' hx'
      exact hF i x' hx'
    have hM : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Mf i) x := by
      rcases i with _ | i
      · rw [hMnone]; exact hcomp R hRd x (hUsrc hi) hx
      · have : Mf (some i) = fun _ => 0 := by funext x'; simp [hMf, hmOf]
        rw [this]; exact mdifferentiableAt_const
    have he : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (e i) x :=
      ((η i).2 x hi).mdifferentiableAt ((hU i).mem_nhds hi)
    exact ((hM.sub he).congr_of_eventuallyEq hev).mdifferentiableWithinAt
  -- the chart expression at `y`
  set H : ℂ → ℂ := e none ∘ φ.symm with hHdef
  have hyU0 : y ∈ U none := by
    have := (D none).center_mem_disc (s := s) (by norm_num)
    rwa [hD0] at this
  have hcU : φ.target ∩ φ.symm ⁻¹' U none ∈ 𝓝 c :=
    (isOpen_extChartAt_target_inter_preimage (hU none) y).mem_nhds
      ⟨mem_extChartAt_target y, by rw [mem_preimage, extChartAt_to_inv]; exact hyU0⟩
  have hH : AnalyticAt ℂ H c :=
    (MDifferentiableOn.differentiableOn_chart (hU none) (η none).2 y).analyticAt hcU
  have hFchart : ∀ᶠ z in 𝓝 c, (F ∘ φ.symm) z = R z - H z := by
    filter_upwards [hcU] with z hz
    simp only [Function.comp_apply, hF none _ hz.2, hHdef, hMnone]
    rw [show φ (φ.symm z) = z from φ.right_inv hz.1]
  -- the order of the pole
  exact meromorphicAt_and_order_neg_of_principalParts g ⟨k0, hk0⟩ hH hFchart

end AnalyticGeometry
