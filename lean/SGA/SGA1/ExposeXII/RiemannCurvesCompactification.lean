/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannCurvesPuncturedPlaneGroup
import SGA.Foundations.Analytic.RiemannSurfaceMeromorphic

/-!
# SGA 1, Exposé XII, 5.1 for `ℂ ∖ S`: separating functions from a compactification

Let `p : E → ℂ ∖ S` be a finite covering. Classically, `E` is the complement of finitely many
points in a compact Riemann surface `Ē`, on which `p` is a local coordinate at the points of `E`
(fill in the punctures with the local models `w ↦ wⁿ` of the covering over small punctured
discs). This file states that as `PuncturedPlaneCompactificationStatement` (pure topology and
chart bookkeeping, with no analysis), and derives from it, with the analytic heart
(`AnalyticGeometry.exists_meromorphic_single_pole`,
`SGA.Foundations.Analytic.RiemannSurfaceMeromorphic`: on a compact Riemann surface every point is
the only pole of a meromorphic function), the analytic input `FiberSeparatingFunctionStatement`
of the algebraic half (`fiberSeparatingFunctionStatement_of_compactification`). Hence the Riemann
existence theorem for `ℂ ∖ S` follows from the compactification alone
(`PuncturedPlane.isEquivalence_pointsFunctor_coordRing_of_compactification`).

The compactification statement is proved (`puncturedPlaneCompactification`,
`SGA.SGA1.ExposeXII.GAGAFiberSeparating`), which makes the `_of_compactification` theorems here
unconditional: `fiberSeparatingFunction`, `PuncturedPlane.riemannExistence_coordRing`,
`PuncturedPlane.riemannExistence_finiteEtale` and
`PuncturedPlane.etaleFundamentalGroup_mulEquiv_completion_freeGroup` (same file).

Proof of the derivation: let `e₁, …, e_d` be the fibre over `z`, and `f_k` a meromorphic
function on `Ē` with a single pole, of order `m_k`, at `e_k`. In the coordinate `t = p` at `e_k`,
`f_k = (t - z)^{-m_k} g_k` with `g_k(z) ≠ 0`, so `G_k = (t - z)^{m_k} f_k` is holomorphic on `E`,
does not vanish at `e_k` and vanishes at the `e_j`, `j ≠ k`
(`Compactification.exists_holAt_of_pole`). Then `F = ∑ k G_k / G_k(e_k)` takes the value `k` at
`e_k`. It is holomorphic on `E`, and of moderate growth because `Ē` is compact: `f_k` is bounded
away from `e_k`, so `|G_k| ≤ C (1 + |t|)^{m_k}`.

This route is this project's, not SGA's (see `SGA.SGA1.ExposeXII.RiemannCurves`).
-/

noncomputable section

open Topology Set Filter Polynomial
open scoped Manifold ContDiff

namespace SGA.SGA1.ExposeXII

/-- Filling in the punctures of a finite covering of `ℂ ∖ S`: for `S ⊂ ℂ` finite
and `p : E → ℂ ∖ S` a connected finite covering, `E` is an open subset of a compact Riemann
surface `M` (a compact Hausdorff complex manifold of dimension one, mathlib's
`IsManifold 𝓘(ℂ) ω`), through an open embedding `ι`, such that `p` is the chart of `M` at the
points of `E`: the chart at `ι e` has its source inside `ι(E)`, where it is `p`. (Classically
`M ∖ ι(E)` is finite: one point for each connected component of `p⁻¹` of a small punctured disc
around each point of `S ∪ {∞}`; this is not needed.) Proved: `puncturedPlaneCompactification`
(`SGA.SGA1.ExposeXII.GAGAFiberSeparating`). -/
def PuncturedPlaneCompactificationStatement : Prop :=
  ∀ (S : Finset ℂ) (E : Type) [TopologicalSpace E] [ConnectedSpace E]
    (p : E → {z : ℂ // z ∉ S}), IsCoveringMap p → (∀ z, (p ⁻¹' {z}).Finite) →
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : T2Space M) (_ : CompactSpace M)
      (_ : ChartedSpace ℂ M) (_ : IsManifold 𝓘(ℂ) ω M) (ι : E → M),
      IsOpenEmbedding ι ∧ ∀ e, (chartAt ℂ (ι e)).source ⊆ range ι ∧
        ∀ e', ι e' ∈ (chartAt ℂ (ι e)).source → chartAt ℂ (ι e) (ι e') = p e'

namespace Compactification

section HolAt

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

lemma extChartAt_symm_eq (x : M) : ⇑(extChartAt 𝓘(ℂ) x).symm = (chartAt ℂ x).symm := by
  ext t
  simp

lemma extChartAt_eq (x : M) : ⇑(extChartAt 𝓘(ℂ) x) = chartAt ℂ x := by
  ext t
  simp

/-- `G : M → ℂ` is holomorphic at `x`, in the chart at `x`. -/
def HolAt (G : M → ℂ) (x : M) : Prop :=
  DifferentiableAt ℂ (G ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

lemma HolAt.add {G G' : M → ℂ} {x : M} (h : HolAt G x) (h' : HolAt G' x) :
    HolAt (G + G') x :=
  DifferentiableAt.add h h'

lemma HolAt.const_mul {G : M → ℂ} {x : M} (h : HolAt G x) (c : ℂ) :
    HolAt (fun y ↦ c * G y) x :=
  DifferentiableAt.const_mul h c

lemma holAt_finsetSum {ι : Type*} (s : Finset ι) {G : ι → M → ℂ} {x : M}
    (h : ∀ i ∈ s, HolAt (G i) x) : HolAt (fun y ↦ ∑ i ∈ s, G i y) x := by
  have : (fun y ↦ ∑ i ∈ s, G i y) ∘ (chartAt ℂ x).symm =
      fun t ↦ ∑ i ∈ s, (G i ∘ (chartAt ℂ x).symm) t := rfl
  unfold HolAt
  rw [this]
  exact DifferentiableAt.fun_sum fun i hi ↦ h i hi

/-- A function holomorphic at `x` in the chart is continuous at `x`. -/
lemma HolAt.continuousAt {G : M → ℂ} {x : M} (h : HolAt G x) : ContinuousAt G x := by
  have heq : G =ᶠ[𝓝 x] (G ∘ (chartAt ℂ x).symm) ∘ chartAt ℂ x := by
    filter_upwards [chart_source_mem_nhds ℂ x] with y hy
    simp only [Function.comp_apply, (chartAt ℂ x).left_inv hy]
  have hd : DifferentiableAt ℂ (G ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := h
  exact ContinuousAt.congr (hd.continuousAt.comp ((chartAt ℂ x).continuousAt
    (mem_chart_source ℂ x))) heq.symm

/-- A function holomorphic on an open set is holomorphic in the chart at each of its points. -/
lemma holAt_of_mdifferentiableOn [IsManifold 𝓘(ℂ) 1 M] {f : M → ℂ} {W : Set M} (hW : IsOpen W)
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f W) {x : M} (hx : x ∈ W) : HolAt f x := by
  have := AnalyticGeometry.differentiableAt_chart_of_mdifferentiableOn hW hf x
    (mem_extChartAt_target x) (by rwa [extChartAt_to_inv])
  rw [extChartAt_symm_eq, extChartAt_eq] at this
  exact this

end HolAt

section Embedding

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {S : Finset ℂ} {E : Type*}
  {p : E → {z : ℂ // z ∉ S}} {ι : E → M}

/-- The coordinate `p`, extended by `0` to `M`. -/
def coord (p : E → {z : ℂ // z ∉ S}) (ι : E → M) : M → ℂ :=
  Function.extend ι (fun e ↦ (p e : ℂ)) 0

variable (hι : Function.Injective ι) (hsrc : ∀ e, (chartAt ℂ (ι e)).source ⊆ range ι)
  (hch : ∀ e e', ι e' ∈ (chartAt ℂ (ι e)).source → chartAt ℂ (ι e) (ι e') = p e')

omit [TopologicalSpace M] [ChartedSpace ℂ M] in
include hι in
lemma coord_apply (e : E) : coord p ι (ι e) = p e :=
  hι.extend_apply _ _ e

include hι hsrc hch in
/-- In the chart at a point of `E`, the coordinate `p` is the identity. -/
lemma coord_chart_symm (e : E) {t : ℂ} (ht : t ∈ (chartAt ℂ (ι e)).target) :
    coord p ι ((chartAt ℂ (ι e)).symm t) = t := by
  obtain ⟨e', he'⟩ := hsrc e ((chartAt ℂ (ι e)).map_target ht)
  rw [← he', coord_apply hι, ← hch e e' (he' ▸ (chartAt ℂ (ι e)).map_target ht), he',
    (chartAt ℂ (ι e)).right_inv ht]

include hch in
lemma chartAt_self (e : E) : chartAt ℂ (ι e) (ι e) = p e :=
  hch e e (mem_chart_source ℂ (ι e))

include hι hsrc hch in
/-- The coordinate is holomorphic on `E`. -/
lemma holAt_coord (e : E) : HolAt (coord p ι) (ι e) := by
  have : coord p ι ∘ (chartAt ℂ (ι e)).symm =ᶠ[𝓝 (chartAt ℂ (ι e) (ι e))] id := by
    filter_upwards [(chartAt ℂ (ι e)).open_target.mem_nhds (mem_chart_target ℂ (ι e))] with t ht
    exact coord_chart_symm hι hsrc hch e ht
  exact differentiableAt_id.congr_of_eventuallyEq this

include hch in
/-- A function on `M` holomorphic at the points of `E` restricts to a holomorphic function on the
covering `E` of `ℂ ∖ S` (`PuncturedPlane.IsHolomorphic`). -/
theorem isHolomorphic_comp [TopologicalSpace E] (hιc : Continuous ι) {G : M → ℂ}
    (hG : ∀ e, HolAt G (ι e)) :
    PuncturedPlane.IsHolomorphic p (G ∘ ι) := by
  intro U hU _ s hs hps t₀ ht₀
  let u₀ : U := ⟨t₀, ht₀⟩
  let e₀ := s u₀
  let c := chartAt ℂ (ι e₀)
  have hV : IsOpen {u : U | ι (s u) ∈ c.source} :=
    c.open_source.preimage (hιc.comp hs)
  have hu₀ : u₀ ∈ {u : U | ι (s u) ∈ c.source} := mem_chart_source ℂ (ι e₀)
  have hct₀ : c (ι e₀) = t₀ := (chartAt_self hch e₀).trans (hps u₀)
  have hnhds : Subtype.val '' {u : U | ι (s u) ∈ c.source} ∈ 𝓝 t₀ :=
    (hU.isOpenMap_subtype_val _ hV).mem_nhds ⟨u₀, hu₀, rfl⟩
  have heq : Function.extend (fun z : U ↦ (z : ℂ)) ((G ∘ ι) ∘ s) 0 =ᶠ[𝓝 t₀]
      G ∘ c.symm := by
    filter_upwards [hnhds] with t ht
    obtain ⟨u, hu, rfl⟩ := ht
    rw [Subtype.val_injective.extend_apply]
    have h1 : c (ι (s u)) = u := (hch e₀ (s u) hu).trans (hps u)
    simp only [Function.comp_apply, ← h1, c.left_inv hu]
  have hd : DifferentiableAt ℂ (G ∘ c.symm) t₀ := hct₀ ▸ hG e₀
  exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt

end Embedding

section Pole

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) ω M] {S : Finset ℂ} {E : Type*} {p : E → {z : ℂ // z ∉ S}} {ι : E → M}
  (hι : Function.Injective ι) (hsrc : ∀ e, (chartAt ℂ (ι e)).source ⊆ range ι)
  (hch : ∀ e e', ι e' ∈ (chartAt ℂ (ι e)).source → chartAt ℂ (ι e) (ι e') = p e')

include hι hsrc hch in
/-- Killing the pole of a meromorphic function with a single pole at a point `e` of `E` by a
power of `p - p(e)` (`AnalyticGeometry.exists_meromorphic_single_pole`): a function `G` on `M`,
holomorphic at the points of `E`, not vanishing at `e`, vanishing at the other points of the fibre
of `e`, and with `|G| ≤ K (1 + |p|)ᵐ` on `E` (`M` is compact). -/
theorem exists_holAt_of_pole (e : E) :
    ∃ (G : M → ℂ) (m : ℕ) (K : ℝ), (∀ e', HolAt G (ι e')) ∧ G (ι e) ≠ 0 ∧
      (∀ e', e' ≠ e → (p e' : ℂ) = p e → G (ι e') = 0) ∧
      ∀ e', ‖G (ι e')‖ ≤ K * (1 + ‖(p e' : ℂ)‖) ^ m := by
  classical
  obtain ⟨f, hf, hmer, hord⟩ := AnalyticGeometry.exists_meromorphic_single_pole (ι e)
  set c := chartAt ℂ (ι e) with hc
  set z₀ : ℂ := (p e : ℂ) with hz₀
  have hcz : c (ι e) = z₀ := chartAt_self hch e
  rw [extChartAt_symm_eq, extChartAt_eq, ← hc, hcz] at hmer hord
  obtain ⟨g, hga, hg0, hfg⟩ := (meromorphicOrderAt_ne_top_iff hmer).mp hord.ne_top
  set n := (meromorphicOrderAt (f ∘ c.symm) z₀).untop₀ with hn_def
  have hn : n < 0 := by
    have h1 : ((n : ℤ) : WithTop ℤ) = meromorphicOrderAt (f ∘ c.symm) z₀ :=
      WithTop.coe_untop₀_of_ne_top hord.ne_top
    rw [← h1] at hord
    exact_mod_cast hord
  set m : ℕ := (-n).toNat with hm_def
  have hm : (m : ℤ) = -n := Int.toNat_of_nonneg (by omega)
  have hm1 : 1 ≤ m := by omega
  let G : M → ℂ := fun x ↦ if x = ι e then g z₀ else (coord p ι x - z₀) ^ m * f x
  -- the representation of `G` in the chart at `e`
  have hrep : ∀ᶠ t in 𝓝 z₀, t ∈ c.target ∧ G (c.symm t) = g t := by
    have h1 : ∀ᶠ t in 𝓝 z₀, t ≠ z₀ → (f ∘ c.symm) t = (t - z₀) ^ n • g t :=
      eventually_nhdsWithin_iff.mp hfg
    have h2 : c.target ∈ 𝓝 z₀ := hcz ▸ c.open_target.mem_nhds (mem_chart_target ℂ (ι e))
    filter_upwards [h1, h2] with t ht ht'
    refine ⟨ht', ?_⟩
    by_cases htz : t = z₀
    · subst htz
      have : c.symm (c (ι e)) = ι e := c.left_inv (mem_chart_source ℂ (ι e))
      simp only [G, ← hcz, this, ↓reduceIte]
    · have hne : c.symm t ≠ ι e := by
        intro h
        apply htz
        rw [← c.right_inv ht', h, hcz]
      have hcs : coord p ι (c.symm t) = t := coord_chart_symm hι hsrc hch e ht'
      simp only [G, hne, ↓reduceIte, hcs]
      have := ht htz
      simp only [Function.comp_apply, smul_eq_mul] at this
      rw [this, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ (sub_ne_zero.mpr htz), hm,
        neg_add_cancel, zpow_zero, one_mul]
  refine ⟨G, m, ?_⟩
  -- holomorphy
  have hhol : ∀ e', HolAt G (ι e') := by
    intro e'
    by_cases he' : ι e' = ι e
    · rw [he']
      unfold HolAt
      rw [← hc, hcz]
      exact hga.differentiableAt.congr_of_eventuallyEq (hrep.mono fun t ht ↦ ht.2)
    · set c' := chartAt ℂ (ι e')
      have hW : IsOpen ({ι e}ᶜ : Set M) := isOpen_compl_singleton
      have hfd := holAt_of_mdifferentiableOn hW hf (x := ι e') he'
      have hev : ∀ᶠ t in 𝓝 (c' (ι e')), t ∈ c'.target ∧ c'.symm t ∈ ({ι e}ᶜ : Set M) := by
        have h1 : c'.target ∈ 𝓝 (c' (ι e')) := c'.open_target.mem_nhds (mem_chart_target ℂ _)
        have h2 : c'.symm ⁻¹' ({ι e}ᶜ : Set M) ∈ 𝓝 (c' (ι e')) := by
          apply c'.continuousAt_symm (mem_chart_target ℂ _)
          rw [c'.left_inv (mem_chart_source ℂ _)]
          exact hW.mem_nhds he'
        filter_upwards [h1, h2] with t h1 h2
        exact ⟨h1, h2⟩
      have heq : G ∘ c'.symm =ᶠ[𝓝 (c' (ι e'))] fun t ↦ (t - z₀) ^ m * (f ∘ c'.symm) t := by
        filter_upwards [hev] with t ht
        have h2 : ¬ c'.symm t = ι e := ht.2
        have hcs : coord p ι (c'.symm t) = t := coord_chart_symm hι hsrc hch e' ht.1
        simp only [Function.comp_apply, G, h2, ↓reduceIte, hcs]
      exact (((differentiableAt_id.sub_const z₀).pow m).mul hfd).congr_of_eventuallyEq heq
  -- the bound
  obtain ⟨ρ, hρ, hρs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hrep.and (hga.eventually_analyticAt.mono fun t ht ↦ ht.continuousAt))
  have hgc : ContinuousOn g (Metric.closedBall z₀ ρ) := fun t ht ↦ ((hρs ht).2).continuousWithinAt
  obtain ⟨K₁, hK₁⟩ := (isCompact_closedBall z₀ ρ).exists_bound_of_continuousOn hgc
  have hball : Metric.ball z₀ ρ ⊆ c.target := fun t ht ↦
    (hρs (Metric.ball_subset_closedBall ht)).1.1
  set O := c.symm '' Metric.ball z₀ ρ
  have hO : IsOpen O := c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hball
  have heO : ι e ∈ O := ⟨z₀, Metric.mem_ball_self hρ, by
    rw [← hcz]
    exact c.left_inv (mem_chart_source ℂ (ι e))⟩
  have hfc : ContinuousOn f Oᶜ := hf.continuousOn.mono fun x hx h ↦ hx (h ▸ heO)
  obtain ⟨K₂, hK₂⟩ := (hO.isClosed_compl.isCompact).exists_bound_of_continuousOn hfc
  refine ⟨max K₁ 0 + (1 + ‖z₀‖) ^ m * max K₂ 0, hhol, ?_, ?_, ?_⟩
  · simp only [G, ↓reduceIte]
    exact hg0
  · intro e' he' hpe
    have hne : ι e' ≠ ι e := fun h ↦ he' (hι h)
    simp only [G, hne, ↓reduceIte, coord_apply hι, hpe, sub_self, zero_pow (by omega : m ≠ 0),
      zero_mul]
  · intro e'
    have hp1 : 1 ≤ (1 + ‖(p e' : ℂ)‖) ^ m := one_le_pow₀ (by linarith [norm_nonneg (p e' : ℂ)])
    have hK₂' : 0 ≤ (1 + ‖z₀‖) ^ m * max K₂ 0 := by positivity
    by_cases hO' : ι e' ∈ O
    · obtain ⟨t, ht, hte⟩ := hO'
      have hGt : G (ι e') = g t := by
        rw [← hte]
        exact (hρs (Metric.ball_subset_closedBall ht)).1.2
      rw [hGt]
      calc ‖g t‖ ≤ max K₁ 0 := (hK₁ t (Metric.ball_subset_closedBall ht)).trans (le_max_left _ _)
        _ ≤ max K₁ 0 * (1 + ‖(p e' : ℂ)‖) ^ m := le_mul_of_one_le_right (le_max_right _ _) hp1
        _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_right hK₂'
    · have hne : ι e' ≠ ι e := fun h ↦ hO' (h ▸ heO)
      have hfe := hK₂ (ι e') hO'
      simp only [G, hne, ↓reduceIte, coord_apply hι]
      rw [norm_mul, norm_pow]
      have h1 : ‖(p e' : ℂ) - z₀‖ ≤ (1 + ‖z₀‖) * (1 + ‖(p e' : ℂ)‖) := by
        calc ‖(p e' : ℂ) - z₀‖ ≤ ‖(p e' : ℂ)‖ + ‖z₀‖ := norm_sub_le _ _
          _ ≤ (1 + ‖z₀‖) * (1 + ‖(p e' : ℂ)‖) := by
            nlinarith [norm_nonneg (p e' : ℂ), norm_nonneg z₀]
      calc ‖(p e' : ℂ) - z₀‖ ^ m * ‖f (ι e')‖
          ≤ ((1 + ‖z₀‖) * (1 + ‖(p e' : ℂ)‖)) ^ m * max K₂ 0 := by
            gcongr
            exact hfe.trans (le_max_left _ _)
        _ = (1 + ‖z₀‖) ^ m * max K₂ 0 * (1 + ‖(p e' : ℂ)‖) ^ m := by
            rw [mul_pow]
            ring
        _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_left (le_max_right _ _)

end Pole

section Assembly

variable {S : Finset ℂ} {E : Type*} [TopologicalSpace E] {p : E → {z : ℂ // z ∉ S}}

/-- A separating function for the fibre over `z₀`, from a compactification of `E` in which `p` is
the chart at the points of `E`: `F = ∑ₖ k Gₖ / Gₖ(eₖ)`, `Gₖ` from `exists_holAt_of_pole`. -/
theorem exists_separating_of_compactification {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] {ι : E → M}
    (hι : IsOpenEmbedding ι) (hsrc : ∀ e, (chartAt ℂ (ι e)).source ⊆ range ι)
    (hch : ∀ e e', ι e' ∈ (chartAt ℂ (ι e)).source → chartAt ℂ (ι e) (ι e') = p e')
    (hfin : ∀ z, (p ⁻¹' {z}).Finite) (z₀ : {z : ℂ // z ∉ S}) :
    ∃ F : E → ℂ, Continuous F ∧ PuncturedPlane.IsHolomorphic p F ∧
      PuncturedPlane.IsModerate p F ∧ Set.InjOn F (p ⁻¹' {z₀}) := by
  classical
  set s := (hfin z₀).toFinset with hs
  choose G m K hhol hne hzero hbound using fun e ↦
    exists_holAt_of_pole (M := M) hι.injective hsrc hch e
  let k : E → ℂ := fun e ↦ if he : e ∈ s then ((s.equivFin ⟨e, he⟩ : ℕ) : ℂ) else 0
  let wt : E → ℂ := fun e ↦ k e / G e (ι e)
  let Ĝ : M → ℂ := fun x ↦ ∑ e ∈ s, wt e * G e x
  have hĜ (e' : E) : HolAt Ĝ (ι e') :=
    holAt_finsetSum s fun e _ ↦ (hhol e e').const_mul (wt e)
  refine ⟨Ĝ ∘ ι, ?_, isHolomorphic_comp hch hι.continuous hĜ, ?_, ?_⟩
  · -- continuity
    exact continuous_iff_continuousAt.mpr fun e' ↦
      (hĜ e').continuousAt.comp hι.continuous.continuousAt
  · -- moderate growth
    let N : ℕ := s.sup m
    let L : ℝ := ∑ e ∈ s, ‖wt e‖ * max (K e) 0
    refine ⟨L * ∏ a ∈ S, (1 + ‖a‖) ^ N, N, fun e' ↦ ?_⟩
    set q : ℂ := (p e' : ℂ)
    have hq1 : 1 ≤ 1 + ‖q‖ := le_add_of_nonneg_right (norm_nonneg q)
    have hF : ‖(Ĝ ∘ ι) e'‖ ≤ L * (1 + ‖q‖) ^ N := by
      simp only [Function.comp_apply, Ĝ, L, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e he ↦ ?_)
      rw [norm_mul, mul_assoc]
      gcongr
      calc ‖G e (ι e')‖ ≤ K e * (1 + ‖q‖) ^ m e := hbound e e'
        _ ≤ max (K e) 0 * (1 + ‖q‖) ^ m e := by gcongr; exact le_max_left _ _
        _ ≤ max (K e) 0 * (1 + ‖q‖) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq1 (Finset.le_sup (f := m) he))
            (le_max_right _ _)
    have hP : ∏ a ∈ S, ‖q - a‖ ^ N ≤ (∏ a ∈ S, (1 + ‖a‖) ^ N) * (1 + ‖q‖) ^ (N * S.card) := by
      have h1 : ∏ a ∈ S, ‖q - a‖ ^ N ≤ ∏ a ∈ S, ((1 + ‖a‖) ^ N * (1 + ‖q‖) ^ N) :=
        Finset.prod_le_prod (fun a _ ↦ by positivity) fun a _ ↦ by
          rw [← mul_pow]
          gcongr
          calc ‖q - a‖ ≤ ‖q‖ + ‖a‖ := norm_sub_le _ _
            _ ≤ (1 + ‖a‖) * (1 + ‖q‖) := by nlinarith [norm_nonneg q, norm_nonneg a]
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul] at h1
      exact h1
    have hL : 0 ≤ L := Finset.sum_nonneg fun e _ ↦ by positivity
    calc ‖(Ĝ ∘ ι) e'‖ * ∏ a ∈ S, ‖q - a‖ ^ N
        ≤ L * (1 + ‖q‖) ^ N * ((∏ a ∈ S, (1 + ‖a‖) ^ N) * (1 + ‖q‖) ^ (N * S.card)) :=
          mul_le_mul hF hP (by positivity) (by positivity)
      _ = L * (∏ a ∈ S, (1 + ‖a‖) ^ N) * (1 + ‖q‖) ^ (N * (S.card + 1)) := by
          rw [mul_add, mul_one, pow_add]
          ring
  · -- injectivity on the fibre
    have hval (e' : E) (he' : e' ∈ p ⁻¹' {z₀}) : (Ĝ ∘ ι) e' = k e' := by
      have he's : e' ∈ s := (hfin z₀).mem_toFinset.mpr he'
      simp only [Function.comp_apply, Ĝ]
      rw [Finset.sum_eq_single e']
      · simp only [wt]
        exact div_mul_cancel₀ _ (hne e')
      · intro e he hee'
        have hpe : (p e' : ℂ) = p e := by
          rw [show p e' = z₀ from he', show p e = z₀ from (hfin z₀).mem_toFinset.mp he]
        rw [hzero e e' (Ne.symm hee') hpe, mul_zero]
      · intro h
        exact absurd he's h
    intro e₁ he₁ e₂ he₂ h
    rw [hval e₁ he₁, hval e₂ he₂] at h
    have he₁s : e₁ ∈ s := (hfin z₀).mem_toFinset.mpr he₁
    have he₂s : e₂ ∈ s := (hfin z₀).mem_toFinset.mpr he₂
    simp only [k, he₁s, he₂s, dite_true, Nat.cast_inj] at h
    exact congrArg Subtype.val (s.equivFin.injective (Fin.ext h))

end Assembly

end Compactification

/-- XII.5.1 for curves, analytic input: the compactification of finite coverings of `ℂ ∖ S`
(`PuncturedPlaneCompactificationStatement`) and the meromorphic functions with a single pole on
compact Riemann surfaces (`AnalyticGeometry.exists_meromorphic_single_pole`) give a
separating function for every fibre (`FiberSeparatingFunctionStatement`). -/
theorem fiberSeparatingFunctionStatement_of_compactification
    (Hc : PuncturedPlaneCompactificationStatement) : FiberSeparatingFunctionStatement := by
  intro S E _ _ p hp hfin z
  obtain ⟨M, _, _, _, _, _, ι, hι, hM⟩ := Hc S E p hp hfin
  exact Compactification.exists_separating_of_compactification hι (fun e ↦ (hM e).1)
    (fun e e' h ↦ (hM e).2 e' h) hfin z

namespace PuncturedPlane

/-- **XII.5.1 for `ℂ ∖ S`, conditionally on the compactification**: if finite coverings of
`ℂ ∖ S` can be compactified (`PuncturedPlaneCompactificationStatement`, pure topology), the
Riemann existence theorem holds for `Spec ℂ[t][1/∏_{a ∈ S} (t - a)]`. -/
theorem isEquivalence_pointsFunctor_coordRing_of_compactification
    (Hc : PuncturedPlaneCompactificationStatement) (S : Finset ℂ) :
    (pointsFunctor ℂ (coordRing S)).IsEquivalence :=
  isEquivalence_pointsFunctor_coordRing (fiberSeparatingFunctionStatement_of_compactification Hc) S

/-- XII.5.2 (and XIII.2.12 in genus `0`) for `ℂ ∖ S`, conditionally on the compactification: the
étale fundamental group of `ℙ¹_ℂ` minus `|S| + 1` points is the free profinite group on `S`. -/
theorem nonempty_etaleFundamentalGroup_continuousMulEquiv_completion_freeGroup_of_compactification
    (Hc : PuncturedPlaneCompactificationStatement) (S : Finset ℂ)
    (x : SchemePoints ℂ (AlgebraicGeometry.Spec (.of (coordRing S)))) :
    Nonempty (ExposeV.etaleFundamentalGroup ℂ x.1 ≃ₜ*
      ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup S))) :=
  nonempty_etaleFundamentalGroup_continuousMulEquiv_completion_freeGroup
    (fiberSeparatingFunctionStatement_of_compactification Hc) S x

/-- XII.5.1 for finite étale coverings of `ℂ ∖ S` (e.g. smooth affine curves minus finitely many
points), conditionally on the compactification. -/
theorem isEquivalence_pointsFunctor_finiteEtale_of_compactification
    (Hc : PuncturedPlaneCompactificationStatement) (S : Finset ℂ)
    (B : CommAlgCat.FiniteEtale.{0} (coordRing S)) :
    letI := algebraOfFiniteEtale ℂ (coordRing S) B
    (pointsFunctor ℂ B).IsEquivalence :=
  isEquivalence_pointsFunctor_finiteEtale (fiberSeparatingFunctionStatement_of_compactification Hc)
    S B

end PuncturedPlane

end SGA.SGA1.ExposeXII
