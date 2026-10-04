/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Homotopy.Lifting

/-!
# Maps which are coverings away from a fibre: lifting paths and contractions

Let `p : E → X` be a proper map with finite fibres which is a covering map over a subset `W ⊆ X`
(`IsCoveringMapOn p W`), e.g. a branched covering of `ℂⁿ` with `W` the complement of the branch
locus. This file lifts paths and homotopies which stay in `W` except at their end:

* `IsCoveringMapOn.exists_path_lift`: a path `γ` from `y` to `x₀` with `γ(t) ∈ W` for `t < 1`
  lifts to a path from a given `e` over `y` to the only point `x` over `x₀` in a neighbourhood `U`
  of `x` which is closed in `p⁻¹(γ)` (lift on `[0, 1)`, which is simply connected, and use the
  compactness of `p⁻¹(γ)` at `t = 1`);
* `IsCoveringMapOn.locallyPathConnectedSpace`: `E` is locally path-connected if `p⁻¹(W)` is dense
  and points of small balls in `W` are joined to the centre by paths staying in `W` before the end;
* `IsCoveringMapOn.nonempty_homotopyRel_id_const`: a covering of a punctured ball `B(z₀, r) ∖ {z₀}`
  of a real normed space contracts onto the point `x` over `z₀`, by lifting the radial homotopy.

These are the arguments for the local topology of analytic sets through branched coverings, without
triangulation.

## References

* [R. Gunning, H. Rossi, *Analytic functions of several complex variables*, III.B]
* [A. Hatcher, *Algebraic Topology*, §1.3][hatcher02]
-/

open Topology Set Filter Metric

namespace IsCoveringMapOn

/-! ### Lifting paths through a map which is a covering away from the endpoint -/

section Lift

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

omit [TopologicalSpace E] in
private lemma extend_mem_of_lt_one {y x₀ : X} (γ : Path y x₀) {W : Set X}
    (hγ : ∀ t : unitInterval, t ≠ 1 → γ t ∈ W) {t : ℝ} (ht : t < 1) : γ.extend t ∈ W := by
  rcases le_or_gt t 0 with h0 | h0
  · rw [Path.extend_of_le_zero _ h0, ← γ.source]
    exact hγ 0 zero_ne_one
  · rw [Path.extend_apply _ ⟨h0.le, ht.le⟩]
    exact hγ _ fun h ↦ ht.ne (congrArg Subtype.val h)

variable [T2Space X]

/-- Lifting a path `γ` from `y` to `x₀` through a map `p` which is a covering over a set `W`
containing `γ(t)` for `t < 1`. The lift starting at `e ∈ U` stays in `U` (assumed open and closed
in `p⁻¹(γ)`) and converges at `t = 1` to the only point `x` of `U` over `x₀`, provided `p⁻¹(γ)` is
compact. -/
theorem exists_path_lift {p : E → X} {W : Set X} (hp : IsCoveringMapOn p W)
    (hpc : Continuous p) {y x₀ : X} (γ : Path y x₀) (hγ : ∀ t : unitInterval, t ≠ 1 → γ t ∈ W)
    (hK : IsCompact (p ⁻¹' range γ)) {U : Set E} (hU : IsOpen U)
    (hUc : closure U ∩ p ⁻¹' range γ ⊆ U) {e x : E} (he : e ∈ U) (hpe : p e = y)
    (hxU : x ∈ U) (hpx : p x = x₀) (hx : ∀ x' ∈ U, p x' = x₀ → x' = x) :
    ∃ Γ : Path e x, (∀ t, Γ t ∈ U) ∧ ∀ t, p (Γ t) = γ t := by
  classical
  -- lift `γ` on `(-∞, 1)`, a convex hence simply connected and locally path-connected space
  let A := Iio (1 : ℝ)
  have hA : Convex ℝ A := convex_Iio 1
  have : ContractibleSpace A := hA.contractibleSpace ⟨0, by norm_num [A]⟩
  have : LocallyPathConnectedSpace A := hA.locallyPathConnectedSpace
  let f : C(A, X) := ⟨fun t ↦ γ.extend t, by fun_prop⟩
  let a₀ : A := ⟨0, by norm_num [A]⟩
  obtain ⟨F, ⟨hF0, hpF⟩, -⟩ := hp.existsUnique_continuousMap_lifts f (a₀ := a₀) (e₀ := e)
    (by simp [f, a₀, hpe]) fun t ↦ extend_mem_of_lt_one γ hγ t.2
  have hpF' (t : A) : p (F t) = γ.extend t := congrFun hpF t
  -- the lift stays in `U`
  have hFU : range F ⊆ U := by
    refine (isPreconnected_range F.continuous).subset_of_closure_inter_subset hU
      ⟨e, ⟨a₀, hF0⟩, he⟩ ?_
    rintro _ ⟨hcl, t, rfl⟩
    refine hUc ⟨hcl, ?_⟩
    rw [mem_preimage, hpF', ← Path.extend_range]
    exact mem_range_self _
  -- the extension by `x` at `1`
  let G : ℝ → E := fun t ↦ if h : t < 1 then F ⟨t, h⟩ else x
  have hGF (t : ℝ) (h : t < 1) : G t = F ⟨t, h⟩ := by simp [G, h]
  have hG1 : G 1 = x := by simp [G]
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), t < 1 := self_mem_nhdsWithin
  have hlim : Tendsto G (𝓝[<] 1) (𝓝 x) := by
    refine hK.tendsto_nhds_of_unique_mapClusterPt ?_ fun c hc hcl ↦ ?_
    · filter_upwards [hev] with t ht
      rw [hGF t ht, mem_preimage, hpF', ← Path.extend_range]
      exact mem_range_self _
    · have hcU : c ∈ closure U := by
        refine hcl.mem_closure_of_mem (s := U) (mem_map.mpr ?_)
        filter_upwards [hev] with t ht
        rw [mem_preimage, hGF t ht]
        exact hFU (mem_range_self _)
      have hpc' : p c = x₀ := by
        have h1 : MapClusterPt (p c) (𝓝[<] 1) (p ∘ G) := hcl.continuousAt_comp hpc.continuousAt
        have h2 : Tendsto (p ∘ G) (𝓝[<] 1) (𝓝 x₀) := by
          have : Tendsto γ.extend (𝓝[<] 1) (𝓝 x₀) := by
            simpa using (γ.continuous_extend.tendsto 1).mono_left nhdsWithin_le_nhds
          refine this.congr' ?_
          filter_upwards [hev] with t ht
          rw [Function.comp_apply, hGF t ht, hpF']
        by_contra hne
        have h3 : ClusterPt (p c) (𝓝 x₀) := ClusterPt.mono h1 h2
        exact h3.ne (disjoint_iff.mp (disjoint_nhds_nhds.mpr hne))
      exact hx c (hUc ⟨hcU, hc⟩) hpc'
  have hGc : ContinuousOn G (Iic 1) := by
    have hGo : ContinuousOn G (Iio 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      convert F.continuous using 1
      funext t
      exact hGF t t.2
    intro t ht
    rcases (mem_Iic.mp ht).lt_or_eq with ht | rfl
    · exact (hGo.continuousAt (isOpen_Iio.mem_nhds ht)).continuousWithinAt
    · rw [← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt, hG1]
      exact hlim
  refine ⟨⟨⟨fun t ↦ G t, hGc.comp_continuous continuous_subtype_val fun t ↦ t.2.2⟩, ?_, ?_⟩,
    fun t ↦ ?_, fun t ↦ ?_⟩
  · simpa [hGF 0 one_pos] using hF0
  · simpa using hG1
  · change G t ∈ U
    rcases (show (t : ℝ) ≤ 1 from t.2.2).lt_or_eq with ht | ht
    · rw [hGF t ht]
      exact hFU (mem_range_self _)
    · rw [ht, hG1]
      exact hxU
  · change p (G t) = γ t
    rcases (show (t : ℝ) ≤ 1 from t.2.2).lt_or_eq with ht | ht
    · rw [hGF t ht, hpF', Path.extend_extends']
    · have : t = 1 := Subtype.ext ht
      rw [ht, hG1, hpx, this, γ.target]

end Lift

/-! ### Local path-connectedness -/

section LPC

variable {E X : Type*} [TopologicalSpace E] [T2Space E] [MetricSpace X]

omit [T2Space E] in
/-- Over a small ball around `p x`, every point of `E` lies in `U ∪ U₂`, if `p` is proper, `U` an
open neighbourhood of `x` and `U₂` an open set containing the rest of the fibre of `x` (the tube
lemma `IsClosedMap.eventually_nhds_fiber`). -/
private lemma exists_preimage_ball_subset_union {p : E → X} (hp : IsProperMap p) {x : E}
    {U U₂ : Set E} (hU : IsOpen U) (hU₂ : IsOpen U₂) (hxU : x ∈ U)
    (hfib : p ⁻¹' {p x} \ {x} ⊆ U₂) : ∃ r > 0, p ⁻¹' ball (p x) r ⊆ U ∪ U₂ := by
  have h := hp.isClosedMap.eventually_nhds_fiber (p := (· ∈ U ∪ U₂)) (p x) fun x₀ hx₀ ↦ by
    by_cases h : x₀ = x
    · subst h; exact (hU.union hU₂).mem_nhds (Or.inl hxU)
    · exact (hU.union hU₂).mem_nhds (Or.inr (hfib ⟨hx₀, h⟩))
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp h
  exact ⟨r, hr, fun y hy ↦ hrs hy y rfl⟩

/-- The local step of `IsCoveringMapOn.locallyPathConnectedSpace`: near `x`, every point lying over
`W` is joined to `x` inside a given neighbourhood `N`. -/
theorem exists_mem_nhds_joinedIn {p : E → X} {W : Set X} (hcov : IsCoveringMapOn p W)
    (hp : IsProperMap p) (hfin : ∀ z, (p ⁻¹' {z}).Finite)
    (hW : ∀ (z₀ a : X) (r : ℝ), a ∈ ball z₀ r → a ∈ W →
      ∃ γ : Path a z₀, (∀ t, γ t ∈ ball z₀ r) ∧ ∀ t : unitInterval, t ≠ 1 → γ t ∈ W)
    (x : E) {N : Set E} (hN : N ∈ 𝓝 x) :
    ∃ V ∈ 𝓝 x, V ⊆ N ∧ ∀ y ∈ V, p y ∈ W → JoinedIn N y x := by
  set z₀ := p x
  -- separate `x` from the rest of its fibre
  have hfib : IsCompact (p ⁻¹' {z₀} \ {x}) := ((hfin z₀).sdiff).isCompact
  obtain ⟨U₁, U₂, hU₁, hU₂, hxU₁, hfU₂, hdisj⟩ := SeparatedNhds.of_isCompact_isCompact
    isCompact_singleton hfib (disjoint_singleton_left.mpr fun h ↦ h.2 rfl)
  set U := U₁ ∩ interior N
  have hUo : IsOpen U := hU₁.inter isOpen_interior
  have hxU : x ∈ U := ⟨hxU₁ rfl, mem_interior_iff_mem_nhds.mpr hN⟩
  -- over a small ball around `z₀`, everything lies in `U ∪ U₂` (properness)
  obtain ⟨r, hr, hrU⟩ := exists_preimage_ball_subset_union hp hUo hU₂ hxU hfU₂
  refine ⟨U ∩ p ⁻¹' ball z₀ r, inter_mem (hUo.mem_nhds hxU)
    (hp.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds z₀ hr)),
    inter_subset_left.trans (inter_subset_right.trans interior_subset), fun y ⟨hyU, hyr⟩ hyW ↦ ?_⟩
  obtain ⟨γ, hγr, hγW⟩ := hW z₀ (p y) r hyr hyW
  have hUc : closure U ∩ p ⁻¹' range γ ⊆ U := by
    rintro u ⟨hu, t, ht⟩
    rcases hrU (show p u ∈ ball z₀ r from ht ▸ hγr t) with hu' | hu'
    · exact hu'
    · exact absurd hu'
        (((hdisj.mono_left inter_subset_left).closure_left hU₂).notMem_of_mem_left hu)
  have hx' (x' : E) (hx'U : x' ∈ U) (hx'z : p x' = z₀) : x' = x := by
    by_contra hne
    exact hdisj.notMem_of_mem_left hx'U.1 (hfU₂ ⟨hx'z, hne⟩)
  obtain ⟨Γ, hΓU, -⟩ := hcov.exists_path_lift hp.continuous γ hγW
    (hp.isCompact_preimage (isCompact_range γ.continuous)) hUo hUc hyU rfl hxU rfl hx'
  exact ⟨Γ, fun t ↦ interior_subset (hΓU t).2⟩

/-- A space `E` with a proper map `p : E → X` with finite fibres to a metric space, which is a
covering over a subset `W` with dense preimage, is locally path-connected, provided every point of
a ball lying in `W` is joined to the centre by a path in the ball which stays in `W` before its
endpoint. -/
theorem locallyPathConnectedSpace {p : E → X} {W : Set X} (hcov : IsCoveringMapOn p W)
    (hp : IsProperMap p) (hfin : ∀ z, (p ⁻¹' {z}).Finite) (hdense : Dense (p ⁻¹' W))
    (hW : ∀ (z₀ a : X) (r : ℝ), a ∈ ball z₀ r → a ∈ W →
      ∃ γ : Path a z₀, (∀ t, γ t ∈ ball z₀ r) ∧ ∀ t : unitInterval, t ≠ 1 → γ t ∈ W) :
    LocallyPathConnectedSpace E := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x u hu hxu
  obtain ⟨V, hV, hVu, hVj⟩ := hcov.exists_mem_nhds_joinedIn hp hfin hW x (hu.mem_nhds hxu)
  refine mem_of_superset (interior_mem_nhds.mpr hV) fun y hy ↦ ?_
  obtain ⟨V', hV', hV'V, hV'j⟩ := hcov.exists_mem_nhds_joinedIn hp hfin hW y
    (isOpen_interior.mem_nhds hy)
  obtain ⟨y', hy'W, hy'V'⟩ := hdense.inter_nhds_nonempty hV'
  have h1 : JoinedIn u y' y := (hV'j y' hy'V' hy'W).mono (interior_subset.trans hVu)
  have h2 : JoinedIn u y' x := hVj y' (interior_subset (hV'V hy'V')) hy'W
  exact h2.symm.trans h1

omit [T2Space E] in
/-- Variant of `exists_preimage_ball_subset_union` for the radial contraction below: if `x` is
separated from the rest of its fibre by `U₁`, `U₂`, then points of `U₁` over small balls around
`p x` lie in any given neighbourhood `N` of `x`. -/
private lemma exists_ball_mem_of_separated {p : E → X} (hp : IsProperMap p) {x : E}
    {U₁ U₂ : Set E} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hxU₁ : x ∈ U₁)
    (hfU₂ : p ⁻¹' {p x} \ {x} ⊆ U₂) (hdisj : Disjoint U₁ U₂) {N : Set E} (hN : N ∈ 𝓝 x) :
    ∃ ρ > 0, ∀ y ∈ U₁, p y ∈ ball (p x) ρ → y ∈ N := by
  obtain ⟨ρ, hρ, hρU⟩ := exists_preimage_ball_subset_union hp (hU₁.inter isOpen_interior) hU₂
    ⟨hxU₁, mem_interior_iff_mem_nhds.mpr hN⟩ hfU₂
  refine ⟨ρ, hρ, fun y hy hyρ ↦ ?_⟩
  rcases hρU hyρ with hy' | hy'
  · exact interior_subset hy'.2
  · exact (hdisj.notMem_of_mem_left hy hy').elim

end LPC

/-! ### Contracting a covering of a punctured ball -/

section Contraction

variable {E X : Type*} [TopologicalSpace E] [T2Space E] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Radial contraction: let `π : E → X` be a covering over the punctured ball `B(z₀, r) ∖ {z₀}` of a
real normed space, and `V ⊆ π⁻¹(B(z₀, r))` an open set, closed in `π⁻¹(B(z₀, r))`, whose only point
over `z₀` is `x`, such that points of `V` over small balls around `z₀` are close to `x`. Then `V`
contracts onto `x` relative to `x`: lift the radial homotopy `z ↦ z₀ + (1 - s)(z - z₀)` on
`s ∈ [0, 1)` and send `s = 1` to `x`. -/
theorem nonempty_homotopyRel_id_const {π : E → X} {z₀ : X} {r : ℝ}
    (hcov : IsCoveringMapOn π (ball z₀ r \ {z₀})) (hπ : Continuous π) {V : Set E} (hVo : IsOpen V)
    (hVb : V ⊆ π ⁻¹' ball z₀ r) (hVc : closure V ∩ π ⁻¹' ball z₀ r ⊆ V) {x : E} (hxV : x ∈ V)
    (hx : ∀ y ∈ V, π y = z₀ ↔ y = x)
    (hshrink : ∀ N ∈ 𝓝 x, ∃ ρ > 0, ∀ y ∈ V, π y ∈ ball z₀ ρ → y ∈ N) :
    Nonempty ((ContinuousMap.id V).HomotopyRel (ContinuousMap.const V ⟨x, hxV⟩)
      {⟨x, hxV⟩}) := by
  classical
  set D := ball z₀ r \ {z₀}
  have cov := hcov.isCoveringMap_restrictPreimage
  have hπx : π x = z₀ := (hx x hxV).mpr rfl
  -- the radial homotopy on `D`, parametrized by `(y, s)`, `y ∈ V ∖ {x}`, `s ∈ [0, 1)`
  have hmemD (y : {y : E // y ∈ V ∧ y ≠ x}) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
      z₀ + c • (π y.1 - z₀) ∈ D := by
    have hyz : π y.1 ≠ z₀ := fun h ↦ y.2.2 ((hx y.1 y.2.1).mp h)
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hc0]
      calc c * ‖π y.1 - z₀‖ ≤ 1 * ‖π y.1 - z₀‖ := by gcongr
        _ = dist (π y.1) z₀ := by rw [one_mul, dist_eq_norm]
        _ < r := hVb y.2.1
    · rw [mem_singleton_iff, add_eq_left, smul_eq_zero]
      exact not_or.mpr ⟨hc0.ne', sub_ne_zero.mpr hyz⟩
  have hts (τ : unitInterval) (s : Ico (0 : ℝ) 1) : 0 < 1 - (τ : ℝ) * s := by
    have : (τ : ℝ) * s < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left s.2.1 τ.2.2) s.2.2
    linarith
  have hts' (τ : unitInterval) (s : Ico (0 : ℝ) 1) : 1 - (τ : ℝ) * s ≤ 1 := by
    have : 0 ≤ (τ : ℝ) * s := mul_nonneg τ.2.1 s.2.1
    linarith
  let K : C(unitInterval × ({y : E // y ∈ V ∧ y ≠ x} × Ico (0 : ℝ) 1), D) :=
    ⟨fun p ↦ ⟨z₀ + (1 - (p.1 : ℝ) * p.2.2) • (π p.2.1.1 - z₀),
      hmemD p.2.1 (hts p.1 p.2.2) (hts' p.1 p.2.2)⟩, by fun_prop⟩
  let f : C({y : E // y ∈ V ∧ y ≠ x} × Ico (0 : ℝ) 1, π ⁻¹' D) := ⟨fun a ↦ ⟨a.1.1, by
    simpa using hmemD a.1 one_pos le_rfl⟩, by fun_prop⟩
  have hK0 (a : {y : E // y ∈ V ∧ y ≠ x} × Ico (0 : ℝ) 1) :
      K (0, a) = D.restrictPreimage π (f a) := by
    apply Subtype.ext
    simp [K, f]
  let L := cov.liftHomotopy K f hK0
  have hL (τ : unitInterval) (a : {y : E // y ∈ V ∧ y ≠ x} × Ico (0 : ℝ) 1) :
      π (L (τ, a)).1 = z₀ + (1 - (τ : ℝ) * a.2) • (π a.1.1 - z₀) :=
    congrArg Subtype.val (congrFun (cov.liftHomotopy_lifts K f hK0) (τ, a))
  have hL0 (a : {y : E // y ∈ V ∧ y ≠ x} × Ico (0 : ℝ) 1) : (L (0, a)).1 = a.1.1 :=
    congrArg Subtype.val (cov.liftHomotopy_zero K f hK0 a)
  -- the end of the lifted radial path
  let G : {y : E // y ∈ V ∧ y ≠ x} × Ico (0 : ℝ) 1 → E := fun a ↦ (L (1, a)).1
  have hGc : Continuous G := continuous_subtype_val.comp (L.continuous.comp (by fun_prop))
  have hGπ (a : {y : E // y ∈ V ∧ y ≠ x} × Ico (0 : ℝ) 1) :
      π (G a) = z₀ + (1 - (a.2 : ℝ)) • (π a.1.1 - z₀) := by
    simpa using hL 1 a
  have hGV (a : {y : E // y ∈ V ∧ y ≠ x} × Ico (0 : ℝ) 1) : G a ∈ V := by
    have hc : Continuous fun τ : unitInterval ↦ (L (τ, a)).1 :=
      continuous_subtype_val.comp (L.continuous.comp (by fun_prop))
    have hsub := (isPreconnected_range hc).subset_of_closure_inter_subset hVo
      ⟨a.1.1, ⟨0, hL0 a⟩, a.1.2.1⟩ (by
        rintro _ ⟨hcl, τ, rfl⟩
        exact hVc ⟨hcl, (L (τ, a)).2.1⟩)
    exact hsub ⟨1, rfl⟩
  have hG0 (y : {y : E // y ∈ V ∧ y ≠ x}) (h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1) :
      G (y, ⟨0, h0⟩) = y.1 := by
    have := cov.const_of_comp (g := fun τ : unitInterval ↦ L (τ, (y, ⟨0, h0⟩)))
      (L.continuous.comp (by fun_prop)) (fun τ τ' ↦ by
        apply Subtype.ext
        change π (L (τ, (y, ⟨0, h0⟩))).1 = π (L (τ', (y, ⟨0, h0⟩))).1
        rw [hL, hL]
        simp) 1 0
    change (L (1, (y, ⟨0, h0⟩))).1 = y.1
    rw [this, hL0]
  -- the contraction: `G` off `x` and for `s < 1`, and `x` elsewhere
  let F : unitInterval × V → V := fun p ↦
    if h : (p.2 : E) ≠ x ∧ (p.1 : ℝ) < 1 then
      ⟨G (⟨p.2, p.2.2, h.1⟩, ⟨p.1, p.1.2.1, h.2⟩), hGV _⟩
    else ⟨x, hxV⟩
  have hFgood (p : unitInterval × V) (h : (p.2 : E) ≠ x ∧ (p.1 : ℝ) < 1) :
      F p = ⟨G (⟨p.2, p.2.2, h.1⟩, ⟨p.1, p.1.2.1, h.2⟩), hGV _⟩ := dite_eq_left h
  have hFbad (p : unitInterval × V) (h : ¬((p.2 : E) ≠ x ∧ (p.1 : ℝ) < 1)) :
      F p = ⟨x, hxV⟩ := dite_eq_right h
  have hO : IsOpen {p : unitInterval × V | (p.2 : E) ≠ x ∧ (p.1 : ℝ) < 1} :=
    (isOpen_ne_fun (continuous_subtype_val.comp continuous_snd) continuous_const).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const)
  have hFc : Continuous F := by
    refine continuous_iff_continuousAt.mpr fun p ↦ ?_
    by_cases h : (p.2 : E) ≠ x ∧ (p.1 : ℝ) < 1
    · refine ContinuousOn.continuousAt ?_ (hO.mem_nhds h)
      rw [continuousOn_iff_continuous_domRestrict]
      have : (Set.domRestrict {p : unitInterval × V | (p.2 : E) ≠ x ∧ (p.1 : ℝ) < 1} F) =
          fun q ↦ ⟨G (⟨q.1.2, q.1.2.2, q.2.1⟩, ⟨q.1.1, q.1.1.2.1, q.2.2⟩), hGV _⟩ := by
        funext q
        exact hFgood q.1 q.2
      rw [this]
      exact (hGc.comp (by fun_prop)).subtype_mk _
    · rw [ContinuousAt, hFbad p h, tendsto_subtype_rng]
      intro N hN
      obtain ⟨ρ, hρ, hρN⟩ := hshrink N hN
      let ψ : unitInterval × V → ℝ := fun q ↦ (1 - (q.1 : ℝ)) * ‖π q.2 - z₀‖
      have hψ : Continuous ψ := by fun_prop
      have hψp : ψ p = 0 := by
        rcases not_and_or.mp h with h1 | h1
        · rw [not_not] at h1
          simp [ψ, h1, hπx]
        · have : (p.1 : ℝ) = 1 := le_antisymm p.1.2.2 (not_lt.mp h1)
          simp [ψ, this]
      have hev : ∀ᶠ q in 𝓝 p, ψ q < ρ := hψ.continuousAt.eventually_lt continuous_const.continuousAt
        (by rw [hψp]; exact hρ)
      refine mem_map.mpr ?_
      filter_upwards [hev] with q hq
      change (F q : E) ∈ N
      by_cases hq' : (q.2 : E) ≠ x ∧ (q.1 : ℝ) < 1
      · rw [hFgood q hq']
        refine hρN _ (hGV _) ?_
        rw [mem_ball, dist_eq_norm, hGπ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hq'.2])]
        exact hq
      · rw [hFbad q hq']
        exact mem_of_mem_nhds hN
  refine ⟨⟨⟨⟨F, hFc⟩, fun y ↦ ?_, fun y ↦ ?_⟩, fun t y hy ↦ ?_⟩⟩
  · change F (0, y) = y
    by_cases hy : (y : E) = x
    · rw [hFbad _ (by simp [hy])]
      exact Subtype.ext hy.symm
    · rw [hFgood _ ⟨hy, by simp⟩]
      exact Subtype.ext (hG0 ⟨y, y.2, hy⟩ _)
  · exact hFbad _ (by simp)
  · rw [mem_singleton_iff] at hy
    subst hy
    exact hFbad _ (by simp)

/-- The radial contraction for a proper map with finite fibres `π : E → X` which is a covering over
a punctured ball `B(z₀, r) ∖ {z₀}`: every point `x` over `z₀` has arbitrarily small open
neighbourhoods `V` contracting onto `x` relative to `x`. -/
theorem exists_nonempty_homotopyRel_id_const {π : E → X} {z₀ : X} {r : ℝ} (hr : 0 < r)
    (hcov : IsCoveringMapOn π (ball z₀ r \ {z₀})) (hp : IsProperMap π)
    (hfin : (π ⁻¹' {z₀}).Finite) {x : E} (hx : π x = z₀) {N : Set E} (hN : N ∈ 𝓝 x) :
    ∃ (V : Set E) (hxV : x ∈ V), IsOpen V ∧ V ⊆ N ∧
      Nonempty ((ContinuousMap.id V).HomotopyRel (ContinuousMap.const V ⟨x, hxV⟩) {⟨x, hxV⟩}) := by
  subst hx
  set z₀ := π x
  have hfib : IsCompact (π ⁻¹' {z₀} \ {x}) := (hfin.sdiff).isCompact
  obtain ⟨U₁, U₂, hU₁, hU₂, hxU₁, hfU₂, hdisj⟩ := SeparatedNhds.of_isCompact_isCompact
    isCompact_singleton hfib (disjoint_singleton_left.mpr fun h ↦ h.2 rfl)
  set U := U₁ ∩ interior N
  have hUo : IsOpen U := hU₁.inter isOpen_interior
  have hxU : x ∈ U := ⟨hxU₁ rfl, mem_interior_iff_mem_nhds.mpr hN⟩
  obtain ⟨r₂, hr₂, hr₂U⟩ := exists_preimage_ball_subset_union hp hUo hU₂ hxU hfU₂
  set ρ := min r r₂
  have hρ : 0 < ρ := lt_min hr hr₂
  set V := U ∩ π ⁻¹' ball z₀ ρ
  have hxV : x ∈ V := ⟨hxU, mem_ball_self hρ⟩
  have hVo : IsOpen V := hUo.inter (isOpen_ball.preimage hp.continuous)
  refine ⟨V, hxV, hVo, inter_subset_left.trans (inter_subset_right.trans interior_subset), ?_⟩
  refine (hcov.mono (sdiff_subset_sdiff_left (ball_subset_ball (min_le_left _ _))))
    |>.nonempty_homotopyRel_id_const hp.continuous hVo inter_subset_right ?_ hxV
    (fun y hy ↦ ⟨fun hyz ↦ ?_, fun h ↦ h ▸ rfl⟩) fun N' hN' ↦ ?_
  · rintro u ⟨hu, hub⟩
    refine ⟨?_, hub⟩
    rcases hr₂U (ball_subset_ball (min_le_right _ _) hub) with hu' | hu'
    · exact hu'
    · exact absurd hu' (((hdisj.mono_left inter_subset_left).closure_left hU₂).notMem_of_mem_left
        (closure_mono inter_subset_left hu))
  · by_contra hne
    exact hdisj.notMem_of_mem_left hy.1.1 (hfU₂ ⟨hyz, hne⟩)
  · obtain ⟨ρ', hρ', h⟩ := exists_ball_mem_of_separated hp hU₁ hU₂ (hxU₁ rfl) hfU₂ hdisj hN'
    exact ⟨ρ', hρ', fun y hy hyρ ↦ h y hy.1.1 hyρ⟩

end Contraction

end IsCoveringMapOn
