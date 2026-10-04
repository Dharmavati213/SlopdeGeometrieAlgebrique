/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.RiemannSurfacePunctures
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Filling in the punctures of a finite covering of `ℂ ∖ S`

Let `p : E → ℂ ∖ S` be a covering map with finite fibres, `S` finite
(`AnalyticGeometry.PuncturedPlaneCovering`). Adding one point for each end of `E`
(`PuncturedPlaneCovering.End`: a connected component of `E` over a small punctured disc around a
puncture `a ∈ S` or around `∞`) gives the space `PuncturedPlaneCovering.Fill`, which is a compact
Riemann surface:

* the topology is the final topology for the inclusion `Fill.ofE : E → Ē` and, for each end `ε`,
  the map `endMap ε` from the disc `{w | |wⁿ| < r}` of the Kummer coordinate of `ε` (`w ↦ ε` at
  `w = 0`); both are open embeddings (`isOpenEmbedding_ofE`, `isOpenEmbedding_endMap`);
* `Ē` is Hausdorff and compact (instances);
* the charts are the sheets of `p` at points of `E` (`eChart`, the chart is `p` itself) and the
  Kummer coordinate `w` at the ends (`endChart`); the coordinate changes are the identity,
  `w ↦ punctureCoordInv a (wⁿ)` and its local inverses (`w = (z - a)^{1/n}`, resp.
  `z^{-1/n}`), which are holomorphic, so `Ē` is a complex manifold (`IsManifold 𝓘(ℂ) ω`).

This is the compact Riemann surface obtained from a finite covering of `ℂ ∖ S` by filling in the
punctures (Forster, *Lectures on Riemann surfaces*, Theorem 8.4, for the analytic continuation of
an algebraic function; here for an arbitrary finite covering, with the Kummer charts of
Forster 5.10).

## References

* [O. Forster, *Lectures on Riemann Surfaces*, 5.10 and 8.4][forster1981]
-/

noncomputable section

open Set Topology Metric Filter
open scoped Manifold ContDiff

namespace AnalyticGeometry

namespace PuncturedPlaneCovering

variable {S : Finset ℂ} (C : PuncturedPlaneCovering S)

/-! ### The Kummer coordinate of an end -/

/-- The disc `{w | |wⁿ| < r}` of the Kummer coordinate of the end `ε`, `n = degree ε`. -/
def endDisc (ε : C.End) : Set ℂ := {w | w ^ C.degree ε ∈ ball (0 : ℂ) (radius S)}

lemma isOpen_endDisc (ε : C.End) : IsOpen (C.endDisc ε) :=
  isOpen_ball.preimage (continuous_pow _)

lemma zero_mem_endDisc (ε : C.End) : (0 : ℂ) ∈ C.endDisc ε := by
  simp [endDisc, zero_pow (C.degree_ne_zero ε), radius_pos]

/-- The point of `E` in the end `ε` with Kummer coordinate `w ≠ 0`. -/
def endPoint (ε : C.End) (w : {w : ℂ // w ^ C.degree ε ∈ endBase S}) : C.E :=
  ((C.kummer ε).symm w).1.1

lemma isOpenEmbedding_endPoint (ε : C.End) : IsOpenEmbedding (C.endPoint ε) :=
  ((C.isOpen_endNbhd ε.1).isOpenEmbedding_subtypeVal.comp
    (C.isClopen_endSet ε).isOpen.isOpenEmbedding_subtypeVal).comp
      (C.kummer ε).symm.isOpenEmbedding

lemma endPoint_mem_endNbhd (ε : C.End) (w : {w : ℂ // w ^ C.degree ε ∈ endBase S}) :
    C.endPoint ε w ∈ C.endNbhd ε.1 :=
  ((C.kummer ε).symm w).1.2

lemma punctureCoord_proj_endPoint (ε : C.End) (w : {w : ℂ // w ^ C.degree ε ∈ endBase S}) :
    punctureCoord ε.1 (C.proj (C.endPoint ε w)) = (w : ℂ) ^ C.degree ε := by
  have := C.kummer_pow ε ((C.kummer ε).symm w)
  rw [Homeomorph.apply_symm_apply] at this
  exact this.symm

lemma proj_endPoint (ε : C.End) (w : {w : ℂ // w ^ C.degree ε ∈ endBase S}) :
    C.proj (C.endPoint ε w) = punctureCoordInv ε.1 ((w : ℂ) ^ C.degree ε) := by
  rw [← punctureCoord_proj_endPoint, punctureCoordInv_punctureCoord]

/-- Every point of `E` over the punctured disc around `a` lies in an end over `a`. -/
lemma exists_endPoint_eq {a : Option S} {x : C.E} (hx : x ∈ C.endNbhd a) :
    ∃ ε : C.End, ε.1 = a ∧ ∃ w, C.endPoint ε w = x := by
  refine ⟨⟨a, ConnectedComponents.mk ⟨x, hx⟩⟩, rfl, C.kummer _ ⟨⟨x, hx⟩, rfl⟩, ?_⟩
  simp [endPoint]

/-- Distinct ends are disjoint. -/
lemma endPoint_ne_endPoint {ε ε' : C.End} (h : ε ≠ ε') (w : {w : ℂ // w ^ C.degree ε ∈ endBase S})
    (w' : {w : ℂ // w ^ C.degree ε' ∈ endBase S}) : C.endPoint ε w ≠ C.endPoint ε' w' := by
  intro heq
  obtain ⟨a, c⟩ := ε
  obtain ⟨a', c'⟩ := ε'
  set y := (C.kummer ⟨a, c⟩).symm w with hy
  set y' := (C.kummer ⟨a', c'⟩).symm w' with hy'
  have heq' : y.1.1 = y'.1.1 := heq
  by_cases haa : a = a'
  · subst haa
    apply h
    have h1 : ConnectedComponents.mk y.1 = c := y.2
    have h2 : ConnectedComponents.mk y'.1 = c' := y'.2
    have : y.1 = y'.1 := Subtype.ext heq'
    rw [← h1, ← h2, this]
  · exact punctureCoord_notMem_of_ne haa y.1.2 (heq' ▸ y'.1.2)

/-- The inclusion of the punctured Kummer disc in the Kummer disc. -/
def inclDisc (ε : C.End) (w : {w : ℂ // w ^ C.degree ε ∈ endBase S}) : C.endDisc ε :=
  ⟨w, w.2.1⟩

lemma isOpenEmbedding_inclDisc (ε : C.End) : IsOpenEmbedding (C.inclDisc ε) := by
  rw [← IsOpenEmbedding.of_comp_iff _ (C.isOpen_endDisc ε).isOpenEmbedding_subtypeVal]
  exact IsOpen.isOpenEmbedding_subtypeVal (s := {w : ℂ | w ^ C.degree ε ∈ endBase S})
    ((isOpen_ball.sdiff isClosed_singleton).preimage (continuous_pow _))

/-! ### The compactification -/

/-- The compactification of `E`: `E` together with one point for each end. -/
inductive Fill (C : PuncturedPlaneCovering S) : Type
  | ofE (e : C.E) : Fill C
  | atEnd (ε : C.End) : Fill C

lemma mem_endBase_of_ne_zero (ε : C.End) {w : ℂ} (hw : w ∈ C.endDisc ε) (h : w ≠ 0) :
    w ^ C.degree ε ∈ endBase S :=
  ⟨hw, fun h' => h (pow_eq_zero_iff (C.degree_ne_zero ε) |>.mp h')⟩

/-- The Kummer disc of the end `ε`, as a neighbourhood of `ε` in `Ē`. -/
def endMap (ε : C.End) (w : C.endDisc ε) : C.Fill :=
  if h : (w : ℂ) = 0 then .atEnd ε else .ofE (C.endPoint ε ⟨w, C.mem_endBase_of_ne_zero ε w.2 h⟩)

lemma endMap_inclDisc (ε : C.End) (w : {w : ℂ // w ^ C.degree ε ∈ endBase S}) :
    C.endMap ε (C.inclDisc ε w) = .ofE (C.endPoint ε w) := by
  have hw : (w : ℂ) ≠ 0 := fun h => w.2.2 (by rw [h, zero_pow (C.degree_ne_zero ε)]; rfl)
  simp [endMap, inclDisc, hw]

lemma endMap_zero (ε : C.End) : C.endMap ε ⟨0, C.zero_mem_endDisc ε⟩ = .atEnd ε := by
  simp [endMap]

lemma endMap_eq_ofE_iff {ε : C.End} {w : C.endDisc ε} {x : C.E} :
    C.endMap ε w = .ofE x ↔ ∃ w', C.inclDisc ε w' = w ∧ C.endPoint ε w' = x := by
  constructor
  · intro h
    by_cases hw : (w : ℂ) = 0
    · simp [endMap, hw] at h
    · refine ⟨⟨w, C.mem_endBase_of_ne_zero ε w.2 hw⟩, rfl, ?_⟩
      simpa [endMap, hw] using h
  · rintro ⟨w', rfl, rfl⟩
    exact C.endMap_inclDisc ε w'

lemma endMap_eq_atEnd_iff {ε ε' : C.End} {w : C.endDisc ε} :
    C.endMap ε w = .atEnd ε' ↔ ε = ε' ∧ (w : ℂ) = 0 := by
  by_cases hw : (w : ℂ) = 0 <;> simp [endMap, hw, eq_comm]

lemma endMap_injective (ε : C.End) : Function.Injective (C.endMap ε) := by
  intro w w' h
  by_cases hw : (w : ℂ) = 0
  · have h' : C.endMap ε w' = .atEnd ε := by rw [← h]; simp [endMap, hw]
    rw [endMap_eq_atEnd_iff] at h'
    exact Subtype.ext (hw.trans h'.2.symm)
  · have h1 : C.endMap ε w = .ofE (C.endPoint ε ⟨w, C.mem_endBase_of_ne_zero ε w.2 hw⟩) := by
      simp [endMap, hw]
    rw [h1, eq_comm, endMap_eq_ofE_iff] at h
    obtain ⟨w'', rfl, h2⟩ := h
    have := (C.isOpenEmbedding_endPoint ε).injective h2
    rw [this]
    rfl

lemma endMap_ne_endMap {ε ε' : C.End} (h : ε ≠ ε') (w : C.endDisc ε) (w' : C.endDisc ε') :
    C.endMap ε w ≠ C.endMap ε' w' := by
  intro heq
  by_cases hw : (w : ℂ) = 0
  · have h' : C.endMap ε' w' = .atEnd ε := by rw [← heq]; simp [endMap, hw]
    exact h ((endMap_eq_atEnd_iff C).mp h').1.symm
  · have h1 : C.endMap ε w = .ofE (C.endPoint ε ⟨w, C.mem_endBase_of_ne_zero ε w.2 hw⟩) := by
      simp [endMap, hw]
    rw [h1, eq_comm, endMap_eq_ofE_iff] at heq
    obtain ⟨w'', -, h2⟩ := heq
    exact C.endPoint_ne_endPoint h _ _ h2.symm

instance : TopologicalSpace C.Fill :=
  TopologicalSpace.coinduced Fill.ofE (inferInstanceAs (TopologicalSpace C.E)) ⊔
    ⨆ ε : C.End, TopologicalSpace.coinduced (C.endMap ε) inferInstance

lemma isOpen_fill_iff {s : Set C.Fill} :
    IsOpen s ↔ IsOpen (Fill.ofE ⁻¹' s) ∧ ∀ ε, IsOpen (C.endMap ε ⁻¹' s) :=
  isOpen_sup.trans (and_congr Iff.rfl isOpen_iSup_iff)

lemma continuous_ofE : Continuous (Fill.ofE : C.E → C.Fill) :=
  continuous_iff_coinduced_le.mpr le_sup_left

lemma continuous_endMap (ε : C.End) : Continuous (C.endMap ε) :=
  continuous_iff_coinduced_le.mpr (le_sup_of_le_right (le_iSup (fun ε =>
    TopologicalSpace.coinduced (C.endMap ε) inferInstance) ε))

lemma ofE_injective : Function.Injective (Fill.ofE : C.E → C.Fill) := fun _ _ h => Fill.ofE.inj h

lemma isOpenEmbedding_ofE : IsOpenEmbedding (Fill.ofE : C.E → C.Fill) := by
  refine .of_continuous_injective_isOpenMap C.continuous_ofE C.ofE_injective
    fun O hO => (C.isOpen_fill_iff).mpr ⟨?_, fun ε => ?_⟩
  · rwa [C.ofE_injective.preimage_image]
  · have : C.endMap ε ⁻¹' (Fill.ofE '' O) = C.inclDisc ε '' (C.endPoint ε ⁻¹' O) := by
      ext w
      simp only [mem_preimage, mem_image]
      constructor
      · rintro ⟨x, hx, hxw⟩
        obtain ⟨w', hw', rfl⟩ := (endMap_eq_ofE_iff C).mp hxw.symm
        exact ⟨w', hx, hw'⟩
      · rintro ⟨w', hw', rfl⟩
        exact ⟨_, hw', (C.endMap_inclDisc ε w').symm⟩
    rw [this]
    exact (C.isOpenEmbedding_inclDisc ε).isOpenMap _
      (hO.preimage (C.isOpenEmbedding_endPoint ε).continuous)

lemma isOpenEmbedding_endMap (ε : C.End) : IsOpenEmbedding (C.endMap ε) := by
  refine .of_continuous_injective_isOpenMap (C.continuous_endMap ε) (C.endMap_injective ε)
    fun W hW => (C.isOpen_fill_iff).mpr ⟨?_, fun ε' => ?_⟩
  · have : Fill.ofE ⁻¹' (C.endMap ε '' W) = C.endPoint ε '' (C.inclDisc ε ⁻¹' W) := by
      ext x
      simp only [mem_preimage, mem_image]
      constructor
      · rintro ⟨w, hw, hwx⟩
        obtain ⟨w', rfl, rfl⟩ := (endMap_eq_ofE_iff C).mp hwx
        exact ⟨w', hw, rfl⟩
      · rintro ⟨w', hw', rfl⟩
        exact ⟨_, hw', C.endMap_inclDisc ε w'⟩
    rw [this]
    exact (C.isOpenEmbedding_endPoint ε).isOpenMap _
      (hW.preimage (C.isOpenEmbedding_inclDisc ε).continuous)
  · by_cases h : ε = ε'
    · subst h
      rwa [(C.endMap_injective ε).preimage_image]
    · convert isOpen_empty
      ext w'
      simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false, not_exists, not_and]
      exact fun w _ hw => C.endMap_ne_endMap h w w' hw

/-! ### `Ē` is a compact Hausdorff space -/

omit C in
/-- A point of `ℂ ∖ S` has a neighbourhood avoiding a small punctured disc around a puncture. -/
lemma exists_nhds_punctureCoord_notMem (a : Option S) {z : ℂ} (hz : z ∉ S) :
    ∃ ρ > 0, ∃ N ∈ 𝓝 z, ∀ z' ∈ N, punctureCoord a z' ∉ ball (0 : ℂ) ρ \ {0} := by
  cases a with
  | some a =>
    have hza : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hz (h ▸ a.2))
    refine ⟨‖z - a‖ / 2, half_pos hza, ball z (‖z - a‖ / 2), ball_mem_nhds _ (half_pos hza),
      fun z' hz' h => ?_⟩
    simp only [punctureCoord, Set.mem_sdiff, mem_ball, dist_zero_right] at h
    rw [mem_ball, dist_eq_norm] at hz'
    have : ‖z - a‖ ≤ ‖z' - z‖ + ‖z' - a‖ := by
      calc ‖z - a‖ = ‖(z' - a) - (z' - z)‖ := by ring_nf
        _ ≤ ‖z' - a‖ + ‖z' - z‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith [h.1]
  | none =>
    refine ⟨(‖z‖ + 1)⁻¹, by positivity, ball z 1, ball_mem_nhds _ one_pos, fun z' hz' h => ?_⟩
    simp only [punctureCoord, Set.mem_sdiff, mem_ball, dist_zero_right, norm_inv,
      mem_singleton_iff, inv_eq_zero] at h
    rw [mem_ball, dist_eq_norm] at hz'
    have h1 : ‖z'‖ < ‖z‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z' z
      linarith
    have h2 := (inv_lt_inv₀ (norm_pos_iff.mpr h.2) (by positivity)).mp h.1
    linarith

instance : T2Space C.Fill := by
  have key : ∀ (e : C.E) (ε : C.End), ∃ u v : Set C.Fill, IsOpen u ∧ IsOpen v ∧
      Fill.ofE e ∈ u ∧ Fill.atEnd ε ∈ v ∧ Disjoint u v := by
    intro e ε
    obtain ⟨ρ, hρ, N, hN, hNρ⟩ := exists_nhds_punctureCoord_notMem ε.1 (C.proj_notMem e)
    obtain ⟨N', hN'N, hN'o, heN'⟩ := _root_.mem_nhds_iff.mp hN
    refine ⟨Fill.ofE '' (C.proj ⁻¹' N'),
      C.endMap ε '' {w | (w : ℂ) ^ C.degree ε ∈ ball (0 : ℂ) ρ},
      C.isOpenEmbedding_ofE.isOpenMap _ (hN'o.preimage C.continuous_proj),
      (C.isOpenEmbedding_endMap ε).isOpenMap _
        (isOpen_ball.preimage ((continuous_pow _).comp continuous_subtype_val)),
      ⟨e, heN', rfl⟩, ⟨⟨0, C.zero_mem_endDisc ε⟩, ?_, C.endMap_zero ε⟩, ?_⟩
    · simp [zero_pow (C.degree_ne_zero ε), hρ]
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨w, hw, hwx⟩
    obtain ⟨w', rfl, rfl⟩ := (endMap_eq_ofE_iff C).mp hwx
    apply hNρ _ (hN'N hx)
    rw [punctureCoord_proj_endPoint]
    exact ⟨hw, w'.2.2⟩
  refine ⟨fun x y hxy => ?_⟩
  rcases x with e | ε <;> rcases y with e' | ε'
  · obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation fun h => hxy (congrArg Fill.ofE h)
    exact ⟨_, _, C.isOpenEmbedding_ofE.isOpenMap _ hu, C.isOpenEmbedding_ofE.isOpenMap _ hv,
      ⟨_, hxu, rfl⟩, ⟨_, hyv, rfl⟩, (Set.disjoint_image_iff C.ofE_injective).mpr huv⟩
  · exact key e ε'
  · obtain ⟨u, v, hu, hv, hu', hv', huv⟩ := key e' ε
    exact ⟨v, u, hv, hu, hv', hu', huv.symm⟩
  · have hne : ε ≠ ε' := fun h => hxy (congrArg Fill.atEnd h)
    refine ⟨range (C.endMap ε), range (C.endMap ε'), (C.isOpenEmbedding_endMap ε).isOpen_range,
      (C.isOpenEmbedding_endMap ε').isOpen_range, ⟨_, C.endMap_zero ε⟩, ⟨_, C.endMap_zero ε'⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨w, rfl⟩ ⟨w', hw'⟩
    exact C.endMap_ne_endMap hne w w' hw'.symm

instance : CompactSpace C.Fill := by
  set ρ := radius S / 2 with hρdef
  have hρ : 0 < ρ := half_pos radius_pos
  have hρr : ρ < radius S := half_lt_self radius_pos
  set K : Set ℂ := closedBall 0 ρ⁻¹ ∩ ⋂ a ∈ S, (ball a ρ)ᶜ with hKdef
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).inter_right (isClosed_biInter fun a _ => isOpen_ball.isClosed_compl)
  have hKS : K ⊆ {z | z ∉ S} := fun z hz hzS =>
    (mem_iInter₂.mp hz.2 z hzS) (mem_ball_self hρ)
  have hnotK : ∀ z, z ∉ S → z ∉ K → ∃ a : Option S, punctureCoord a z ∈ ball (0 : ℂ) ρ \ {0} := by
    intro z hzS hzK
    simp only [hKdef, mem_inter_iff, mem_closedBall, dist_zero_right, mem_iInter, mem_compl_iff,
      mem_ball, not_and_or, not_le, not_forall, not_not] at hzK
    rcases hzK with h | ⟨a, ha, h⟩
    · refine ⟨none, ?_, ?_⟩
      · simp only [punctureCoord, mem_ball, dist_zero_right, norm_inv]
        exact inv_lt_of_inv_lt₀ hρ h
      · simp only [punctureCoord, mem_singleton_iff, inv_eq_zero]
        rintro rfl
        simp at h
        linarith [inv_pos.mpr hρ]
    · refine ⟨some ⟨a, ha⟩, ?_, ?_⟩
      · simpa [punctureCoord, dist_eq_norm] using h
      · simp only [punctureCoord, mem_singleton_iff, sub_eq_zero]
        rintro rfl
        exact hzS ha
  have h1 : IsCompact (C.proj ⁻¹' K) :=
    (C.isCoveringMap.isProperMap_of_finite C.finite_fiber).isCompact_preimage
      (Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by
        rw [Subtype.range_coe_subtype]; exact hKS))
  have h2 : ∀ ε : C.End, IsCompact {w : C.endDisc ε | ‖(w : ℂ) ^ C.degree ε‖ ≤ ρ} := by
    intro ε
    have hc : IsCompact {w : ℂ | ‖w ^ C.degree ε‖ ≤ ρ} := by
      refine Metric.isCompact_of_isClosed_isBounded
        (isClosed_le (continuous_norm.comp (continuous_pow _)) continuous_const)
        (isBounded_closedBall (x := (0 : ℂ)) (r := max 1 ρ) |>.subset fun w hw => ?_)
      rw [mem_closedBall, dist_zero_right]
      by_cases h : ‖w‖ ≤ 1
      · exact h.trans (le_max_left _ _)
      · refine le_trans ?_ (le_max_right _ _)
        have := le_self_pow₀ (le_of_not_ge h) (C.degree_ne_zero ε)
        rw [← norm_pow] at this
        exact this.trans hw
    exact Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      rw [Subtype.range_coe_subtype]
      intro w hw
      simp only [Set.mem_ofPred_eq] at hw
      simp only [endDisc, Set.mem_ofPred_eq, mem_ball, dist_zero_right]
      exact hw.trans_lt hρr)
  have huniv : (univ : Set C.Fill) = Fill.ofE '' (C.proj ⁻¹' K) ∪
      ⋃ ε, C.endMap ε '' {w : C.endDisc ε | ‖(w : ℂ) ^ C.degree ε‖ ≤ ρ} := by
    refine (eq_univ_of_forall fun x => ?_).symm
    rcases x with e | ε
    · by_cases he : C.proj e ∈ K
      · exact Or.inl ⟨e, he, rfl⟩
      · obtain ⟨a, ha⟩ := hnotK _ (C.proj_notMem e) he
        have hmem : e ∈ C.endNbhd a := ⟨ball_subset_ball hρr.le ha.1, ha.2⟩
        obtain ⟨ε, rfl, w, rfl⟩ := C.exists_endPoint_eq hmem
        refine Or.inr (mem_iUnion.mpr ⟨ε, C.inclDisc ε w, ?_, C.endMap_inclDisc ε w⟩)
        have := C.punctureCoord_proj_endPoint ε w
        simp only [Set.mem_ofPred_eq, inclDisc]
        rw [← this]
        have := ha.1
        rw [mem_ball, dist_zero_right] at this
        exact this.le
    · refine Or.inr (mem_iUnion.mpr ⟨ε, ⟨0, C.zero_mem_endDisc ε⟩, ?_, C.endMap_zero ε⟩)
      simp [zero_pow (C.degree_ne_zero ε), hρ.le]
  refine ⟨?_⟩
  rw [huniv]
  exact (h1.image C.continuous_ofE).union
    (isCompact_iUnion fun ε => (h2 ε).image (C.continuous_endMap ε))

/-! ### Charts -/

/-- A sheet of `p` through `e`: an open partial homeomorphism `E → ℂ ∖ S` which is `p`. -/
def sheet (e : C.E) : OpenPartialHomeomorph C.E {z : ℂ // z ∉ S} :=
  (C.isCoveringMap.isLocalHomeomorph e).choose

lemma mem_sheet_source (e : C.E) : e ∈ (C.sheet e).source :=
  (C.isCoveringMap.isLocalHomeomorph e).choose_spec.1

lemma coe_sheet (e : C.E) : ⇑(C.sheet e) = C.p :=
  (C.isCoveringMap.isLocalHomeomorph e).choose_spec.2.symm

omit C in
lemma isOpenEmbedding_val_compl : IsOpenEmbedding (Subtype.val : {z : ℂ // z ∉ S} → ℂ) :=
  IsOpen.isOpenEmbedding_subtypeVal (s := {z : ℂ | z ∉ S}) S.finite_toSet.isClosed.isOpen_compl

/-- The chart of `Ē` at a point `e` of `E`: the projection `p` on a sheet through `e`. -/
def eChart (e : C.E) : OpenPartialHomeomorph C.Fill ℂ :=
  haveI : Nonempty C.E := ⟨e⟩
  haveI : Nonempty {z : ℂ // z ∉ S} := ⟨C.p e⟩
  ((C.isOpenEmbedding_ofE.toOpenPartialHomeomorph Fill.ofE).symm.trans (C.sheet e)).trans
    (isOpenEmbedding_val_compl.toOpenPartialHomeomorph Subtype.val)

@[simp] lemma eChart_apply_ofE (e y : C.E) : C.eChart e (Fill.ofE y) = C.proj y := by
  have : Nonempty C.E := ⟨e⟩
  simp only [eChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv, IsOpenEmbedding.toOpenPartialHomeomorph_apply,
    C.coe_sheet e, proj]

lemma mem_eChart_source_iff (e : C.E) (x : C.Fill) :
    x ∈ (C.eChart e).source ↔ ∃ y ∈ (C.sheet e).source, x = Fill.ofE y := by
  have : Nonempty C.E := ⟨e⟩
  simp only [eChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, IsOpenEmbedding.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ, mem_inter_iff, mem_range, mem_preimage]
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_left_inv] at hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    rwa [IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

lemma ofE_mem_eChart_source (e : C.E) : Fill.ofE e ∈ (C.eChart e).source :=
  (C.mem_eChart_source_iff e _).mpr ⟨e, C.mem_sheet_source e, rfl⟩

lemma atEnd_notMem_eChart_source (e : C.E) (ε : C.End) : Fill.atEnd ε ∉ (C.eChart e).source := by
  rw [mem_eChart_source_iff]
  rintro ⟨y, -, h⟩
  cases h

lemma mem_eChart_target_iff (e : C.E) (z : ℂ) :
    z ∈ (C.eChart e).target ↔ ∃ hz : z ∉ S, (⟨z, hz⟩ : {z : ℂ // z ∉ S}) ∈ (C.sheet e).target := by
  have : Nonempty C.E := ⟨e⟩
  have : Nonempty {z : ℂ // z ∉ S} := ⟨C.p e⟩
  simp only [eChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, IsOpenEmbedding.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ, mem_inter_iff, mem_range, mem_preimage]
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_left_inv] at hy
    exact ⟨y.2, hy⟩
  · rintro ⟨hz, hy⟩
    refine ⟨⟨⟨z, hz⟩, rfl⟩, ?_⟩
    rw [show z = ((⟨z, hz⟩ : {z : ℂ // z ∉ S}) : ℂ) from rfl,
      IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
    exact hy

lemma eChart_symm_apply (e : C.E) {z : ℂ} (hz : z ∉ S) :
    (C.eChart e).symm z = Fill.ofE ((C.sheet e).symm ⟨z, hz⟩) := by
  have : Nonempty C.E := ⟨e⟩
  have : Nonempty {z : ℂ // z ∉ S} := ⟨C.p e⟩
  simp only [eChart, OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
    Function.comp_apply, IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  exact congrArg _ (congrArg _ (isOpenEmbedding_val_compl.toOpenPartialHomeomorph_left_inv
    (f := (Subtype.val : {z : ℂ // z ∉ S} → ℂ)) (x := ⟨z, hz⟩)))

/-- The chart of `Ē` at an end `ε`: the Kummer coordinate. -/
def endChart (ε : C.End) : OpenPartialHomeomorph C.Fill ℂ :=
  haveI : Nonempty (C.endDisc ε) := ⟨⟨0, C.zero_mem_endDisc ε⟩⟩
  ((C.isOpenEmbedding_endMap ε).toOpenPartialHomeomorph (C.endMap ε)).symm.trans
    ((C.isOpen_endDisc ε).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val)

@[simp] lemma endChart_apply_endMap (ε : C.End) (w : C.endDisc ε) :
    C.endChart ε (C.endMap ε w) = w := by
  have : Nonempty (C.endDisc ε) := ⟨⟨0, C.zero_mem_endDisc ε⟩⟩
  simp only [endChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv, IsOpenEmbedding.toOpenPartialHomeomorph_apply]

lemma endChart_source (ε : C.End) : (C.endChart ε).source = range (C.endMap ε) := by
  have : Nonempty (C.endDisc ε) := ⟨⟨0, C.zero_mem_endDisc ε⟩⟩
  simp only [endChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, IsOpenEmbedding.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ]

lemma endChart_target (ε : C.End) : (C.endChart ε).target = C.endDisc ε := by
  have : Nonempty (C.endDisc ε) := ⟨⟨0, C.zero_mem_endDisc ε⟩⟩
  ext z
  simp only [endChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, IsOpenEmbedding.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ, mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    exact w.2
  · intro hz
    exact ⟨⟨z, hz⟩, rfl⟩

lemma endChart_symm_apply (ε : C.End) {z : ℂ} (hz : z ∈ C.endDisc ε) :
    (C.endChart ε).symm z = C.endMap ε ⟨z, hz⟩ := by
  have : Nonempty (C.endDisc ε) := ⟨⟨0, C.zero_mem_endDisc ε⟩⟩
  simp only [endChart, OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
    Function.comp_apply, IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  exact congrArg _ ((C.isOpen_endDisc ε).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv
    (f := (Subtype.val : C.endDisc ε → ℂ)) (x := ⟨z, hz⟩))

/-- The charts of `Ē`. -/
def fillChart : C.Fill → OpenPartialHomeomorph C.Fill ℂ
  | .ofE e => C.eChart e
  | .atEnd ε => C.endChart ε

instance : ChartedSpace ℂ C.Fill where
  atlas := range C.fillChart
  chartAt := C.fillChart
  mem_chart_source x := by
    cases x with
    | ofE e => exact C.ofE_mem_eChart_source e
    | atEnd ε =>
      change _ ∈ (C.endChart ε).source
      rw [endChart_source]
      exact ⟨_, C.endMap_zero ε⟩
  chart_mem_atlas x := mem_range_self x

lemma chartAt_ofE (e : C.E) : chartAt ℂ (Fill.ofE e : C.Fill) = C.eChart e := rfl

lemma chartAt_atEnd (ε : C.End) : chartAt ℂ (Fill.atEnd ε : C.Fill) = C.endChart ε := rfl

/-! ### Holomorphic coordinate changes -/

/-- Two sheet charts differ by the identity. -/
lemma eChart_trans_eChart_apply (e e' : C.E) {z : ℂ}
    (hz : z ∈ ((C.eChart e).symm.trans (C.eChart e')).source) :
    ((C.eChart e).symm.trans (C.eChart e')) z = z := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
  obtain ⟨hzS, hzt⟩ := (C.mem_eChart_target_iff e z).mp hz.1
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, C.eChart_symm_apply e hzS,
    eChart_apply_ofE, proj]
  have := (C.sheet e).right_inv hzt
  rw [C.coe_sheet] at this
  rw [this]

/-- From a sheet chart to a Kummer chart: `w` with `punctureCoordInv a (wⁿ) = z`. -/
lemma eChart_trans_endChart_spec (e : C.E) (ε : C.End) {z : ℂ}
    (hz : z ∈ ((C.eChart e).symm.trans (C.endChart ε)).source) :
    ((C.eChart e).symm.trans (C.endChart ε)) z ≠ 0 ∧
      punctureCoordInv ε.1 (((C.eChart e).symm.trans (C.endChart ε)) z ^ C.degree ε) = z := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
  obtain ⟨hzS, hzt⟩ := (C.mem_eChart_target_iff e z).mp hz.1
  have h2 := hz.2
  rw [mem_preimage, endChart_source, C.eChart_symm_apply e hzS] at h2
  obtain ⟨w, hw⟩ := h2
  obtain ⟨w', rfl, hw'⟩ := (endMap_eq_ofE_iff C).mp hw
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, C.eChart_symm_apply e hzS,
    ← hw, endChart_apply_endMap]
  refine ⟨fun h => w'.2.2 ?_, ?_⟩
  · change (w' : ℂ) = 0 at h
    rw [h, zero_pow (C.degree_ne_zero ε)]
    rfl
  · change punctureCoordInv ε.1 ((w' : ℂ) ^ C.degree ε) = z
    rw [← proj_endPoint, hw', proj, ← C.coe_sheet e, (C.sheet e).right_inv hzt]

lemma differentiableAt_eChart_trans_endChart (e : C.E) (ε : C.End) {z : ℂ}
    (hz : z ∈ ((C.eChart e).symm.trans (C.endChart ε)).source) :
    DifferentiableAt ℂ ((C.eChart e).symm.trans (C.endChart ε)) z := by
  set τ := (C.eChart e).symm.trans (C.endChart ε) with hτ
  have hsrc : τ.source ∈ 𝓝 z := τ.open_source.mem_nhds hz
  obtain ⟨hne, -⟩ := C.eChart_trans_endChart_spec e ε hz
  obtain ⟨d, hd, hderiv⟩ := hasDerivAt_punctureCoordInv ε.1 (pow_ne_zero (C.degree ε) hne)
  have hf : HasDerivAt (fun w => punctureCoordInv ε.1 (w ^ C.degree ε))
      (d * (C.degree ε * τ z ^ (C.degree ε - 1))) (τ z) :=
    hderiv.comp (τ z) (hasDerivAt_pow _ _)
  refine (HasDerivAt.of_local_left_inverse (τ.continuousAt hz) hf ?_ ?_).differentiableAt
  · exact mul_ne_zero hd (mul_ne_zero (Nat.cast_ne_zero.mpr (C.degree_ne_zero ε))
      (pow_ne_zero _ hne))
  · filter_upwards [hsrc] with y hy using (C.eChart_trans_endChart_spec e ε hy).2

/-- From a Kummer chart to a sheet chart: `w ↦ punctureCoordInv a (wⁿ)`. -/
lemma endChart_trans_eChart_spec (ε : C.End) (e : C.E) {z : ℂ}
    (hz : z ∈ ((C.endChart ε).symm.trans (C.eChart e)).source) :
    z ≠ 0 ∧ ((C.endChart ε).symm.trans (C.eChart e)) z = punctureCoordInv ε.1 (z ^ C.degree ε) := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, endChart_target]
    at hz
  have h2 := hz.2
  rw [mem_preimage, C.endChart_symm_apply ε hz.1, mem_eChart_source_iff] at h2
  obtain ⟨y, -, hy⟩ := h2
  obtain ⟨w', hw'1, rfl⟩ := (endMap_eq_ofE_iff C).mp hy
  have hz' : z = w' := (congrArg Subtype.val hw'1).symm
  refine ⟨?_, ?_⟩
  · rw [hz']
    intro h
    apply w'.2.2
    rw [h, zero_pow (C.degree_ne_zero ε)]
    rfl
  · rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, C.endChart_symm_apply ε hz.1, hy,
      eChart_apply_ofE, proj_endPoint, ← hz']

lemma differentiableAt_endChart_trans_eChart (ε : C.End) (e : C.E) {z : ℂ}
    (hz : z ∈ ((C.endChart ε).symm.trans (C.eChart e)).source) :
    DifferentiableAt ℂ ((C.endChart ε).symm.trans (C.eChart e)) z := by
  set τ := (C.endChart ε).symm.trans (C.eChart e) with hτ
  have hsrc : τ.source ∈ 𝓝 z := τ.open_source.mem_nhds hz
  obtain ⟨hne, -⟩ := C.endChart_trans_eChart_spec ε e hz
  refine DifferentiableAt.congr_of_eventuallyEq
    (f := fun w => punctureCoordInv ε.1 (w ^ C.degree ε)) ?_ ?_
  · exact (differentiableAt_punctureCoordInv ε.1 (pow_ne_zero _ hne)).comp z
      (differentiableAt_pow _)
  · filter_upwards [hsrc] with y hy using (C.endChart_trans_eChart_spec ε e hy).2

/-- Two Kummer charts with overlapping domains are the same, and differ by the identity. -/
lemma endChart_trans_endChart_apply (ε ε' : C.End) {z : ℂ}
    (hz : z ∈ ((C.endChart ε).symm.trans (C.endChart ε')).source) :
    ((C.endChart ε).symm.trans (C.endChart ε')) z = z := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, endChart_target]
    at hz
  obtain ⟨hz1, h2⟩ := hz
  rw [mem_preimage, C.endChart_symm_apply ε hz1, endChart_source] at h2
  obtain ⟨w, hw⟩ := h2
  have hεε : ε = ε' := by
    by_contra h
    exact C.endMap_ne_endMap h _ _ hw.symm
  subst hεε
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, C.endChart_symm_apply ε hz1,
    endChart_apply_endMap]

/-- `Ē` is a compact Riemann surface. -/
instance : IsManifold 𝓘(ℂ) ω C.Fill := by
  refine isManifold_of_contDiffOn 𝓘(ℂ) ω C.Fill fun c c' hc hc' => ?_
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id_eq,
    inter_univ, Function.id_comp, Function.comp_id]
  refine DifferentiableOn.contDiffOn (fun z hz => DifferentiableAt.differentiableWithinAt ?_)
    (c.symm.trans c').open_source
  have hsrc : (c.symm.trans c').source ∈ 𝓝 z := (c.symm.trans c').open_source.mem_nhds hz
  obtain ⟨x, rfl⟩ := hc
  obtain ⟨x', rfl⟩ := hc'
  cases x with
  | ofE e =>
    cases x' with
    | ofE e' =>
      exact differentiableAt_id.congr_of_eventuallyEq
        (by filter_upwards [hsrc] with y hy using C.eChart_trans_eChart_apply e e' hy)
    | atEnd ε' => exact C.differentiableAt_eChart_trans_endChart e ε' hz
  | atEnd ε =>
    cases x' with
    | ofE e' => exact C.differentiableAt_endChart_trans_eChart ε e' hz
    | atEnd ε' =>
      exact differentiableAt_id.congr_of_eventuallyEq
        (by filter_upwards [hsrc] with y hy using C.endChart_trans_endChart_apply ε ε' hy)

end PuncturedPlaneCovering

end AnalyticGeometry
