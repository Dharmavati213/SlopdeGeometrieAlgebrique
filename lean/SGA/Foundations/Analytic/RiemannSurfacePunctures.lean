/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.PuncturedDiscConnected

/-!
# The ends of a finite covering of `ℂ ∖ S`

Let `S ⊂ ℂ` be finite and `p : E → ℂ ∖ S` a covering map with finite fibres
(`AnalyticGeometry.PuncturedPlaneCovering`). Over a small punctured disc around a puncture
`a ∈ S`, or around `∞`, the covering splits into finitely many connected components, the *ends*
of `E` (`PuncturedPlaneCovering.End`), and each end is a Kummer covering `w ↦ wⁿ` of the
punctured disc (Forster, *Lectures on Riemann surfaces*, 5.10; here
`Complex.exists_homeomorph_powRestrict_of_connectedSpace`):
`PuncturedPlaneCovering.kummer`, with `kummer_pow`. Filling in one point per end gives a compact
Riemann surface, built in `RiemannSurfaceCompactification.lean`.

The punctures are indexed by `Option S` (`none` is `∞`), with the local coordinates
`punctureCoord a z = z - a` and `punctureCoord none z = z⁻¹`
(`AnalyticGeometry.punctureCoord`), and `PuncturedPlaneCovering.radius` is a radius for which
the punctured discs `{z | 0 < |punctureCoord a z| < r}` are pairwise disjoint and avoid `S`.

General facts on covering maps used here: a covering map with finite fibres is closed and
proper (`IsCoveringMap.isClosedMap_of_finite`, `IsCoveringMap.isProperMap_of_finite`), its
restriction to a clopen subset is a covering map (`IsCoveringMap.comp_subtypeVal_of_isClopen`),
and a covering space of a Hausdorff space is Hausdorff (`IsCoveringMap.t2Space`).

## References

* [O. Forster, *Lectures on Riemann Surfaces*, §5 and Theorem 8.4][forster1981]
-/

noncomputable section

open Set Topology Metric Filter

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}

/-- A covering map with finite fibres is a closed map. -/
theorem isClosedMap_of_finite (hf : IsCoveringMap f) (hfin : ∀ x, (f ⁻¹' {x}).Finite) :
    IsClosedMap f := by
  intro C hC
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨-, U, hxU, hU, -, H, hH⟩ := hf x
  have : Finite (f ⁻¹' {x}) := hfin x
  set O : Set U := {u | ∀ i : f ⁻¹' {x}, ((H.symm (u, i) : f ⁻¹' U) : E) ∉ C} with hOdef
  have hO : IsOpen O := by
    rw [hOdef, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => hC.isOpen_compl.preimage (by fun_prop)
  have hxO : (⟨x, hxU⟩ : U) ∈ O := by
    intro i hi
    apply hx
    refine ⟨_, hi, ?_⟩
    have h := hH (H.symm (⟨x, hxU⟩, i))
    rw [Homeomorph.apply_symm_apply] at h
    exact h.symm
  refine Filter.mem_of_superset ((hU.isOpenMap_subtype_val O hO).mem_nhds ⟨_, hxO, rfl⟩) ?_
  rintro _ ⟨u, hu, rfl⟩ ⟨e, heC, hfe⟩
  have heU : e ∈ f ⁻¹' U := by rw [mem_preimage, hfe]; exact u.2
  have h1 : (H ⟨e, heU⟩).1 = u := Subtype.ext (by rw [hH]; exact hfe)
  have h2 : H.symm (u, (H ⟨e, heU⟩).2) = ⟨e, heU⟩ := by
    rw [← h1, Prod.mk.eta, Homeomorph.symm_apply_apply]
  exact hu (H ⟨e, heU⟩).2 (by rw [h2]; exact heC)

/-- A covering map with finite fibres is proper. -/
theorem isProperMap_of_finite (hf : IsCoveringMap f) (hfin : ∀ x, (f ⁻¹' {x}).Finite) :
    IsProperMap f :=
  isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨hf.continuous, hf.isClosedMap_of_finite hfin, fun x => (hfin x).isCompact⟩

/-- A covering space of a Hausdorff space is Hausdorff. -/
theorem t2Space [T2Space X] (hf : IsCoveringMap f) : T2Space E := by
  refine ⟨fun x y hxy => ?_⟩
  by_cases h : f x = f y
  · exact hf.isSeparatedMap x y h hxy
  · obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation h
    exact ⟨f ⁻¹' u, f ⁻¹' v, hu.preimage hf.continuous, hv.preimage hf.continuous, hxu, hyv,
      huv.preimage f⟩

/-- The restriction of a covering map with finite fibres and Hausdorff total space to a clopen
subset is a covering map. -/
theorem comp_subtypeVal_of_isClopen [T2Space E] (hf : IsCoveringMap f)
    (hfin : ∀ x, (f ⁻¹' {x}).Finite) {U : Set E} (hU : IsClopen U) :
    IsCoveringMap (f ∘ (Subtype.val : U → E)) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    ((hf.isClosedMap_of_finite hfin).comp hU.isClosed.isClosedEmbedding_subtypeVal.isClosedMap)
    (fun x _ => ?_) ?_
  · rw [Set.preimage_comp]
    exact (hfin x).preimage Subtype.val_injective.injOn
  · rw [Set.preimage_univ, ← isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    exact hf.isLocalHomeomorph.comp hU.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph

end IsCoveringMap

namespace AnalyticGeometry

/-- The local coordinate at a puncture of `ℂ ∖ S`: `z - a` at `a ∈ S`, `z⁻¹` at `∞` (`none`). -/
def punctureCoord {S : Finset ℂ} : Option S → ℂ → ℂ
  | some a => fun z => z - a
  | none => fun z => z⁻¹

/-- The inverse of `punctureCoord a`: `w + a`, resp. `w⁻¹`. -/
def punctureCoordInv {S : Finset ℂ} : Option S → ℂ → ℂ
  | some a => fun w => w + a
  | none => fun w => w⁻¹

section PunctureCoord

variable {S : Finset ℂ}

@[simp] lemma punctureCoordInv_punctureCoord (a : Option S) (z : ℂ) :
    punctureCoordInv a (punctureCoord a z) = z := by
  cases a <;> simp [punctureCoord, punctureCoordInv]

@[simp] lemma punctureCoord_punctureCoordInv (a : Option S) (w : ℂ) :
    punctureCoord a (punctureCoordInv a w) = w := by
  cases a <;> simp [punctureCoord, punctureCoordInv]

/-- `punctureCoord a` is continuous wherever it does not vanish. -/
lemma continuousAt_punctureCoord (a : Option S) {z : ℂ} (hz : punctureCoord a z ≠ 0) :
    ContinuousAt (punctureCoord a) z := by
  cases a with
  | some a => exact (continuous_id.sub continuous_const).continuousAt
  | none =>
    simp only [punctureCoord, ne_eq, inv_eq_zero] at hz ⊢
    exact continuousAt_inv₀ hz

/-- `punctureCoordInv a` is holomorphic away from `0`. -/
lemma differentiableAt_punctureCoordInv (a : Option S) {w : ℂ} (hw : w ≠ 0) :
    DifferentiableAt ℂ (punctureCoordInv a) w := by
  cases a with
  | some a => exact (differentiableAt_id.add_const _)
  | none => exact differentiableAt_inv hw

/-- The derivative of `punctureCoordInv a` does not vanish away from `0`. -/
lemma hasDerivAt_punctureCoordInv (a : Option S) {w : ℂ} (hw : w ≠ 0) :
    ∃ d : ℂ, d ≠ 0 ∧ HasDerivAt (punctureCoordInv a) d w := by
  cases a with
  | some a => exact ⟨1, one_ne_zero, (hasDerivAt_id w).add_const _⟩
  | none => exact ⟨-(w ^ 2)⁻¹, by simp [hw], hasDerivAt_inv hw⟩

/-- There is a radius `r` for which the punctured discs `{z | 0 < |punctureCoord a z| < r}` around
the punctures are pairwise disjoint and do not meet `S`. -/
theorem exists_puncture_radius (S : Finset ℂ) :
    ∃ r : ℝ, 0 < r ∧
      (∀ a b : Option S, a ≠ b → ∀ z, punctureCoord a z ∈ ball (0 : ℂ) r \ {0} →
        punctureCoord b z ∉ ball (0 : ℂ) r \ {0}) ∧
      ∀ a : Option S, ∀ z, punctureCoord a z ∈ ball (0 : ℂ) r \ {0} → z ∉ S := by
  have h1 : ∀ᶠ r in 𝓝 (0 : ℝ), r < 1 / 2 := eventually_lt_nhds (by norm_num)
  have h2 : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ a b : S, a ≠ b → 2 * r < ‖(a : ℂ) - b‖ := by
    rw [Filter.eventually_all]
    intro a
    rw [Filter.eventually_all]
    intro b
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall fun _ h => (h hab).elim
    · have hpos : 0 < ‖(a : ℂ) - b‖ / 2 :=
        div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hab (Subtype.ext h))) two_pos
      filter_upwards [eventually_lt_nhds hpos] with r hr _
      linarith
  have h3 : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ a : S, r * (‖(a : ℂ)‖ + 2) < 1 := by
    rw [Filter.eventually_all]
    intro a
    have hpos : 0 < 1 / (‖(a : ℂ)‖ + 2) := by positivity
    filter_upwards [eventually_lt_nhds hpos] with r hr
    rwa [lt_div_iff₀ (by positivity)] at hr
  obtain ⟨r, ⟨⟨hr1, hr2⟩, hr3⟩, hr0⟩ :=
    ((h1.and h2).and h3).filter_mono nhdsWithin_le_nhds |>.and self_mem_nhdsWithin |>.exists
      (f := 𝓝[>] (0 : ℝ))
  -- the point at `∞`: `|z| > 1 / r`
  have hinf : ∀ z : ℂ, punctureCoord (S := S) none z ∈ ball (0 : ℂ) r \ {0} → 1 / r < ‖z‖ := by
    intro z hz
    simp only [punctureCoord, Set.mem_sdiff, mem_ball, dist_zero_right, norm_inv,
      mem_singleton_iff, inv_eq_zero] at hz
    have hn := norm_pos_iff.mpr hz.2
    have h := mul_lt_mul_of_pos_right hz.1 hn
    rw [inv_mul_cancel₀ hn.ne'] at h
    rw [div_lt_iff₀ hr0]
    linarith [mul_comm r ‖z‖]
  have hmem : ∀ (a : S) (z : ℂ), punctureCoord (some a) z ∈ ball (0 : ℂ) r \ {0} →
      ‖z - a‖ < r ∧ z ≠ a := by
    intro a z hz
    simp only [punctureCoord, Set.mem_sdiff, mem_ball, dist_zero_right, mem_singleton_iff,
      sub_eq_zero] at hz
    exact hz
  have hbig : ∀ a : S, ‖(a : ℂ)‖ + 1 < 1 / r := by
    intro a
    have := hr3 a
    rw [lt_div_iff₀ hr0]
    nlinarith
  refine ⟨r, hr0, ?_, ?_⟩
  · intro a b hab z hza hzb
    cases a with
    | none =>
      cases b with
      | none => exact hab rfl
      | some b =>
        have h := hinf z hza
        have hb := (hmem b z hzb).1
        have := norm_le_norm_add_norm_sub' z b
        have := hbig b
        linarith
    | some a =>
      cases b with
      | none =>
        have h := hinf z hzb
        have ha := (hmem a z hza).1
        have := norm_le_norm_add_norm_sub' z a
        have := hbig a
        linarith
      | some b =>
        have hab' : a ≠ b := fun h => hab (by rw [h])
        have := hr2 a b hab'
        have ha := (hmem a z hza).1
        have hb := (hmem b z hzb).1
        have : ‖(a : ℂ) - b‖ ≤ ‖z - a‖ + ‖z - b‖ := by
          calc ‖(a : ℂ) - b‖ = ‖(z - b) - (z - a)‖ := by ring_nf
            _ ≤ ‖z - b‖ + ‖z - a‖ := norm_sub_le _ _
            _ = _ := add_comm _ _
        linarith
  · intro a z hz hzS
    cases a with
    | none =>
      have h := hinf z hz
      have := hbig ⟨z, hzS⟩
      simp only at this
      linarith [norm_nonneg z]
    | some a =>
      obtain ⟨ha, hne⟩ := hmem a z hz
      have hza : (⟨z, hzS⟩ : S) ≠ a := fun h => hne (congrArg Subtype.val h)
      have := hr2 ⟨z, hzS⟩ a hza
      simp only at this
      linarith

end PunctureCoord

/-- A covering map with finite fibres of the punctured plane `ℂ ∖ S`, `S` finite. -/
structure PuncturedPlaneCovering (S : Finset ℂ) where
  /-- The total space. -/
  E : Type
  [top : TopologicalSpace E]
  /-- The projection. -/
  p : E → {z : ℂ // z ∉ S}
  isCoveringMap : IsCoveringMap p
  finite_fiber : ∀ z, (p ⁻¹' {z}).Finite

namespace PuncturedPlaneCovering

attribute [instance] top

variable {S : Finset ℂ} (C : PuncturedPlaneCovering S)

/-- The projection `E → ℂ`. -/
def proj (e : C.E) : ℂ := C.p e

lemma proj_notMem (e : C.E) : C.proj e ∉ S := (C.p e).2

lemma continuous_proj : Continuous C.proj :=
  continuous_subtype_val.comp C.isCoveringMap.continuous

instance : T2Space C.E := C.isCoveringMap.t2Space

instance : LocallyPathConnectedSpace C.E := by
  have : LocallyPathConnectedSpace {z : ℂ // z ∉ S} :=
    (S.finite_toSet.isClosed.isOpen_compl : IsOpen ((S : Set ℂ)ᶜ)).locallyPathConnectedSpace
  exact C.isCoveringMap.isLocalHomeomorph.locallyPathConnectedSpace

/-- The radius of the punctured discs around the punctures (`exists_puncture_radius`). -/
def radius (S : Finset ℂ) : ℝ := (exists_puncture_radius S).choose

lemma radius_pos : 0 < radius S := (exists_puncture_radius S).choose_spec.1

lemma punctureCoord_notMem_of_ne {a b : Option S} (hab : a ≠ b) {z : ℂ}
    (hz : punctureCoord a z ∈ ball (0 : ℂ) (radius S) \ {0}) :
    punctureCoord b z ∉ ball (0 : ℂ) (radius S) \ {0} :=
  (exists_puncture_radius S).choose_spec.2.1 a b hab z hz

lemma notMem_of_punctureCoord_mem {a : Option S} {z : ℂ}
    (hz : punctureCoord a z ∈ ball (0 : ℂ) (radius S) \ {0}) : z ∉ S :=
  (exists_puncture_radius S).choose_spec.2.2 a z hz

/-- The punctured disc of radius `radius S`, the base of the ends. -/
abbrev endBase (S : Finset ℂ) : Set ℂ := ball (0 : ℂ) (radius S) \ {0}

/-- The part of `E` over the punctured disc around the puncture `a`. -/
def endNbhd (a : Option S) : Set C.E := {e | punctureCoord a (C.proj e) ∈ endBase S}

lemma isOpen_endNbhd (a : Option S) : IsOpen (C.endNbhd a) := by
  rw [isOpen_iff_mem_nhds]
  intro e he
  have hc : ContinuousAt (fun e => punctureCoord a (C.proj e)) e :=
    (continuousAt_punctureCoord a (fun h => he.2 h)).comp C.continuous_proj.continuousAt
  exact hc.preimage_mem_nhds ((isOpen_ball.sdiff isClosed_singleton).mem_nhds he)

instance (a : Option S) : LocallyPathConnectedSpace (C.endNbhd a) :=
  (C.isOpen_endNbhd a).locallyPathConnectedSpace

/-- The projection of `endNbhd a` to the punctured disc, in the coordinate `punctureCoord a`. -/
def endProj (a : Option S) (e : C.endNbhd a) : endBase S :=
  ⟨punctureCoord a (C.proj e), e.2⟩

/-- The homeomorphism `punctureCoord a` from the punctured disc around `a` in `ℂ ∖ S` to
`endBase S`. -/
def punctureHomeomorph (a : Option S) :
    {z : {z : ℂ // z ∉ S} // punctureCoord a z ∈ endBase S} ≃ₜ endBase S where
  toFun z := ⟨punctureCoord a z.1, z.2⟩
  invFun w := ⟨⟨punctureCoordInv a w, notMem_of_punctureCoord_mem
    (by rw [punctureCoord_punctureCoordInv]; exact w.2)⟩,
    by simp only [punctureCoord_punctureCoordInv]; exact w.2⟩
  left_inv z := by simp
  right_inv w := by simp
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_iff_continuousAt.mpr fun z => ?_) _
    exact ContinuousAt.comp (g := punctureCoord a)
      (f := fun z : {z : {z : ℂ // z ∉ S} // punctureCoord a z ∈ endBase S} => ((z.1 : _) : ℂ))
      (continuousAt_punctureCoord a (fun h => z.2.2 h)) (by fun_prop : Continuous _).continuousAt
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk
      (continuous_iff_continuousAt.mpr fun w => ?_) _) _
    exact (differentiableAt_punctureCoordInv a w.2.2).continuousAt.comp
      continuous_subtype_val.continuousAt

theorem isCoveringMap_endProj (a : Option S) : IsCoveringMap (C.endProj a) := by
  have h := (C.isCoveringMap.restrictPreimage
    {z : {z : ℂ // z ∉ S} | punctureCoord a z ∈ endBase S}).homeomorph_comp
      (punctureHomeomorph a)
  exact h

lemma finite_endProj_fiber (a : Option S) (w : endBase S) :
    (C.endProj a ⁻¹' {w}).Finite := by
  refine ((C.finite_fiber ⟨punctureCoordInv a w, notMem_of_punctureCoord_mem
    (by rw [punctureCoord_punctureCoordInv]; exact w.2)⟩).preimage
      Subtype.val_injective.injOn).subset ?_
  intro e he
  simp only [mem_preimage, mem_singleton_iff, endProj] at he ⊢
  apply Subtype.ext
  simp only
  rw [← he, punctureCoordInv_punctureCoord]
  rfl

/-- The ends of `E`: the connected components of the part of `E` over the punctured disc around
a puncture. -/
def End : Type := Σ a : Option S, ConnectedComponents (C.endNbhd a)

/-- The end `ε`, as a subset of `endNbhd ε.1`. -/
def endSet (ε : C.End) : Set (C.endNbhd ε.1) := ConnectedComponents.mk ⁻¹' {ε.2}

lemma isClopen_endSet (ε : C.End) : IsClopen (C.endSet ε) := by
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe ε.2
  rw [endSet, ← hx, connectedComponents_preimage_singleton]
  exact isClopen_connectedComponent

instance (ε : C.End) : ConnectedSpace (C.endSet ε) := by
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe ε.2
  have : C.endSet ε = connectedComponent x := by
    rw [endSet, ← hx, connectedComponents_preimage_singleton]
  rw [← isConnected_iff_connectedSpace, this]
  exact isConnected_connectedComponent

/-- The projection of an end to the punctured disc. -/
def endProjK (ε : C.End) : C.endSet ε → endBase S := C.endProj ε.1 ∘ Subtype.val

lemma isCoveringMap_endProjK (ε : C.End) : IsCoveringMap (C.endProjK ε) :=
  (C.isCoveringMap_endProj ε.1).comp_subtypeVal_of_isClopen (C.finite_endProj_fiber ε.1)
    (C.isClopen_endSet ε)

lemma exists_kummer (ε : C.End) :
    ∃ (n : ℕ) (_ : n ≠ 0) (φ : C.endSet ε ≃ₜ {w : ℂ // w ^ n ∈ endBase S}),
      ∀ x, Complex.powRestrict (endBase S) n (φ x) = C.endProjK ε x :=
  Complex.exists_homeomorph_powRestrict_of_connectedSpace
    (isOpen_ball.sdiff isClosed_singleton) (fun h => h.2 rfl)
    (Complex.isSimplyConnected_exp_preimage_ball_diff_zero radius_pos)
    (C.isCoveringMap_endProjK ε) fun w => by
      rw [endProjK, Set.preimage_comp]
      exact (C.finite_endProj_fiber ε.1 w).preimage Subtype.val_injective.injOn

/-- The ramification index of the end `ε`. -/
def degree (ε : C.End) : ℕ := (C.exists_kummer ε).choose

lemma degree_ne_zero (ε : C.End) : C.degree ε ≠ 0 := (C.exists_kummer ε).choose_spec.choose

/-- The Kummer coordinate of the end `ε`: `ε ≃ₜ {w | 0 < |wⁿ| < r}` with
`wⁿ = punctureCoord a (p e)`. -/
def kummer (ε : C.End) : C.endSet ε ≃ₜ {w : ℂ // w ^ C.degree ε ∈ endBase S} :=
  (C.exists_kummer ε).choose_spec.choose_spec.choose

lemma kummer_pow (ε : C.End) (x : C.endSet ε) :
    (C.kummer ε x : ℂ) ^ C.degree ε = punctureCoord ε.1 (C.proj x.1.1) :=
  congrArg Subtype.val ((C.exists_kummer ε).choose_spec.choose_spec.choose_spec x)

instance finite_end : Finite C.End := by
  have : ∀ a : Option S, Finite (ConnectedComponents (C.endNbhd a)) := by
    intro a
    set b : endBase S := ⟨(radius S / 2 : ℝ), by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (half_pos radius_pos)]
        exact half_lt_self radius_pos
      · simp only [mem_singleton_iff, Complex.ofReal_eq_zero]
        exact (half_pos radius_pos).ne'⟩ with hb
    have hpt : ∀ c : ConnectedComponents (C.endNbhd a),
        ∃ x : C.endNbhd a, x ∈ C.endSet ⟨a, c⟩ ∧ C.endProj a x = b := by
      intro c
      obtain ⟨w, hw⟩ : ∃ w : ℂ, w ^ C.degree ⟨a, c⟩ = b :=
        ⟨_, Complex.cpow_nat_inv_pow _ (C.degree_ne_zero ⟨a, c⟩)⟩
      set y := (C.kummer ⟨a, c⟩).symm ⟨w, by rw [hw]; exact b.2⟩
      refine ⟨y.1, y.2, Subtype.ext ?_⟩
      have := C.kummer_pow ⟨a, c⟩ y
      rw [Homeomorph.apply_symm_apply] at this
      simp only at this
      rw [← hw, this]
      rfl
    choose x hxK hxb using hpt
    have hinj : Function.Injective x := by
      intro c c' h
      have h1 := hxK c
      have h2 := hxK c'
      rw [h] at h1
      simp only [endSet, mem_preimage, mem_singleton_iff] at h1 h2
      exact h1.symm.trans h2
    have : Finite (C.endProj a ⁻¹' {b}) := C.finite_endProj_fiber a b
    exact Finite.of_injective (fun c => (⟨x c, hxb c⟩ : C.endProj a ⁻¹' {b}))
      fun c c' h => hinj (congrArg Subtype.val h)
  unfold End
  infer_instance

end PuncturedPlaneCovering

end AnalyticGeometry
