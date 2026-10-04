/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Homotopy.LocallyContractible
import Mathlib.Topology.LocallyFinite
import SGA.Foundations.Topology.CoveringMapOn

/-!
# Points with small neighbourhoods contracting onto them

`HasContractibleNhdsRel x` says that `x` has arbitrarily small open neighbourhoods `V` which
strongly deformation retract onto `x`: there is a homotopy from `id_V` to the constant map `x`
fixing `x`. A space all of whose points have this property is strongly locally contractible
(`StronglyLocallyContractibleSpace.of_forall_hasContractibleNhdsRel`), hence locally path-connected
and semilocally simply connected.

The property is local and topological: it is invariant under homeomorphisms
(`HasContractibleNhdsRel.homeomorph`), passes to and from open subspaces
(`HasContractibleNhdsRel.subtype`, `HasContractibleNhdsRel.of_subtype`) and along local
homeomorphisms (`IsLocalHomeomorph.hasContractibleNhdsRel_iff`). Unlike plain local
contractibility, it glues along a finite closed cover whose members through `x` meet only at `x`
(`HasContractibleNhdsRel.of_finite_isClosed_cover`), since the contractions agree on the
intersections. A point over the centre of a punctured ball over which a proper map with finite
fibres is a covering has the property (`HasContractibleNhdsRel.of_isCoveringMapOn_ball`, the radial
contraction): this gives the local contractibility of complex algebraic curves.

## References

* [A. Hatcher, *Algebraic Topology*, §0][hatcher02]
-/

open Topology Set Filter Metric

section ContractibleNhds

variable {E : Type*} [TopologicalSpace E]

/-- `x` has arbitrarily small open neighbourhoods `V` which contract onto `x` by a homotopy fixing
`x` (a strong deformation retraction of `V` onto `x`). -/
def HasContractibleNhdsRel (x : E) : Prop :=
  ∀ N ∈ 𝓝 x, ∃ (V : Set E) (hxV : x ∈ V), IsOpen V ∧ V ⊆ N ∧
    Nonempty ((ContinuousMap.id V).HomotopyRel (ContinuousMap.const V ⟨x, hxV⟩) {⟨x, hxV⟩})

/-- A space in which every point has arbitrarily small open neighbourhoods contracting onto it is
strongly locally contractible. -/
theorem StronglyLocallyContractibleSpace.of_forall_hasContractibleNhdsRel
    (h : ∀ x : E, HasContractibleNhdsRel x) : StronglyLocallyContractibleSpace E where
  contractible_basis x := by
    rw [hasBasis_self]
    intro t ht
    obtain ⟨V, hxV, hVo, hVt, ⟨H⟩⟩ := h x t ht
    exact ⟨V, hVo.mem_nhds hxV, (contractible_iff_id_nullhomotopic V).mpr
      ⟨⟨x, hxV⟩, ⟨H.toHomotopy⟩⟩, hVt⟩

/-- A contraction of `V` onto `v` relative to `v` transports along a homeomorphism `V ≃ₜ W`. -/
theorem Homeomorph.nonempty_homotopyRel_id_const {V W : Type*} [TopologicalSpace V]
    [TopologicalSpace W] (e : V ≃ₜ W) {v : V}
    (H : (ContinuousMap.id V).HomotopyRel (ContinuousMap.const V v) {v})
    {w : W} (hw : e v = w) :
    Nonempty ((ContinuousMap.id W).HomotopyRel (ContinuousMap.const W w) {w}) := by
  subst hw
  refine ⟨⟨⟨⟨fun p ↦ e (H (p.1, e.symm p.2)), by fun_prop⟩, fun y ↦ ?_, fun y ↦ ?_⟩,
    fun t y hy ↦ ?_⟩⟩
  · change e (H (0, e.symm y)) = y
    rw [H.apply_zero]
    exact e.apply_symm_apply y
  · change e (H (1, e.symm y)) = e v
    rw [H.apply_one]
    rfl
  · rw [mem_singleton_iff] at hy
    subst hy
    change e (H (t, e.symm (e v))) = e v
    rw [e.symm_apply_apply, H.eq_fst t (mem_singleton _)]
    rfl

/-- `HasContractibleNhdsRel` is invariant under homeomorphisms. -/
theorem HasContractibleNhdsRel.homeomorph {Y : Type*} [TopologicalSpace Y] (e : E ≃ₜ Y) {x : E}
    (h : HasContractibleNhdsRel x) : HasContractibleNhdsRel (e x) := by
  intro N hN
  obtain ⟨V, hxV, hVo, hVN, ⟨H⟩⟩ := h (e ⁻¹' N) (e.continuous.continuousAt.preimage_mem_nhds hN)
  exact ⟨e '' V, ⟨x, hxV, rfl⟩, e.isOpenMap V hVo, image_subset_iff.mpr hVN,
    Homeomorph.nonempty_homotopyRel_id_const (e.image V) H rfl⟩

/-- `HasContractibleNhdsRel` can be checked in an open neighbourhood. -/
theorem HasContractibleNhdsRel.of_subtype {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (h : HasContractibleNhdsRel (⟨x, hx⟩ : U)) : HasContractibleNhdsRel x := by
  intro N hN
  obtain ⟨V, hxV, hVo, hVN, ⟨H⟩⟩ :=
    h (Subtype.val ⁻¹' N) (continuous_subtype_val.continuousAt.preimage_mem_nhds hN)
  exact ⟨Subtype.val '' V, ⟨_, hxV, rfl⟩, hU.isOpenMap_subtype_val V hVo,
    image_subset_iff.mpr hVN,
    Homeomorph.nonempty_homotopyRel_id_const (IsEmbedding.subtypeVal.homeomorphImage V) H
      (Subtype.ext rfl)⟩

/-- `HasContractibleNhdsRel` restricts to open neighbourhoods. -/
theorem HasContractibleNhdsRel.subtype {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (h : HasContractibleNhdsRel x) : HasContractibleNhdsRel (⟨x, hx⟩ : U) := by
  intro N hN
  obtain ⟨V, hxV, hVo, hVN, ⟨H⟩⟩ :=
    h _ (hU.isOpenEmbedding_subtypeVal.image_mem_nhds.mpr hN)
  have hVU : V ⊆ U := hVN.trans (Subtype.coe_image_subset U N)
  have hV : Subtype.val '' (Subtype.val ⁻¹' V : Set U) = V := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hVU]
  let e : (Subtype.val ⁻¹' V : Set U) ≃ₜ V :=
    (IsEmbedding.subtypeVal.homeomorphImage _).trans (Homeomorph.setCongr hV)
  refine ⟨Subtype.val ⁻¹' V, hxV, hVo.preimage continuous_subtype_val, fun y hy ↦ ?_,
    Homeomorph.nonempty_homotopyRel_id_const e.symm H (e.symm_apply_eq.mpr (Subtype.ext rfl))⟩
  obtain ⟨z, hz, hzy⟩ := hVN hy
  rwa [← Subtype.ext hzy]

/-- `HasContractibleNhdsRel` is invariant under local homeomorphisms. -/
theorem IsLocalHomeomorph.hasContractibleNhdsRel_iff {Y : Type*} [TopologicalSpace Y]
    {f : Y → E} (hf : IsLocalHomeomorph f) (y : Y) :
    HasContractibleNhdsRel y ↔ HasContractibleNhdsRel (f y) := by
  obtain ⟨φ, hy, rfl⟩ := hf y
  let e := φ.toHomeomorphSourceTarget
  constructor
  · intro h
    have := (h.subtype φ.open_source hy).homeomorph e
    exact HasContractibleNhdsRel.of_subtype φ.open_target (φ.map_source hy) this
  · intro h
    have := (h.subtype φ.open_target (φ.map_source hy)).homeomorph e.symm
    refine HasContractibleNhdsRel.of_subtype φ.open_source hy ?_
    convert this using 1
    exact (e.symm_apply_eq.mpr (Subtype.ext rfl)).symm

/-- Gluing contractions along a finite closed cover: if the members of the cover through `x` meet
pairwise only at `x` near `x`, and `x` has small neighbourhoods contracting onto it in each of
them, then so it does in the whole space. -/
theorem HasContractibleNhdsRel.of_finite_isClosed_cover {ι : Type*} [Finite ι] {C : ι → Set E}
    (hC : ∀ i, IsClosed (C i)) (hcov : ∀ y, ∃ i, y ∈ C i) {x : E}
    (hiso : ∀ i j, i ≠ j → x ∈ C i → x ∈ C j → ∀ᶠ y in 𝓝 x, y ∈ C i → y ∈ C j → y = x)
    (h : ∀ i (hi : x ∈ C i), HasContractibleNhdsRel (⟨x, hi⟩ : C i)) :
    HasContractibleNhdsRel x := by
  classical
  intro N hN
  -- a neighbourhood `O` of `x` meeting only the members through `x`, pairwise only at `x`
  have hM : N ∩ (⋂ i, (if x ∈ C i then univ else (C i)ᶜ)) ∩
      {y | ∀ i j, i ≠ j → x ∈ C i → x ∈ C j → y ∈ C i → y ∈ C j → y = x} ∈ 𝓝 x := by
    refine inter_mem (inter_mem hN (iInter_mem.mpr fun i ↦ ?_)) ?_
    · split_ifs with hi
      · exact univ_mem
      · exact (hC i).isOpen_compl.mem_nhds hi
    · have : ∀ i j, ∀ᶠ y in 𝓝 x, i ≠ j → x ∈ C i → x ∈ C j → y ∈ C i → y ∈ C j → y = x :=
        fun i j ↦ by
          by_cases hij : i ≠ j ∧ x ∈ C i ∧ x ∈ C j
          · filter_upwards [hiso i j hij.1 hij.2.1 hij.2.2] with y hy _ _ _ using hy
          · exact Eventually.of_forall fun y h1 h2 h3 ↦ (hij ⟨h1, h2, h3⟩).elim
      filter_upwards [eventually_all.mpr fun i ↦ eventually_all.mpr (this i)] with y hy
      exact hy
  set O := interior (N ∩ (⋂ i, (if x ∈ C i then univ else (C i)ᶜ)) ∩
      {y | ∀ i j, i ≠ j → x ∈ C i → x ∈ C j → y ∈ C i → y ∈ C j → y = x})
  have hOo : IsOpen O := isOpen_interior
  have hxO : x ∈ O := mem_interior_iff_mem_nhds.mpr hM
  have hON : O ⊆ N := interior_subset.trans (inter_subset_left.trans inter_subset_left)
  have hOC (y : E) (hy : y ∈ O) (i : ι) (hyi : y ∈ C i) : x ∈ C i := by
    by_contra hi
    have := mem_iInter.mp (interior_subset hy).1.2 i
    rw [ite_eq_right hi] at this
    exact this hyi
  have hOij (y : E) (hy : y ∈ O) (i j : ι) (hij : i ≠ j) (hyi : y ∈ C i) (hyj : y ∈ C j) :
      y = x :=
    (interior_subset hy).2 i j hij (hOC y hy i hyi) (hOC y hy j hyj) hyi hyj
  -- contractible neighbourhoods in each member through `x`
  have hloc (i : ι) (hi : x ∈ C i) := h i hi (Subtype.val ⁻¹' O)
    (continuous_subtype_val.continuousAt.preimage_mem_nhds (hOo.mem_nhds hxO))
  choose Vi hxVi hVio hViO Hi using hloc
  choose Wi hWio hWiV using fun i (hi : x ∈ C i) ↦ isOpen_induced_iff.mp (hVio i hi)
  -- the glued neighbourhood
  set V := O ∩ ⋂ i, (if hi : x ∈ C i then Wi i hi ∪ (C i)ᶜ else univ)
  have hVo : IsOpen V := hOo.inter (isOpen_iInter_of_finite fun i ↦ by
    split_ifs with hi
    · exact (hWio i hi).union (hC i).isOpen_compl
    · exact isOpen_univ)
  have hxW (i : ι) (hi : x ∈ C i) : x ∈ Wi i hi := by
    have : (⟨x, hi⟩ : C i) ∈ Subtype.val ⁻¹' Wi i hi := (hWiV i hi).symm ▸ hxVi i hi
    exact this
  have hxV : x ∈ V := ⟨hxO, mem_iInter.mpr fun i ↦ by
    split_ifs with hi
    · exact Or.inl (hxW i hi)
    · trivial⟩
  have hVO : V ⊆ O := inter_subset_left
  have hmemVi (y : E) (hy : y ∈ V) (i : ι) (hyi : y ∈ C i) :
      (⟨y, hyi⟩ : C i) ∈ Vi i (hOC y (hVO hy) i hyi) := by
    have hi := hOC y (hVO hy) i hyi
    have := mem_iInter.mp hy.2 i
    rw [dite_eq_left hi] at this
    rcases this with h | h
    · rw [← hWiV i hi]; exact h
    · exact (h hyi).elim
  have hVi_V (i : ι) (hi : x ∈ C i) (z : C i) (hz : z ∈ Vi i hi) : (z : E) ∈ V := by
    have hzO : (z : E) ∈ O := hViO i hi hz
    refine ⟨hzO, mem_iInter.mpr fun j ↦ ?_⟩
    split_ifs with hj
    · by_cases hzj : (z : E) ∈ C j
      · by_cases hij : i = j
        · subst hij
          left
          have : z ∈ Subtype.val ⁻¹' Wi i hj := (hWiV i hj).symm ▸ hz
          exact this
        · left
          rw [hOij z hzO i j hij z.2 hzj]
          exact hxW j hj
      · exact Or.inr hzj
    · trivial
  -- the glued homotopy
  let H (i : ι) (hi : x ∈ C i) := (Hi i hi).some
  have hHx (i : ι) (hi : x ∈ C i) (t : unitInterval) (y : E) (hy : y ∈ C i)
      (hyV : (⟨y, hy⟩ : C i) ∈ Vi i hi) (hyx : y = x) :
      ((H i hi (t, ⟨⟨y, hy⟩, hyV⟩) : C i) : E) = x := by
    subst hyx
    rw [ContinuousMap.HomotopyRel.eq_fst _ t (mem_singleton _)]
    rfl
  have hHcongr (i j : ι) (hij : i = j) (hi : x ∈ C i) (hj : x ∈ C j) (t : unitInterval) (y : E)
      (hyi : y ∈ C i) (hyj : y ∈ C j) (hVi : (⟨y, hyi⟩ : C i) ∈ Vi i hi)
      (hVj : (⟨y, hyj⟩ : C j) ∈ Vi j hj) :
      ((H i hi (t, ⟨⟨y, hyi⟩, hVi⟩) : C i) : E) = ((H j hj (t, ⟨⟨y, hyj⟩, hVj⟩) : C j) : E) := by
    subst hij
    rfl
  let idx : V → ι := fun y ↦ (hcov y).choose
  have hidx (y : V) : (y : E) ∈ C (idx y) := (hcov y).choose_spec
  have hxi (y : V) : x ∈ C (idx y) := hOC y (hVO y.2) _ (hidx y)
  let F : unitInterval × V → V := fun p ↦
    ⟨((H (idx p.2) (hxi p.2) (p.1, ⟨⟨p.2, hidx p.2⟩, hmemVi p.2 p.2.2 _ (hidx p.2)⟩) :
      C (idx p.2)) : E), hVi_V _ _ _ (Subtype.prop _)⟩
  have hFj (j : ι) (hj : x ∈ C j) (p : unitInterval × V) (hpj : (p.2 : E) ∈ C j) :
      (F p : E) = ((H j hj (p.1, ⟨⟨p.2, hpj⟩, hmemVi p.2 p.2.2 j hpj⟩) : C j) : E) := by
    by_cases hij : idx p.2 = j
    · exact hHcongr _ _ hij _ _ _ _ _ _ _ _
    · rw [hHx _ _ _ _ _ _ (hOij p.2 (hVO p.2.2) _ _ hij (hidx p.2) hpj),
        hHx _ _ _ _ _ _ (hOij p.2 (hVO p.2.2) _ _ hij (hidx p.2) hpj)]
  have hFc : Continuous F := by
    refine continuous_induced_rng.mpr ?_
    refine LocallyFinite.continuous (f := fun j ↦ {p : unitInterval × V | (p.2 : E) ∈ C j})
      (locallyFinite_of_finite _) (eq_univ_of_forall fun p ↦ mem_iUnion.mpr (hcov p.2))
      (fun j ↦ (hC j).preimage (continuous_subtype_val.comp continuous_snd)) fun j ↦ ?_
    by_cases hj : x ∈ C j
    · rw [continuousOn_iff_continuous_domRestrict]
      have : Set.domRestrict {p : unitInterval × V | (p.2 : E) ∈ C j} (Subtype.val ∘ F) =
          fun q ↦ ((H j hj (q.1.1, ⟨⟨q.1.2, q.2⟩, hmemVi q.1.2 q.1.2.2 j q.2⟩) : C j) : E) := by
        funext q
        exact hFj j hj q.1 q.2
      rw [this]
      refine continuous_subtype_val.comp (continuous_subtype_val.comp
        ((H j hj).continuous.comp ?_))
      refine (continuous_fst.comp continuous_subtype_val).prodMk ?_
      exact ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk
        _).subtype_mk _
    · have : {p : unitInterval × V | (p.2 : E) ∈ C j} = ∅ :=
        eq_empty_of_forall_notMem fun p hp ↦ hj (hOC p.2 (hVO p.2.2) j hp)
      rw [this]
      exact continuousOn_empty _
  refine ⟨V, hxV, hVo, hVO.trans hON, ⟨⟨⟨⟨F, hFc⟩, fun y ↦ ?_, fun y ↦ ?_⟩, fun t y hy ↦ ?_⟩⟩⟩
  · apply Subtype.ext
    change (F (0, y) : E) = y
    rw [hFj (idx y) (hxi y) (0, y) (hidx y)]
    exact congrArg (fun z : Vi (idx y) (hxi y) ↦ ((z : C (idx y)) : E))
      ((H (idx y) (hxi y)).apply_zero _)
  · apply Subtype.ext
    change (F (1, y) : E) = x
    rw [hFj (idx y) (hxi y) (1, y) (hidx y)]
    exact congrArg (fun z : Vi (idx y) (hxi y) ↦ ((z : C (idx y)) : E))
      ((H (idx y) (hxi y)).apply_one _)
  · rw [mem_singleton_iff] at hy
    subst hy
    apply Subtype.ext
    change (F (t, ⟨x, hxV⟩) : E) = x
    rw [hFj (idx ⟨x, hxV⟩) (hxi _) (t, ⟨x, hxV⟩) (hidx _)]
    exact hHx _ _ _ _ _ _ rfl


/-- The radial contraction: for a proper map `π : E → X` to a real normed space with finite fibres,
which is a covering over a punctured ball `B(π x, r) ∖ {π x}`, the point `x` has arbitrarily small
open neighbourhoods contracting onto it. -/
theorem HasContractibleNhdsRel.of_isCoveringMapOn_ball [T2Space E] {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {π : E → X} (hp : IsProperMap π) {x : E} {r : ℝ}
    (hr : 0 < r) (hcov : IsCoveringMapOn π (ball (π x) r \ {π x})) (hfin : (π ⁻¹' {π x}).Finite) :
    HasContractibleNhdsRel x := fun _ hN ↦
  hcov.exists_nonempty_homotopyRel_id_const hr hp hfin rfl hN

end ContractibleNhds
