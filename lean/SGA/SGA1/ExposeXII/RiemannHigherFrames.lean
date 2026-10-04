/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigherRigidity
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Fibrewise isomorphic coverings become isomorphic over a covering of the base

Let `π : P → B` have a continuous section `sec` and pointed charts at every point
(`RiemannHigher.PointedChart`), and let `p₁ : E₁ → P`, `p₂ : E₂ → P` be coverings with finite
fibres which are isomorphic over every fibre `π⁻¹(b)` (`FibreIso`), the fibres of `p₁` over
`sec b` having `n` points. The *frames* `(b, v₁, v₂)` (`RiemannHigher.FrameSpace`), with `v₁` an
enumeration of the fibre of `p₁` over `sec b` and `v₂ = ψ ∘ v₁` for an isomorphism
`ψ : E₁|_{π⁻¹(b)} ≅ E₂|_{π⁻¹(b)}`, form a finite covering `M → B`
(`RiemannHigher.isCoveringMap_frameProj`), surjective, and over `M` the two coverings become
isomorphic: the tautological map `(m, e) ↦ ψ_m(e)` is continuous and bijective
(`RiemannHigher.exists_frame_iso`). The isomorphism `ψ` is unique given the frame, since `π⁻¹(b)`
is connected (`eq_of_forall_proj_eq_x₀`), and in a pointed chart all the data are constant along
the base.

This is the step "fibrewise algebraic implies algebraic after a finite étale base change" of the
induction of XII.5.1 in higher dimension (`SGA.SGA1.ExposeXII.RiemannHigher`): with `B` the points
of a variety for which XII.5.1 is known, the covering `M` is algebraic. General topology.
-/
noncomputable section

open Topology unitInterval Set

namespace SGA.SGA1.ExposeXII.RiemannHigher

universe u v w₁ w₂

variable {B : Type u} {P : Type v} {E₁ : Type w₁} {E₂ : Type w₂} [TopologicalSpace B]
  [TopologicalSpace P] [TopologicalSpace E₁] [TopologicalSpace E₂] {π : P → B} {sec : B → P}
  (hsec : ∀ b, π (sec b) = b) (p₁ : E₁ → P) (p₂ : E₂ → P) (n : ℕ)

/-- `(b, v₁, v₂)` is a frame pair: `v₁` enumerates the fibre of `p₁` over `sec b`, and `v₂ = ψ ∘ v₁`
for an isomorphism `ψ` of the coverings `p₁`, `p₂` over the fibre `π⁻¹(b)`. -/
structure IsFramePair (b : B) (v₁ : Fin n → E₁) (v₂ : Fin n → E₂) : Prop where
  over₁ : ∀ k, p₁ (v₁ k) = sec b
  over₂ : ∀ k, p₂ (v₂ k) = sec b
  enum : ∀ e, p₁ e = sec b → ∃! k, v₁ k = e
  ext : ∃ ψ : FibreSpace p₁ π b → FibreSpace p₂ π b, Continuous ψ ∧ Function.Bijective ψ ∧
    (∀ e, p₂ (ψ e).1 = p₁ e.1) ∧ ∀ k, (ψ ⟨v₁ k, by rw [over₁ k, hsec]⟩).1 = v₂ k

/-- The space of frame pairs, as a subspace of `B × E₁ⁿ × E₂ⁿ`. -/
def FrameSpace : Type _ :=
  {m : B × (Fin n → E₁) × (Fin n → E₂) // IsFramePair hsec p₁ p₂ n m.1 m.2.1 m.2.2}

instance : TopologicalSpace (FrameSpace hsec p₁ p₂ n) := instTopologicalSpaceSubtype

/-- The projection of a frame pair to `B`. -/
def frameProj (m : FrameSpace hsec p₁ p₂ n) : B := m.1.1

omit [TopologicalSpace P] in
lemma continuous_frameProj : Continuous (frameProj hsec p₁ p₂ n) :=
  continuous_fst.comp continuous_subtype_val

section Chart

variable {hsec p₁ p₂ n} {b₀ : B} (K : PointedChart π sec hsec b₀)

/-- The fibre over `x₀` of the slice of `p : E → P` in the chart `K`. -/
abbrev SliceFibre {E : Type*} [TopologicalSpace E] (p : E → P) : Type _ :=
  {z : K.Slice p // K.sliceProj p z = K.x₀}

variable (p₁ p₂ n) in
/-- Frame pairs at the level of the slices of a chart. -/
structure IsSliceFramePair (u₁ : Fin n → SliceFibre K p₁) (u₂ : Fin n → SliceFibre K p₂) :
    Prop where
  enum : ∀ z : SliceFibre K p₁, ∃! k, u₁ k = z
  ext : ∃ ψ : K.Slice p₁ → K.Slice p₂, Continuous ψ ∧ Function.Bijective ψ ∧
    (∀ z, K.sliceProj p₂ (ψ z) = K.sliceProj p₁ z) ∧ ∀ k, ψ (u₁ k).1 = (u₂ k).1

variable (p₁ p₂ n) in
/-- The slice frame pairs of a chart (a discrete space). -/
abbrev SliceFrames : Type _ :=
  {u : (Fin n → SliceFibre K p₁) × (Fin n → SliceFibre K p₂) //
    IsSliceFramePair p₁ p₂ n K u.1 u.2}

/-- A point of `E` over `sec b`, `b ∈ N`, as a point of the slice fibre. -/
def toSliceFibre {E : Type*} [TopologicalSpace E] {p : E → P} (hp : IsCoveringMap p) {b : B}
    (hb : b ∈ K.N) (e : E) (he : p e = sec b) : SliceFibre K p :=
  ⟨K.fibreChart hp hb ⟨e, by rw [he, hsec]⟩, K.sliceProj_fibreChart_of_eq_sec hp hb _ he⟩

lemma toSliceFibre_injective {E : Type*} [TopologicalSpace E] {p : E → P} (hp : IsCoveringMap p)
    {b : B} (hb : b ∈ K.N) {e e' : E} (he : p e = sec b) (he' : p e' = sec b)
    (h : toSliceFibre K hp hb e he = toSliceFibre K hp hb e' he') : e = e' :=
  congrArg Subtype.val ((K.fibreChart hp hb).injective (congrArg Subtype.val h))

lemma exists_toSliceFibre_eq {E : Type*} [TopologicalSpace E] {p : E → P} (hp : IsCoveringMap p)
    {b : B} (hb : b ∈ K.N) (z : SliceFibre K p) :
    ∃ e, ∃ he : p e = sec b, toSliceFibre K hp hb e he = z := by
  let e := (K.fibreChart hp hb).symm z.1
  have he : K.sliceProj p (K.fibreChart hp hb e) = K.x₀ := by
    rw [Homeomorph.apply_symm_apply]
    exact z.2
  refine ⟨e.1, K.eq_sec_of_sliceProj_fibreChart hp hb e he, Subtype.ext ?_⟩
  change K.fibreChart hp hb ⟨e.1, _⟩ = z.1
  rw [Subtype.coe_eta, Homeomorph.apply_symm_apply]

/-- Two points over `π⁻¹(b)`, `b ∈ N`, are equal if their images in `F` are. -/
lemma eq_of_snd_Θ_eq {b : B} (hb : b ∈ K.N) {x y : P} (hx : π x = b) (hy : π y = b)
    (h : (K.Θ ⟨x, by rw [hx]; exact hb⟩).2 = (K.Θ ⟨y, by rw [hy]; exact hb⟩).2) : x = y :=
  fibreSpace_eq_of_fibreCoord_eq K.Θ K.fst_Θ hb hx hy h

/-- Frame pairs over `b ∈ N` correspond to frame pairs of the slices. -/
theorem isFramePair_iff (hp₁ : IsCoveringMap p₁) (hp₂ : IsCoveringMap p₂) {b : B}
    (hb : b ∈ K.N) (v₁ : Fin n → E₁) (v₂ : Fin n → E₂) (h₁ : ∀ k, p₁ (v₁ k) = sec b)
    (h₂ : ∀ k, p₂ (v₂ k) = sec b) :
    IsFramePair hsec p₁ p₂ n b v₁ v₂ ↔ IsSliceFramePair p₁ p₂ n K
      (fun k ↦ toSliceFibre K hp₁ hb (v₁ k) (h₁ k))
      (fun k ↦ toSliceFibre K hp₂ hb (v₂ k) (h₂ k)) := by
  let χ₁ := K.fibreChart hp₁ hb
  let χ₂ := K.fibreChart hp₂ hb
  -- compatibility of the fibre charts with the projections
  have hproj₁ (e : FibreSpace p₁ π b) : K.sliceProj p₁ (χ₁ e) =
      (K.Θ ⟨p₁ e.1, by rw [e.2]; exact hb⟩).2 := K.sliceProj_fibreChart hp₁ hb e
  have hproj₂ (e : FibreSpace p₂ π b) : K.sliceProj p₂ (χ₂ e) =
      (K.Θ ⟨p₂ e.1, by rw [e.2]; exact hb⟩).2 := K.sliceProj_fibreChart hp₂ hb e
  constructor
  · rintro ⟨hov₁, hov₂, henum, ψ, hψc, hψb, hψp, hψv⟩
    refine ⟨fun z ↦ ?_, ?_⟩
    · obtain ⟨e, he, rfl⟩ := exists_toSliceFibre_eq K hp₁ hb z
      obtain ⟨k, hk, hkuniq⟩ := henum e he
      exact ⟨k, by simp only [hk], fun k' hk' ↦ hkuniq k'
        (toSliceFibre_injective K hp₁ hb (h₁ k') he hk')⟩
    · refine ⟨χ₂ ∘ ψ ∘ χ₁.symm, χ₂.continuous.comp (hψc.comp χ₁.symm.continuous),
        χ₂.bijective.comp (hψb.comp χ₁.symm.bijective), fun z ↦ ?_, fun k ↦ ?_⟩
      · simp only [Function.comp_apply, hproj₂]
        conv_rhs => rw [← χ₁.apply_symm_apply z, hproj₁]
        congr 2
        exact Subtype.ext (hψp _)
      · change χ₂ (ψ (χ₁.symm (χ₁ ⟨v₁ k, _⟩))) = χ₂ ⟨v₂ k, _⟩
        rw [Homeomorph.symm_apply_apply]
        exact congrArg χ₂ (Subtype.ext (hψv k))
  · rintro ⟨henum, ψ₀, hψc, hψb, hψp, hψv⟩
    refine ⟨h₁, h₂, fun e he ↦ ?_, ?_⟩
    · obtain ⟨k, hk, hkuniq⟩ := henum (toSliceFibre K hp₁ hb e he)
      exact ⟨k, toSliceFibre_injective K hp₁ hb (h₁ k) he hk, fun k' hk' ↦ hkuniq k'
        (by simp only [hk'])⟩
    · refine ⟨χ₂.symm ∘ ψ₀ ∘ χ₁, χ₂.symm.continuous.comp (hψc.comp χ₁.continuous),
        χ₂.symm.bijective.comp (hψb.comp χ₁.bijective), fun e ↦ ?_, fun k ↦ ?_⟩
      · refine eq_of_snd_Θ_eq K hb ((χ₂.symm (ψ₀ (χ₁ e))).2) e.2 ?_
        rw [← hproj₂, ← hproj₁]
        simp only [Function.comp_apply, Homeomorph.apply_symm_apply, hψp]
      · change (χ₂.symm (ψ₀ (χ₁ ⟨v₁ k, _⟩))).1 = v₂ k
        have := hψv k
        change ψ₀ (χ₁ ⟨v₁ k, _⟩) = χ₂ ⟨v₂ k, _⟩ at this
        rw [this, Homeomorph.symm_apply_apply]

lemma toSliceFibre_symm {E : Type*} [TopologicalSpace E] {p : E → P} (hp : IsCoveringMap p)
    {b : B} (hb : b ∈ K.N) (z : SliceFibre K p) (h : p ((K.fibreChart hp hb).symm z.1).1 = sec b) :
    toSliceFibre K hp hb ((K.fibreChart hp hb).symm z.1).1 h = z := by
  refine Subtype.ext ?_
  change K.fibreChart hp hb ⟨((K.fibreChart hp hb).symm z.1).1, _⟩ = z.1
  rw [Subtype.coe_eta, Homeomorph.apply_symm_apply]

lemma proj_fibreChart_symm {E : Type*} [TopologicalSpace E] {p : E → P} (hp : IsCoveringMap p)
    {b : B} (hb : b ∈ K.N) (z : SliceFibre K p) : p ((K.fibreChart hp hb).symm z.1).1 = sec b :=
  K.eq_sec_of_sliceProj_fibreChart hp hb _ (by rw [Homeomorph.apply_symm_apply]; exact z.2)

instance {E : Type*} [TopologicalSpace E] {p : E → P} [Fact (IsCoveringMap p)] :
    DiscreteTopology (SliceFibre K p) :=
  ((K.isCoveringMap_sliceProj Fact.out) K.x₀).discreteTopology_fiber

variable (hp₁ : IsCoveringMap p₁) (hp₂ : IsCoveringMap p₂)

/-- The slice frame pair of a frame pair over `N`. -/
def toSliceFrames (m : FrameSpace hsec p₁ p₂ n) (hm : frameProj hsec p₁ p₂ n m ∈ K.N) :
    SliceFrames p₁ p₂ n K :=
  ⟨(fun k ↦ toSliceFibre K hp₁ hm (m.1.2.1 k) (m.2.over₁ k),
    fun k ↦ toSliceFibre K hp₂ hm (m.1.2.2 k) (m.2.over₂ k)),
    (isFramePair_iff K hp₁ hp₂ hm _ _ m.2.over₁ m.2.over₂).mp m.2⟩

/-- The frame pair over `b ∈ N` of a slice frame pair. -/
def ofSliceFrames (b : K.N) (u : SliceFrames p₁ p₂ n K) : FrameSpace hsec p₁ p₂ n :=
  ⟨(b, fun k ↦ ((K.fibreChart hp₁ b.2).symm (u.1.1 k).1).1,
    fun k ↦ ((K.fibreChart hp₂ b.2).symm (u.1.2 k).1).1), by
    refine (isFramePair_iff K hp₁ hp₂ b.2 _ _ (fun k ↦ proj_fibreChart_symm K hp₁ b.2 _)
      (fun k ↦ proj_fibreChart_symm K hp₂ b.2 _)).mpr ?_
    convert u.2 using 1
    · exact funext fun k ↦ toSliceFibre_symm K hp₁ b.2 _ _
    · exact funext fun k ↦ toSliceFibre_symm K hp₂ b.2 _ _⟩

/-- The frame pairs over `N` are `N` times the slice frame pairs. -/
def frameChart : {m : FrameSpace hsec p₁ p₂ n // frameProj hsec p₁ p₂ n m ∈ K.N} ≃ₜ
    K.N × SliceFrames p₁ p₂ n K where
  toFun m := (⟨frameProj hsec p₁ p₂ n m.1, m.2⟩, toSliceFrames K hp₁ hp₂ m.1 m.2)
  invFun x := ⟨ofSliceFrames K hp₁ hp₂ x.1 x.2, x.1.2⟩
  left_inv m := by
    refine Subtype.ext (Subtype.ext (Prod.ext rfl (Prod.ext (funext fun k ↦ ?_)
      (funext fun k ↦ ?_))))
    · change ((K.fibreChart hp₁ m.2).symm (K.fibreChart hp₁ m.2 ⟨_, _⟩)).1 = _
      rw [Homeomorph.symm_apply_apply]
    · change ((K.fibreChart hp₂ m.2).symm (K.fibreChart hp₂ m.2 ⟨_, _⟩)).1 = _
      rw [Homeomorph.symm_apply_apply]
  right_inv x := by
    refine Prod.ext rfl (Subtype.ext (Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_)))
    · exact toSliceFibre_symm K hp₁ x.1.2 _ (proj_fibreChart_symm K hp₁ x.1.2 _)
    · exact toSliceFibre_symm K hp₂ x.1.2 _ (proj_fibreChart_symm K hp₂ x.1.2 _)
  continuous_toFun := by
    refine (((continuous_frameProj hsec p₁ p₂ n).comp continuous_subtype_val).subtype_mk _).prodMk
      (Continuous.subtype_mk (Continuous.prodMk (continuous_pi fun k ↦ ?_)
        (continuous_pi fun k ↦ ?_)) _)
    · refine Continuous.subtype_mk ?_ _
      refine continuous_snd.comp ((K.chart hp₁).symm.continuous.comp (Continuous.subtype_mk ?_ _))
      exact (continuous_apply k).comp (continuous_fst.comp (continuous_snd.comp
        (continuous_subtype_val.comp continuous_subtype_val)))
    · refine Continuous.subtype_mk ?_ _
      refine continuous_snd.comp ((K.chart hp₂).symm.continuous.comp (Continuous.subtype_mk ?_ _))
      exact (continuous_apply k).comp (continuous_snd.comp (continuous_snd.comp
        (continuous_subtype_val.comp continuous_subtype_val)))
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    refine (continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_pi fun k ↦ ?_).prodMk (continuous_pi fun k ↦ ?_))
    · refine continuous_subtype_val.comp ((K.chart hp₁).continuous.comp ?_)
      exact continuous_fst.prodMk (continuous_subtype_val.comp ((continuous_apply k).comp
        (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))))
    · refine continuous_subtype_val.comp ((K.chart hp₂).continuous.comp ?_)
      exact continuous_fst.prodMk (continuous_subtype_val.comp ((continuous_apply k).comp
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))))

lemma frameChart_fst (m : {m : FrameSpace hsec p₁ p₂ n // frameProj hsec p₁ p₂ n m ∈ K.N}) :
    ((frameChart K hp₁ hp₂ m).1 : B) = frameProj hsec p₁ p₂ n m.1 := rfl

/-- The frame pairs over the interior of `N` are its product with the slice frame pairs. -/
def frameChartInterior :
    {m : FrameSpace hsec p₁ p₂ n // frameProj hsec p₁ p₂ n m ∈ interior K.N} ≃ₜ
      interior K.N × SliceFrames p₁ p₂ n K where
  toFun m := (⟨frameProj hsec p₁ p₂ n m.1, m.2⟩,
    (frameChart K hp₁ hp₂ ⟨m.1, interior_subset m.2⟩).2)
  invFun x := ⟨((frameChart K hp₁ hp₂).symm (⟨x.1.1, interior_subset x.1.2⟩, x.2)).1, by
    have := frameChart_fst K hp₁ hp₂ ((frameChart K hp₁ hp₂).symm (⟨x.1.1, interior_subset x.1.2⟩,
      x.2))
    rw [Homeomorph.apply_symm_apply] at this
    rw [← this]
    exact x.1.2⟩
  left_inv m := by
    refine Subtype.ext ?_
    change ((frameChart K hp₁ hp₂).symm (⟨frameProj hsec p₁ p₂ n m.1, interior_subset m.2⟩,
      (frameChart K hp₁ hp₂ ⟨m.1, interior_subset m.2⟩).2)).1 = m.1
    have h : ((⟨frameProj hsec p₁ p₂ n m.1, interior_subset m.2⟩ : K.N),
        (frameChart K hp₁ hp₂ ⟨m.1, interior_subset m.2⟩).2) =
        frameChart K hp₁ hp₂ ⟨m.1, interior_subset m.2⟩ := Prod.ext (Subtype.ext rfl) rfl
    rw [h, Homeomorph.symm_apply_apply]
  right_inv x := by
    have h := (frameChart K hp₁ hp₂).apply_symm_apply (⟨x.1.1, interior_subset x.1.2⟩, x.2)
    refine Prod.ext (Subtype.ext (congrArg (fun y ↦ (y.1 : B)) h)) ?_
    change (frameChart K hp₁ hp₂ ⟨_, _⟩).2 = x.2
    rw [Subtype.coe_eta, h]
  continuous_toFun := by
    refine (((continuous_frameProj hsec p₁ p₂ n).comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp ((frameChart K hp₁ hp₂).continuous.comp ?_))
    exact continuous_subtype_val.subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_subtype_val.comp
      ((frameChart K hp₁ hp₂).symm.continuous.comp ?_)) _
    exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd

include hp₁ hp₂ in
/-- The projection of frame pairs is evenly covered over a pointed chart. -/
theorem isEvenlyCovered_frameProj :
    IsEvenlyCovered (frameProj hsec p₁ p₂ n) b₀ (SliceFrames p₁ p₂ n K) := by
  have : Fact (IsCoveringMap p₁) := ⟨hp₁⟩
  have : Fact (IsCoveringMap p₂) := ⟨hp₂⟩
  exact ⟨inferInstance, interior K.N, K.mem_interior_N, isOpen_interior,
    isOpen_interior.preimage (continuous_frameProj hsec p₁ p₂ n), frameChartInterior K hp₁ hp₂,
    fun _ ↦ rfl⟩

/-- Conjugating a map of coverings over `π⁻¹(b)` by the fibre charts gives a map over `F`. -/
lemma sliceProj_conj (hp₁ : IsCoveringMap p₁) (hp₂ : IsCoveringMap p₂) {b : B} (hb : b ∈ K.N)
    (ψ : FibreSpace p₁ π b → FibreSpace p₂ π b) (hψp : ∀ e, p₂ (ψ e).1 = p₁ e.1)
    (z : K.Slice p₁) :
    K.sliceProj p₂ (K.fibreChart hp₂ hb (ψ ((K.fibreChart hp₁ hb).symm z))) = K.sliceProj p₁ z := by
  rw [K.sliceProj_fibreChart hp₂ hb]
  conv_rhs => rw [← (K.fibreChart hp₁ hb).apply_symm_apply z, K.sliceProj_fibreChart hp₁ hb]
  congr 2
  exact Subtype.ext (hψp _)

end Chart

section Global

variable {hsec p₁ p₂ n}

/-- The isomorphism over `π⁻¹(b)` attached to a frame pair. -/
def frameIsoFun (m : FrameSpace hsec p₁ p₂ n) :
    FibreSpace p₁ π (frameProj hsec p₁ p₂ n m) → FibreSpace p₂ π (frameProj hsec p₁ p₂ n m) :=
  Classical.choose m.2.ext

omit [TopologicalSpace B] [TopologicalSpace P] in
lemma frameIsoFun_spec (m : FrameSpace hsec p₁ p₂ n) :
    Continuous (frameIsoFun m) ∧ Function.Bijective (frameIsoFun m) ∧
      (∀ e, p₂ (frameIsoFun m e).1 = p₁ e.1) ∧
      ∀ k, (frameIsoFun m ⟨m.1.2.1 k, by rw [m.2.over₁ k, hsec]; rfl⟩).1 = m.1.2.2 k :=
  Classical.choose_spec m.2.ext

variable (hsec p₁ p₂ n) in
/-- The pullback of `E₁` to the frame pairs. -/
abbrev FrameTotal₁ : Type _ :=
  {q : FrameSpace hsec p₁ p₂ n × E₁ // frameProj hsec p₁ p₂ n q.1 = π (p₁ q.2)}

variable (hsec p₁ p₂ n) in
/-- The pullback of `E₂` to the frame pairs. -/
abbrev FrameTotal₂ : Type _ :=
  {q : FrameSpace hsec p₁ p₂ n × E₂ // frameProj hsec p₁ p₂ n q.1 = π (p₂ q.2)}

/-- The tautological map `(m, e) ↦ (m, ψ_m(e))` from the pullback of `E₁` to that of `E₂`. -/
def frameIso (q : FrameTotal₁ hsec p₁ p₂ n) : FrameTotal₂ hsec p₁ p₂ n :=
  ⟨(q.1.1, (frameIsoFun q.1.1 ⟨q.1.2, q.2.symm⟩).1), (frameIsoFun q.1.1 ⟨q.1.2, q.2.symm⟩).2.symm⟩

omit [TopologicalSpace B] [TopologicalSpace P] in
lemma frameIso_fst (q : FrameTotal₁ hsec p₁ p₂ n) : (frameIso q).1.1 = q.1.1 := rfl

omit [TopologicalSpace B] [TopologicalSpace P] in
lemma proj_frameIso (q : FrameTotal₁ hsec p₁ p₂ n) : p₂ (frameIso q).1.2 = p₁ q.1.2 :=
  (frameIsoFun_spec q.1.1).2.2.1 _

omit [TopologicalSpace B] [TopologicalSpace P] in
lemma frameIso_bijective : Function.Bijective (frameIso (hsec := hsec) (p₁ := p₁) (p₂ := p₂)
    (n := n)) := by
  refine ⟨fun q q' h ↦ ?_, fun q ↦ ?_⟩
  · have h₁ : q.1.1 = q'.1.1 := congrArg (fun x ↦ x.1.1) h
    obtain ⟨⟨m, e⟩, he⟩ := q
    obtain ⟨⟨m', e'⟩, he'⟩ := q'
    simp only at h₁
    subst h₁
    have h₂ := congrArg (fun x ↦ x.1.2) h
    simp only [frameIso] at h₂
    have := (frameIsoFun_spec m).2.1.1 (Subtype.ext h₂)
    exact Subtype.ext (Prod.ext rfl (congrArg Subtype.val this))
  · obtain ⟨⟨m, e₂⟩, he₂⟩ := q
    obtain ⟨e, he⟩ := (frameIsoFun_spec m).2.1.2 ⟨e₂, he₂.symm⟩
    refine ⟨⟨(m, e.1), e.2.symm⟩, Subtype.ext (Prod.ext rfl ?_)⟩
    simp only [frameIso]
    exact congrArg Subtype.val he

/-- The tautological map is continuous: over a pointed chart, on the open set of frame pairs with
given slice frames, it is the product of the identity of `N` with one isomorphism of slices. -/
theorem continuous_frameIso (hchart : ∀ b₀, Nonempty (PointedChart π sec hsec b₀))
    (hp₁ : IsCoveringMap p₁) (hp₂ : IsCoveringMap p₂) :
    Continuous (frameIso (hsec := hsec) (p₁ := p₁) (p₂ := p₂) (n := n)) := by
  refine continuous_iff_continuousAt.mpr fun q₀ ↦ ?_
  let K := (hchart (frameProj hsec p₁ p₂ n q₀.1.1)).some
  have hq₀ : frameProj hsec p₁ p₂ n q₀.1.1 ∈ interior K.N := K.mem_interior_N
  let u₀ := toSliceFrames K hp₁ hp₂ q₀.1.1 (interior_subset hq₀)
  -- the open set of frame pairs over the interior of `N` with slice frames `u₀`
  let V : Set (FrameSpace hsec p₁ p₂ n) := {m | ∃ h : frameProj hsec p₁ p₂ n m ∈ interior K.N,
    toSliceFrames K hp₁ hp₂ m (interior_subset h) = u₀}
  have hV : IsOpen V := by
    have : DiscreteTopology (SliceFrames p₁ p₂ n K) := (isEvenlyCovered_frameProj K hp₁ hp₂).1
    have hU : IsOpen {m | frameProj hsec p₁ p₂ n m ∈ interior K.N} :=
      isOpen_interior.preimage (continuous_frameProj hsec p₁ p₂ n)
    have h₁ : IsOpen ((fun m : {m // frameProj hsec p₁ p₂ n m ∈ interior K.N} ↦
        (frameChartInterior K hp₁ hp₂ m).2) ⁻¹' {u₀}) :=
      (isOpen_discrete _).preimage (continuous_snd.comp (frameChartInterior K hp₁ hp₂).continuous)
    convert hU.isOpenMap_subtype_val _ h₁ using 1
    ext m
    constructor
    · rintro ⟨h, hu⟩
      exact ⟨⟨m, h⟩, hu, rfl⟩
    · rintro ⟨⟨m', h⟩, hu, rfl⟩
      exact ⟨h, hu⟩
  let W : Set (FrameTotal₁ hsec p₁ p₂ n) := {q | q.1.1 ∈ V}
  have hW : IsOpen W := hV.preimage (continuous_fst.comp continuous_subtype_val)
  have hq₀W : q₀ ∈ W := ⟨hq₀, rfl⟩
  refine ContinuousOn.continuousAt ?_ (hW.mem_nhds hq₀W)
  rw [continuousOn_iff_continuous_domRestrict]
  -- on `W`, `frameIso` is given by the chart and one isomorphism `ψ₀` of slices
  obtain ⟨ψ₀, hψ₀c, -, hψ₀p, hψ₀v⟩ := u₀.2.ext
  have hmem (q : W) : π (p₁ q.1.1.2) ∈ K.N := q.1.2 ▸ interior_subset q.2.1
  let g : W → FrameTotal₂ hsec p₁ p₂ n := fun q ↦
    ⟨(q.1.1.1, (K.chart hp₂ (⟨frameProj hsec p₁ p₂ n q.1.1.1, interior_subset q.2.1⟩,
      ψ₀ ((K.chart hp₁).symm ⟨q.1.1.2, hmem q⟩).2)).1),
      (K.proj_chart hp₂ (⟨frameProj hsec p₁ p₂ n q.1.1.1, interior_subset q.2.1⟩, _)).symm⟩
  have hg : Continuous g := by
    refine Continuous.subtype_mk ((continuous_fst.comp (continuous_subtype_val.comp
      continuous_subtype_val)).prodMk ?_) _
    refine continuous_subtype_val.comp ((K.chart hp₂).continuous.comp ?_)
    refine (Continuous.subtype_mk ((continuous_frameProj hsec p₁ p₂ n).comp
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))) _).prodMk ?_
    refine hψ₀c.comp (continuous_snd.comp ((K.chart hp₁).symm.continuous.comp ?_))
    exact Continuous.subtype_mk (continuous_snd.comp (continuous_subtype_val.comp
      continuous_subtype_val)) _
  convert hg using 1
  funext q
  obtain ⟨hb', hu⟩ := q.2
  have hb := interior_subset hb'
  set m := q.1.1.1
  set b := frameProj hsec p₁ p₂ n m
  let χ₁ := K.fibreChart hp₁ hb
  let χ₂ := K.fibreChart hp₂ hb
  let ψ := frameIsoFun m
  obtain ⟨hψc, -, hψp, hψv⟩ := frameIsoFun_spec m
  -- uniqueness of the isomorphism of slices extending the frames
  have huniq : (fun z ↦ χ₂ (ψ (χ₁.symm z))) = ψ₀ := by
    refine eq_of_forall_proj_eq_x₀ (K.isCoveringMap_sliceProj hp₁)
      (K.isCoveringMap_sliceProj hp₂) (χ₂.continuous.comp (hψc.comp χ₁.symm.continuous)) hψ₀c
      (sliceProj_conj K hp₁ hp₂ hb ψ hψp) hψ₀p K.x₀ fun z hz ↦ ?_
    obtain ⟨k, hk, -⟩ := u₀.2.enum ⟨z, hz⟩
    have hk₁ : (⟨z, hz⟩ : SliceFibre K p₁) = toSliceFibre K hp₁ hb (m.1.2.1 k) (m.2.over₁ k) := by
      rw [← hk, ← hu]
      rfl
    have hk₂ : (u₀.1.2 k).1 = χ₂ ⟨m.1.2.2 k, by rw [m.2.over₂ k, hsec]; rfl⟩ := by
      rw [← hu]
      rfl
    have hz' : z = χ₁ ⟨m.1.2.1 k, by rw [m.2.over₁ k, hsec]; rfl⟩ := congrArg Subtype.val hk₁
    calc χ₂ (ψ (χ₁.symm z)) = χ₂ (ψ ⟨m.1.2.1 k, by rw [m.2.over₁ k, hsec]; rfl⟩) := by
          rw [hz', Homeomorph.symm_apply_apply]
      _ = χ₂ ⟨m.1.2.2 k, by rw [m.2.over₂ k, hsec]; rfl⟩ := congrArg χ₂ (Subtype.ext (hψv k))
      _ = (u₀.1.2 k).1 := hk₂.symm
      _ = ψ₀ (u₀.1.1 k).1 := (hψ₀v k).symm
      _ = ψ₀ z := by rw [hk]
  refine Subtype.ext (Prod.ext rfl ?_)
  change (ψ ⟨q.1.1.2, q.1.2.symm⟩).1 = (K.chart hp₂ (⟨b, hb⟩, ψ₀ (χ₁ ⟨q.1.1.2, q.1.2.symm⟩))).1
  rw [← huniq]
  dsimp only
  rw [Homeomorph.symm_apply_apply]
  change (ψ _).1 = (χ₂.symm (χ₂ (ψ _))).1
  rw [Homeomorph.symm_apply_apply]

/-- Frame pairs form a covering of the base. -/
theorem isCoveringMap_frameProj (hchart : ∀ b₀, Nonempty (PointedChart π sec hsec b₀))
    (hp₁ : IsCoveringMap p₁) (hp₂ : IsCoveringMap p₂) :
    IsCoveringMap (frameProj hsec p₁ p₂ n) := fun b₀ ↦
  (isEvenlyCovered_frameProj (hchart b₀).some hp₁ hp₂).to_isEvenlyCovered_preimage

omit [TopologicalSpace B] [TopologicalSpace P] in
/-- Frame pairs over a point are finitely many if the fibres of `p₁`, `p₂` are finite. -/
theorem finite_frameProj_preimage (hfin₁ : ∀ x, (p₁ ⁻¹' {x}).Finite)
    (hfin₂ : ∀ x, (p₂ ⁻¹' {x}).Finite) (b : B) : (frameProj hsec p₁ p₂ n ⁻¹' {b}).Finite := by
  have : Finite (p₁ ⁻¹' {sec b}) := (hfin₁ _).to_subtype
  have : Finite (p₂ ⁻¹' {sec b}) := (hfin₂ _).to_subtype
  have hb (m : frameProj hsec p₁ p₂ n ⁻¹' {b}) : m.1.1.1 = b := m.2
  let f : (frameProj hsec p₁ p₂ n ⁻¹' {b}) →
      (Fin n → p₁ ⁻¹' {sec b}) × (Fin n → p₂ ⁻¹' {sec b}) := fun m ↦
    (fun k ↦ ⟨m.1.1.2.1 k, by
      rw [mem_preimage, mem_singleton_iff, m.1.2.over₁ k, hb m]⟩,
    fun k ↦ ⟨m.1.1.2.2 k, by
      rw [mem_preimage, mem_singleton_iff, m.1.2.over₂ k, hb m]⟩)
  have hf : Function.Injective f := fun m m' h ↦ by
    have h₁ : m.1.1.2.1 = m'.1.1.2.1 := funext fun k ↦ congrArg Subtype.val (congr_fun
      (congrArg Prod.fst h) k)
    have h₂ : m.1.1.2.2 = m'.1.1.2.2 := funext fun k ↦ congrArg Subtype.val (congr_fun
      (congrArg Prod.snd h) k)
    exact Subtype.ext (Subtype.ext (Prod.ext ((hb m).trans (hb m').symm) (Prod.ext h₁ h₂)))
  exact Set.finite_coe_iff.mp (Finite.of_injective f hf)

omit [TopologicalSpace B] [TopologicalSpace P] in
/-- Frame pairs exist over every point if the coverings are isomorphic over every fibre and the
fibres of `p₁` over the section have `n` points. -/
theorem surjective_frameProj (hiso : ∀ b, FibreIso p₁ p₂ π b)
    (hcard : ∀ b, Nat.card (p₁ ⁻¹' {sec b}) = n) (hfin₁ : ∀ x, (p₁ ⁻¹' {x}).Finite) :
    Function.Surjective (frameProj hsec p₁ p₂ n) := by
  intro b
  obtain ⟨φ, hφ⟩ := hiso b
  have : Finite (p₁ ⁻¹' {sec b}) := (hfin₁ _).to_subtype
  let e : Fin n ≃ p₁ ⁻¹' {sec b} := ((Finite.equivFin _).trans (finCongr (hcard b))).symm
  have hv₁ (k : Fin n) : p₁ (e k).1 = sec b := (e k).2
  refine ⟨⟨(b, fun k ↦ (e k).1, fun k ↦ (φ ⟨(e k).1, by rw [hv₁ k, hsec]⟩).1),
    ⟨hv₁, fun k ↦ by rw [hφ]; exact hv₁ k, fun x hx ↦ ?_,
      φ, φ.continuous, φ.bijective, hφ, fun k ↦ rfl⟩⟩, rfl⟩
  refine ⟨e.symm ⟨x, hx⟩, by simp, fun k hk ↦ ?_⟩
  rw [Equiv.eq_symm_apply]
  exact Subtype.ext hk

/-- **Fibrewise isomorphic coverings become isomorphic over a finite covering of the base.** Let
`π : P → B` have a continuous section `sec` and pointed charts at every point, and let `p₁`, `p₂`
be coverings of `P` with finite fibres, isomorphic over every fibre `π⁻¹(b)`, the fibres of `p₁`
over `sec b` having `n` points. Then there are a covering `M → B` with finite fibres, surjective,
and a continuous bijection `M ×_B E₁ → M ×_B E₂` over `M ×_B P`. -/
theorem exists_frame_iso (hchart : ∀ b₀, Nonempty (PointedChart π sec hsec b₀))
    (hp₁ : IsCoveringMap p₁) (hp₂ : IsCoveringMap p₂) (hfin₁ : ∀ x, (p₁ ⁻¹' {x}).Finite)
    (hfin₂ : ∀ x, (p₂ ⁻¹' {x}).Finite) (hiso : ∀ b, FibreIso p₁ p₂ π b)
    (hcard : ∀ b, Nat.card (p₁ ⁻¹' {sec b}) = n) :
    ∃ (M : Type (max u w₁ w₂)) (_ : TopologicalSpace M) (pM : M → B), IsCoveringMap pM ∧
      (∀ b, (pM ⁻¹' {b}).Finite) ∧ Function.Surjective pM ∧
      ∃ Φ : {q : M × E₁ // pM q.1 = π (p₁ q.2)} → {q : M × E₂ // pM q.1 = π (p₂ q.2)},
        Continuous Φ ∧ Function.Bijective Φ ∧ ∀ q, (Φ q).1.1 = q.1.1 ∧ p₂ (Φ q).1.2 = p₁ q.1.2 :=
  ⟨FrameSpace hsec p₁ p₂ n, inferInstance, frameProj hsec p₁ p₂ n,
    isCoveringMap_frameProj hchart hp₁ hp₂, finite_frameProj_preimage hfin₁ hfin₂,
    surjective_frameProj hiso hcard hfin₁, frameIso, continuous_frameIso hchart hp₁ hp₂,
    frameIso_bijective, fun q ↦ ⟨rfl, proj_frameIso q⟩⟩

end Global

end SGA.SGA1.ExposeXII.RiemannHigher
