/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigherTransport

/-!
# Sections of coverings that are trivial

For a covering map `q : C → X`:

* `isOpen_range_of_section`: the image of a continuous section is open;
* `section_eq_of_eq`: over a preconnected `X`, two continuous sections agreeing at a point agree;
* `IsSectionCovered q`: every point of `C` lies on a continuous section (a trivial covering, for
  `X` connected), `sectionThrough`, and `continuous_uncurry_sectionThrough`: over a preconnected
  `X`, `(x, c) ↦ (section through c)(x)` is continuous (the section through `c` is locally
  constant in `c`).

These are the first pieces of the statement "a covering of the total space of a locally trivial
family with connected fibres which is trivial on every fibre comes from the base", used for the
covering of fibrewise isomorphisms in the induction step of XII.5.1 in higher dimension
(`SGA.SGA1.ExposeXII.RiemannHigher`). General topology.
-/
noncomputable section

open Topology unitInterval Set

namespace SGA.SGA1.ExposeXII.RiemannHigher

section Sections

variable {X C : Type*} [TopologicalSpace X] [TopologicalSpace C] {q : C → X}
  (hq : IsCoveringMap q)

include hq in
/-- The image of a continuous section of a covering map is open (a continuous section of a local
homeomorphism is an open embedding, `IsLocalHomeomorph.isOpenEmbedding_of_comp`). -/
lemma isOpen_range_of_section {s : X → C} (hs : Continuous s) (hsq : ∀ x, q (s x) = x) :
    IsOpen (range s) :=
  (hq.isLocalHomeomorph.isOpenEmbedding_of_comp
    (by convert IsOpenEmbedding.id; exact funext hsq) hs).isOpen_range

include hq in
/-- Two continuous sections of a covering over a preconnected space agreeing at a point are
equal. -/
lemma section_eq_of_eq [PreconnectedSpace X] {s s' : X → C} (hs : Continuous s)
    (hs' : Continuous s') (hsq : ∀ x, q (s x) = x) (hsq' : ∀ x, q (s' x) = x) {x₀ : X}
    (h : s x₀ = s' x₀) : s = s' :=
  hq.eq_of_comp_eq hs hs' (funext fun x ↦ by simp [hsq, hsq']) x₀ h

variable (q) in
/-- Every point of `C` lies on a continuous section of `q : C → X` (a trivial covering when `X`
is connected). -/
def IsSectionCovered : Prop :=
  ∀ c : C, ∃ s : X → C, Continuous s ∧ (∀ x, q (s x) = x) ∧ s (q c) = c

/-- The section through `c` of a section-covered map. -/
def sectionThrough (h : IsSectionCovered q) (c : C) : X → C := (h c).choose

lemma continuous_sectionThrough (h : IsSectionCovered q) (c : C) :
    Continuous (sectionThrough h c) := (h c).choose_spec.1

lemma sectionThrough_spec (h : IsSectionCovered q) (c : C) (x : X) :
    q (sectionThrough h c x) = x := (h c).choose_spec.2.1 x

lemma sectionThrough_self (h : IsSectionCovered q) (c : C) : sectionThrough h c (q c) = c :=
  (h c).choose_spec.2.2

include hq in
/-- Over a preconnected base, the section through a point of the image of a section `s` is `s`. -/
lemma sectionThrough_eq [PreconnectedSpace X] (h : IsSectionCovered q) {s : X → C}
    (hs : Continuous s) (hsq : ∀ x, q (s x) = x) {c : C} (hc : c ∈ range s) :
    sectionThrough h c = s := by
  obtain ⟨x, rfl⟩ := hc
  refine section_eq_of_eq hq (continuous_sectionThrough h _) hs (sectionThrough_spec h _) hsq
    (x₀ := x) ?_
  have := sectionThrough_self h (s x)
  rwa [hsq] at this

include hq in
/-- For a section-covered covering of a preconnected space, the point of the section through `c`
over `x` depends continuously on `(x, c)` (the section through `c` is locally constant in `c`). -/
lemma continuous_uncurry_sectionThrough [PreconnectedSpace X] (h : IsSectionCovered q) :
    Continuous fun xc : X × C ↦ sectionThrough h xc.2 xc.1 := by
  refine continuous_iff_continuousAt.mpr fun xc₀ ↦ ?_
  set s := sectionThrough h xc₀.2
  have hs := continuous_sectionThrough h xc₀.2
  have hsq := sectionThrough_spec h xc₀.2
  have hmem : xc₀.2 ∈ range s := ⟨q xc₀.2, sectionThrough_self h xc₀.2⟩
  have hev : ∀ᶠ xc in 𝓝 xc₀, sectionThrough h xc.2 xc.1 = s xc.1 := by
    have : ∀ᶠ xc in 𝓝 xc₀, xc.2 ∈ range s :=
      continuous_snd.continuousAt.preimage_mem_nhds
        ((isOpen_range_of_section hq hs hsq).mem_nhds hmem)
    filter_upwards [this] with xc hxc
    rw [sectionThrough_eq hq h hs hsq hxc]
  exact ((hs.comp continuous_fst).continuousAt).congr (hev.mono fun _ h ↦ h.symm)

end Sections

end SGA.SGA1.ExposeXII.RiemannHigher
