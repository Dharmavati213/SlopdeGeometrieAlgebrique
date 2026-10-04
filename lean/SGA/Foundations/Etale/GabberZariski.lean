/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import SGA.Foundations.EtaleStalkProper
import SGA.Foundations.Etale.ProperBaseChangeClopen
import SGA.Foundations.Etale.TorsorEtale
import SGA.Foundations.Etale.LocalAcyclicityStrictLocalization

/-!
# Zariski `H⁰` over a noetherian henselian local ring

Let `Z` be proper over a noetherian henselian local ring `A`, with closed fibre `Z₀`. For a sheaf
`G` on the Zariski site of `Z`, `Γ(Z, G) = Γ(Z₀, G|_{Z₀})` (Stacks 0A0B, 09ZG). We prove the
surjectivity for the sheaves that occur in Gabber's proof of the proper base change theorem in
degree `0`, namely the sheaves `i^{-1}(F|_{Z_{Zar}})` for `F` an étale sheaf on `Z`: a section of
the étale inverse image `i^* F` over `Z₀` which is Zariski-locally (around each point of `Z₀`) the
restriction of a section of `F` comes from a global section of `F`
(`AlgebraicGeometry.exists_eq_of_forall_closedFibre_of_henselianLocalRing`).

The topological core is a gluing lemma for finitely many charts
(`exists_open_subordinate_of_clopenLifting`): if `X₀ ⊆ X` is closed, every nonempty closed set
meets `X₀`, and for every closed `T` the clopen subsets of `T ∩ X₀` are traces of clopen subsets of
`T`, then finitely many local sections `s_a` over opens `W_a` covering `X₀`, any two of which agree
near each point of `X₀` where both are defined, can be shrunk to a cover of `X` on which they glue.
This replaces the reduction in Stacks 09ZG to constant sheaves on closed subsets: each point gets
the pattern of charts and agreements at it (finitely many patterns `y`), the classes of mutually
agreeing charts at the points of `X₀ ∩ T_y` (`T_y` the closed set of points whose pattern is
smaller than `y`) form a locally constant function on `X₀ ∩ T_y`, which lifts to `T_y`
(`exists_eventually_eq_of_clopenLifting`); the lifted functions determine the shrunk charts. For
`Z` proper over `A`, the hypotheses on `X₀ = Z₀` are the henselian clopen lifting of registry row
A23 applied to the reduced closed subschemes of `Z`
(`AlgebraicGeometry.exists_isClosed_diff_of_henselianLocalRing`) and
`AlgebraicGeometry.eq_empty_of_isClosed_of_forall_ne_closedPoint`.

## References

* [Stacks Project, Tag 0A0B](https://stacks.math.columbia.edu/tag/0A0B)
* [Stacks Project, Tag 09ZG](https://stacks.math.columbia.edu/tag/09ZG)
* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
-/

open Filter Topology

section Lift

variable {X : Type*} [TopologicalSpace X] {X₀ : Set X}

/-- On a closed set `T`, the preimage of any set under a function which is locally constant on
`T` is closed. (This is `ContinuousOn.preimage_isClosed_of_isClosed` for the discrete topology on
`S`, stated without putting a topology on `S`.) -/
lemma isClosed_inter_preimage_of_eventually_eq {S : Type*} {T : Set X} (hT : IsClosed T)
    {f : X → S} (hf : ∀ x ∈ T, ∀ᶠ x' in 𝓝 x, x' ∈ T → f x' = f x) (s : Set S) :
    IsClosed (T ∩ f ⁻¹' s) := by
  rw [isClosed_iff_frequently]
  intro x hx
  have hxT : x ∈ T := isClosed_iff_frequently.1 hT x (hx.mono fun _ h ↦ h.1)
  obtain ⟨y, ⟨hyT, hys⟩, hy⟩ := (hx.and_eventually (hf x hxT)).exists
  refine ⟨hxT, ?_⟩
  change f x ∈ s
  rw [← hy hyT]
  exact hys

/-- Lifting locally constant functions with finitely many values from `T ∩ X₀` to `T`, for
closed sets `T`, given that clopen subsets of `T ∩ X₀` lift to clopen subsets of `T` and that
every nonempty closed set meets `X₀`. -/
lemma exists_eventually_eq_of_clopenLifting
    (hL : ∀ T : Set X, IsClosed T → ∀ K : Set X, K ⊆ T ∩ X₀ → IsClosed K →
      IsClosed ((T ∩ X₀) \ K) → ∃ C : Set X, C ⊆ T ∧ IsClosed C ∧ IsClosed (T \ C) ∧ C ∩ X₀ = K)
    (hM : ∀ T : Set X, IsClosed T → T ∩ X₀ = ∅ → T = ∅) (hX₀ : IsClosed X₀)
    {S : Type*} [Finite S] {T : Set X} (hT : IsClosed T) (g : X → S)
    (hg : ∀ z ∈ T ∩ X₀, ∀ᶠ z' in 𝓝 z, z' ∈ T ∩ X₀ → g z' = g z) :
    ∃ f : X → S, (∀ x ∈ T, ∀ᶠ x' in 𝓝 x, x' ∈ T → f x' = f x) ∧ ∀ z ∈ T ∩ X₀, f z = g z := by
  classical
  have := Fintype.ofFinite S
  suffices H : ∀ s : Finset S, ∀ T : Set X, IsClosed T → ∀ g : X → S,
      (∀ z ∈ T ∩ X₀, ∀ᶠ z' in 𝓝 z, z' ∈ T ∩ X₀ → g z' = g z) → (∀ z ∈ T ∩ X₀, g z ∈ s) →
      ∃ f : X → S, (∀ x ∈ T, ∀ᶠ x' in 𝓝 x, x' ∈ T → f x' = f x) ∧
        ∀ z ∈ T ∩ X₀, f z = g z from
    H Finset.univ T hT g hg fun _ _ ↦ Finset.mem_univ _
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro T hT g _ hgs
    have : T = ∅ := hM T hT (Set.eq_empty_of_forall_notMem fun z hz ↦ by
      simpa using hgs z hz)
    subst this
    exact ⟨g, fun x hx ↦ hx.elim, fun z hz ↦ rfl⟩
  | insert a s ha ih =>
    intro T hT g hg hgs
    have hTX₀ : IsClosed (T ∩ X₀) := hT.inter hX₀
    let K := T ∩ X₀ ∩ g ⁻¹' {a}
    have hK : IsClosed K := isClosed_inter_preimage_of_eventually_eq hTX₀ hg {a}
    have hK' : IsClosed ((T ∩ X₀) \ K) := by
      have : (T ∩ X₀) \ K = T ∩ X₀ ∩ g ⁻¹' {a}ᶜ := by
        ext z
        simp [K]
      rw [this]
      exact isClosed_inter_preimage_of_eventually_eq hTX₀ hg {a}ᶜ
    obtain ⟨C, hCT, hC, hTC, hCK⟩ := hL T hT K Set.inter_subset_left hK hK'
    obtain ⟨f', hf'₁, hf'₂⟩ := ih (T \ C) hTC g
      (fun z hz ↦ (hg z ⟨hz.1.1, hz.2⟩).mono fun z' h hz' ↦ h ⟨hz'.1.1, hz'.2⟩)
      (fun z hz ↦ by
        have hzK : z ∉ K := fun h ↦ hz.1.2 (hCK ▸ h).1
        have : g z ≠ a := fun h ↦ hzK ⟨⟨hz.1.1, hz.2⟩, h⟩
        rcases Finset.mem_insert.1 (hgs z ⟨hz.1.1, hz.2⟩) with h | h
        · exact absurd h this
        · exact h)
    refine ⟨fun x ↦ if x ∈ C then a else f' x, fun x hx ↦ ?_, fun z hz ↦ ?_⟩
    · by_cases hxC : x ∈ C
      · have : (T \ C)ᶜ ∈ 𝓝 x := hTC.isOpen_compl.mem_nhds fun h ↦ h.2 hxC
        filter_upwards [this] with x' hx' hx'T
        have : x' ∈ C := by
          by_contra h
          exact hx' ⟨hx'T, h⟩
        simp [this, hxC]
      · have : Cᶜ ∈ 𝓝 x := hC.isOpen_compl.mem_nhds hxC
        filter_upwards [this, hf'₁ x ⟨hx, hxC⟩] with x' hx'C hx' hx'T
        have hx'C' : x' ∉ C := hx'C
        simp only [hx'C', hxC, ↓reduceIte]
        exact hx' ⟨hx'T, hx'C'⟩
    · by_cases hzC : z ∈ C
      · have : z ∈ K := hCK ▸ ⟨hzC, hz.2⟩
        simp only [hzC, ↓reduceIte]
        exact this.2.symm
      · simp only [hzC, ↓reduceIte]
        exact hf'₂ z ⟨⟨hz.1, hzC⟩, hz.2⟩

end Lift

section Glue

variable {X : Type*} [TopologicalSpace X] {X₀ : Set X}

/-- **Gluing finitely many charts over a closed set lifting clopens** (the topological core of
Stacks 09ZG for sheaves given by finitely many local sections). Let `X₀ ⊆ X` be closed, such that
every nonempty closed set meets `X₀` and clopen subsets of `T ∩ X₀` lift to clopen subsets of
`T` for every closed `T`. Let `W a` be finitely many open sets covering `X₀`, and `Ag a b` open
sets forming an equivalence relation (`W a ⊆ Ag a a`; think "the local sections `s_a` and `s_b`
agree"), with `X₀ ∩ W a ∩ W b ⊆ Ag a b`. Then there are open `V a ⊆ W a` covering `X` with
`V a ∩ V b ⊆ Ag a b`: the local sections glue after shrinking. -/
theorem exists_open_subordinate_of_clopenLifting
    (hL : ∀ T : Set X, IsClosed T → ∀ K : Set X, K ⊆ T ∩ X₀ → IsClosed K →
      IsClosed ((T ∩ X₀) \ K) → ∃ C : Set X, C ⊆ T ∧ IsClosed C ∧ IsClosed (T \ C) ∧ C ∩ X₀ = K)
    (hM : ∀ T : Set X, IsClosed T → T ∩ X₀ = ∅ → T = ∅) (hX₀ : IsClosed X₀)
    {ι : Type*} [Finite ι] (W : ι → Set X) (hW : ∀ a, IsOpen (W a)) (Ag : ι → ι → Set X)
    (hAg : ∀ a b, IsOpen (Ag a b)) (hrefl : ∀ a, W a ⊆ Ag a a)
    (hsymm : ∀ a b, Ag a b ⊆ Ag b a) (htrans : ∀ a b c, Ag a b ∩ Ag b c ⊆ Ag a c)
    (hcov : X₀ ⊆ ⋃ a, W a) (h₀ : ∀ a b, X₀ ∩ W a ∩ W b ⊆ Ag a b) :
    ∃ V : ι → Set X, (∀ a, IsOpen (V a)) ∧ (∀ a, V a ⊆ W a) ∧ (⋃ a, V a) = Set.univ ∧
      ∀ a b, V a ∩ V b ⊆ Ag a b := by
  classical
  -- the pattern of a point: the charts containing it, and the pairs agreeing at it
  let π : X → Set ι × Set (ι × ι) := fun x ↦ ({a | x ∈ W a}, {p | x ∈ Ag p.1 p.2})
  let Tc : Set ι × Set (ι × ι) → Set X := fun y ↦
    {x | (∀ a, x ∈ W a → a ∈ y.1) ∧ ∀ a b, x ∈ Ag a b → (a, b) ∈ y.2}
  have hTc (y : Set ι × Set (ι × ι)) : IsClosed (Tc y) := by
    have : Tc y = (⋂ a, ⋂ (_ : a ∉ y.1), (W a)ᶜ) ∩
        ⋂ a, ⋂ b, ⋂ (_ : (a, b) ∉ y.2), (Ag a b)ᶜ := by
      ext x
      simp only [Tc, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨fun a ha hx ↦ ha (h₁ a hx), fun a b hab hx ↦ hab (h₂ a b hx)⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨fun a hx ↦ by_contra fun ha ↦ h₁ a ha hx,
          fun a b hx ↦ by_contra fun hab ↦ h₂ a b hab hx⟩
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun a ↦ isClosed_iInter fun _ ↦ ?_)
      (isClosed_iInter fun a ↦ isClosed_iInter fun b ↦ isClosed_iInter fun _ ↦ ?_)
    · exact (hW a).isClosed_compl
    · exact (hAg a b).isClosed_compl
  have hπ (x : X) : x ∈ Tc (π x) := ⟨fun _ h ↦ h, fun _ _ h ↦ h⟩
  -- the value at a pattern `y` of a point `z`: the class of the charts containing `z`
  let g : Set ι × Set (ι × ι) → X → Set ι := fun y z ↦ {a | ∃ b, z ∈ W b ∧ (a, b) ∈ y.2}
  have hfin : Finite (Set.range π) := Subtype.finite
  have hpat (y : Set.range π) {a b c : ι} (h₁ : (a, b) ∈ y.1.2) (h₂ : (c, b) ∈ y.1.2) :
      (a, c) ∈ y.1.2 := by
    obtain ⟨_, x₁, rfl⟩ := y
    exact htrans a b c ⟨h₁, hsymm c b h₂⟩
  have hg (y : Set.range π) :
      ∀ z ∈ Tc y ∩ X₀, ∀ᶠ z' in 𝓝 z, z' ∈ Tc y ∩ X₀ → g y z' = g y z := by
    intro z hz
    have hN : ∀ᶠ z' in 𝓝 z, ∀ b, z ∈ W b → z' ∈ W b :=
      eventually_all.2 fun b ↦ by
        by_cases hb : z ∈ W b
        · filter_upwards [(hW b).mem_nhds hb] with z' hz' _ using hz'
        · exact Eventually.of_forall fun _ h ↦ absurd h hb
    filter_upwards [hN] with z' hz'N hz'
    ext a
    constructor
    · rintro ⟨b', hz'b', hab'⟩
      obtain ⟨b₀, hb₀⟩ := Set.mem_iUnion.1 (hcov hz.2)
      have : z' ∈ Ag b₀ b' := h₀ b₀ b' ⟨⟨hz'.2, hz'N b₀ hb₀⟩, hz'b'⟩
      exact ⟨b₀, hb₀, hpat y hab' (hz'.1.2 b₀ b' this)⟩
    · rintro ⟨b, hzb, hab⟩
      exact ⟨b, hz'N b hzb, hab⟩
  choose f hf₁ hf₂ using fun y : Set.range π ↦
    exists_eventually_eq_of_clopenLifting hL hM hX₀ (hTc y) (g y) (hg y)
  -- the lifted values are classes
  have hval (y : Set.range π) (x : X) (hx : x ∈ Tc y) :
      ∃ z ∈ Tc y ∩ X₀, f y x = g y z := by
    by_contra! H
    let Bad := Tc y ∩ f y ⁻¹' {S | ∀ z ∈ Tc y ∩ X₀, S ≠ g y z}
    have hBad : IsClosed Bad := isClosed_inter_preimage_of_eventually_eq (hTc y) (hf₁ y) _
    have : Bad = ∅ := hM Bad hBad (Set.eq_empty_of_forall_notMem fun z hz ↦
      hz.1.2 z ⟨hz.1.1, hz.2⟩ (hf₂ y z ⟨hz.1.1, hz.2⟩))
    exact (Set.eq_empty_iff_forall_notMem.1 this) x ⟨hx, H⟩
  have hclass (y : Set.range π) (z : X) (hz : z ∈ Tc y ∩ X₀) {a a' : ι} (ha : a ∈ g y z)
      (ha' : a' ∈ g y z) : (a, a') ∈ y.1.2 := by
    obtain ⟨b, hzb, hab⟩ := ha
    obtain ⟨b', hzb', hab'⟩ := ha'
    have hbb' : (b, b') ∈ y.1.2 := hz.1.2 b b' (h₀ b b' ⟨⟨hz.2, hzb⟩, hzb'⟩)
    exact hpat y hab (hpat y hab' hbb')
  let V : ι → Set X := fun a ↦
    {x | ∀ᶠ x' in 𝓝 x, x' ∈ W a ∧ ∀ y : Set.range π, x' ∈ Tc y → a ∈ f y x'}
  have hVo (a : ι) : IsOpen (V a) := isOpen_setOfPred_eventually_nhds
  refine ⟨V, hVo, fun a x hx ↦ hx.self_of_nhds.1, ?_, fun a b x hx ↦ ?_⟩
  · -- the `V a` cover a neighbourhood of `X₀`, hence everything
    have hX₀V : X₀ ⊆ ⋃ a, V a := by
      intro z hz
      obtain ⟨a, hza⟩ := Set.mem_iUnion.1 (hcov hz)
      refine Set.mem_iUnion.2 ⟨a, ?_⟩
      refine Filter.Eventually.and ((hW a).mem_nhds hza) (eventually_all.2 fun y ↦ ?_)
      by_cases hzy : z ∈ Tc y
      · filter_upwards [hf₁ y z hzy] with x' hx' hx'y
        rw [hx' hx'y, hf₂ y z ⟨hzy, hz⟩]
        exact ⟨a, hza, hzy.2 a a (hrefl a hza)⟩
      · filter_upwards [(hTc y).isOpen_compl.mem_nhds hzy] with x' hx' hx'y
        exact absurd hx'y hx'
    have hopen : IsOpen (⋃ a, V a) := isOpen_iUnion hVo
    have := hM _ hopen.isClosed_compl (Set.eq_empty_of_forall_notMem fun z hz ↦ hz.1 (hX₀V hz.2))
    exact Set.compl_empty_iff.1 this
  · -- on `V a ∩ V b` the charts `a` and `b` agree
    let y : Set.range π := ⟨π x, x, rfl⟩
    have ha := hx.1.self_of_nhds.2 y (hπ x)
    have hb := hx.2.self_of_nhds.2 y (hπ x)
    obtain ⟨z, hz, hfz⟩ := hval y x (hπ x)
    rw [hfz] at ha hb
    exact hclass y z hz ha hb

end Glue

universe u

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry

open CategoryTheory Limits Opposite IsLocalRing

section ClosedSubsets

variable {A : CommRingCat.{u}} [HenselianLocalRing A] [IsNoetherianRing A] {Z : Scheme.{u}}
  (q : Z ⟶ Spec A) [IsProper q]

/-- **Clopen lifting for closed subsets** of a scheme `Z` proper over a noetherian henselian local
ring: if `T ⊆ Z` is closed and `K ⊆ T ∩ q⁻¹(m)` is clopen in the trace `T ∩ q⁻¹(m)` of `T` on the
closed fibre, then `K = C ∩ q⁻¹(m)` for some `C ⊆ T` clopen in `T`
(`exists_isClopen_inter_eq_of_henselianLocalRing` for the reduced closed subscheme on `T`). -/
theorem exists_isClosed_diff_of_henselianLocalRing (T : Set Z) (hT : IsClosed T) (K : Set Z)
    (hKT : K ⊆ T ∩ q ⁻¹' {closedPoint A}) (hK : IsClosed K)
    (hK' : IsClosed ((T ∩ q ⁻¹' {closedPoint A}) \ K)) :
    ∃ C : Set Z, C ⊆ T ∧ IsClosed C ∧ IsClosed (T \ C) ∧ C ∩ q ⁻¹' {closedPoint A} = K := by
  let I := Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩
  let ι := I.subschemeι
  have hι : Topology.IsClosedEmbedding ι := ι.isClosedEmbedding
  have hrange : Set.range ι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  have hmem (x : I.subscheme) : (ι ≫ q) x = closedPoint A ↔ q (ι x) = closedPoint A := by
    rw [Scheme.Hom.comp_apply]
  obtain ⟨U, hU, hUV⟩ := exists_isClopen_inter_eq_of_henselianLocalRing (ι ≫ q) (ι ⁻¹' K)
    (fun x hx ↦ (hmem x).2 (hKT hx).2) (hK.preimage ι.continuous)
    (ι ⁻¹' ((T ∩ q ⁻¹' {closedPoint A}) \ K)ᶜ) (hK'.isOpen_compl.preimage ι.continuous) (by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_sdiff]
      constructor
      · rintro ⟨h₁, h₂⟩
        by_contra hK
        exact h₁ ⟨⟨hrange ▸ ⟨x, rfl⟩, h₂⟩, hK⟩
      · intro hx
        exact ⟨fun h ↦ h.2 hx, (hKT hx).2⟩)
  refine ⟨ι '' U, ?_, hι.isClosedMap _ hU.1, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hrange ▸ ⟨x, rfl⟩
  · have : T \ ι '' U = ι '' Uᶜ := by
      rw [← hrange, ← Set.image_univ, ← Set.image_sdiff hι.injective]
      congr 1
      ext
      simp
    rw [this]
    exact hι.isClosedMap _ hU.2.isClosed_compl
  · ext z
    constructor
    · rintro ⟨⟨x, hxU, rfl⟩, hm⟩
      have : x ∈ U ∩ (ι ≫ q) ⁻¹' {closedPoint A} := ⟨hxU, (hmem x).2 hm⟩
      rw [hUV] at this
      exact this
    · intro hz
      obtain ⟨x, rfl⟩ : z ∈ Set.range ι := hrange ▸ (hKT hz).1
      have : x ∈ ι ⁻¹' K := hz
      rw [← hUV] at this
      exact ⟨⟨x, this.1, rfl⟩, (hKT hz).2⟩

omit [IsNoetherianRing A] in
include q in
/-- Over a local ring, a closed subset of a universally closed `Z` missing the closed fibre is
empty (`eq_empty_of_isClosed_of_forall_ne_closedPoint`, in the form used by
`exists_open_subordinate_of_clopenLifting`). -/
lemma eq_empty_of_isClosed_of_inter_closedFibre_eq_empty (T : Set Z) (hT : IsClosed T)
    (h : T ∩ q ⁻¹' {closedPoint A} = ∅) : T = ∅ :=
  eq_empty_of_isClosed_of_forall_ne_closedPoint q hT fun z hz hzm ↦
    (Set.eq_empty_iff_forall_notMem.1 h) z ⟨hz, hzm⟩

/-- **Gluing finitely many charts on a scheme proper over a noetherian henselian local ring**:
`exists_open_subordinate_of_clopenLifting` for `X₀` the closed fibre. -/
theorem exists_open_subordinate_of_henselianLocalRing {ι : Type*} [Finite ι] (W : ι → Set Z)
    (hW : ∀ a, IsOpen (W a)) (Ag : ι → ι → Set Z) (hAg : ∀ a b, IsOpen (Ag a b))
    (hrefl : ∀ a, W a ⊆ Ag a a) (hsymm : ∀ a b, Ag a b ⊆ Ag b a)
    (htrans : ∀ a b c, Ag a b ∩ Ag b c ⊆ Ag a c)
    (hcov : q ⁻¹' {closedPoint A} ⊆ ⋃ a, W a)
    (h₀ : ∀ a b, q ⁻¹' {closedPoint A} ∩ W a ∩ W b ⊆ Ag a b) :
    ∃ V : ι → Set Z, (∀ a, IsOpen (V a)) ∧ (∀ a, V a ⊆ W a) ∧ (⋃ a, V a) = Set.univ ∧
      ∀ a b, V a ∩ V b ⊆ Ag a b :=
  exists_open_subordinate_of_clopenLifting
    (fun T hT K hKT hK hK' ↦ exists_isClosed_diff_of_henselianLocalRing q T hT K hKT hK hK')
    (eq_empty_of_isClosed_of_inter_closedFibre_eq_empty q)
    ((isClosed_singleton_closedPoint A).preimage q.continuous) W hW Ag hAg hrefl hsymm htrans
    hcov h₀

end ClosedSubsets

namespace Scheme.Etale

variable {X : Scheme.{u}}

/-- An open subscheme `U` as an étale `X`-scheme. -/
abbrev ofOpens (U : X.Opens) : X.Etale := Etale.mk U.ι

/-- The inclusion `U ≤ V` of open subschemes as a morphism of étale `X`-schemes. -/
def ofOpensHom {U V : X.Opens} (h : U ≤ V) : ofOpens U ⟶ ofOpens V :=
  MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι h) trivial

@[simp]
lemma ofOpensHom_left {U V : X.Opens} (h : U ≤ V) : (ofOpensHom h).left = X.homOfLE h := rfl

@[reassoc (attr := simp)]
lemma ofOpensHom_comp {U V W : X.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W) :
    ofOpensHom h₁ ≫ ofOpensHom h₂ = ofOpensHom (h₁.trans h₂) := by
  apply MorphismProperty.Over.Hom.ext
  exact X.homOfLE_homOfLE h₁ h₂

/-- An étale `X`-scheme `Y` whose image lies in the open `U` maps to `U`. -/
def liftOfOpens {Y : X.Etale} {U : X.Opens} (h : Set.range Y.hom ⊆ (U : Set X)) : Y ⟶ ofOpens U :=
  let f : Y.left ⟶ X := Y.hom
  MorphismProperty.Over.homMk
    (AlgebraicGeometry.IsOpenImmersion.lift U.ι f ((Scheme.Opens.range_ι U).symm ▸ h))
    (AlgebraicGeometry.IsOpenImmersion.lift_fac U.ι f _) trivial

lemma range_hom_subset {Y : X.Etale} {U : X.Opens} (g : Y ⟶ ofOpens U) :
    Set.range Y.hom ⊆ (U : Set X) := by
  rintro _ ⟨y, rfl⟩
  have e := congrArg (fun f ↦ f y) (MorphismProperty.Over.w g)
  simp only [Scheme.Hom.comp_apply] at e
  exact (congrArg (· ∈ (U : Set X)) e).mp ((Scheme.Opens.range_ι U).le ⟨_, rfl⟩)

lemma eq_liftOfOpens_comp_ofOpensHom {Y : X.Etale} {U V : X.Opens} (h : U ≤ V) (g : Y ⟶ ofOpens V)
    (hY : Set.range Y.hom ⊆ (U : Set X)) : g = liftOfOpens hY ≫ ofOpensHom h := by
  apply MorphismProperty.Over.Hom.ext
  have e₁ : g.left ≫ V.ι = (liftOfOpens hY).left ≫ U.ι :=
    (MorphismProperty.Over.w g).trans (MorphismProperty.Over.w (liftOfOpens hY)).symm
  have e₂ : ((liftOfOpens hY).left ≫ X.homOfLE h) ≫ V.ι = (liftOfOpens hY).left ≫ U.ι :=
    (Category.assoc _ _ _).trans (congrArg _ (X.homOfLE_ι h))
  exact (cancel_mono V.ι).1 (e₁.trans e₂.symm)

end Scheme.Etale

section Sheaves

open Scheme.Etale

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (Type u))

/-- Sections over an open subscheme which agree locally (for the Zariski topology) agree. -/
lemma Scheme.eq_of_forall_mem_opens {U : X.Opens} {σ σ' : F.obj.obj (op (ofOpens U))}
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧
      F.obj.map (ofOpensHom hV).op σ = F.obj.map (ofOpensHom hV).op σ') : σ = σ' := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  let ι := {V : X.Opens //
    ∃ hV : V ≤ U, F.obj.map (ofOpensHom hV).op σ = F.obj.map (ofOpensHom hV).op σ'}
  have hcov : Sieve.ofArrows (fun i : ι ↦ ofOpens i.1) (fun i ↦ ofOpensHom i.2.1) ∈
      X.smallEtaleTopology (ofOpens U) := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun u ↦ ?_
    obtain ⟨V, hV, hxV, hVσ⟩ := h u.1 u.2
    refine Set.mem_iUnion.2 ⟨⟨V, hV, hVσ⟩, ⟨u.1, hxV⟩, ?_⟩
    exact Subtype.ext (Scheme.homOfLE_apply hV ⟨u.1, hxV⟩)
  refine (hF _ hcov).isSeparatedFor.ext ?_
  rintro Y f ⟨_, g, _, ⟨i⟩, rfl⟩
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, i.2.2]

/-- Gluing sections over a Zariski open cover. -/
lemma Scheme.exists_eq_of_forall_opens {ι : Type*} (V : ι → X.Opens) (hV : ∀ x, ∃ a, x ∈ V a)
    (σ : ∀ a, F.obj.obj (op (ofOpens (V a))))
    (hσ : ∀ a b, F.obj.map (ofOpensHom (inf_le_left : V a ⊓ V b ≤ V a)).op (σ a) =
      F.obj.map (ofOpensHom (inf_le_right : V a ⊓ V b ≤ V b)).op (σ b)) :
    ∃ t : F.obj.obj (op (Etale.top X)),
      ∀ a, F.obj.map ((Etale.isTerminalTop X).from (ofOpens (V a))).op t = σ a := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  have hcov : Sieve.ofArrows (fun a ↦ ofOpens (V a))
      (fun a ↦ (Etale.isTerminalTop X).from (ofOpens (V a))) ∈
        X.smallEtaleTopology (Etale.top X) := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨a, ha⟩ := hV x
    exact Set.mem_iUnion.2 ⟨a, ⟨x, ha⟩, rfl⟩
  have hS := (Presieve.isSheafFor_iff_generate _).2 (hF _ hcov)
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hS σ (fun a b Y gi gj _ ↦ by
    have hY : Set.range Y.hom ⊆ ((V a ⊓ V b : X.Opens) : Set X) := fun y hy ↦
      ⟨range_hom_subset gi hy, range_hom_subset gj hy⟩
    rw [eq_liftOfOpens_comp_ofOpensHom inf_le_left gi hY,
      eq_liftOfOpens_comp_ofOpensHom inf_le_right gj hY, op_comp, op_comp, Functor.map_comp_apply,
      Functor.map_comp_apply, hσ a b])
  exact ⟨t, ht⟩

end Sheaves

section Henselian

open Scheme.Etale

variable {A : CommRingCat.{u}} [HenselianLocalRing A] [IsNoetherianRing A] {Z : Scheme.{u}}
  (q : Z ⟶ Spec A) [IsProper q] (F : Sheaf Z.smallEtaleTopology (Type u))

/-- **Zariski `H⁰` over a noetherian henselian local ring, chart form** (Stacks 0A0B, noetherian
case): let `Z` be proper over a noetherian henselian local ring `A`, `F` an étale sheaf on `Z`, and
`s a ∈ F(W a)` finitely many sections over opens `W a` covering the closed fibre, any two of which
agree on a neighbourhood of each point of the closed fibre where both are defined. Then there is a
global section of `F` which agrees with each `s a` near each point of the closed fibre in `W a`. -/
theorem exists_section_of_forall_closedFibre_of_henselianLocalRing {ι : Type*} [Finite ι]
    (W : ι → Z.Opens) (s : ∀ a, F.obj.obj (op (ofOpens (W a))))
    (hcov : ∀ z, q z = closedPoint A → ∃ a, z ∈ W a)
    (h₀ : ∀ a b z, q z = closedPoint A → z ∈ W a → z ∈ W b → ∃ (U : Z.Opens) (ha : U ≤ W a)
      (hb : U ≤ W b), z ∈ U ∧ F.obj.map (ofOpensHom ha).op (s a) =
        F.obj.map (ofOpensHom hb).op (s b)) :
    ∃ t : F.obj.obj (op (Scheme.Etale.top Z)), ∀ a z, q z = closedPoint A → z ∈ W a →
      ∃ (U : Z.Opens) (ha : U ≤ W a), z ∈ U ∧
        F.obj.map ((Scheme.Etale.isTerminalTop Z).from (ofOpens U)).op t =
          F.obj.map (ofOpensHom ha).op (s a) := by
  let Ag : ι → ι → Set Z := fun a b ↦ {z | ∃ (U : Z.Opens) (ha : U ≤ W a) (hb : U ≤ W b),
    z ∈ U ∧ F.obj.map (ofOpensHom ha).op (s a) = F.obj.map (ofOpensHom hb).op (s b)}
  have hAg (a b : ι) : IsOpen (Ag a b) := isOpen_iff_forall_mem_open.2
    fun z ⟨U, ha, hb, hz, h⟩ ↦ ⟨U, fun z' hz' ↦ ⟨U, ha, hb, hz', h⟩, U.2, hz⟩
  have hrefl (a : ι) : (W a : Set Z) ⊆ Ag a a := fun z hz ↦ ⟨W a, le_rfl, le_rfl, hz, rfl⟩
  have hsymm (a b : ι) : Ag a b ⊆ Ag b a := fun z ⟨U, ha, hb, hz, h⟩ ↦ ⟨U, hb, ha, hz, h.symm⟩
  have hres {U U' V : Z.Opens} (h₁ : U' ≤ U) (h₂ : U ≤ V) (σ : F.obj.obj (op (ofOpens V))) :
      F.obj.map (ofOpensHom h₁).op (F.obj.map (ofOpensHom h₂).op σ) =
        F.obj.map (ofOpensHom (h₁.trans h₂)).op σ := by
    rw [← Functor.map_comp_apply, ← op_comp, ofOpensHom_comp]
  have htrans (a b c : ι) : Ag a b ∩ Ag b c ⊆ Ag a c := by
    rintro z ⟨⟨U₁, ha, hb, hz₁, h₁⟩, ⟨U₂, hb', hc, hz₂, h₂⟩⟩
    refine ⟨U₁ ⊓ U₂, inf_le_left.trans ha, inf_le_right.trans hc, ⟨hz₁, hz₂⟩, ?_⟩
    have e₁ := congrArg (F.obj.map (ofOpensHom (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op) h₁
    have e₂ := congrArg (F.obj.map (ofOpensHom (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op) h₂
    rw [hres, hres] at e₁ e₂
    exact e₁.trans e₂
  obtain ⟨V, hVo, hVW, hVcov, hVAg⟩ := exists_open_subordinate_of_henselianLocalRing q
    (fun a ↦ (W a : Set Z)) (fun a ↦ (W a).2) Ag hAg hrefl hsymm htrans
    (fun z hz ↦ by
      obtain ⟨a, ha⟩ := hcov z hz
      exact Set.mem_iUnion.2 ⟨a, ha⟩)
    (fun a b z ⟨⟨hz, ha⟩, hb⟩ ↦ h₀ a b z hz ha hb)
  let V' : ι → Z.Opens := fun a ↦ ⟨V a, hVo a⟩
  have hV'W (a : ι) : V' a ≤ W a := hVW a
  have hV'cov (x : Z) : ∃ a, x ∈ V' a := Set.mem_iUnion.1 (hVcov ▸ Set.mem_univ x)
  obtain ⟨t, ht⟩ := Scheme.exists_eq_of_forall_opens F V' hV'cov
    (fun a ↦ F.obj.map (ofOpensHom (hV'W a)).op (s a)) (fun a b ↦ by
      apply Scheme.eq_of_forall_mem_opens F
      intro x hx
      obtain ⟨U, ha, hb, hxU, hU⟩ := hVAg a b ⟨hx.1, hx.2⟩
      refine ⟨U ⊓ (V' a ⊓ V' b), inf_le_right, ⟨hxU, hx⟩, ?_⟩
      rw [hres, hres, hres, hres]
      have := congrArg (F.obj.map (ofOpensHom (inf_le_left : U ⊓ (V' a ⊓ V' b) ≤ U)).op) hU
      rw [hres, hres] at this
      exact this)
  refine ⟨t, fun a z hz hza ↦ ?_⟩
  obtain ⟨b, hzb⟩ := hV'cov z
  obtain ⟨U, ha, hb, hzU, hU⟩ := h₀ a b z hz hza (hVW b hzb)
  refine ⟨U ⊓ V' b, inf_le_left.trans ha, ⟨hzU, hzb⟩, ?_⟩
  have e₁ : F.obj.map ((Scheme.Etale.isTerminalTop Z).from (ofOpens (U ⊓ V' b))).op t =
      F.obj.map (ofOpensHom (inf_le_right : U ⊓ V' b ≤ V' b)).op
        (F.obj.map ((Scheme.Etale.isTerminalTop Z).from (ofOpens (V' b))).op t) := by
    rw [← Functor.map_comp_apply, ← op_comp,
      (Scheme.Etale.isTerminalTop Z).hom_ext (ofOpensHom _ ≫ _)
        ((Scheme.Etale.isTerminalTop Z).from (ofOpens (U ⊓ V' b)))]
  rw [e₁, ht b, hres]
  have := congrArg (F.obj.map (ofOpensHom (inf_le_left : U ⊓ V' b ≤ U)).op) hU
  rw [hres, hres] at this
  exact this.symm

/-- **Zariski `H⁰` over a noetherian henselian local ring** (Stacks 0A0B, noetherian case, for the
sheaves `i^{-1}(F|_{Z_{Zar}})`): let `Z` be proper over a noetherian henselian local ring `A`,
`i : Z₀ ⟶ Z` its closed fibre and `F` an étale sheaf on `Z`. A section `t'` of `i^* F` over `Z₀`
which, near every point of the closed fibre, is the restriction of a section of `F` over a Zariski
open of `Z`, is the restriction of a global section of `F`. -/
theorem exists_eq_of_forall_closedFibre_of_henselianLocalRing {Z₀ : Scheme.{u}} {i : Z₀ ⟶ Z}
    {q₀ : Z₀ ⟶ Spec (.of (ResidueField A))}
    (hi : IsPullback i q₀ q (Spec.map (CommRingCat.ofHom (residue A))))
    (t' : ((Scheme.etalePullback i).obj F).obj.obj (op (Scheme.Etale.top Z₀)))
    (ht' : ∀ z, q z = closedPoint A → ∃ (W : Z.Opens) (s : F.obj.obj (op (ofOpens W))), z ∈ W ∧
      ((Scheme.etaleAdjunction i).unit.app F).hom.app (op (ofOpens W)) s =
        ((Scheme.etalePullback i).obj F).obj.map
          ((Scheme.Etale.isTerminalTop Z₀).from ((Scheme.Etale.pullback i).obj (ofOpens W))).op
            t') :
    ∃ t : F.obj.obj (op (Scheme.Etale.top Z)), Scheme.etaleSectionsRestrict i F t = t' := by
  classical
  let G := (Scheme.etalePullback i).obj F
  let η := (Scheme.etaleAdjunction i).unit.app F
  have hG := (isSheaf_iff_isSheaf_of_type _ _).1 G.property
  have hrange : Set.range i = q ⁻¹' {closedPoint A} :=
    range_eq_preimage_closedPoint_of_isPullback hi
  have hres {U U' V : Z.Opens} (h₁ : U' ≤ U) (h₂ : U ≤ V) (σ : F.obj.obj (op (ofOpens V))) :
      F.obj.map (ofOpensHom h₁).op (F.obj.map (ofOpensHom h₂).op σ) =
        F.obj.map (ofOpensHom (h₁.trans h₂)).op σ := by
    rw [← Functor.map_comp_apply, ← op_comp, ofOpensHom_comp]
  -- the images of restrictions of the local sections are restrictions of `t'`
  have hnat {W V : Z.Opens} (h : V ≤ W) (s : F.obj.obj (op (ofOpens W)))
      (hs : η.hom.app (op (ofOpens W)) s = G.obj.map ((Scheme.Etale.isTerminalTop Z₀).from
        ((Scheme.Etale.pullback i).obj (ofOpens W))).op t') :
      η.hom.app (op (ofOpens V)) (F.obj.map (ofOpensHom h).op s) =
        G.obj.map ((Scheme.Etale.isTerminalTop Z₀).from
          ((Scheme.Etale.pullback i).obj (ofOpens V))).op t' := by
    have n : η.hom.app (op (ofOpens V)) (F.obj.map (ofOpensHom h).op s) =
        G.obj.map ((Scheme.Etale.pullback i).map (ofOpensHom h)).op
          (η.hom.app (op (ofOpens W)) s) :=
      NatTrans.naturality_apply η.hom (ofOpensHom h).op s
    rw [n, hs, ← Functor.map_comp_apply, ← op_comp,
      (Scheme.Etale.isTerminalTop Z₀).hom_ext (_ ≫ (Scheme.Etale.isTerminalTop Z₀).from _)
        ((Scheme.Etale.isTerminalTop Z₀).from _)]
  -- finitely many local sections cover the closed fibre
  choose W s hzW hs using fun z : {z : Z // q z = closedPoint A} ↦ ht' z.1 z.2
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace q
  have hcpt : IsCompact (q ⁻¹' {closedPoint A}) :=
    ((isClosed_singleton_closedPoint A).preimage q.continuous).isCompact
  obtain ⟨S, hS⟩ := hcpt.elim_finite_subcover (fun z ↦ (W z : Set Z)) (fun z ↦ (W z).2)
    (fun z hz ↦ Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzW ⟨z, hz⟩⟩)
  -- agreement near the closed fibre
  have h₀ (a b : S) (z : Z) (hz : q z = closedPoint A) (ha : z ∈ W a) (hb : z ∈ W b) :
      ∃ (U : Z.Opens) (ha : U ≤ W a) (hb : U ≤ W b), z ∈ U ∧
        F.obj.map (ofOpensHom ha).op (s a) = F.obj.map (ofOpensHom hb).op (s b) := by
    let V := W a ⊓ W b
    let σ := F.obj.map (ofOpensHom (inf_le_left : V ≤ W a)).op (s a)
    let σ' := F.obj.map (ofOpensHom (inf_le_right : V ≤ W b)).op (s b)
    have hk : G.obj.map (𝟙 _ : (Scheme.Etale.pullback i).obj (ofOpens V) ⟶ _).op
        (η.hom.app (op (ofOpens V)) σ) =
        G.obj.map (𝟙 _ : (Scheme.Etale.pullback i).obj (ofOpens V) ⟶ _).op
          (η.hom.app (op (ofOpens V)) σ') := by
      rw [hnat _ _ (hs a), hnat _ _ (hs b)]
    have hL := Scheme.range_subset_etaleAgreementLocus i (𝟙 _) hk
    let L := Scheme.etaleAgreementLocus F σ σ'
    have hLo : IsOpen L := Scheme.isOpen_etaleAgreementLocus σ σ'
    obtain ⟨z₀, hz₀⟩ : z ∈ Set.range i := hrange ▸ hz
    let w : (ofOpens V).left := ⟨z, ha, hb⟩
    obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := V.ι) (g := i) w z₀
      hz₀.symm
    have hwL : w ∈ L := by
      have := hL ⟨p, rfl⟩
      rw [← hp]
      exact this
    let U : Z.Opens := ⟨V.ι '' L, V.ι.isOpenEmbedding.isOpenMap L hLo⟩
    have hUV : U ≤ V := by
      rintro _ ⟨x, -, rfl⟩
      exact (Scheme.Opens.range_ι V).le ⟨x, rfl⟩
    refine ⟨U, hUV.trans inf_le_left, hUV.trans inf_le_right, ⟨w, hwL, rfl⟩, ?_⟩
    rw [← hres hUV inf_le_left, ← hres hUV inf_le_right]
    refine Scheme.map_eq_of_range_subset_etaleAgreementLocus (ofOpensHom hUV) ?_
    rintro _ ⟨u, rfl⟩
    obtain ⟨x, hxL, hx⟩ := u.2
    have : (ofOpensHom hUV).left u = x := by
      apply V.ι.isOpenEmbedding.injective
      have e := congrArg (fun φ ↦ φ u) (Z.homOfLE_ι hUV)
      simp only [Scheme.Hom.comp_apply] at e
      exact e.trans hx.symm
    rw [this]
    exact hxL
  obtain ⟨t, ht⟩ := exists_section_of_forall_closedFibre_of_henselianLocalRing q F
    (fun a : S ↦ W a) (fun a ↦ s a)
    (fun z hz ↦ by
      obtain ⟨a, ha⟩ := Set.mem_iUnion₂.1 (hS hz)
      exact ⟨⟨a, ha.1⟩, ha.2⟩)
    h₀
  refine ⟨t, ?_⟩
  -- near every point of `Z₀`, the restriction of `t` is that of `t'`
  have hloc (z₀ : Z₀) : ∃ U : Z.Opens, i z₀ ∈ U ∧
      G.obj.map ((Scheme.Etale.isTerminalTop Z₀).from
        ((Scheme.Etale.pullback i).obj (ofOpens U))).op (Scheme.etaleSectionsRestrict i F t) =
      G.obj.map ((Scheme.Etale.isTerminalTop Z₀).from
        ((Scheme.Etale.pullback i).obj (ofOpens U))).op t' := by
    have hz : q (i z₀) = closedPoint A := hrange.le ⟨z₀, rfl⟩
    obtain ⟨a, ha⟩ := Set.mem_iUnion₂.1 (hS hz)
    obtain ⟨U, hUa, hzU, hU⟩ := ht ⟨a, ha.1⟩ (i z₀) hz ha.2
    refine ⟨U, hzU, ?_⟩
    have hsec : (Scheme.Etale.isTerminalTop Z₀).from ((Scheme.Etale.pullback i).obj (ofOpens U)) ≫
        Scheme.Etale.sectionOfHom i (Scheme.Etale.top Z) i (Category.comp_id i) =
          (Scheme.Etale.pullback i).map ((Scheme.Etale.isTerminalTop Z).from (ofOpens U)) := by
      apply MorphismProperty.Over.Hom.ext
      apply pullback.hom_ext
      · change pullback.snd U.ι i ≫ pullback.lift i (𝟙 Z₀) _ ≫ pullback.fst (𝟙 Z) i =
          pullback.lift (pullback.fst U.ι i ≫ U.ι) (pullback.snd U.ι i) _ ≫ pullback.fst (𝟙 Z) i
        rw [pullback.lift_fst, pullback.lift_fst, pullback.condition]
      · change pullback.snd U.ι i ≫ pullback.lift i (𝟙 Z₀) _ ≫ pullback.snd (𝟙 Z) i =
          pullback.lift (pullback.fst U.ι i ≫ U.ι) (pullback.snd U.ι i) _ ≫ pullback.snd (𝟙 Z) i
        rw [pullback.lift_snd, pullback.lift_snd, Category.comp_id]
    have n : η.hom.app (op (ofOpens U))
        (F.obj.map ((Scheme.Etale.isTerminalTop Z).from (ofOpens U)).op t) =
        G.obj.map ((Scheme.Etale.pullback i).map
          ((Scheme.Etale.isTerminalTop Z).from (ofOpens U))).op
            (η.hom.app (op (Scheme.Etale.top Z)) t) :=
      NatTrans.naturality_apply η.hom _ t
    rw [Scheme.etaleSectionsRestrict, Scheme.sectionAlong, ← Functor.map_comp_apply, ← op_comp,
      hsec, ← n, hU]
    exact hnat hUa (s a) (hs a)
  choose U hzU hU using hloc
  have hcov : Sieve.ofArrows (fun z₀ : Z₀ ↦ (Scheme.Etale.pullback i).obj (ofOpens (U z₀)))
      (fun z₀ ↦ (Scheme.Etale.isTerminalTop Z₀).from _) ∈
        Z₀.smallEtaleTopology (Scheme.Etale.top Z₀) := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun z₀ ↦ ?_
    obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback (f := (U z₀).ι) (g := i)
      ⟨i z₀, hzU z₀⟩ z₀ rfl
    exact Set.mem_iUnion.2 ⟨z₀, p, hp⟩
  refine (hG _ hcov).isSeparatedFor.ext ?_
  rintro Y f ⟨_, g, _, ⟨z₀⟩, rfl⟩
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hU z₀]

end Henselian

end AlgebraicGeometry
