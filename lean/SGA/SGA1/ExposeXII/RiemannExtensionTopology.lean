/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannExtensionLocal
import SGA.Foundations.Analytic.RiemannSurfacePunctures

/-!
# SGA 1, Exposé XII, 5.1 for curves: extending maps of coverings across punctures

Topological part of the extension of the Riemann existence theorem across finitely many points
of a normal curve (`SGA.SGA1.ExposeXII.RiemannExtension`). Let `p : E → X` be a covering map,
`Y` Hausdorff, `q : Y → X` a closed map, `Ω ⊆ X` open, and suppose every point `x ∉ Ω` has
connected punctured neighbourhoods `N` with `N ∖ {x} ⊆ Ω` (for curves: `x` is a regular point
and the points outside `Ω` are isolated), and `q⁻¹(x)` finite.

* `exists_tendsto_nhdsWithin`: a continuous map `f` on a punctured neighbourhood of `e`, lying over
  `p`, converges at `e` to a point of `q⁻¹(p e)`: its cluster values lie in the finite fibre and
  the punctured neighbourhoods are connected.
* `exists_continuous_extension`: hence a continuous `Φ₀ : p⁻¹(Ω) → Y` over `X` extends to a
  continuous `Φ : E → Y` over `X`.
* `injective_of_extension`: if moreover `Φ₀` is an open embedding of `p⁻¹(Ω)` whose image contains
  `q⁻¹(Ω)` and the points of `Y` over `X ∖ Ω` have connected punctured neighbourhoods, then `Φ` is
  injective: two points of a fibre with the same image would put a connected punctured
  neighbourhood of that image into two sheets of `E`.
* `isPreconnected_compl_of_forall`: removing from a connected space a closed set of points with
  connected punctured neighbourhoods leaves it connected; e.g. `p⁻¹(Ω)` is connected when `E` is
  (`isPreconnected_preimage_of_preconnectedSpace`).

General topology, no reference beyond the classical arguments for branched coverings (e.g.
Forster, *Lectures on Riemann surfaces*, §8).
-/

noncomputable section

open Topology Set Filter

namespace SGA.SGA1.ExposeXII

namespace RiemannExtension

variable {E X Y : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]

/-- A preconnected set contained in a union of pairwise disjoint open sets `U i`, `i ∈ F`, and
meeting `U i₀` is contained in `U i₀`. -/
lemma subset_of_isPreconnected_of_pairwiseDisjoint {ι : Type*} {s : Set Y} (hs : IsPreconnected s)
    {F : Set ι} {U : ι → Set Y} (hU : ∀ i, IsOpen (U i)) (hd : F.PairwiseDisjoint U)
    (hsub : s ⊆ ⋃ i ∈ F, U i) {i₀ : ι} (hi₀ : i₀ ∈ F) (hne : (s ∩ U i₀).Nonempty) :
    s ⊆ U i₀ := by
  refine hs.subset_left_of_subset_union (hU i₀) (isOpen_biUnion (s := F \ {i₀}) fun i _ ↦ hU i)
    ?_ ?_ hne
  · rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hd hi₀ hi.1 (Ne.symm hi.2)
  · intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hsub hz)
    by_cases h : i = i₀
    · exact Or.inl (h ▸ hzi)
    · exact Or.inr (mem_iUnion₂.mpr ⟨i, ⟨hi, h⟩, hzi⟩)

section Sheet

variable {p : E → X} (hp : IsCoveringMap p) {Ω : Set X}
include hp

/-- Connected punctured neighbourhoods lift along a covering map. -/
lemma hasConnectedPuncturedNhds_of_isCoveringMap {e : E}
    (h : HasConnectedPuncturedNhds (p e)) : HasConnectedPuncturedNhds e := by
  obtain ⟨s, hes, hps⟩ := hp.isLocalHomeomorph e
  rw [hps] at h
  exact HasConnectedPuncturedNhds.of_openPartialHomeomorph s hes h

/-- If `N ∖ {p e} ⊆ Ω` for a neighbourhood `N` of `p e`, then some neighbourhood `N'` of `e` has
`N' ∖ {e}` over `Ω` (through the sheet of the covering containing `e`). -/
lemma exists_mem_nhds_diff_subset {e : E} {N : Set X} (hN : N ∈ 𝓝 (p e))
    (hNΩ : N \ {p e} ⊆ Ω) : ∃ N' ∈ 𝓝 e, N' \ {e} ⊆ p ⁻¹' Ω := by
  obtain ⟨s, hes, hps⟩ := hp.isLocalHomeomorph e
  refine ⟨s.source ∩ p ⁻¹' N, inter_mem (s.open_source.mem_nhds hes)
    (hp.continuous.continuousAt hN), ?_⟩
  rintro e' ⟨⟨he's, he'N⟩, he'e⟩
  refine hNΩ ⟨he'N, fun h ↦ he'e ?_⟩
  rw [mem_singleton_iff, hps] at h
  exact s.injOn he's hes h

end Sheet

/-- **Limits at a puncture**: let `Y` be Hausdorff, `q : Y → X` a closed map with `q⁻¹(x)`
finite, and `f` a continuous map on a punctured neighbourhood `N₀ ∖ {e}` of a point `e` with
connected punctured neighbourhoods, lying over a map `p` continuous at `e` with `p e = x`. Then
`f` converges at `e` to a point of `q⁻¹(x)`. -/
theorem exists_tendsto_nhdsWithin [T2Space Y] {q : Y → X} (hq : IsClosedMap q) {x : X}
    (hfin : (q ⁻¹' {x}).Finite) {p : E → X} {e : E} (he : HasConnectedPuncturedNhds e)
    (hpc : ContinuousAt p e) (hpe : p e = x) {N₀ : Set E} (hN₀ : N₀ ∈ 𝓝 e) {f : E → Y}
    (hf : ContinuousOn f (N₀ \ {e})) (hfq : ∀ e' ∈ N₀ \ {e}, q (f e') = p e') :
    ∃ y, q y = x ∧ Tendsto f (𝓝[≠] e) (𝓝 y) := by
  classical
  by_contra! H
  set F := q ⁻¹' {x}
  have hW : ∀ y, ∃ W ∈ 𝓝 y, y ∈ F → ∃ᶠ e' in 𝓝[≠] e, f e' ∉ W := by
    intro y
    by_cases hy : y ∈ F
    · obtain ⟨W, hW, hWf⟩ := not_tendsto_iff_exists_frequently_notMem.mp (H y hy)
      exact ⟨W, hW, fun _ ↦ hWf⟩
    · exact ⟨univ, univ_mem, fun h ↦ absurd h hy⟩
  choose W hWy hWf using hW
  obtain ⟨U, hU, hUd⟩ := hfin.t2_separation
  let O : Y → Set Y := fun y ↦ interior (W y) ∩ U y
  have hOo (y : Y) : IsOpen (O y) := isOpen_interior.inter (hU y).2
  have hOd : F.PairwiseDisjoint O := hUd.mono fun y ↦ inter_subset_right
  -- away from the `O y`, the image under `q` misses a neighbourhood of `x`
  set K := (⋃ y ∈ F, O y)ᶜ
  have hK : IsClosed (q '' K) :=
    hq _ (isOpen_biUnion fun y _ ↦ hOo y).isClosed_compl
  have hxK : x ∉ q '' K := by
    rintro ⟨y, hyK, rfl⟩
    exact hyK (mem_iUnion₂.mpr ⟨y, rfl, interior_mem_nhds.mpr (hWy y) |> mem_of_mem_nhds,
      (hU y).1⟩)
  have hM : N₀ ∩ p ⁻¹' (q '' K)ᶜ ∈ 𝓝 e :=
    inter_mem hN₀ (hpc (hK.isOpen_compl.mem_nhds (hpe ▸ hxK)))
  obtain ⟨N', hN'M, hN'o, heN', hN'c, z₀, hz₀N', hz₀e⟩ := he _ hM
  have hsub : f '' (N' \ {e}) ⊆ ⋃ y ∈ F, O y := by
    rintro _ ⟨e', ⟨he'N', he'e⟩, rfl⟩
    by_contra hK'
    refine (hN'M he'N').2 ⟨f e', hK', ?_⟩
    exact hfq e' ⟨(hN'M he'N').1, he'e⟩
  have hcont : ContinuousOn f (N' \ {e}) :=
    hf.mono fun e' he' ↦ ⟨(hN'M he'.1).1, he'.2⟩
  have hconn : IsPreconnected (f '' (N' \ {e})) := hN'c.image f hcont
  obtain ⟨y₀, hy₀F, hy₀⟩ := mem_iUnion₂.mp (hsub ⟨z₀, ⟨hz₀N', hz₀e⟩, rfl⟩)
  have hall : f '' (N' \ {e}) ⊆ O y₀ :=
    subset_of_isPreconnected_of_pairwiseDisjoint hconn hOo hOd hsub hy₀F
      ⟨f z₀, ⟨z₀, ⟨hz₀N', hz₀e⟩, rfl⟩, hy₀⟩
  have hev : ∀ᶠ e' in 𝓝[≠] e, f e' ∈ W y₀ :=
    Filter.mem_of_superset (sdiff_mem_nhdsWithin_compl (hN'o.mem_nhds heN') {e})
      fun e' he' ↦ show f e' ∈ W y₀ from interior_subset (hall ⟨e', he', rfl⟩).1
  exact (hWf y₀ hy₀F) (hev.mono fun _ h h' ↦ h' h)

section Extension

variable {p : E → X} {q : Y → X} {Ω : Set X}

/-- **Extension of a map of coverings across punctures**: let `p : E → X` be a covering map,
`Y` Hausdorff, `q : Y → X` a closed map, `Ω ⊆ X` open, such that every `x ∉ Ω` has connected
punctured neighbourhoods, some neighbourhood `N` of `x` with `N ∖ {x} ⊆ Ω`, and finite fibre
`q⁻¹(x)`. Then every continuous `Φ₀` on `p⁻¹(Ω)` lying over `X` extends to a continuous
`Φ : E → Y` over `X`. -/
theorem exists_continuous_extension [T2Space Y] (hp : IsCoveringMap p) (hq : IsClosedMap q)
    (hΩ : IsOpen Ω) (hpunct : ∀ x ∉ Ω, HasConnectedPuncturedNhds x)
    (hiso : ∀ x ∉ Ω, ∃ N ∈ 𝓝 x, N \ {x} ⊆ Ω) (hfin : ∀ x ∉ Ω, (q ⁻¹' {x}).Finite)
    {Φ₀ : E → Y} (hΦc : ContinuousOn Φ₀ (p ⁻¹' Ω)) (hΦq : ∀ e, p e ∈ Ω → q (Φ₀ e) = p e) :
    ∃ Φ : E → Y, Continuous Φ ∧ (∀ e, q (Φ e) = p e) ∧ ∀ e, p e ∈ Ω → Φ e = Φ₀ e := by
  classical
  have hlim : ∀ e, p e ∉ Ω → ∃ y, q y = p e ∧ Tendsto Φ₀ (𝓝[≠] e) (𝓝 y) ∧
      ∃ N' ∈ 𝓝 e, N' \ {e} ⊆ p ⁻¹' Ω := by
    intro e he
    obtain ⟨N, hN, hNΩ⟩ := hiso _ he
    obtain ⟨N', hN', hN'Ω⟩ := exists_mem_nhds_diff_subset hp hN hNΩ
    obtain ⟨y, hy, hlim⟩ := exists_tendsto_nhdsWithin hq (hfin _ he)
      (hasConnectedPuncturedNhds_of_isCoveringMap hp (hpunct _ he)) hp.continuous.continuousAt rfl
      hN' (hΦc.mono hN'Ω) fun e' he' ↦ hΦq e' (hN'Ω he')
    exact ⟨y, hy, hlim, N', hN', hN'Ω⟩
  choose y hyq hyt N' hN' hN'Ω using hlim
  let Φ : E → Y := fun e ↦ if h : p e ∈ Ω then Φ₀ e else y e h
  have hΦΩ (e : E) (he : p e ∈ Ω) : Φ e = Φ₀ e := dite_eq_left he
  refine ⟨Φ, continuous_iff_continuousAt.mpr fun e ↦ ?_, fun e ↦ ?_, hΦΩ⟩
  · by_cases he : p e ∈ Ω
    · have hU : p ⁻¹' Ω ∈ 𝓝 e := (hΩ.preimage hp.continuous).mem_nhds he
      refine ((hΦc.continuousAt hU).congr ?_)
      filter_upwards [hU] with e' he'
      exact (hΦΩ e' he').symm
    · rw [continuousAt_iff_punctured_nhds]
      have : Φ e = y e he := dite_eq_right he
      rw [this]
      refine (hyt e he).congr' ?_
      filter_upwards [sdiff_mem_nhdsWithin_compl (hN' e he) {e}] with e' he'
      exact (hΦΩ e' (hN'Ω e he he')).symm
  · by_cases he : p e ∈ Ω
    · rw [hΦΩ e he, hΦq e he]
    · change q (dite _ _ _) = _
      rw [dite_eq_right he]
      exact hyq e he

/-- **Injectivity of the extension**: in the situation of `exists_continuous_extension`, assume
moreover that `p` has finite fibres, `X` and `Y` are Hausdorff, `q` is continuous, `Φ` restricted
to `p⁻¹(Ω)` is an open embedding whose image contains `q⁻¹(Ω)`, and the points of `Y` over `X ∖ Ω`
have connected punctured neighbourhoods. Then the continuous `Φ : E → Y` over `X` is injective.

Two points `e₁ ≠ e₂` of a fibre over `x ∉ Ω` with image `y` would make the connected set
`Φ⁻¹(M ∖ {y}) ∩ p⁻¹(Ω)`, `M` a small connected punctured neighbourhood of `y`, meet the disjoint
neighbourhoods of `e₁` and `e₂` which contain it. -/
theorem injective_of_extension [T2Space X] [T2Space Y] (hp : IsCoveringMap p)
    (hpfin : ∀ x, (p ⁻¹' {x}).Finite) (hqc : Continuous q)
    (hpunct : ∀ x ∉ Ω, HasConnectedPuncturedNhds x) (hiso : ∀ x ∉ Ω, ∃ N ∈ 𝓝 x, N \ {x} ⊆ Ω)
    (hfin : ∀ x ∉ Ω, (q ⁻¹' {x}).Finite) {Φ : E → Y} (hΦ : Continuous Φ)
    (hΦq : ∀ e, q (Φ e) = p e) (hemb : IsOpenEmbedding ((p ⁻¹' Ω).domRestrict Φ))
    (hrange : q ⁻¹' Ω ⊆ Φ '' (p ⁻¹' Ω)) (hYpunct : ∀ y, q y ∉ Ω → HasConnectedPuncturedNhds y) :
    Function.Injective Φ := by
  classical
  have : T2Space E := hp.t2Space
  have hΦproper : IsProperMap Φ := isProperMap_of_comp_of_t2 hΦ hqc (by
    have : q ∘ Φ = p := funext hΦq
    rw [this]
    exact hp.isProperMap_of_finite hpfin)
  intro e₁ e₂ h12
  by_contra hne
  have hx : p e₂ = p e₁ := by rw [← hΦq, ← h12, hΦq]
  by_cases hΩ1 : p e₁ ∈ Ω
  · exact hne (congrArg Subtype.val
      (hemb.injective (a₁ := ⟨e₁, hΩ1⟩) (a₂ := ⟨e₂, show p e₂ ∈ Ω from hx ▸ hΩ1⟩) h12))
  set x := p e₁
  set y := Φ e₁
  have hqy : q y = x := hΦq e₁
  have hF : (Φ ⁻¹' {y}).Finite := (hpfin x).subset fun e he ↦ by
    simp only [mem_preimage, mem_singleton_iff] at he ⊢
    rw [← hΦq, he, hqy]
  obtain ⟨U, hU, hUd⟩ := hF.t2_separation
  set K := (⋃ e ∈ Φ ⁻¹' {y}, U e)ᶜ
  have hK : IsClosed (Φ '' K) :=
    hΦproper.isClosedMap _ (isOpen_biUnion fun e _ ↦ (hU e).2).isClosed_compl
  have hyK : y ∉ Φ '' K := by
    rintro ⟨e, heK, hey⟩
    exact heK (mem_iUnion₂.mpr ⟨e, hey, (hU e).1⟩)
  obtain ⟨N, hN, hNΩ⟩ := hiso x hΩ1
  set G := q ⁻¹' {x} \ {y}
  have hG : IsClosed G := ((hfin x hΩ1).subset sdiff_subset).isClosed
  have hW : (Φ '' K)ᶜ ∩ q ⁻¹' (interior N) ∩ Gᶜ ∈ 𝓝 y := by
    refine inter_mem (inter_mem (hK.isOpen_compl.mem_nhds hyK)
      (hqc.continuousAt.preimage_mem_nhds ?_)) (hG.isOpen_compl.mem_nhds fun h ↦ h.2 rfl)
    rw [hqy]
    exact interior_mem_nhds.mpr hN
  obtain ⟨M, hMW, hMo, hyM, hMc, -⟩ := hYpunct y (hqy ▸ hΩ1) _ hW
  set A := M \ {y}
  have hAΩ : A ⊆ q ⁻¹' Ω := by
    rintro a ⟨haM, hay⟩
    by_contra hqa
    have hqaN : q a ∈ N := interior_subset (hMW haM).1.2
    have : q a = x := by
      by_contra h
      exact hqa (hNΩ ⟨hqaN, h⟩)
    exact (hMW haM).2 ⟨this, hay⟩
  set P := Φ ⁻¹' A ∩ p ⁻¹' Ω
  have hPc : IsPreconnected P := by
    set f := (p ⁻¹' Ω).domRestrict Φ
    have hfA : f '' (f ⁻¹' A) = A := image_preimage_eq_of_subset fun a ha ↦ by
      obtain ⟨e, he, hea⟩ := hrange (hAΩ ha)
      exact ⟨⟨e, he⟩, hea⟩
    have hs : IsPreconnected (f ⁻¹' A) := by
      have : IsPreconnected (f '' (f ⁻¹' A)) := by rw [hfA]; exact hMc
      exact hemb.isInducing.isPreconnected_image.mp this
    have : P = Subtype.val '' (f ⁻¹' A) := by
      ext e
      constructor
      · rintro ⟨heA, heΩ⟩
        exact ⟨⟨e, heΩ⟩, heA, rfl⟩
      · rintro ⟨e', he'A, rfl⟩
        exact ⟨he'A, e'.2⟩
    rw [this]
    exact hs.image _ continuous_subtype_val.continuousOn
  have hPsub : P ⊆ ⋃ e ∈ Φ ⁻¹' {y}, U e := fun e' he' ↦ by
    by_contra h
    exact (hMW he'.1.1).1.1 ⟨e', h, rfl⟩
  have hmeet : ∀ e, Φ e = y → (P ∩ U e).Nonempty := by
    intro e he
    have hpe : p e = x := by rw [← hΦq, he, hqy]
    have hpeΩ : p e ∉ Ω := hpe ▸ hΩ1
    obtain ⟨N₁, hN₁, hN₁Ω⟩ := exists_mem_nhds_diff_subset (Ω := Ω) hp (hpe ▸ hN)
      (by rw [hpe]; exact hNΩ)
    have : (𝓝[≠] e).NeBot :=
      (hasConnectedPuncturedNhds_of_isCoveringMap hp (hpunct _ hpeΩ)).neBot
    have hev : ∀ᶠ e' in 𝓝[≠] e, e' ∈ P ∩ U e := by
      have h1 : Φ ⁻¹' M ∩ U e ∩ N₁ ∈ 𝓝 e :=
        inter_mem (inter_mem (hΦ.continuousAt.preimage_mem_nhds (hMo.mem_nhds (he ▸ hyM)))
          ((hU e).2.mem_nhds (hU e).1)) hN₁
      filter_upwards [sdiff_mem_nhdsWithin_compl h1 {e}] with e' he'
      obtain ⟨⟨⟨hM, hUe⟩, hN₁'⟩, he'e⟩ := he'
      have hΩ' : p e' ∈ Ω := hN₁Ω ⟨hN₁', he'e⟩
      refine ⟨⟨⟨hM, fun h ↦ hΩ1 ?_⟩, hΩ'⟩, hUe⟩
      rw [mem_singleton_iff] at h
      rw [← hqy, ← h, hΦq]
      exact hΩ'
    exact hev.exists
  have h1 := subset_of_isPreconnected_of_pairwiseDisjoint hPc (fun e ↦ (hU e).2) hUd hPsub
    (show e₁ ∈ Φ ⁻¹' {y} from rfl) (hmeet e₁ rfl)
  obtain ⟨e', he'P, he'U⟩ := hmeet e₂ h12.symm
  exact Set.disjoint_left.mp (hUd (show e₁ ∈ Φ ⁻¹' {y} from rfl)
    (show e₂ ∈ Φ ⁻¹' {y} from h12.symm) hne) (h1 he'P) he'U

end Extension

section Connected

/-- Removing from a preconnected space a closed set `Z` of points with connected (nonempty)
punctured neighbourhoods `N`, `N ∩ Z = {z}`, leaves a preconnected set. -/
theorem isPreconnected_compl_of_forall [PreconnectedSpace E] {Z : Set E} (hZ : IsClosed Z)
    (h : ∀ z ∈ Z, ∃ N, IsOpen N ∧ z ∈ N ∧ N ∩ Z = {z} ∧ IsPreconnected (N \ {z}) ∧
      (N \ {z}).Nonempty) :
    IsPreconnected Zᶜ := by
  classical
  intro u v hu hv huv ⟨a, haZ, hau⟩ ⟨b, hbZ, hbv⟩
  by_contra! hempty
  choose! N hNo hzN hNZ hNc hNn using h
  have hsub (z : E) (hz : z ∈ Z) : N z \ {z} ⊆ Zᶜ := fun w hw hwZ ↦
    hw.2 (by rw [← hNZ z hz]; exact ⟨hw.1, hwZ⟩)
  -- each punctured neighbourhood lies in `u` or in `v`
  have hsplit (z : E) (hz : z ∈ Z) : N z \ {z} ⊆ u ∨ N z \ {z} ⊆ v := by
    by_cases h1 : (N z \ {z} ∩ u).Nonempty
    · by_cases h2 : (N z \ {z} ∩ v).Nonempty
      · obtain ⟨w, hw, hwuv⟩ := hNc z hz u v hu hv ((hsub z hz).trans huv) h1 h2
        exact absurd (hempty.subset ⟨hsub z hz hw, hwuv⟩) (notMem_empty _)
      · exact Or.inl fun w hw ↦ ((huv (hsub z hz hw)).resolve_right fun hwv ↦ h2 ⟨w, hw, hwv⟩)
    · exact Or.inr fun w hw ↦ ((huv (hsub z hz hw)).resolve_left fun hwu ↦ h1 ⟨w, hw, hwu⟩)
  set u' := (u ∩ Zᶜ) ∪ ⋃ z ∈ {z ∈ Z | N z \ {z} ⊆ u}, N z
  set v' := (v ∩ Zᶜ) ∪ ⋃ z ∈ {z ∈ Z | N z \ {z} ⊆ v}, N z
  have hu' : IsOpen u' :=
    (hu.inter hZ.isOpen_compl).union (isOpen_biUnion fun z hz ↦ hNo z hz.1)
  have hv' : IsOpen v' :=
    (hv.inter hZ.isOpen_compl).union (isOpen_biUnion fun z hz ↦ hNo z hz.1)
  have hcover : (univ : Set E) ⊆ u' ∪ v' := by
    intro w _
    by_cases hwZ : w ∈ Z
    · rcases hsplit w hwZ with h | h
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨w, ⟨hwZ, h⟩, hzN w hwZ⟩))
      · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨w, ⟨hwZ, h⟩, hzN w hwZ⟩))
    · rcases huv hwZ with h | h
      · exact Or.inl (Or.inl ⟨h, hwZ⟩)
      · exact Or.inr (Or.inl ⟨h, hwZ⟩)
  obtain ⟨w, -, hwu', hwv'⟩ := isPreconnected_univ u' v' hu' hv' hcover
    ⟨a, trivial, Or.inl ⟨hau, haZ⟩⟩ ⟨b, trivial, Or.inl ⟨hbv, hbZ⟩⟩
  -- a point of `u'` outside `Z` lies in `u`; a point of `u'` in `Z` is a centre `z` with
  -- `N z ∖ {z} ⊆ u`
  have key (s s' : Set E) (hs' : s' = (s ∩ Zᶜ) ∪ ⋃ z ∈ {z ∈ Z | N z \ {z} ⊆ s}, N z)
      (hws : w ∈ s') : (w ∉ Z → w ∈ s) ∧ (w ∈ Z → N w \ {w} ⊆ s) := by
    rw [hs'] at hws
    rcases hws with ⟨hws, hwZ'⟩ | hws
    · exact ⟨fun _ ↦ hws, fun hwZ ↦ absurd hwZ hwZ'⟩
    · obtain ⟨z, ⟨hzZ, hzs⟩, hwN⟩ := mem_iUnion₂.mp hws
      have hwz : w ∈ Z → w = z := fun hwZ ↦ by
        have : w ∈ N z ∩ Z := ⟨hwN, hwZ⟩
        rwa [hNZ z hzZ] at this
      refine ⟨fun hwZ ↦ hzs ⟨hwN, fun h ↦ hwZ ((mem_singleton_iff.mp h) ▸ hzZ)⟩,
        fun hwZ ↦ (hwz hwZ) ▸ hzs⟩
  obtain ⟨hu1, hu2⟩ := key u u' rfl hwu'
  obtain ⟨hv1, hv2⟩ := key v v' rfl hwv'
  by_cases hwZ : w ∈ Z
  · obtain ⟨t, ht⟩ := hNn w hwZ
    exact absurd (hempty.subset ⟨hsub w hwZ ht, hu2 hwZ ht, hv2 hwZ ht⟩) (notMem_empty _)
  · exact absurd (hempty.subset ⟨hwZ, hu1 hwZ, hv1 hwZ⟩) (notMem_empty _)

/-- If `E` is connected and covers `X`, and every `x ∉ Ω` has connected punctured neighbourhoods
and a neighbourhood `N` with `N ∖ {x} ⊆ Ω`, then `p⁻¹(Ω)` is connected (removing finitely many
points from a connected surface). -/
theorem isPreconnected_preimage_of_preconnectedSpace [PreconnectedSpace E] {p : E → X}
    {Ω : Set X} (hp : IsCoveringMap p) (hΩ : IsOpen Ω)
    (hpunct : ∀ x ∉ Ω, HasConnectedPuncturedNhds x)
    (hiso : ∀ x ∉ Ω, ∃ N ∈ 𝓝 x, N \ {x} ⊆ Ω) : IsPreconnected (p ⁻¹' Ω) := by
  have : p ⁻¹' Ω = (p ⁻¹' Ωᶜ)ᶜ := by rw [preimage_compl, compl_compl]
  rw [this]
  refine isPreconnected_compl_of_forall (hΩ.isClosed_compl.preimage hp.continuous) fun e he ↦ ?_
  obtain ⟨N, hN, hNΩ⟩ := hiso _ he
  obtain ⟨N₁, hN₁, hN₁Ω⟩ := exists_mem_nhds_diff_subset hp hN hNΩ
  obtain ⟨N', hN'N₁, hN'o, heN', hN'c, hN'n⟩ :=
    hasConnectedPuncturedNhds_of_isCoveringMap hp (hpunct _ he) N₁ hN₁
  refine ⟨N', hN'o, heN', ?_, hN'c, hN'n⟩
  ext w
  constructor
  · rintro ⟨hwN', hwZ⟩
    by_contra hwe
    exact hwZ (hN₁Ω ⟨hN'N₁ hwN', hwe⟩)
  · rintro rfl
    exact ⟨heN', he⟩

end Connected

/-! ### Extension across the complement of a dense open subset

The same statements with the isolated points replaced by the complement of a dense open `U ⊆ X`
whose points have small neighbourhoods with preconnected trace on `U` (`HasPreconnectedTraces`):
for `X` a normal variety and `U` the complement of a hypersurface, this is the local
irreducibility `TopologicallyUnibranchStatement` (registry row C30). Promised to ret-hd for the
extension across divisors in dimension `≥ 2`; the isolated-point versions above are the curve case.
-/

section Traces

/-- `x` has arbitrarily small open neighbourhoods `V` whose trace `V ∩ U` on `U` is preconnected
(the form of `TopologicallyUnibranchStatement` for `U = {g ≠ 0}`). -/
def HasPreconnectedTraces (U : Set X) (x : X) : Prop :=
  ∀ W ∈ 𝓝 x, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ IsPreconnected (V ∩ U)

variable {p : E → X} {q : Y → X} {U : Set X}

/-- Preconnected traces lift along a covering map. -/
lemma hasPreconnectedTraces_of_isCoveringMap (hp : IsCoveringMap p) {e : E}
    (h : HasPreconnectedTraces U (p e)) : HasPreconnectedTraces (p ⁻¹' U) e := by
  obtain ⟨s, hes, hps⟩ := hp.isLocalHomeomorph e
  intro W hW
  have hse : s e = p e := by rw [hps]
  have hW' : s.target ∩ s.symm ⁻¹' (interior W) ∈ 𝓝 (p e) := by
    rw [← hse]
    exact Filter.inter_mem (s.open_target.mem_nhds (s.map_source hes))
      (s.continuousAt_symm (s.map_source hes) <| by
        rw [s.left_inv hes]; exact interior_mem_nhds.mpr hW)
  obtain ⟨V, hVo, hxV, hVW, hVc⟩ := h _ hW'
  have hVt : V ⊆ s.target := fun z hz ↦ (hVW hz).1
  have hps' (z : X) (hz : z ∈ s.target) : p (s.symm z) = z := by
    rw [hps]
    exact s.right_inv hz
  refine ⟨s.symm '' V, s.isOpen_image_symm_of_subset_target hVo hVt,
    ⟨p e, hxV, by rw [← hse, s.left_inv hes]⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact interior_subset (hVW hz).2
  · have : s.symm '' V ∩ p ⁻¹' U = s.symm '' (V ∩ U) := by
      ext w
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hzU⟩
        refine ⟨z, ⟨hz, ?_⟩, rfl⟩
        rw [mem_preimage, hps' z (hVt hz)] at hzU
        exact hzU
      · rintro ⟨z, ⟨hz, hzU⟩, rfl⟩
        refine ⟨⟨z, hz, rfl⟩, ?_⟩
        rw [mem_preimage, hps' z (hVt hz)]
        exact hzU
    rw [this]
    exact hVc.image _ (s.continuousOn_symm.mono (inter_subset_left.trans hVt))

/-- **Limits along a dense open subset**: let `Y` be Hausdorff, `q : Y → X` a closed map with
`q⁻¹(x)` finite, `V ⊆ E` with `𝓝[V] e ≠ ⊥` and `e` having small neighbourhoods with preconnected
trace on `V`, and `f` continuous on `V` lying over a map `p` continuous at `e` with `p e = x`.
Then `f` converges along `𝓝[V] e` to a point of `q⁻¹(x)`. -/
theorem exists_tendsto_nhdsWithin_of_hasPreconnectedTraces [T2Space Y] (hq : IsClosedMap q)
    {x : X} (hfin : (q ⁻¹' {x}).Finite) {V : Set E} {e : E} (he : HasPreconnectedTraces V e)
    (hne : (𝓝[V] e).NeBot) (hpc : ContinuousAt p e) (hpe : p e = x) {f : E → Y}
    (hf : ContinuousOn f V) (hfq : ∀ e' ∈ V, q (f e') = p e') :
    ∃ y, q y = x ∧ Tendsto f (𝓝[V] e) (𝓝 y) := by
  classical
  by_contra! H
  set F := q ⁻¹' {x}
  have hW : ∀ y, ∃ W ∈ 𝓝 y, y ∈ F → ∃ᶠ e' in 𝓝[V] e, f e' ∉ W := by
    intro y
    by_cases hy : y ∈ F
    · obtain ⟨W, hW, hWf⟩ := not_tendsto_iff_exists_frequently_notMem.mp (H y hy)
      exact ⟨W, hW, fun _ ↦ hWf⟩
    · exact ⟨univ, univ_mem, fun h ↦ absurd h hy⟩
  choose W hWy hWf using hW
  obtain ⟨O', hO', hO'd⟩ := hfin.t2_separation
  let O : Y → Set Y := fun y ↦ interior (W y) ∩ O' y
  have hOo (y : Y) : IsOpen (O y) := isOpen_interior.inter (hO' y).2
  have hOd : F.PairwiseDisjoint O := hO'd.mono fun y ↦ inter_subset_right
  set K := (⋃ y ∈ F, O y)ᶜ
  have hK : IsClosed (q '' K) :=
    hq _ (isOpen_biUnion fun y _ ↦ hOo y).isClosed_compl
  have hxK : x ∉ q '' K := by
    rintro ⟨y, hyK, rfl⟩
    exact hyK (mem_iUnion₂.mpr ⟨y, rfl, interior_mem_nhds.mpr (hWy y) |> mem_of_mem_nhds,
      (hO' y).1⟩)
  have hM : p ⁻¹' (q '' K)ᶜ ∈ 𝓝 e := hpc (hK.isOpen_compl.mem_nhds (hpe ▸ hxK))
  obtain ⟨N, hNo, heN, hNM, hNc⟩ := he _ hM
  have hNV : N ∩ V ∈ 𝓝[V] e := by
    rw [inter_comm]
    exact inter_mem_nhdsWithin V (hNo.mem_nhds heN)
  have hsub : f '' (N ∩ V) ⊆ ⋃ y ∈ F, O y := by
    rintro _ ⟨e', ⟨he'N, he'V⟩, rfl⟩
    by_contra hK'
    exact hNM he'N ⟨f e', hK', hfq e' he'V⟩
  have hconn : IsPreconnected (f '' (N ∩ V)) := hNc.image f (hf.mono inter_subset_right)
  obtain ⟨z₀, hz₀⟩ := Filter.nonempty_of_mem hNV
  obtain ⟨y₀, hy₀F, hy₀⟩ := mem_iUnion₂.mp (hsub ⟨z₀, hz₀, rfl⟩)
  have hall : f '' (N ∩ V) ⊆ O y₀ :=
    subset_of_isPreconnected_of_pairwiseDisjoint hconn hOo hOd hsub hy₀F ⟨f z₀, ⟨z₀, hz₀, rfl⟩, hy₀⟩
  have hev : ∀ᶠ e' in 𝓝[V] e, f e' ∈ W y₀ :=
    Filter.mem_of_superset hNV fun e' he' ↦
      show f e' ∈ W y₀ from interior_subset (hall ⟨e', he', rfl⟩).1
  exact (hWf y₀ hy₀F) (hev.mono fun _ h h' ↦ h' h)

/-- **Extension of a map of coverings across the complement of a dense open subset**: let
`p : E → X` be a covering map, `Y` regular and Hausdorff, `q : Y → X` a closed map, `U ⊆ X` open and
dense such that every `x ∉ U` has small neighbourhoods with preconnected trace on `U` and finite
fibre `q⁻¹(x)`. Then every continuous `Φ₀` on `p⁻¹(U)` lying over `X` extends to a continuous
`Φ : E → Y` over `X`. -/
theorem exists_continuous_extension_of_hasPreconnectedTraces [T2Space Y] [RegularSpace Y]
    (hp : IsCoveringMap p) (hq : IsClosedMap q) (hU : IsOpen U) (hd : Dense U)
    (htr : ∀ x ∉ U, HasPreconnectedTraces U x) (hfin : ∀ x ∉ U, (q ⁻¹' {x}).Finite)
    {Φ₀ : E → Y} (hΦc : ContinuousOn Φ₀ (p ⁻¹' U)) (hΦq : ∀ e, p e ∈ U → q (Φ₀ e) = p e) :
    ∃ Φ : E → Y, Continuous Φ ∧ (∀ e, q (Φ e) = p e) ∧ ∀ e, p e ∈ U → Φ e = Φ₀ e := by
  classical
  have hdE : Dense (p ⁻¹' U) := hd.preimage hp.isOpenMap
  have hne (e : E) : (𝓝[p ⁻¹' U] e).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdE e)
  have hlim : ∀ e, p e ∉ U → ∃ y, q y = p e ∧ Tendsto Φ₀ (𝓝[p ⁻¹' U] e) (𝓝 y) := fun e he ↦
    exists_tendsto_nhdsWithin_of_hasPreconnectedTraces hq (hfin _ he)
      (hasPreconnectedTraces_of_isCoveringMap hp (htr _ he)) (hne e) hp.continuous.continuousAt
      rfl hΦc fun e' he' ↦ hΦq e' he'
  choose y hyq hyt using hlim
  let Φ : E → Y := fun e ↦ if h : p e ∈ U then Φ₀ e else y e h
  have hΦU (e : E) (he : p e ∈ U) : Φ e = Φ₀ e := dite_eq_left he
  -- `Φ` is the limit of `Φ₀` along `p⁻¹(U)` everywhere
  have hΦt (e : E) : Tendsto Φ₀ (𝓝[p ⁻¹' U] e) (𝓝 (Φ e)) := by
    by_cases he : p e ∈ U
    · rw [hΦU e he]
      exact (hΦc.continuousAt ((hU.preimage hp.continuous).mem_nhds he)).tendsto.mono_left
        nhdsWithin_le_nhds
    · change Tendsto Φ₀ _ (𝓝 (dite _ _ _))
      rw [dite_eq_right he]
      exact hyt e he
  refine ⟨Φ, continuous_iff_continuousAt.mpr fun e ↦ ?_, fun e ↦ ?_, hΦU⟩
  · intro W hW
    obtain ⟨W', hW', hW'c, hW'W⟩ := exists_mem_nhds_isClosed_subset hW
    obtain ⟨N, hNo, heN, hNW'⟩ := mem_nhdsWithin.mp (hΦt e hW')
    refine Filter.mem_map.mpr (Filter.mem_of_superset (hNo.mem_nhds heN) fun e' he' ↦ hW'W ?_)
    have : ∀ᶠ e'' in 𝓝[p ⁻¹' U] e', Φ₀ e'' ∈ W' :=
      Filter.mem_of_superset (inter_mem_nhdsWithin _ (hNo.mem_nhds he')) fun e'' he'' ↦
        hNW' ⟨he''.2, he''.1⟩
    exact hW'c.mem_of_tendsto (hΦt e') this
  · by_cases he : p e ∈ U
    · rw [hΦU e he, hΦq e he]
    · change q (dite _ _ _) = _
      rw [dite_eq_right he]
      exact hyq e he

/-- **Injectivity of the extension** across the complement of a dense open `U`: assume `p` is a
covering map with finite fibres, `X` and `Y` are Hausdorff, `q` is continuous, `Φ : E → Y` is
continuous over `X`, its restriction to `p⁻¹(U)` is an open embedding whose image contains
`q⁻¹(U)`, and every point of `Y` over `X ∖ U` has small neighbourhoods with preconnected trace on
`q⁻¹(U)`. Then `Φ` is injective. -/
theorem injective_of_extension_of_hasPreconnectedTraces [T2Space X] [T2Space Y]
    (hp : IsCoveringMap p) (hpfin : ∀ x, (p ⁻¹' {x}).Finite) (hqc : Continuous q) (hd : Dense U)
    {Φ : E → Y} (hΦ : Continuous Φ) (hΦq : ∀ e, q (Φ e) = p e)
    (hemb : IsOpenEmbedding ((p ⁻¹' U).domRestrict Φ)) (hrange : q ⁻¹' U ⊆ Φ '' (p ⁻¹' U))
    (hYtr : ∀ y, q y ∉ U → HasPreconnectedTraces (q ⁻¹' U) y) :
    Function.Injective Φ := by
  classical
  have : T2Space E := hp.t2Space
  have hdE : Dense (p ⁻¹' U) := hd.preimage hp.isOpenMap
  have hΦproper : IsProperMap Φ := isProperMap_of_comp_of_t2 hΦ hqc (by
    have : q ∘ Φ = p := funext hΦq
    rw [this]
    exact hp.isProperMap_of_finite hpfin)
  intro e₁ e₂ h12
  by_contra hne
  have hx : p e₂ = p e₁ := by rw [← hΦq, ← h12, hΦq]
  by_cases hU1 : p e₁ ∈ U
  · exact hne (congrArg Subtype.val
      (hemb.injective (a₁ := ⟨e₁, hU1⟩) (a₂ := ⟨e₂, show p e₂ ∈ U from hx ▸ hU1⟩) h12))
  set y := Φ e₁
  have hF : (Φ ⁻¹' {y}).Finite := (hpfin (p e₁)).subset fun e he ↦ by
    simp only [mem_preimage, mem_singleton_iff] at he ⊢
    rw [← hΦq, he]
    exact hΦq e₁
  obtain ⟨O, hO, hOd⟩ := hF.t2_separation
  set K := (⋃ e ∈ Φ ⁻¹' {y}, O e)ᶜ
  have hK : IsClosed (Φ '' K) :=
    hΦproper.isClosedMap _ (isOpen_biUnion fun e _ ↦ (hO e).2).isClosed_compl
  have hyK : y ∉ Φ '' K := by
    rintro ⟨e, heK, hey⟩
    exact heK (mem_iUnion₂.mpr ⟨e, hey, (hO e).1⟩)
  obtain ⟨M, hMo, hyM, hMK, hMc⟩ :=
    hYtr y (by rw [hΦq]; exact hU1) _ (hK.isOpen_compl.mem_nhds hyK)
  set A := M ∩ q ⁻¹' U
  set P := Φ ⁻¹' A ∩ p ⁻¹' U
  have hPc : IsPreconnected P := by
    set f := (p ⁻¹' U).domRestrict Φ
    have hfA : f '' (f ⁻¹' A) = A := image_preimage_eq_of_subset fun a ha ↦ by
      obtain ⟨e, he, hea⟩ := hrange ha.2
      exact ⟨⟨e, he⟩, hea⟩
    have hs : IsPreconnected (f ⁻¹' A) := by
      have : IsPreconnected (f '' (f ⁻¹' A)) := by rw [hfA]; exact hMc
      exact hemb.isInducing.isPreconnected_image.mp this
    have : P = Subtype.val '' (f ⁻¹' A) := by
      ext e
      constructor
      · rintro ⟨heA, heU⟩
        exact ⟨⟨e, heU⟩, heA, rfl⟩
      · rintro ⟨e', he'A, rfl⟩
        exact ⟨he'A, e'.2⟩
    rw [this]
    exact hs.image _ continuous_subtype_val.continuousOn
  have hPsub : P ⊆ ⋃ e ∈ Φ ⁻¹' {y}, O e := fun e' he' ↦ by
    by_contra h
    exact hMK he'.1.1 ⟨e', h, rfl⟩
  have hmeet : ∀ e, Φ e = y → (P ∩ O e).Nonempty := by
    intro e he
    have hN : Φ ⁻¹' M ∩ O e ∈ 𝓝 e :=
      inter_mem (hΦ.continuousAt.preimage_mem_nhds (hMo.mem_nhds (he ▸ hyM)))
        ((hO e).2.mem_nhds (hO e).1)
    obtain ⟨e', ⟨he'M, he'O⟩, he'U⟩ := mem_closure_iff_nhds.mp (hdE e) _ hN
    refine ⟨e', ⟨⟨he'M, ?_⟩, he'U⟩, he'O⟩
    rw [mem_preimage, hΦq]
    exact he'U
  have h1 := subset_of_isPreconnected_of_pairwiseDisjoint hPc (fun e ↦ (hO e).2) hOd hPsub
    (show e₁ ∈ Φ ⁻¹' {y} from rfl) (hmeet e₁ rfl)
  obtain ⟨e', he'P, he'O⟩ := hmeet e₂ h12.symm
  exact Set.disjoint_left.mp (hOd (show e₁ ∈ Φ ⁻¹' {y} from rfl)
    (show e₂ ∈ Φ ⁻¹' {y} from h12.symm) hne) (h1 he'P) he'O

/-- A dense open subset `V` of a preconnected space is preconnected if every point outside `V` has
a neighbourhood with preconnected trace on `V`. -/
theorem isPreconnected_of_dense_of_traces [PreconnectedSpace E] {V : Set E} (hVd : Dense V)
    (h : ∀ e ∉ V, ∃ N, IsOpen N ∧ e ∈ N ∧ IsPreconnected (N ∩ V)) : IsPreconnected V := by
  classical
  intro u v hu hv huv ⟨a, haV, hau⟩ ⟨b, hbV, hbv⟩
  by_contra! hempty
  -- every point has an open neighbourhood whose trace on `V` lies in `u` or in `v`
  have hside (e : E) : ∃ N, IsOpen N ∧ e ∈ N ∧ (N ∩ V ⊆ u ∨ N ∩ V ⊆ v) := by
    by_cases he : e ∈ V
    · rcases huv he with heu | hev
      · exact ⟨u, hu, heu, Or.inl inter_subset_left⟩
      · exact ⟨v, hv, hev, Or.inr inter_subset_left⟩
    · obtain ⟨N, hNo, heN, hNc⟩ := h e he
      refine ⟨N, hNo, heN, ?_⟩
      by_cases h1 : (N ∩ V ∩ u).Nonempty
      · by_cases h2 : (N ∩ V ∩ v).Nonempty
        · obtain ⟨w, hw, hwuv⟩ := hNc u v hu hv (fun w hw ↦ huv hw.2) h1 h2
          exact absurd (hempty.subset ⟨hw.2, hwuv⟩) (notMem_empty _)
        · exact Or.inl fun w hw ↦ (huv hw.2).resolve_right fun hwv ↦ h2 ⟨w, hw, hwv⟩
      · exact Or.inr fun w hw ↦ (huv hw.2).resolve_left fun hwu ↦ h1 ⟨w, hw, hwu⟩
  choose N hNo heN hNs using hside
  set u' := ⋃ e ∈ {e | N e ∩ V ⊆ u}, N e
  set v' := ⋃ e ∈ {e | N e ∩ V ⊆ v}, N e
  have hcover : (univ : Set E) ⊆ u' ∪ v' := fun e _ ↦ by
    rcases hNs e with h' | h'
    · exact Or.inl (mem_iUnion₂.mpr ⟨e, h', heN e⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨e, h', heN e⟩)
  have hau' : a ∈ u' := by
    rcases hNs a with h' | h'
    · exact mem_iUnion₂.mpr ⟨a, h', heN a⟩
    · exact absurd (hempty.subset ⟨haV, hau, h' ⟨heN a, haV⟩⟩) (notMem_empty _)
  have hbv' : b ∈ v' := by
    rcases hNs b with h' | h'
    · exact absurd (hempty.subset ⟨hbV, h' ⟨heN b, hbV⟩, hbv⟩) (notMem_empty _)
    · exact mem_iUnion₂.mpr ⟨b, h', heN b⟩
  obtain ⟨w, -, hwu', hwv'⟩ := isPreconnected_univ u' v'
    (isOpen_biUnion fun e _ ↦ hNo e) (isOpen_biUnion fun e _ ↦ hNo e) hcover
    ⟨a, trivial, hau'⟩ ⟨b, trivial, hbv'⟩
  obtain ⟨e₁, he₁, hw₁⟩ := mem_iUnion₂.mp hwu'
  obtain ⟨e₂, he₂, hw₂⟩ := mem_iUnion₂.mp hwv'
  obtain ⟨z, ⟨hz₁, hz₂⟩, hzV⟩ := mem_closure_iff.mp (hVd w) _
    ((hNo e₁).inter (hNo e₂)) ⟨hw₁, hw₂⟩
  exact absurd (hempty.subset ⟨hzV, he₁ ⟨hz₁, hzV⟩, he₂ ⟨hz₂, hzV⟩⟩) (notMem_empty _)

/-- If `E` is connected and covers `X`, `U ⊆ X` is open and dense, and every `x ∉ U` has a small
neighbourhood with preconnected trace on `U`, then `p⁻¹(U)` is connected. -/
theorem isPreconnected_preimage_of_hasPreconnectedTraces [PreconnectedSpace E]
    (hp : IsCoveringMap p) (hd : Dense U) (htr : ∀ x ∉ U, HasPreconnectedTraces U x) :
    IsPreconnected (p ⁻¹' U) := by
  refine isPreconnected_of_dense_of_traces (hd.preimage hp.isOpenMap) fun e he ↦ ?_
  obtain ⟨N, hNo, heN, -, hNc⟩ := hasPreconnectedTraces_of_isCoveringMap hp (htr _ he) univ
    univ_mem
  exact ⟨N, hNo, heN, hNc⟩

end Traces

end RiemannExtension

/-- `X(K)` is a regular space when `K` is (it is a subspace of `K^A`); needed by
`RiemannExtension.exists_continuous_extension_of_hasPreconnectedTraces` for `Y = T(ℂ)`. -/
instance Points.instRegularSpace {K A : Type*} [Field K] [TopologicalSpace K] [RegularSpace K]
    [CommRing A] [Algebra K A] : RegularSpace (Points K A) :=
  Points.isEmbedding_coe.isInducing.regularSpace

namespace RiemannExtension

end RiemannExtension

end SGA.SGA1.ExposeXII
