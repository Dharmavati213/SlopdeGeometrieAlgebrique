/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Constructible
import SGA.Foundations.Limits.FiniteEtale
import SGA.Foundations.Limits.PropertiesLimit

/-!
# Constructible sets over a limit; surjectivity descends

Let `c.pt = lim E i` be the limit of a cofiltered diagram of quasi-compact and quasi-separated
schemes with affine transition maps.

* `AlgebraicGeometry.Scheme.exists_preimage_eq_empty_of_isConstructible` (EGA IV 8.3.4): a
  constructible subset `T` of some `E j` whose preimage in `c.pt` is empty has empty preimage in
  some `E k`. Constructible sets are finite unions of sets `U ∩ Z` (`U` quasi-compact open, `Z`
  closed); for such a piece the statement is Stacks 01Z3 (mathlib's
  `exists_mem_of_isClosed_of_nonempty`) applied over `U`.
* `AlgebraicGeometry.Scheme.exists_preimage_eq_univ_of_isConstructible`: the same for `T` whose
  preimage is everything.
* `AlgebraicGeometry.Scheme.exists_preimage_subset_of_isConstructible`: EGA IV 8.3.4 as stated
  there, for an inclusion between the preimages of two constructible sets.
* `AlgebraicGeometry.Scheme.limitDescends_surjective` (EGA IV 8.10.5 (vi)): surjectivity of a
  morphism of finite presentation descends to a finite level. The image is constructible by
  Chevalley's theorem (mathlib's `Scheme.Hom.isLocallyConstructible_image`).

## References

* [EGA IV₃, 8.3.4, 8.10.5][EGA4]
* [Stacks Project, Tag 01Z3](https://stacks.math.columbia.edu/tag/01Z3)
-/

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] {c : Cone E}

set_option backward.isDefEq.respectTransparency false in
/-- Let `U ⊆ E j` be a quasi-compact open and `Z ⊆ E j` a closed set. If the preimage of `U ∩ Z`
in the limit `c.pt` is empty, then its preimage in some `E k` is empty (Stacks 01Z3 over `U`). -/
theorem Scheme.exists_preimage_inter_eq_empty (hc : IsLimit c) {j : I} (U : (E.obj j).Opens)
    (hU : IsCompact (U : Set (E.obj j))) {Z : Set (E.obj j)} (hZ : IsClosed Z)
    (h : c.π.app j ⁻¹' ((U : Set (E.obj j)) ∩ Z) = ∅) :
    ∃ k : Over j, E.map k.hom ⁻¹' ((U : Set (E.obj j)) ∩ Z) = ∅ := by
  by_contra! H
  let D := opensDiagram E j U
  let ι := opensDiagramι E j U
  have hDc (i : Over j) : CompactSpace (D.obj i) := Scheme.compactSpace_opensDiagram_obj hU i
  let W (i : Over j) : Set (D.obj i) := (ι.app i ≫ E.map i.hom) ⁻¹' Z
  have hWc (i : Over j) : IsClosed (W i) := hZ.preimage (ι.app i ≫ E.map i.hom).continuous
  obtain ⟨s, hs⟩ := exists_mem_of_isClosed_of_nonempty D (opensCone E c j U)
    (isLimitOpensCone E c hc j U) W hWc
    (fun i ↦ by
      obtain ⟨y, hyU, hyZ⟩ := H i
      exact ⟨⟨y, hyU⟩, hyZ⟩)
    (fun i ↦ (hWc i).isCompact)
    (fun {i i'} f x hx ↦ by
      change (D.map f ≫ ι.app i' ≫ E.map i'.hom) x ∈ Z
      rw [← Category.assoc, ι.naturality f]
      change (ι.app i ≫ E.map f.left ≫ E.map i'.hom) x ∈ Z
      rw [← E.map_comp, Over.w f]
      exact hx)
  have hs' : ((opensCone E c j U).π.app (Over.mk (𝟙 j)) ≫ ι.app (Over.mk (𝟙 j)) ≫
      E.map (𝟙 j)) s ∈ Z := hs (Over.mk (𝟙 j))
  have e2 : (opensCone E c j U).π.app (Over.mk (𝟙 j)) ≫ ι.app (Over.mk (𝟙 j)) ≫ E.map (𝟙 j) =
      (c.π.app j ⁻¹ᵁ U).ι ≫ c.π.app j := by
    simp [ι]
  rw [e2] at hs'
  have hmem : (c.π.app j ⁻¹ᵁ U).ι s ∈ c.π.app j ⁻¹' ((U : Set (E.obj j)) ∩ Z) :=
    ⟨s.2, hs'⟩
  rw [h] at hmem
  exact hmem

/-- EGA IV 8.3.4: let `T ⊆ E j` be constructible. If the preimage of `T` in the limit `c.pt` is
empty, then its preimage in some `E k` is empty. -/
theorem Scheme.exists_preimage_eq_empty_of_isConstructible (hc : IsLimit c)
    [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)] {j : I}
    {T : Set (E.obj j)} (hT : IsConstructible T) (h : c.π.app j ⁻¹' T = ∅) :
    ∃ k : Over j, E.map k.hom ⁻¹' T = ∅ := by
  classical
  obtain ⟨S, hSf, hS, rfl⟩ := IsConstructible.isFiniteUnionOpenInterClosed hT
  have key : ∀ p ∈ S, ∃ k : Over j, E.map k.hom ⁻¹' (p.1 ∩ p.2) = ∅ := fun p hp ↦ by
    obtain ⟨h1, h2, h3, -⟩ := hS p hp
    refine Scheme.exists_preimage_inter_eq_empty hc ⟨p.1, h1⟩ h2 h3 ?_
    exact Set.subset_eq_empty
      (Set.preimage_mono (Set.subset_biUnion_of_mem (u := fun p ↦ p.1 ∩ p.2) hp)) h
  choose k hk using key
  let K : hSf.toFinset → Over j := fun x ↦ k x.1 ((Set.Finite.mem_toFinset hSf).mp x.2)
  obtain ⟨m, fm⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image K)
  replace fm : ∀ (p) (hp : p ∈ S), m ⟶ k p hp := fun p hp ↦
    (@fm (K ⟨p, (Set.Finite.mem_toFinset hSf).mpr hp⟩)
      (Finset.mem_image_of_mem K (Finset.mem_univ _))).some
  refine ⟨m, ?_⟩
  rw [Set.preimage_iUnion₂]
  refine Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
  simp only [Set.mem_iUnion] at hx
  obtain ⟨p, hp, hx⟩ := hx
  suffices E.map m.hom ⁻¹' (p.1 ∩ p.2) = ∅ by rw [this] at hx; exact hx
  rw [← Over.w (fm p hp), E.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
    hk p hp, Set.preimage_empty]

/-- EGA IV 8.3.4: let `T ⊆ E j` be constructible. If the preimage of `T` in the limit `c.pt` is
everything, then its preimage in some `E k` is everything. -/
theorem Scheme.exists_preimage_eq_univ_of_isConstructible (hc : IsLimit c)
    [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)] {j : I}
    {T : Set (E.obj j)} (hT : IsConstructible T) (h : c.π.app j ⁻¹' T = Set.univ) :
    ∃ k : Over j, E.map k.hom ⁻¹' T = Set.univ := by
  obtain ⟨k, hk⟩ := Scheme.exists_preimage_eq_empty_of_isConstructible hc hT.compl
    (by rw [Set.preimage_compl, h, Set.compl_univ])
  exact ⟨k, by rwa [Set.preimage_compl, Set.compl_empty_iff] at hk⟩

/-- EGA IV 8.3.4 in the form of an inclusion: let `T, T' ⊆ E j` be constructible. If the preimage
of `T` in the limit `c.pt` is contained in that of `T'`, the same holds in some `E k`. (Apply
`exists_preimage_eq_empty_of_isConstructible` to `T \ T'`.) -/
theorem Scheme.exists_preimage_subset_of_isConstructible (hc : IsLimit c)
    [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)] {j : I}
    {T T' : Set (E.obj j)} (hT : IsConstructible T) (hT' : IsConstructible T')
    (h : c.π.app j ⁻¹' T ⊆ c.π.app j ⁻¹' T') :
    ∃ k : Over j, E.map k.hom ⁻¹' T ⊆ E.map k.hom ⁻¹' T' := by
  obtain ⟨k, hk⟩ := Scheme.exists_preimage_eq_empty_of_isConstructible hc
    (IsConstructible.sdiff hT hT') (by rw [Set.preimage_sdiff, Set.sdiff_eq_empty]; exact h)
  exact ⟨k, by rwa [Set.preimage_sdiff, Set.sdiff_eq_empty] at hk⟩

/-- EGA IV 8.10.5 (vi): surjectivity of a morphism of finite presentation over the limit of a
cofiltered diagram of quasi-compact and quasi-separated schemes with affine transition maps
descends to a finite level. -/
theorem Scheme.limitDescends_surjective : Scheme.LimitDescendsStatement.{u} @Surjective := by
  intro I _ _ E _ _ _ c hc j X Xj qj _ _ _ e q h hq
  have hT : IsConstructible (Set.range qj)ᶜ := by
    have := qj.isLocallyConstructible_image (s := Set.univ) .univ
    rw [Set.image_univ] at this
    exact this.isConstructible.compl
  have hpre : c.π.app j ⁻¹' (Set.range qj)ᶜ = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range, not_exists,
      Set.mem_empty_iff_false, iff_false, not_forall, not_not]
    obtain ⟨y, rfl⟩ := hq.surj x
    exact ⟨e y, by rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]⟩
  obtain ⟨k, hk⟩ := Scheme.exists_preimage_eq_empty_of_isConstructible hc hT hpre
  refine ⟨k.left, k.hom, ⟨fun y ↦ ?_⟩⟩
  have hy : E.map k.hom y ∈ Set.range qj := by
    by_contra hy
    have : y ∈ E.map k.hom ⁻¹' (Set.range qj)ᶜ := hy
    rw [hk] at this
    exact this
  obtain ⟨x, hx⟩ := hy
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback x y hx
  exact ⟨z, hz⟩

end AlgebraicGeometry
