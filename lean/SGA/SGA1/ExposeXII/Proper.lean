/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Projective.Chow
import SGA.SGA1.ExposeXII.ProjectiveSpace
import SGA.SGA1.ExposeXII.ProperMapLocal

/-!
# SGA 1, Exposé XII, 3.2 (v): proper morphisms give proper maps

For `K` an algebraically closed proper normed field (`ℂ`) and `f : X ⟶ Y` a proper morphism of
`K`-schemes locally of finite type, the map `X(K) → Y(K)` is proper
(`SchemePoints.isProperMap_map_of_isProper`); in particular `X(K)` is compact when `X` is proper
over `K` (`SchemePoints.compactSpace_of_isProper`). This is the direct implication of XII.3.2 (v).

The proof reduces to an affine base (properness of maps is local on the target), then to an
integral source (the irreducible components with their reduced structure), where Chow's lemma
(`exists_isHProjective_of_isProper`) gives a surjection `X' ⟶ X` with `X'` a closed subscheme of
some `ℙ(σ; Y)`; `ℙ(σ; Y)(K) → Y(K)` is proper as `ℙ(σ; K)(K)` is compact
(`ProjectivePoints.isProperMap_map_of_isHProjective`), and `X'(K) → X(K)` is surjective.

Conversely (in part), with XII.2.2 (`ClosureComparisonStatement`), a quasi-compact `f` such that
`X(ℂ) → Y(ℂ)` is proper is a closed map (`SchemePoints.isClosedMap_of_isProperMap_map`).
-/

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology Set

namespace SGA.SGA1.ExposeXII

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous map `f : X → Y` is proper if `X` is covered by the images of finitely many
continuous maps `gᵢ : Zᵢ → X` with `f ∘ gᵢ` proper. -/
lemma isProperMap_of_iUnion_range_eq {ι : Type*} [Finite ι] {Z : ι → Type*}
    [∀ i, TopologicalSpace (Z i)] {f : X → Y} (hf : Continuous f) (g : ∀ i, Z i → X)
    (hg : ∀ i, Continuous (g i)) (hfg : ∀ i, IsProperMap (f ∘ g i))
    (hcover : ⋃ i, range (g i) = univ) : IsProperMap f := by
  have hx (x : X) : ∃ i z, g i z = x := by
    have : x ∈ ⋃ i, range (g i) := hcover ▸ mem_univ x
    obtain ⟨i, z, hz⟩ := mem_iUnion.mp this
    exact ⟨i, z, hz⟩
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨hf, fun C hC ↦ ?_, fun y ↦ ?_⟩
  · have : f '' C = ⋃ i, (f ∘ g i) '' (g i ⁻¹' C) := by
      ext y
      simp only [mem_image, mem_iUnion, mem_preimage, Function.comp_apply]
      constructor
      · rintro ⟨x, hxC, rfl⟩
        obtain ⟨i, z, rfl⟩ := hx x
        exact ⟨i, z, hxC, rfl⟩
      · rintro ⟨i, z, hz, rfl⟩
        exact ⟨g i z, hz, rfl⟩
    rw [this]
    exact isClosed_iUnion_of_finite fun i ↦ (hfg i).isClosedMap _ (hC.preimage (hg i))
  · have : f ⁻¹' {y} = ⋃ i, g i '' ((f ∘ g i) ⁻¹' {y}) := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_image, Function.comp_apply]
      constructor
      · rintro rfl
        obtain ⟨i, z, rfl⟩ := hx x
        exact ⟨i, z, rfl, rfl⟩
      · rintro ⟨i, z, hz, rfl⟩
        exact hz
    rw [this]
    exact isCompact_iUnion fun i ↦
      ((hfg i).isCompact_preimage isCompact_singleton).image (hg i)

/-- If `f ∘ i = j ∘ g` with `i`, `j` open embeddings and `range i = f⁻¹(range j)`, and `g` is
proper, then so is the restriction of `f` over `range j`. -/
lemma isProperMap_restrictPreimage_of_isOpenEmbedding {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : X → Y} {g : A → B} {i : A → X} {j : B → Y}
    (hi : IsOpenEmbedding i) (hj : IsOpenEmbedding j) (h : f ∘ i = j ∘ g)
    (hr : range i = f ⁻¹' range j) (hg : IsProperMap g) :
    IsProperMap ((range j).restrictPreimage f) := by
  let ei := hi.toHomeomorph
  let ej := hj.toHomeomorph
  have : (range j).restrictPreimage f =
      ej ∘ g ∘ ei.symm ∘ Homeomorph.setCongr hr.symm := by
    funext x
    obtain ⟨x, hx⟩ := x
    have hx' : x ∈ range i := hr ▸ hx
    obtain ⟨a, rfl⟩ := hx'
    apply Subtype.ext
    have h1 : ei.symm ⟨i a, mem_range_self a⟩ = a := ei.symm_apply_eq.mpr rfl
    simp only [Function.comp_apply, restrictPreimage_coe, Homeomorph.setCongr]
    change f (i a) = j (g (ei.symm ⟨i a, _⟩))
    rw [h1]
    exact congrFun h a
  rw [this]
  exact ej.isProperMap.comp (hg.comp (ei.symm.isProperMap.comp
    (Homeomorph.setCongr hr.symm).isProperMap))

end Topology

/-- An irreducible closed subset `T` of a quasi-separated scheme is the image of a closed immersion
from an integral scheme (`T` with its reduced structure: the scheme-theoretic image of
`Spec κ(ξ) ⟶ X`, `ξ` the generic point of `T`). -/
lemma exists_isIntegral_isClosedImmersion {X : Scheme.{u}} [QuasiSeparatedSpace X] (T : Set X)
    (hT : IsClosed T) (hirr : IsIrreducible T) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ X), IsClosedImmersion ι ∧ IsIntegral Z ∧ range ι = T := by
  let f := X.fromSpecResidueField hirr.genericPoint
  have : IsReduced f.image := IsSchemeTheoreticallyDominant.isReduced f.toImage
  have : IrreducibleSpace f.image := by
    rw [irreducibleSpace_def]
    have := ((IrreducibleSpace.isIrreducible_univ (Spec (X.residueField hirr.genericPoint))).image
      f.toImage f.toImage.continuous.continuousOn).closure
    rwa [image_univ, f.toImage.denseRange.closure_range] at this
  refine ⟨f.image, f.imageι, inferInstance, isIntegral_of_irreducibleSpace_of_isReduced _, ?_⟩
  change range f.ker.subschemeι = T
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
    Scheme.range_fromSpecResidueField, hirr.closure_genericPoint hT]

namespace SchemePoints

variable {K : Type u} [NontriviallyNormedField K] [ProperSpace K] [IsAlgClosed K]

/-- XII.3.2 (v), integral source over an affine base: for `X` integral and proper over an affine
`K`-scheme `Y` locally of finite type, `X(K) → Y(K)` is proper. By Chow's lemma there is a
surjective `π : X' ⟶ X` with `X'` H-projective over `Y`, and `X'(K) → Y(K)` is proper while
`X'(K) → X(K)` is surjective. -/
theorem isProperMap_map_of_isIntegral {X Y : Scheme.{u}} [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))] [IsAffine Y] (f : X ⟶ Y)
    [f.IsOver (Spec (.of K))] [IsProper f] [IsIntegral X] :
    IsProperMap (map (K := K) f) := by
  obtain ⟨X', π, -, hπ, hsurj, hπf, -⟩ := exists_isHProjective_of_isProper f
  let : X'.Over (Spec (.of K)) := .ofHom (π ≫ X ↘ Spec (.of K))
  have : π.IsOver (Spec (.of K)) := ⟨rfl⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of K)) := by
    rw [← comp_over f (Spec (.of K))]
    infer_instance
  have : LocallyOfFiniteType (X' ↘ Spec (.of K)) := by
    change LocallyOfFiniteType (π ≫ X ↘ Spec (.of K))
    infer_instance
  have h₁ : IsProperMap (map (K := K) (π ≫ f)) :=
    ProjectivePoints.isProperMap_map_of_isHProjective (π ≫ f)
  have h₂ : Function.Surjective (map (K := K) π) := surjective_map_of_surjective π hsurj.surj
  rw [map_comp] at h₁
  exact isProperMap_of_comp_of_surj (continuous_map π) (continuous_map f) h₁ h₂

/-- XII.3.2 (v) over an affine base: for `X` proper over an affine `K`-scheme `Y` locally of finite
type, `X(K) → Y(K)` is proper. `X` is noetherian, the union of the finitely many integral closed
subschemes on its irreducible components, to which `isProperMap_map_of_isIntegral` applies. -/
theorem isProperMap_map_of_isAffine {X Y : Scheme.{u}} [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))] [IsAffine Y] (f : X ⟶ Y)
    [f.IsOver (Spec (.of K))] [IsProper f] : IsProperMap (map (K := K) f) := by
  have : LocallyOfFiniteType (X ↘ Spec (.of K)) := by
    rw [← comp_over f (Spec (.of K))]
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have := hfin.to_subtype
  have H (T : irreducibleComponents X) := exists_isIntegral_isClosedImmersion T.1
    (isClosed_of_mem_irreducibleComponents _ T.2) T.2.1
  choose Z ι hι hZ hrange using H
  let (T : irreducibleComponents X) : (Z T).Over (Spec (.of K)) := .ofHom (ι T ≫ X ↘ Spec (.of K))
  have (T : irreducibleComponents X) : (ι T).IsOver (Spec (.of K)) := ⟨rfl⟩
  have (T : irreducibleComponents X) : LocallyOfFiniteType (Z T ↘ Spec (.of K)) := by
    have := hι T
    change LocallyOfFiniteType (ι T ≫ X ↘ Spec (.of K))
    infer_instance
  refine isProperMap_of_iUnion_range_eq (continuous_map f) (fun T ↦ map (K := K) (ι T))
    (fun T ↦ continuous_map _) (fun T ↦ ?_) ?_
  · have := hι T
    have := hZ T
    rw [← map_comp]
    exact isProperMap_map_of_isIntegral (ι T ≫ f)
  · refine eq_univ_of_forall fun p ↦ mem_iUnion.mpr ?_
    obtain ⟨T, hT, hpT⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {p.pt}
      isIrreducible_singleton
    have := hι ⟨T, hT⟩
    obtain ⟨q, hq⟩ := exists_map_eq (ι ⟨T, hT⟩) p (by rw [hrange]; exact hpT rfl)
    exact ⟨⟨T, hT⟩, q, hq⟩

/-- XII.3.2 (v), direct implication: a proper morphism `f : X ⟶ Y` of `K`-schemes locally of
finite type (`K` algebraically closed and proper, e.g. `ℂ`) induces a proper map
`X(K) → Y(K)`. Properness of maps being local on the target, this reduces to affine `Y`
(`isProperMap_map_of_isAffine`). -/
theorem isProperMap_map_of_isProper {X Y : Scheme.{u}} [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))] (f : X ⟶ Y)
    [f.IsOver (Spec (.of K))] [IsProper f] : IsProperMap (map (K := K) f) := by
  refine isProperMap_of_isProperMap_restrictPreimage (continuous_map f) fun y ↦ ?_
  obtain ⟨U, hU, hyU⟩ := exists_isAffineOpen_mem y
  let : U.toScheme.Over (Spec (.of K)) := .ofHom (U.ι ≫ Y ↘ Spec (.of K))
  have : U.ι.IsOver (Spec (.of K)) := ⟨rfl⟩
  let : (f ⁻¹ᵁ U).toScheme.Over (Spec (.of K)) := .ofHom ((f ⁻¹ᵁ U).ι ≫ X ↘ Spec (.of K))
  have : (f ⁻¹ᵁ U).ι.IsOver (Spec (.of K)) := ⟨rfl⟩
  have : (f ∣_ U).IsOver (Spec (.of K)) := ⟨by
    change f ∣_ U ≫ U.ι ≫ Y ↘ Spec (.of K) = (f ⁻¹ᵁ U).ι ≫ X ↘ Spec (.of K)
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, comp_over]⟩
  have : IsProper (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹_› U
  have : IsAffine U := hU
  have : LocallyOfFiniteType (U.toScheme ↘ Spec (.of K)) := by
    change LocallyOfFiniteType (U.ι ≫ Y ↘ Spec (.of K))
    infer_instance
  refine ⟨range (map (K := K) U.ι), (isOpenEmbedding_map U.ι).isOpen_range,
    exists_map_eq_of_isOpenImmersion U.ι y (by rw [Scheme.Opens.range_ι]; exact hyU),
    isProperMap_restrictPreimage_of_isOpenEmbedding (isOpenEmbedding_map (f ⁻¹ᵁ U).ι)
      (isOpenEmbedding_map U.ι) ?_ ?_ (isProperMap_map_of_isAffine (f ∣_ U))⟩
  · funext q
    refine ext ?_
    change (q.1 ≫ (f ⁻¹ᵁ U).ι) ≫ f = (q.1 ≫ f ∣_ U) ≫ U.ι
    rw [Category.assoc, Category.assoc, morphismRestrict_ι]
  · ext p
    constructor
    · rintro ⟨q, rfl⟩
      refine ⟨map (f ∣_ U) q, ext ?_⟩
      change (q.1 ≫ f ∣_ U) ≫ U.ι = (q.1 ≫ (f ⁻¹ᵁ U).ι) ≫ f
      rw [Category.assoc, Category.assoc, morphismRestrict_ι]
    · rintro ⟨q, hq⟩
      refine exists_map_eq_of_isOpenImmersion _ p ?_
      rw [Scheme.Opens.range_ι]
      have : f p.pt = U.ι q.pt := by rw [← pt_map, ← pt_map, hq]
      change f p.pt ∈ U
      rw [this]
      have := mem_range_self (f := U.ι) q.pt
      rwa [Scheme.Opens.range_ι] at this

/-- XII.3.2 (v), absolute case: for `X` proper over `K`, the space `X(K)` is compact. -/
theorem compactSpace_of_isProper {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [IsProper (X ↘ Spec (.of K))] : CompactSpace (SchemePoints K X) := by
  let := selfOver (K := K)
  have := subsingleton_selfOver (K := K)
  have : (X ↘ Spec (.of K)).IsOver (Spec (.of K)) := ⟨Category.comp_id _⟩
  have : LocallyOfFiniteType (Spec (.of K) ↘ Spec (.of K)) := by
    change LocallyOfFiniteType (𝟙 _)
    infer_instance
  have h := isProperMap_map_of_isProper (K := K) (X ↘ Spec (.of K))
  exact ⟨by
    simpa using h.isCompact_preimage (Set.subsingleton_of_subsingleton (s := univ)).isCompact⟩

omit [ProperSpace K] in
/-- A `K`-point of `X` lying over a point of `f(T)`, `T ⊆ X` closed, lifts to a `K`-point of `T`. -/
theorem exists_map_eq_of_mem_image {X Y : Scheme.{u}} [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] (f : X ⟶ Y) [f.IsOver (Spec (.of K))]
    {T : Set X} (hT : IsClosed T) (y : SchemePoints K Y) (hy : y.pt ∈ f '' T) :
    ∃ x : SchemePoints K X, x.pt ∈ T ∧ map f x = y := by
  let I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨T, hT⟩
  let ι := I.subschemeι
  have hι : range ι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let : I.subscheme.Over (Spec (.of K)) := .ofHom (ι ≫ X ↘ Spec (.of K))
  have : ι.IsOver (Spec (.of K)) := ⟨rfl⟩
  have : LocallyOfFiniteType (I.subscheme ↘ Spec (.of K)) := by
    change LocallyOfFiniteType (ι ≫ X ↘ Spec (.of K))
    infer_instance
  obtain ⟨x, hxT, hxy⟩ := hy
  obtain ⟨q, hq⟩ := exists_map_eq (ι ≫ f) y (by
    rw [← hι] at hxT
    obtain ⟨z, rfl⟩ := hxT
    exact ⟨z, hxy⟩)
  refine ⟨map ι q, ?_, ?_⟩
  · rw [pt_map, ← hι]
    exact mem_range_self _
  · rw [← hq, map_comp]
    rfl

end SchemePoints

namespace SchemePoints

/-- XII.3.2 (v), converse, in part, from XII.2.2: if `f : X ⟶ Y` is quasi-compact between
`ℂ`-schemes locally of finite type and `X(ℂ) → Y(ℂ)` is proper, then `f` is a closed map (SGA
then deduces that `f` is universally closed, by the same argument after base changes locally of
finite type, and separated from XII.3.1 (viii)). -/
theorem isClosedMap_of_isProperMap_map (H : ClosureComparisonStatement) {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]
    [QuasiCompact f] (hf : IsProperMap (map (K := ℂ) f)) : IsClosedMap f := by
  intro T hT
  have : LocallyOfFiniteType (f ≫ Y ↘ Spec (.of ℂ)) := by rw [comp_over]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of ℂ))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of ℂ))
  have hlc : IsLocallyConstructible (f '' T) :=
    f.isLocallyConstructible_image (isLocallyConstructible_of_isClosed hT)
  rw [isClosed_iff_of_closureComparison H hlc]
  have : pt ⁻¹' (f '' T) = map (K := ℂ) f '' (pt ⁻¹' T) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hxT, rfl⟩ := exists_map_eq_of_mem_image f hT y hy
      exact ⟨x, hxT, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.pt, hx, (pt_map f x).symm⟩
  rw [this]
  exact hf.isClosedMap _ (hT.preimage continuous_pt)

end SchemePoints

end SGA.SGA1.ExposeXII
