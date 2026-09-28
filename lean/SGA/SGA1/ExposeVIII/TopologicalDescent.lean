/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Flat.TorsionFree
import SGA.SGA1.ExposeVIII.PropertyDescent

/-!
# SGA 1, Exposé VIII, §4: descent of topological properties

* VIII.4.1: for `g` flat and `Z = f(X)` with `f` quasi-compact,
  `g⁻¹(closure Z) = closure (g⁻¹ Z)`. The proof uses that a point in the closure of the image of
  a quasi-compact morphism is a specialization of a point of the image
  (`exists_specializes_of_mem_closure_range`) and that flat morphisms lift generalizations.
* VIII.4.2–4.4: a flat quasi-compact morphism is a quotient map onto its image; a faithfully flat
  quasi-compact morphism is a topological quotient map, and open (closed) subsets descend.
* VIII.4.5: locally closed images of quasi-compact morphisms descend.
* VIII.4.6: open maps, closed maps, quasi-compact embeddings and homeomorphisms descend.
* VIII.4.7: the universal versions descend (a general fact, `universally_descendsAlong`).
* VIII.4.8: separated and proper morphisms descend.
* VIII.4.9: flat morphisms locally of finite presentation are open (mathlib), and SGA's example
  of a faithfully flat quasi-compact morphism that is not open is formalized with `Y = Spec ℤ`.
  The last example of VIII.4.9 (non-quasi-compact covers) is not formalized.
* VIII.4.10 (variant with a flat module of support `Y'`) is not formalized.
-/

universe u

namespace SGA.SGA1.ExposeVIII

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MorphismProperty Topology

section Closure

/-- In an affine scheme, a point in the closure of the image of `Spec S ⟶ Spec R` is a
specialization of a point of the image (a minimal prime over the kernel lies in the image). -/
lemma exists_specializes_of_mem_closure_range_comap {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {y : PrimeSpectrum R} (hy : y ∈ closure (Set.range (PrimeSpectrum.comap φ))) :
    ∃ x, PrimeSpectrum.comap φ x ⤳ y := by
  rw [PrimeSpectrum.closure_range_comap, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at hy
  obtain ⟨p, hp, hpy⟩ := Ideal.exists_minimalPrimes_le hy
  rw [RingHom.ker_eq_comap_bot] at hp
  obtain ⟨q, hq, -, hqp⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes φ p hp
  refine ⟨⟨q, hq⟩, (PrimeSpectrum.le_iff_specializes _ _).mp ?_⟩
  change q.comap φ ≤ y.asIdeal
  rwa [hqp]

set_option backward.isDefEq.respectTransparency.types false in
/-- A point in the closure of the image of a quasi-compact morphism is a specialization of a
point of the image. -/
theorem exists_specializes_of_mem_closure_range {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {y : Y} (hy : y ∈ closure (Set.range f)) : ∃ x, f x ⤳ y := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  obtain ⟨R, h, hh⟩ := isCompact_iff_exists.mp (f.isCompact_preimage (U := V) hV.isCompact)
  have hrange : Set.range (h ≫ f) = Set.range f ∩ V := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hh]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, rfl⟩, hx⟩
    · rintro ⟨⟨x, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩
  let l : Spec R ⟶ Spec Γ(Y, V) :=
    IsOpenImmersion.lift hV.fromSpec (h ≫ f) (by rw [hrange, hV.range_fromSpec]; simp)
  have hl : l ≫ hV.fromSpec = h ≫ f := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ := Spec.map_surjective l
  obtain ⟨y₀, rfl⟩ : y ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have hy₀ : y₀ ∈ closure (Set.range l) := by
    rw [hV.fromSpec.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      ← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, hl, hrange]
    refine closure_mono (Set.inter_comm _ _).subset (V.isOpen.inter_closure ⟨?_, hy⟩)
    rw [← hV.range_fromSpec]
    exact ⟨y₀, rfl⟩
  rw [← hφ] at hy₀
  obtain ⟨x, hx⟩ := exists_specializes_of_mem_closure_range_comap φ.hom hy₀
  refine ⟨h x, ?_⟩
  have := hx.map hV.fromSpec.continuous
  rwa [← Spec.map_apply, hφ, ← Scheme.Hom.comp_apply, hl, Scheme.Hom.comp_apply] at this

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.4.1: if `g : Y' ⟶ Y` is flat and `Z = f(X)` for a quasi-compact `f : X ⟶ Y`, then
`g⁻¹(closure Z) = closure (g⁻¹ Z)`. -/
theorem preimage_closure_range_eq_closure_preimage {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (g : Y' ⟶ Y) [Flat g] :
    g ⁻¹' closure (Set.range f) = closure (g ⁻¹' Set.range f) := by
  refine subset_antisymm (fun y' hy' ↦ ?_) (g.continuous.closure_preimage_subset _)
  obtain ⟨x, hx⟩ := exists_specializes_of_mem_closure_range f hy'
  obtain ⟨y'', hy'', e⟩ := Flat.generalizingMap g hx
  have : y'' ∈ g ⁻¹' Set.range f := ⟨x, e.symm⟩
  exact closure_mono (Set.singleton_subset_iff.mpr this) (specializes_iff_mem_closure.mp hy'')

set_option backward.isDefEq.respectTransparency.types false in
/-- The image of a closed subset under a quasi-compact morphism is the image of a quasi-compact
morphism (from the closed subset with its reduced structure). -/
lemma exists_quasiCompact_range_eq_image {Y Z : Scheme.{u}} (g : Y ⟶ Z) [QuasiCompact g]
    {T : Set Y} (hT : IsClosed T) :
    ∃ (W : Scheme.{u}) (k : W ⟶ Z), QuasiCompact k ∧ Set.range k = g '' T := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, hT⟩ : TopologicalSpace.Closeds Y)
  refine ⟨I.subscheme, I.subschemeι ≫ g, inferInstance, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, I.range_subschemeι]
  simp [I]

/-- VIII.4.1 for images of closed subsets: if `g` is flat, `f` quasi-compact and `T` closed in `X`,
then `g⁻¹(closure f(T)) = closure (g⁻¹ f(T))`. -/
theorem preimage_closure_image_eq_closure_preimage {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (g : Y' ⟶ Y) [Flat g] {T : Set X} (hT : IsClosed T) :
    g ⁻¹' closure (f '' T) = closure (g ⁻¹' (f '' T)) := by
  obtain ⟨W, k, hk, e⟩ := exists_quasiCompact_range_eq_image f hT
  rw [← e]
  exact preimage_closure_range_eq_closure_preimage k g

end Closure

section Quotient

variable {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)

/-- VIII.4.2: for `g` flat and quasi-compact, a closed subset `Z'` of `Y'` saturated for the
equivalence relation defined by `g` satisfies `Z' = g⁻¹(closure g(Z'))`. -/
theorem eq_preimage_closure_image_of_saturated [Flat g] [QuasiCompact g] {Z' : Set Y'}
    (hZ' : IsClosed Z') (hsat : g ⁻¹' (g '' Z') = Z') : Z' = g ⁻¹' closure (g '' Z') := by
  rw [preimage_closure_image_eq_closure_preimage g g hZ', hsat, hZ'.closure_eq]

/-- VIII.4.2, reformulated: for `g` flat and quasi-compact, the topology of `g(Y')` induced by
`Y` is the quotient topology of `Y'`. -/
theorem isQuotientMap_rangeFactorization [Flat g] [QuasiCompact g] :
    IsQuotientMap (Set.rangeFactorization g) := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨Set.rangeFactorization_surjective, fun s ↦ ⟨fun hs ↦ hs.preimage
    (g.continuous.subtype_mk _), fun hs ↦ ?_⟩⟩
  set Z' := Set.rangeFactorization g ⁻¹' s
  have himg : g '' Z' = Subtype.val '' s := by
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨_, hy', rfl⟩
    · rintro ⟨⟨_, y', rfl⟩, hy, rfl⟩
      exact ⟨y', hy, rfl⟩
  have hsat : g ⁻¹' (g '' Z') = Z' := by
    rw [himg]
    ext y'
    exact ⟨fun ⟨z, hz, e⟩ ↦ by rwa [show z = Set.rangeFactorization g y' from Subtype.ext e] at hz,
      fun h ↦ ⟨_, h, rfl⟩⟩
  have key := eq_preimage_closure_image_of_saturated g hs hsat
  rw [himg] at key
  refine isClosed_induced_iff.mpr ⟨closure (Subtype.val '' s), isClosed_closure, ?_⟩
  ext ⟨_, y', rfl⟩
  exact (Set.ext_iff.mp key y').symm

/-- VIII.4.3: a faithfully flat quasi-compact morphism is a topological quotient map. -/
theorem isQuotientMap_of_flat [Flat g] [QuasiCompact g] [Surjective g] : IsQuotientMap g :=
  Flat.isQuotientMap_of_surjective g

/-- VIII.4.3: for `g` faithfully flat quasi-compact, `Z ⊆ Y` is open iff `g⁻¹ Z` is. -/
theorem isOpen_preimage_iff [Flat g] [QuasiCompact g] [Surjective g] {Z : Set Y} :
    IsOpen (g ⁻¹' Z) ↔ IsOpen Z :=
  (isQuotientMap_of_flat g).isOpen_preimage

/-- VIII.4.3: for `g` faithfully flat quasi-compact, `Z ⊆ Y` is closed iff `g⁻¹ Z` is. -/
theorem isClosed_preimage_iff [Flat g] [QuasiCompact g] [Surjective g] {Z : Set Y} :
    IsClosed (g ⁻¹' Z) ↔ IsClosed Z :=
  (isQuotientMap_of_flat g).isClosed_preimage

/-- Before VIII.4.4: two points of `Y'` have the same image in `Y` iff they are the two
projections of a point of `Y' ×_Y Y'`. -/
theorem exists_fst_snd_iff {a b : Y'} :
    g a = g b ↔ ∃ c, pullback.fst g g c = a ∧ pullback.snd g g c = b := by
  refine ⟨Scheme.Pullback.exists_preimage_pullback a b, ?_⟩
  rintro ⟨c, rfl, rfl⟩
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- Before VIII.4.4: for `g` surjective, the diagram of sets `𝒫(Y) → 𝒫(Y') ⇉ 𝒫(Y'')` is exact:
a subset of `Y'` whose two inverse images in `Y' ×_Y Y'` agree is the inverse image of a unique
subset of `Y`. -/
theorem existsUnique_preimage_eq [Surjective g] {T' : Set Y'}
    (h : pullback.fst g g ⁻¹' T' = pullback.snd g g ⁻¹' T') : ∃! T : Set Y, g ⁻¹' T = T' := by
  refine ⟨g '' T', subset_antisymm (fun a ⟨b, hb, e⟩ ↦ ?_) (Set.subset_preimage_image _ _),
    fun T hT ↦ hT ▸ (Set.image_preimage_eq _ g.surjective).symm⟩
  obtain ⟨c, rfl, rfl⟩ := (exists_fst_snd_iff g).mp e
  change c ∈ pullback.snd g g ⁻¹' T'
  rw [← h]
  exact hb

/-- VIII.4.4 (open sets): for `g` faithfully flat quasi-compact, an open subset of `Y'` whose two
inverse images in `Y' ×_Y Y'` agree is the inverse image of a unique open subset of `Y`. -/
theorem existsUnique_isOpen_preimage_eq [Flat g] [QuasiCompact g] [Surjective g] {U' : Set Y'}
    (hU' : IsOpen U') (h : pullback.fst g g ⁻¹' U' = pullback.snd g g ⁻¹' U') :
    ∃! U : Set Y, IsOpen U ∧ g ⁻¹' U = U' := by
  obtain ⟨U, hU, hU₁⟩ := existsUnique_preimage_eq g h
  exact ⟨U, ⟨(isOpen_preimage_iff g).mp (hU ▸ hU'), hU⟩, fun V hV ↦ hU₁ V hV.2⟩

/-- VIII.4.4 (closed sets): for `g` faithfully flat quasi-compact, a closed subset of `Y'` whose
two inverse images in `Y' ×_Y Y'` agree is the inverse image of a unique closed subset of `Y`. -/
theorem existsUnique_isClosed_preimage_eq [Flat g] [QuasiCompact g] [Surjective g] {F' : Set Y'}
    (hF' : IsClosed F') (h : pullback.fst g g ⁻¹' F' = pullback.snd g g ⁻¹' F') :
    ∃! F : Set Y, IsClosed F ∧ g ⁻¹' F = F' := by
  obtain ⟨F, hF, hF₁⟩ := existsUnique_preimage_eq g h
  exact ⟨F, ⟨(isClosed_preimage_iff g).mp (hF ▸ hF'), hF⟩, fun V hV ↦ hF₁ V hV.2⟩

/-- A quotient map reflects local closedness of sets whose closure commutes with the inverse
image. -/
lemma isLocallyClosed_of_isQuotientMap {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {q : A → B} (hq : IsQuotientMap q) {Z : Set B} (hZ : q ⁻¹' closure Z = closure (q ⁻¹' Z))
    (h : IsLocallyClosed (q ⁻¹' Z)) : IsLocallyClosed Z := by
  rw [isLocallyClosed_iff_isOpen_coborder] at h ⊢
  rw [← hq.isOpen_preimage]
  convert h using 1
  simp only [coborder, Set.preimage_compl, Set.preimage_sdiff, hZ]

/-- VIII.4.5: let `g` be faithfully flat quasi-compact and `Z = f(X)` for a quasi-compact `f`.
Then `Z` is locally closed iff `g⁻¹ Z` is. -/
theorem isLocallyClosed_preimage_iff [Flat g] [QuasiCompact g] [Surjective g]
    {X : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    IsLocallyClosed (g ⁻¹' Set.range f) ↔ IsLocallyClosed (Set.range f) :=
  ⟨isLocallyClosed_of_isQuotientMap (isQuotientMap_of_flat g)
    (preimage_closure_range_eq_closure_preimage f g), fun h ↦ h.preimage g.continuous⟩

end Quotient

section Maps

variable {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

lemma surjective_flat_quasiCompact {f : X ⟶ Z}
    (hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) f) :
    Surjective f ∧ Flat f ∧ QuasiCompact f :=
  ⟨hf.1.1, hf.1.2, hf.2⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.4.6 (open maps): if `f` is faithfully flat quasi-compact and the base change of `g`
along `f` is an open map, so is `g`. -/
instance isOpenMap_descendsAlong_fpqc : DescendsAlong (topologically IsOpenMap)
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    obtain ⟨_, _, _⟩ := surjective_flat_quasiCompact hf
    intro U hU
    rw [← isOpen_preimage_iff f, ← Scheme.image_preimage_eq_of_isPullback h.flip]
    exact hfst _ (hU.preimage snd.continuous)

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.4.6 (closed maps): if `f` is faithfully flat quasi-compact and the base change of `g`
along `f` is a closed map, so is `g`. -/
instance isClosedMap_descendsAlong_fpqc : DescendsAlong (topologically IsClosedMap)
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    obtain ⟨_, _, _⟩ := surjective_flat_quasiCompact hf
    intro F hF
    rw [← isClosed_preimage_iff f, ← Scheme.image_preimage_eq_of_isPullback h.flip]
    exact hfst _ (hF.preimage snd.continuous)

/-- A continuous injective map `g` such that `F = g⁻¹(closure g(F))` for every closed `F` is an
embedding. -/
lemma isEmbedding_of_isClosed_eq {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]
    {k : B → C} (hk : Continuous k) (hinj : Function.Injective k)
    (H : ∀ F : Set B, IsClosed F → k ⁻¹' closure (k '' F) = F) : IsEmbedding k := by
  refine ⟨⟨TopologicalSpace.ext_isClosed fun F ↦ ⟨fun hF ↦ ?_, fun hF ↦ ?_⟩⟩, hinj⟩
  · exact isClosed_induced_iff.mpr ⟨_, isClosed_closure, H F hF⟩
  · obtain ⟨t, ht, rfl⟩ := isClosed_induced_iff.mp hF
    exact ht.preimage hk

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.4.6 (homeomorphisms into), in the form of the N.B. after its proof: if `f` is faithfully
flat (not necessarily quasi-compact), `g` is quasi-compact, and the base change of `g` along `f`
is an embedding, then `g` is an embedding. -/
theorem isEmbedding_of_isPullback (h : IsPullback fst snd f g) [Surjective f] [Flat f]
    [QuasiCompact g] (hfst : IsEmbedding fst) : IsEmbedding g := by
  have : Surjective snd := MorphismProperty.of_isPullback h ‹_›
  refine isEmbedding_of_isClosed_eq g.continuous (injective_of_isPullback h hfst.injective)
    fun F hF ↦ ?_
  apply (Set.preimage_injective.mpr snd.surjective)
  have e₁ : fst '' (snd ⁻¹' F) = f ⁻¹' (g '' F) := Scheme.image_preimage_eq_of_isPullback h.flip F
  rw [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, ← h.w,
    Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
    preimage_closure_image_eq_closure_preimage g f hF, ← e₁,
    ← hfst.isInducing.closure_eq_preimage_closure_image, (hF.preimage snd.continuous).closure_eq]

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.4.6 (homeomorphisms into): if `f` is faithfully flat quasi-compact and the base change
of `g` along `f` is a quasi-compact embedding, so is `g`. -/
instance isEmbedding_inf_quasiCompact_descendsAlong_fpqc :
    DescendsAlong (topologically IsEmbedding ⊓ @QuasiCompact)
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    obtain ⟨_, _, _⟩ := surjective_flat_quasiCompact hf
    have : QuasiCompact fst := hfst.2
    have : QuasiCompact g := of_isPullback_of_descendsAlong h hf this
    exact ⟨isEmbedding_of_isPullback h hfst.1, this⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.4.6 (homeomorphisms): if `f` is faithfully flat quasi-compact and the base change of `g`
along `f` is a homeomorphism, so is `g`. -/
instance isHomeomorph_descendsAlong_fpqc : DescendsAlong (topologically IsHomeomorph)
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    obtain ⟨_, _, _⟩ := surjective_flat_quasiCompact hf
    have hfst' : IsHomeomorph fst := hfst
    exact ⟨g.continuous,
      of_isPullback_of_descendsAlong (P := topologically IsOpenMap) h hf hfst'.isOpenMap,
      bijective_of_isPullback h hfst'.bijective⟩

/-- If `P` descends along `Q`, so does `P.universally`. -/
theorem universally_descendsAlong {C : Type*} [Category C] [HasPullbacks C]
    (P Q : MorphismProperty C) [P.DescendsAlong Q] [Q.IsStableUnderBaseChange] :
    P.universally.DescendsAlong Q where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    intro X' Y' i₁ i₂ g' H
    have hW : IsPullback (pullback.fst f i₂) (pullback.snd f i₂) f i₂ := .of_hasPullback _ _
    have hV := IsPullback.of_hasPullback (pullback.snd f i₂) g'
    refine of_isPullback_of_descendsAlong hV (Q.pullback_snd _ _ hf) ?_
    have outer : IsPullback (pullback.snd (pullback.snd f i₂) g' ≫ i₁)
        (pullback.fst (pullback.snd f i₂) g') g (pullback.fst f i₂ ≫ f) := by
      rw [hW.w]
      exact hV.flip.paste_horiz H.flip
    let j := h.lift (pullback.fst (pullback.snd f i₂) g' ≫ pullback.fst f i₂)
      (pullback.snd (pullback.snd f i₂) g' ≫ i₁) (by simpa using outer.w.symm)
    have hj : IsPullback j (pullback.fst (pullback.snd f i₂) g') fst (pullback.fst f i₂) :=
      IsPullback.of_right (by simpa [j] using outer) (by simp [j]) h.flip
    exact hfst _ _ _ hj.flip

/-- VIII.4.7 (universally open): mathlib's
`descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact`. -/
instance universallyOpen_descendsAlong_fpqc : DescendsAlong @UniversallyOpen
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  inferInstance

/-- VIII.4.7 (universally closed): mathlib's
`descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`. -/
instance universallyClosed_descendsAlong_fpqc : DescendsAlong @UniversallyClosed
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.4.7 (universal homeomorphisms into): quasi-compact universal embeddings descend along
faithfully flat quasi-compact morphisms. -/
instance universally_isEmbedding_inf_quasiCompact_descendsAlong_fpqc :
    DescendsAlong (topologically IsEmbedding ⊓ @QuasiCompact).universally
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  universally_descendsAlong _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.4.7 (universal homeomorphisms):  universal homeomorphisms descend along faithfully flat
quasi-compact morphisms. -/
instance universally_isHomeomorph_descendsAlong_fpqc :
    DescendsAlong (topologically IsHomeomorph).universally (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  universally_descendsAlong _ _

instance topologically_isClosedMap_respectsIso : (topologically IsClosedMap).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isClosedMap) fun _ _ hf hg ↦ hg.comp hf

set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism is separated iff its diagonal (always an immersion) is a closed map. -/
lemma isSeparated_iff_diagonal_isClosedMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSeparated f ↔ IsClosedMap (pullback.diagonal f) :=
  ⟨fun _ ↦ (pullback.diagonal f).isClosedMap, fun h ↦
    ⟨.of_isPreimmersion _ (h.isClosed_range)⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.4.8 (separated): separated morphisms descend along faithfully flat quasi-compact
morphisms, since the diagonal of the base change is a base change of the diagonal. -/
instance isSeparated_descendsAlong_fpqc : DescendsAlong @IsSeparated
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : @IsSeparated = (topologically IsClosedMap).diagonal := by
    ext X Y f
    exact isSeparated_iff_diagonal_isClosedMap f
  rw [this]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.4.8 (proper): proper morphisms descend along faithfully flat quasi-compact morphisms. -/
instance isProper_descendsAlong_fpqc : DescendsAlong @IsProper
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) where
  of_isPullback h hf hfst := by
    have : IsProper _ := hfst
    have : IsSeparated _ := of_isPullback_of_descendsAlong h hf
      (show IsSeparated _ from inferInstance)
    have : UniversallyClosed _ := of_isPullback_of_descendsAlong h hf
      (show UniversallyClosed _ from inferInstance)
    have : LocallyOfFiniteType _ := of_isPullback_of_descendsAlong h hf
      (show LocallyOfFiniteType _ from inferInstance)
    exact ⟨⟩

/-- VIII.4.9: a flat morphism locally of finite presentation (for instance flat of finite type
over a locally noetherian scheme) is (universally) open. -/
theorem isOpenMap_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] : IsOpenMap f :=
  f.isOpenMap

/-- The generic point of `Spec ℤ` is not open. -/
lemma not_isOpen_singleton_bot_int : ¬ IsOpen ({⊥} : Set (PrimeSpectrum ℤ)) := by
  intro h
  obtain ⟨_, ⟨n, rfl⟩, hn, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := ℤ)).exists_subset_of_mem_open
      (Set.mem_singleton ⊥) h
  have hn0 : n ≠ 0 := fun e ↦ by simp [e] at hn
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
  have : Fact p.Prime := ⟨hp⟩
  let P : PrimeSpectrum ℤ := ⟨Ideal.span {(p : ℤ)}, (Ideal.span_singleton_prime (by
    exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)⟩
  have hP : P ∈ PrimeSpectrum.basicOpen n := by
    change n ∉ Ideal.span {(p : ℤ)}
    rw [Ideal.mem_span_singleton]
    intro hdvd
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simp only [Int.natAbs_natCast] at this
    exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hn0) this) (by omega)
  have : P = ⊥ := hsub hP
  have hmem : (p : ℤ) ∈ P.asIdeal := Ideal.mem_span_singleton_self _
  rw [this] at hmem
  change (p : ℤ) ∈ (⊥ : Ideal ℤ) at hmem
  rw [Ideal.mem_bot] at hmem
  exact hp.ne_zero (by exact_mod_cast hmem)

set_option backward.isDefEq.respectTransparency false in
/-- VIII.4.9: a faithfully flat quasi-compact morphism of noetherian schemes need not be open.
SGA's example with `Y = Spec ℤ`: `Spec (ℤ × ℚ) = Spec ℤ ⊔ Spec ℚ ⟶ Spec ℤ` maps the open subset
`Spec ℚ` onto the generic point, which is not open. -/
theorem exists_fpqc_not_isOpenMap :
    ∃ (X Y : Scheme.{0}) (f : X ⟶ Y), Surjective f ∧ Flat f ∧ QuasiCompact f ∧ ¬ IsOpenMap f := by
  let φ : CommRingCat.of ℤ ⟶ CommRingCat.of (ℤ × ℚ) := CommRingCat.ofHom (algebraMap ℤ (ℤ × ℚ))
  refine ⟨_, _, Spec.map φ, ?_, ?_, inferInstance, fun hopen ↦ ?_⟩
  · let ψ : CommRingCat.of (ℤ × ℚ) ⟶ CommRingCat.of ℤ := CommRingCat.ofHom (RingHom.fst ℤ ℚ)
    have e : φ ≫ ψ = 𝟙 _ := by ext n; simp [φ, ψ]
    have : Surjective (Spec.map ψ ≫ Spec.map φ) := by
      rw [← Spec.map_comp, e, Spec.map_id]; infer_instance
    exact Surjective.of_comp (Spec.map ψ) (Spec.map φ)
  · rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    change RingHom.Flat (algebraMap ℤ (ℤ × ℚ))
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  · apply not_isOpen_singleton_bot_int
    have h := hopen _ (PrimeSpectrum.basicOpen ((0, 1) : ℤ × ℚ)).isOpen
    have e : (Spec.map φ) ''
        (PrimeSpectrum.basicOpen ((0, 1) : ℤ × ℚ) : Set (PrimeSpectrum (ℤ × ℚ))) =
          ({⊥} : Set (PrimeSpectrum ℤ)) := by
      ext P
      simp only [Set.mem_image, SetLike.mem_coe, Set.mem_singleton_iff]
      constructor
      · rintro ⟨q, hq, rfl⟩
        rw [PrimeSpectrum.mem_basicOpen] at hq
        apply PrimeSpectrum.ext
        ext n
        simp only [Spec.map_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
          PrimeSpectrum.asIdeal_bot, Ideal.mem_bot]
        refine ⟨fun hn ↦ by_contra fun hn0 ↦ hq ?_, fun hn ↦ by simp [hn]⟩
        have := q.asIdeal.mul_mem_left ((0, (n : ℚ)⁻¹) : ℤ × ℚ) hn
        convert this using 1
        ext <;> simp [φ, hn0]
      · rintro rfl
        refine ⟨⟨RingHom.ker (RingHom.snd ℤ ℚ), RingHom.ker_isPrime _⟩, ?_, ?_⟩
        · rw [PrimeSpectrum.mem_basicOpen]
          simp
        · apply PrimeSpectrum.ext
          ext n
          simp [Spec.map_apply, φ]
    rw [e] at h
    exact h

end Maps

end SGA.SGA1.ExposeVIII
