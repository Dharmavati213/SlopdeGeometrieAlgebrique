/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# SGA 1, Exposé IX, §2: submersive and universally submersive morphisms

A morphism of schemes is *submersive* (IX.2.1) if it is surjective and its target carries
the quotient topology; it is *universally submersive* if every base change is submersive.
Mathlib has no such notion, so both are defined here, as the topological property
`Topology.IsQuotientMap` of the underlying map and its universal version.

We prove the sorites following IX.2.1 (base change, composition, cancellation), the examples
IX.2.2 (surjective open or closed maps; surjective universally open or universally closed
morphisms, in particular proper surjective ones; faithfully flat quasi-compact morphisms),
the exactness IX.2.3 of `Ouv(S) → Ouv(S') ⇉ Ouv(S'')`, and the descent statements IX.2.4
(open and closed maps, universally open, universally closed, separated and proper morphisms
descend along universally submersive morphisms). For IX.2.6 (valuative criterion) the necessity
is proved and the sufficiency recorded as a statement; IX.2.5 (the criterion over a complete
noetherian local ring) is proved in `SGA.SGA1.ExposeIX.SubmersiveCompleteLocal`.
-/

universe u

open CategoryTheory Limits MorphismProperty Topology

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- IX.2.1: a morphism of schemes `f : X ⟶ Y` is *submersive* if it is surjective and `Y`
carries the quotient topology of `X`, i.e. a subset of `Y` whose preimage is open is open. -/
@[mk_iff]
class Submersive : Prop where
  isQuotientMap : IsQuotientMap f

/-- IX.2.1: a morphism is *universally submersive* if all its base changes are submersive. -/
@[mk_iff]
class UniversallySubmersive : Prop where
  universally_submersive : universally @Submersive f

lemma submersive_eq_topologically : @Submersive = topologically @IsQuotientMap := by
  ext X Y f
  exact submersive_iff f

lemma universallySubmersive_eq : @UniversallySubmersive = universally @Submersive := by
  ext X Y f
  exact universallySubmersive_iff f

lemma Scheme.Hom.isQuotientMap [Submersive f] : IsQuotientMap f :=
  Submersive.isQuotientMap

lemma coe_comp_eq_comp : ⇑(f ≫ g) = ⇑g ∘ ⇑f := by
  ext
  simp

instance (priority := 100) Submersive.surjective [Submersive f] : Surjective f :=
  ⟨(Scheme.Hom.isQuotientMap f).surjective⟩

instance (priority := 100) UniversallySubmersive.submersive [UniversallySubmersive f] :
    Submersive f :=
  universally_le _ _ UniversallySubmersive.universally_submersive

instance Submersive.respectsIso : RespectsIso @Submersive := by
  rw [submersive_eq_topologically]
  exact topologically_respectsIso _ (fun e ↦ e.isQuotientMap) (fun _ _ hf hg ↦ hg.comp hf)

instance Submersive.isStableUnderComposition : IsStableUnderComposition @Submersive := by
  rw [submersive_eq_topologically]
  exact topologically_isStableUnderComposition _ (fun _ _ hf hg ↦ hg.comp hf)

instance (priority := 100) Submersive.of_isIso [IsIso f] : Submersive f :=
  ⟨f.homeomorph.isQuotientMap⟩

instance Submersive.comp [Submersive f] [Submersive g] : Submersive (f ≫ g) :=
  comp_mem _ _ _ ‹_› ‹_›

/-- IX.2.1: if `f ≫ g` is submersive, so is `g`. -/
lemma Submersive.of_comp [Submersive (f ≫ g)] : Submersive g :=
  ⟨.of_comp f.continuous g.continuous (coe_comp_eq_comp f g ▸ Scheme.Hom.isQuotientMap (f ≫ g))⟩

instance UniversallySubmersive.respectsIso : RespectsIso @UniversallySubmersive :=
  universallySubmersive_eq ▸ universally_respectsIso _

/-- IX.2.1: universally submersive morphisms are stable under base change. -/
instance UniversallySubmersive.isStableUnderBaseChange :
    IsStableUnderBaseChange @UniversallySubmersive :=
  universallySubmersive_eq ▸ universally_isStableUnderBaseChange _

/-- IX.2.1: universally submersive morphisms are stable under composition. -/
instance UniversallySubmersive.isStableUnderComposition :
    IsStableUnderComposition @UniversallySubmersive := by
  rw [universallySubmersive_eq]
  exact IsStableUnderComposition.universally _

instance UniversallySubmersive.comp [UniversallySubmersive f] [UniversallySubmersive g] :
    UniversallySubmersive (f ≫ g) :=
  comp_mem _ _ _ ‹_› ‹_›

instance (priority := 100) UniversallySubmersive.of_isIso [IsIso f] : UniversallySubmersive f :=
  ⟨fun _ _ _ _ f' H ↦ have : IsIso f' := H.isIso_fst_of_isIso; inferInstance⟩

instance : IsMultiplicative @UniversallySubmersive where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance UniversallySubmersive.fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [UniversallySubmersive g] : UniversallySubmersive (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g ‹_›

set_option backward.isDefEq.respectTransparency.types false in
instance UniversallySubmersive.snd {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [UniversallySubmersive f] : UniversallySubmersive (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g ‹_›

/-- IX.2.1: if `f ≫ g` is universally submersive, so is `g`. -/
lemma UniversallySubmersive.of_comp [UniversallySubmersive (f ≫ g)] :
    UniversallySubmersive g := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have : Submersive (pullback.fst i₁ f ≫ f') :=
    UniversallySubmersive.universally_submersive _ _ _
      ((IsPullback.of_hasPullback i₁ f).paste_horiz H)
  exact Submersive.of_comp (pullback.fst i₁ f) f'

/-! ### IX.2.2: examples -/

/-- IX.2.2: a surjective open morphism is submersive. -/
lemma Submersive.of_isOpenMap [Surjective f] (hf : IsOpenMap f) : Submersive f :=
  ⟨hf.isQuotientMap f.continuous f.surjective⟩

/-- IX.2.2: a surjective closed morphism is submersive. -/
lemma Submersive.of_isClosedMap [Surjective f] (hf : IsClosedMap f) : Submersive f :=
  ⟨hf.isQuotientMap f.continuous f.surjective⟩

/-- IX.2.2: a surjective universally open morphism is universally submersive. -/
instance (priority := 100) UniversallySubmersive.of_universallyOpen [UniversallyOpen f]
    [Surjective f] : UniversallySubmersive f := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have : UniversallyOpen f' := MorphismProperty.of_isPullback H.flip ‹_›
  have : Surjective f' := MorphismProperty.of_isPullback H.flip ‹_›
  exact .of_isOpenMap f' f'.isOpenMap

/-- IX.2.2: a surjective universally closed morphism is universally submersive. -/
instance (priority := 100) UniversallySubmersive.of_universallyClosed [UniversallyClosed f]
    [Surjective f] : UniversallySubmersive f := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have : UniversallyClosed f' := MorphismProperty.of_isPullback H.flip ‹_›
  have : Surjective f' := MorphismProperty.of_isPullback H.flip ‹_›
  exact .of_isClosedMap f' f'.isClosedMap

/-- IX.2.2: a surjective proper morphism is universally submersive. -/
lemma UniversallySubmersive.of_isProper [IsProper f] [Surjective f] :
    UniversallySubmersive f :=
  inferInstance

/-- IX.2.2 (via VIII.4.3): a faithfully flat quasi-compact morphism is universally
submersive. -/
instance (priority := 100) UniversallySubmersive.of_flat [Flat f] [QuasiCompact f]
    [Surjective f] : UniversallySubmersive f := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have : Flat f' := MorphismProperty.of_isPullback H.flip ‹_›
  have : QuasiCompact f' := MorphismProperty.of_isPullback H.flip ‹_›
  have : Surjective f' := MorphismProperty.of_isPullback H.flip ‹_›
  exact ⟨Flat.isQuotientMap_of_surjective f'⟩

/-- A morphism with a section is submersive. -/
lemma Submersive.of_section {s : Y ⟶ X} (hs : s ≫ f = 𝟙 Y) : Submersive f :=
  ⟨.of_inverse s.continuous f.continuous fun y ↦ by
    rw [← Scheme.Hom.comp_apply, hs]; simp⟩

/-- A morphism with a section is universally submersive: its base changes have sections. -/
lemma UniversallySubmersive.of_section {s : Y ⟶ X} (hs : s ≫ f = 𝟙 Y) :
    UniversallySubmersive f := by
  constructor
  intro X' Y' i₁ i₂ f' H
  exact .of_section f' (s := H.lift (𝟙 Y') (i₂ ≫ s) (by simp [hs])) (H.lift_fst _ _ _)

/-! ### IX.2.3: open subsets and submersive morphisms -/

section Opens

variable {S' S : Scheme.{u}} (g : S' ⟶ S)

/-- IX.2.3, injectivity: for surjective `g`, an open subset of `S` is determined by its preimage
in `S'`. -/
lemma preimage_opens_injective [Surjective g] :
    Function.Injective fun U : S.Opens ↦ g ⁻¹ᵁ U := by
  intro U V h
  ext x
  obtain ⟨y, rfl⟩ := g.surjective x
  exact SetLike.ext_iff.mp h y

/-- IX.2.3, a subset `U'` of `S'` whose two preimages in `S' ×_S S'` agree is saturated: it is
the preimage of its image. This only uses that points of `S' ×_S S'` surject onto the
set-theoretic fibre product. -/
lemma preimage_image_eq_of_preimage_fst_eq_preimage_snd {U' : Set S'}
    (h : pullback.fst g g ⁻¹' U' = pullback.snd g g ⁻¹' U') : g ⁻¹' (g '' U') = U' := by
  refine subset_antisymm (fun y ⟨x, hx, hxy⟩ ↦ ?_) (Set.subset_preimage_image _ _)
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  have : z ∈ pullback.fst g g ⁻¹' U' := by simpa [hz₁]
  rw [h] at this
  simpa [hz₂] using this

/-- IX.2.3: if `g : S' ⟶ S` is submersive, an open subset `U'` of `S'` whose two preimages in
`S' ×_S S'` agree is the preimage of a unique open subset of `S`. -/
lemma exists_unique_opens_preimage_eq [Submersive g] (U' : S'.Opens)
    (h : pullback.fst g g ⁻¹ᵁ U' = pullback.snd g g ⁻¹ᵁ U') :
    ∃! U : S.Opens, g ⁻¹ᵁ U = U' := by
  have hsat := preimage_image_eq_of_preimage_fst_eq_preimage_snd g (U' := (U' : Set S'))
    (by simpa using congrArg (fun V : (pullback g g).Opens ↦ (V : Set ↥(pullback g g))) h)
  refine ⟨⟨g '' U', ?_⟩, ?_, fun V hV ↦ preimage_opens_injective g ?_⟩
  · rw [← (Scheme.Hom.isQuotientMap g).isOpen_preimage, hsat]
    exact U'.isOpen
  · exact SetLike.coe_injective hsat
  · exact hV.trans (SetLike.coe_injective hsat).symm

lemma preimage_fst_eq_preimage_snd (U : S.Opens) :
    pullback.fst g g ⁻¹ᵁ (g ⁻¹ᵁ U) = pullback.snd g g ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]

/-- IX.2.3: for a submersive morphism `g : S' ⟶ S`, the diagram of sets of open subsets
`Ouv(S) → Ouv(S') ⇉ Ouv(S' ×_S S')` is exact. -/
noncomputable def opensEquivOfSubmersive [Submersive g] :
    S.Opens ≃ {U' : S'.Opens // pullback.fst g g ⁻¹ᵁ U' = pullback.snd g g ⁻¹ᵁ U'} where
  toFun U := ⟨g ⁻¹ᵁ U, preimage_fst_eq_preimage_snd g U⟩
  invFun U' := (exists_unique_opens_preimage_eq g U'.1 U'.2).choose
  left_inv U := preimage_opens_injective g
    (exists_unique_opens_preimage_eq g _ (preimage_fst_eq_preimage_snd g U)).choose_spec.1
  right_inv U' := Subtype.ext (exists_unique_opens_preimage_eq g U'.1 U'.2).choose_spec.1

end Opens

/-! ### IX.2.4: descent of topological properties -/

section Descent

variable {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

lemma preimage_image_eq_image_preimage (h : IsPullback fst snd f g) (s : Set Y) :
    f ⁻¹' (g '' s) = fst '' (snd ⁻¹' s) :=
  (Scheme.image_preimage_eq_of_isPullback h.flip s).symm

/-- IX.2.4: along a submersive morphism, being an open map descends. -/
lemma isOpenMap_of_isPullback (h : IsPullback fst snd f g) [Submersive f]
    (hfst : IsOpenMap fst) : IsOpenMap g := by
  intro s hs
  rw [← (Scheme.Hom.isQuotientMap f).isOpen_preimage, preimage_image_eq_image_preimage h]
  exact hfst _ (hs.preimage snd.continuous)

/-- IX.2.4: along a submersive morphism, being a closed map descends. -/
lemma isClosedMap_of_isPullback (h : IsPullback fst snd f g) [Submersive f]
    (hfst : IsClosedMap fst) : IsClosedMap g := by
  intro s hs
  rw [← (Scheme.Hom.isQuotientMap f).isClosed_preimage, preimage_image_eq_image_preimage h]
  exact hfst _ (hs.preimage snd.continuous)

/-- IX.2.4: along a submersive morphism, having closed image descends. -/
lemma isClosed_range_of_isPullback (h : IsPullback fst snd f g) [Submersive f]
    (hfst : IsClosed (Set.range fst)) : IsClosed (Set.range g) := by
  rw [← (Scheme.Hom.isQuotientMap f).isClosed_preimage, ← Set.image_univ,
    preimage_image_eq_image_preimage h, Set.preimage_univ, Set.image_univ]
  exact hfst

instance : (topologically @IsOpenMap).DescendsAlong @Submersive where
  of_isPullback h hf hfst := have := hf; isOpenMap_of_isPullback h hfst

instance : (topologically @IsClosedMap).DescendsAlong @Submersive where
  of_isPullback h hf hfst := have := hf; isClosedMap_of_isPullback h hfst

/-- The property of having closed image, used to express separatedness through the
diagonal. -/
def hasClosedRange : MorphismProperty Scheme.{u} :=
  topologically fun f ↦ IsClosed (Set.range f)

instance : hasClosedRange.{u}.RespectsIso := by
  apply RespectsIso.mk
  · intro X Y Z e f (hf : IsClosed _)
    change IsClosed (Set.range ⇑(e.hom ≫ f))
    rwa [coe_comp_eq_comp, e.hom.surjective.range_comp]
  · intro X Y Z e f (hf : IsClosed _)
    change IsClosed (Set.range ⇑(f ≫ e.hom))
    rw [coe_comp_eq_comp, Set.range_comp]
    exact e.hom.isClosedEmbedding.isClosedMap _ hf

instance : hasClosedRange.{u}.DescendsAlong @Submersive where
  of_isPullback h hf hfst := have := hf; isClosed_range_of_isPullback h hfst

/-- IX.2.4: universally open morphisms descend along universally submersive morphisms. -/
instance universallyOpen_descendsAlong :
    DescendsAlong @UniversallyOpen @UniversallySubmersive := by
  apply DescendsAlong.mk'
  intro X Y Z f g _ hf hfst
  have : UniversallyOpen (pullback.fst f g) := hfst
  refine ⟨universally_mk' _ _ fun {T} t _ ↦ ?_⟩
  have : UniversallySubmersive f := hf
  exact isOpenMap_of_isPullback (isPullback_map_snd_snd f t g).flip
    (pullback.fst (pullback.fst f t) (pullback.fst f g)).isOpenMap

/-- IX.2.4: universally closed morphisms descend along universally submersive morphisms. -/
instance universallyClosed_descendsAlong :
    DescendsAlong @UniversallyClosed @UniversallySubmersive := by
  have := universallyClosed_respectsIso
  apply DescendsAlong.mk'
  intro X Y Z f g _ hf hfst
  have : UniversallyClosed (pullback.fst f g) := hfst
  refine ⟨universally_mk' _ _ fun {T} t _ ↦ ?_⟩
  have : UniversallySubmersive f := hf
  exact isClosedMap_of_isPullback (isPullback_map_snd_snd f t g).flip
    (pullback.fst (pullback.fst f t) (pullback.fst f g)).isClosedMap

lemma isSeparated_iff_isClosed_range_diagonal :
    IsSeparated g ↔ IsClosed (Set.range (pullback.diagonal g)) :=
  ⟨fun _ ↦ (pullback.diagonal g).isClosedEmbedding.isClosed_range,
    fun h ↦ ⟨IsClosedImmersion.of_isPreimmersion _ h⟩⟩

lemma isSeparated_eq_diagonal_hasClosedRange : @IsSeparated = diagonal hasClosedRange := by
  ext X Y g
  exact isSeparated_iff_isClosed_range_diagonal

/-- IX.2.4: separated morphisms descend along universally submersive morphisms. -/
instance isSeparated_descendsAlong :
    DescendsAlong @IsSeparated @UniversallySubmersive := by
  have : hasClosedRange.DescendsAlong @UniversallySubmersive :=
    DescendsAlong.of_le (P := hasClosedRange) (Q := @Submersive)
      fun _ _ f (_ : UniversallySubmersive f) ↦ (inferInstance : Submersive f)
  rw [isSeparated_eq_diagonal_hasClosedRange]
  exact instDescendsAlongDiagonalOfRespectsIsoOfIsStableUnderBaseChange _ _

/-- VIII.3.3 (used in IX.2.4 and IX.4.1): quasi-compactness descends along quasi-compact
surjective morphisms. -/
instance quasiCompact_descendsAlong :
    DescendsAlong @QuasiCompact (@Surjective ⊓ @QuasiCompact) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    obtain ⟨hf₁, hf₂⟩ := hf
    refine ⟨fun U hU hc ↦ ?_⟩
    have : g ⁻¹' U = snd '' (fst ⁻¹' (f ⁻¹' U)) := by
      rw [Scheme.image_preimage_eq_of_isPullback h, Set.image_preimage_eq U f.surjective]
    rw [this]
    exact (hfst.isCompact_preimage _ (hU.preimage f.continuous)
      (hf₂.isCompact_preimage U hU hc)).image snd.continuous

/-- IX.2.4: a morphism locally of finite type whose base change along a universally
submersive morphism is proper is proper. In SGA "proper" includes "of finite type", which is
why SGA also assumes the base change quasi-compact; mathlib's `IsProper` only asks for
"locally of finite type" (quasi-compactness follows from universal closedness), so that
hypothesis is not needed here. -/
lemma isProper_of_isPullback (h : IsPullback fst snd f g) [UniversallySubmersive f]
    [LocallyOfFiniteType g] (hfst : IsProper fst) : IsProper g where
  toIsSeparated := of_isPullback_of_descendsAlong h ‹_› hfst.toIsSeparated
  toUniversallyClosed := of_isPullback_of_descendsAlong h ‹_› hfst.toUniversallyClosed

/-- IX.2.4: for a universally submersive `f`, and `g` locally of finite type, `g` is proper
if and only if its base change is. -/
lemma isProper_iff_of_isPullback (h : IsPullback fst snd f g) [UniversallySubmersive f]
    [LocallyOfFiniteType g] : IsProper fst ↔ IsProper g :=
  ⟨isProper_of_isPullback h, fun hg ↦ MorphismProperty.of_isPullback h.flip hg⟩

end Descent

/-! ### IX.2.6: the valuative criterion -/

/-- The closed point of the spectrum of a local ring which is not a field is not open. -/
lemma not_isOpen_singleton_closedPoint (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    (hR : IsLocalRing.maximalIdeal R ≠ ⊥) :
    ¬ IsOpen ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)) := by
  intro h
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : η ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (bot_le (a := IsLocalRing.maximalIdeal R))
  have : η = IsLocalRing.closedPoint R := hη.mem_open h rfl
  exact hR (congrArg PrimeSpectrum.asIdeal this).symm

/-- IX.2.6, necessity: if `g : S' ⟶ S` is universally submersive, then for every `S`-scheme
`T = Spec R` with `R` a discrete valuation ring, the preimage in `S' ×_S T` of the closed point of
`T` is not open. (No hypothesis on `g` or `S` is needed for this direction.) -/
theorem not_isOpen_preimage_closedPoint {S' S : Scheme.{u}} (g : S' ⟶ S)
    [UniversallySubmersive g] (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (t : Spec (.of R) ⟶ S) :
    ¬ IsOpen (pullback.snd g t ⁻¹' {IsLocalRing.closedPoint R}) := by
  rw [(Scheme.Hom.isQuotientMap (pullback.snd g t)).isOpen_preimage]
  exact not_isOpen_singleton_closedPoint R (IsDiscreteValuationRing.not_a_field R)

/-- IX.2.6 (statement only, sufficiency): valuative criterion. A morphism of finite type
`g : S' ⟶ S` with `S` locally noetherian is universally submersive as soon as for every
`T = Spec R ⟶ S` with `R` a discrete valuation ring, the preimage in `S' ×_S T` of the closed
point of `T` is not open. The converse is `not_isOpen_preimage_closedPoint`. -/
def UniversallySubmersiveValuativeCriterionStatement : Prop :=
  ∀ (S' S : Scheme.{u}) (g : S' ⟶ S) [LocallyOfFiniteType g] [QuasiCompact g]
    [IsLocallyNoetherian S],
    (∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        (t : Spec (.of R) ⟶ S),
        ¬ IsOpen (pullback.snd g t ⁻¹' {IsLocalRing.closedPoint R})) →
      UniversallySubmersive g

/-- IX.2.6: granting the sufficiency statement, the valuative criterion as an equivalence. -/
theorem universallySubmersive_iff_forall_not_isOpen
    (H : UniversallySubmersiveValuativeCriterionStatement.{u}) {S' S : Scheme.{u}} (g : S' ⟶ S)
    [LocallyOfFiniteType g] [QuasiCompact g] [IsLocallyNoetherian S] :
    UniversallySubmersive g ↔
      ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        (t : Spec (.of R) ⟶ S),
        ¬ IsOpen (pullback.snd g t ⁻¹' {IsLocalRing.closedPoint R}) :=
  ⟨fun _ R _ _ _ t ↦ not_isOpen_preimage_closedPoint g R t, H S' S g⟩

end SGA.SGA1.ExposeIX
