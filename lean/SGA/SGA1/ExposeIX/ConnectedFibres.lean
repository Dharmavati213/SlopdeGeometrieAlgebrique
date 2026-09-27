/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.MorphismProperty
import SGA.SGA1.ExposeIX.Submersive
import SGA.SGA1.ExposeV.FundamentalGroupFunctoriality

/-!
# SGA 1, Exposé IX, §5: connected fibres and connected coverings

IX.5.6, first assertion (also in IX.3.4): if `g : S' ⟶ S` is universally submersive with
geometrically connected fibres and `S` is connected, then `S'` is connected. Consequently the
inverse image of a connected finite étale covering is connected (`preservesIsConnected_pullback`),
which by V.6.9 is the surjectivity of `π₁(S') → π₁(S)`. Universal homeomorphisms, for instance
finite radicial surjective morphisms, are a special case (remark after IX.5.3).

We also record the remark of V.7 that a finite étale covering is a connected object of the category
of finite étale coverings iff its source is connected (`isConnected_iff_connectedSpace`, from
Exposé V), and that universally closed surjective morphisms are universally submersive
(IX.2.2 a)). Universally
submersive morphisms are written `(topologically IsQuotientMap).universally`.
-/

universe u

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- The topological argument of IX.3.4 and IX.5.6: the source of a quotient map with connected
fibres onto a connected space is connected. -/
theorem connectedSpace_of_isQuotientMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace Y] {f : X → Y} (hf : Topology.IsQuotientMap f)
    (hfib : ∀ y, IsConnected (f ⁻¹' {y})) : ConnectedSpace X := by
  rw [connectedSpace_iff_univ]
  simpa using hf.isCoinducing.isConnected_preimage_of_isClosed hfib isClosed_univ isConnected_univ

variable {S S' : Scheme.{u}} (g : S' ⟶ S)

/-- The class `UniversallySubmersive` of IX.2.1 is `(topologically IsQuotientMap).universally`. -/
lemma universally_isQuotientMap_of_universallySubmersive [UniversallySubmersive g] :
    (topologically Topology.IsQuotientMap).universally g := by
  have h := (universallySubmersive_iff g).mp ‹_›
  rwa [submersive_eq_topologically] at h

/-- IX.5.6, first assertion (also IX.3.4): if `g : S' ⟶ S` is universally submersive with
geometrically connected fibres and `S` is connected, then `S'` is connected. -/
theorem connectedSpace_of_universally_isQuotientMap
    (hg : (topologically Topology.IsQuotientMap).universally g) [GeometricallyConnected g]
    [ConnectedSpace S] : ConnectedSpace S' :=
  connectedSpace_of_isQuotientMap (MorphismProperty.universally_le _ g hg)
    g.isConnected_preimage_singleton

/-- IX.5.6: under the same hypotheses, `X ×_S S'` is connected for every connected `S`-scheme
`X`; in particular `S'' = S' ×_S S'` is connected when `S'` is. -/
theorem connectedSpace_pullback
    (hg : (topologically Topology.IsQuotientMap).universally g) [GeometricallyConnected g]
    {X : Scheme.{u}} (f : X ⟶ S) [ConnectedSpace X] : ConnectedSpace ↥(pullback f g) :=
  connectedSpace_of_universally_isQuotientMap (pullback.fst f g)
    (MorphismProperty.pullback_fst f g hg)

set_option backward.isDefEq.respectTransparency.types false in
/-- A universally closed surjective morphism (for instance a proper surjective one) is universally
submersive (IX.2.2 a)). -/
lemma universally_isQuotientMap_of_universallyClosed [UniversallyClosed g] [Surjective g] :
    (topologically Topology.IsQuotientMap).universally g := fun _ _ _ _ f' H ↦ by
  have : UniversallyClosed f' := MorphismProperty.of_isPullback H.flip ‹UniversallyClosed g›
  have : Surjective f' := MorphismProperty.of_isPullback H.flip ‹Surjective g›
  exact f'.isClosedMap.isQuotientMap f'.continuous f'.surjective

set_option backward.isDefEq.respectTransparency.types false in
/-- A universally closed, universally injective (radicial) and surjective morphism, for instance a
finite radicial surjective one, is a universal homeomorphism. -/
lemma universally_isHomeomorph_of_universallyClosed [UniversallyClosed g] [UniversallyInjective g]
    [Surjective g] : (topologically IsHomeomorph).universally g := fun _ _ _ _ f' H ↦ by
  have : UniversallyClosed f' := MorphismProperty.of_isPullback H.flip ‹UniversallyClosed g›
  have : UniversallyInjective f' := MorphismProperty.of_isPullback H.flip ‹UniversallyInjective g›
  have : Surjective f' := MorphismProperty.of_isPullback H.flip ‹Surjective g›
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨f'.continuous, f'.isClosedMap, f'.injective, f'.surjective⟩

/-- A universal homeomorphism has geometrically connected fibres (its fibres over fields are
points). -/
theorem geometricallyConnected_of_universally_isHomeomorph
    (hg : (topologically IsHomeomorph).universally g) : GeometricallyConnected g := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have hs : IsHomeomorph snd := hg fst y snd h.flip
  exact hs.homeomorph.symm.surjective.connectedSpace hs.homeomorph.symm.continuous

/-- Finite étale morphisms are stable under base change (`inferInstance` does not find the
instance for the infimum). -/
instance isStableUnderBaseChange_isFinite_inf_etale :
    MorphismProperty.IsStableUnderBaseChange (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.inf

local notation "FEt" => (SGA.SGA1.ExposeV.finiteEtaleHom : MorphismProperty Scheme)

instance isMultiplicative_isFinite_inf_etale :
    MorphismProperty.IsMultiplicative (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.inf

instance hasOfPostcompProperty_isFinite_inf_etale :
    MorphismProperty.HasOfPostcompProperty (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u})
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) where
  of_postcomp {_ _ _} f g hg hfg := by
    have : IsFinite g := hg.1
    have : Etale g := hg.2
    exact ⟨MorphismProperty.of_postcomp (W' := @IsSeparated) _ f g inferInstance hfg.1,
      MorphismProperty.of_postcomp (W' := @Etale) _ f g hg.2 hfg.2⟩

section finiteEtale

variable {S : Scheme.{u}}

/-- The empty finite étale covering. -/
noncomputable def emptyCover (S : Scheme.{u}) : MorphismProperty.Over FEt ⊤ S :=
  MorphismProperty.Over.mk ⊤ (isInitialOfIsEmpty.to S : (∅ : Scheme.{u}) ⟶ S)
    ⟨inferInstance, inferInstance⟩

lemma isEmpty_left_of_isInitial {X : MorphismProperty.Over FEt ⊤ S} (h : IsInitial X) :
    IsEmpty X.left :=
  ⟨fun x ↦ (inferInstance : IsEmpty (∅ : Scheme.{u})).false ((h.to (emptyCover S)).left x)⟩

/-- A covering with empty source is initial. -/
noncomputable def isInitialOfIsEmptyLeft (X : MorphismProperty.Over FEt ⊤ S) [IsEmpty X.left] :
    IsInitial X :=
  IsInitial.ofUniqueHom
    (fun Y ↦ MorphismProperty.Over.homMk (isInitialOfIsEmpty.to Y.left)
      (isInitialOfIsEmpty.hom_ext _ _))
    (fun Y m ↦ by
      ext
      exact isInitialOfIsEmpty.hom_ext _ _)

lemma nonempty_left_iff_not_isInitial (X : MorphismProperty.Over FEt ⊤ S) :
    Nonempty X.left ↔ (IsInitial X → False) := by
  refine ⟨fun ⟨x⟩ h ↦ (isEmpty_left_of_isInitial h).false x, fun h ↦ ?_⟩
  by_contra hX
  rw [not_nonempty_iff] at hX
  exact h (isInitialOfIsEmptyLeft X)

/-- V.7: a finite étale covering whose source is connected is a connected object of the category
of finite étale coverings (`SGA.SGA1.ExposeV.FEt.isConnected_of_connectedSpace`). -/
lemma isConnected_of_connectedSpace (X : MorphismProperty.Over FEt ⊤ S) [ConnectedSpace X.left] :
    PreGaloisCategory.IsConnected X :=
  SGA.SGA1.ExposeV.FEt.isConnected_of_connectedSpace (S := S) X

/-- V.7: the source of a connected object of the category of finite étale coverings is
connected (`SGA.SGA1.ExposeV.FEt.connectedSpace_of_isConnected`). -/
lemma connectedSpace_of_isConnected (X : MorphismProperty.Over FEt ⊤ S)
    [h : PreGaloisCategory.IsConnected X] : ConnectedSpace X.left :=
  (SGA.SGA1.ExposeV.FEt.isConnected_iff_connectedSpace (S := S) X).mp h

/-- V.7: a finite étale covering is connected in the category of finite étale coverings if and
only if its source is connected. -/
theorem isConnected_iff_connectedSpace (X : MorphismProperty.Over FEt ⊤ S) :
    PreGaloisCategory.IsConnected X ↔ ConnectedSpace X.left :=
  ⟨fun _ ↦ connectedSpace_of_isConnected X, fun _ ↦ isConnected_of_connectedSpace X⟩

variable (g : S' ⟶ S)

/-- IX.5.6, surjectivity of `π₁(S') → π₁(S)` in categorical form: the inverse image of a connected
finite étale covering along a universally submersive morphism with geometrically connected fibres
is connected. -/
theorem connectedSpace_pullback_left
    (hg : (topologically Topology.IsQuotientMap).universally g) [GeometricallyConnected g]
    (X : MorphismProperty.Over FEt ⊤ S) [ConnectedSpace X.left] :
    ConnectedSpace ((MorphismProperty.Over.pullback FEt ⊤ g).obj X).left := by
  have : ConnectedSpace ((𝟭 Scheme).obj X.left) := ‹_›
  exact connectedSpace_pullback g hg X.hom

/-- IX.5.6: the inverse image functor along a universally submersive morphism with geometrically
connected fibres preserves connected objects. By V.6.9 this is the surjectivity of
`π₁(S') → π₁(S)`. -/
theorem preservesIsConnected_pullback
    (hg : (topologically Topology.IsQuotientMap).universally g) [GeometricallyConnected g] :
    PreGaloisCategory.PreservesIsConnected (MorphismProperty.Over.pullback FEt ⊤ g) where
  preserves {X} _ := by
    have := connectedSpace_of_isConnected X
    have := connectedSpace_pullback_left g hg X
    exact isConnected_of_connectedSpace _

/-- IX.5.6, surjectivity in categorical form, stated with the class `UniversallySubmersive`. -/
theorem preservesIsConnected_pullback_of_universallySubmersive [UniversallySubmersive g]
    [GeometricallyConnected g] :
    PreGaloisCategory.PreservesIsConnected (MorphismProperty.Over.pullback FEt ⊤ g) :=
  preservesIsConnected_pullback g (universally_isQuotientMap_of_universallySubmersive g)

/-- A universal homeomorphism is universally submersive. -/
lemma universally_isQuotientMap_of_universally_isHomeomorph
    (hg : (topologically IsHomeomorph).universally g) :
    (topologically Topology.IsQuotientMap).universally g :=
  MorphismProperty.universally_mono (fun _ _ _ h ↦ IsHomeomorph.isQuotientMap h) g hg

/-- The inverse image along a universal homeomorphism preserves connected finite étale
coverings (the surjectivity half of the topological invariance of `π₁`, remark after IX.5.3). -/
theorem preservesIsConnected_pullback_of_universally_isHomeomorph
    (hg : (topologically IsHomeomorph).universally g) :
    PreGaloisCategory.PreservesIsConnected (MorphismProperty.Over.pullback FEt ⊤ g) :=
  have := geometricallyConnected_of_universally_isHomeomorph g hg
  preservesIsConnected_pullback g (universally_isQuotientMap_of_universally_isHomeomorph g hg)

end finiteEtale

end SGA.SGA1.ExposeIX
