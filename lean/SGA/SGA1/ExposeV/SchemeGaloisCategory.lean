/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeV.FundamentalGroup
import SGA.SGA1.ExposeI.NormalCoverings
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# SGA 1, Exposé V, §7: the Galois category of étale coverings of a scheme

For an arbitrary scheme `S` we verify the axioms of a Galois category for `FEt S` and its
fiber functors `FEt.fiber Ω s̄` at geometric points `s̄ : Spec Ω ⟶ S`, `Ω` separably closed:

* (G 2) sums: `FEt S` has finite coproducts (`FEt.coprodCofanIsColimit`, `FEt.empty`), and
  `F_{s̄}` preserves them;
* (G 3): a monomorphism is the inclusion of a direct summand
  (`FEt.monoInducesIsoOnDirectSummand`);
* (G 5): `F_{s̄}` preserves epimorphisms, since epimorphisms are surjective
  (`FEt.surjective_of_epi`) and surjections are surjective on geometric points;
* (G 6), V.3.7: over a connected base, `F_{s̄}` reflects isomorphisms
  (`FEt.fiber_reflectsIsomorphisms`).

(G 1) and (G 4) come from mathlib. The remaining axiom, quotients by finite groups, is the
class `FEt.HasQuotients S`, proved here for `Spec R` with `R` connected and for every scheme in
`SGA.SGA1.ExposeV.QuotientHasQuotients` (`FEt.hasQuotients`); under it, `FEt S` is a Galois
category for connected `S` (`FEt.galoisCategory`) and every `F_{s̄}` is a fiber functor.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeV

instance : IsZariskiLocalAtSource @Etale :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)

lemma etale_coprod_desc {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X) [Etale f] [Etale g] :
    Etale (coprod.desc f g) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (coprodOpenCover.{u, 0} U V)]
  rintro (⟨⟩ | ⟨⟩)
  · change Etale (coprod.inl ≫ coprod.desc f g)
    rw [coprod.inl_desc]
    infer_instance
  · change Etale (coprod.inr ≫ coprod.desc f g)
    rw [coprod.inr_desc]
    infer_instance

variable {S : Scheme.{u}}

/-- The sum of two étale coverings. -/
noncomputable def FEt.coprodObj (X Y : FEt S) : FEt S :=
  MorphismProperty.Over.mk ⊤ (coprod.desc (X.hom : X.left ⟶ S) (Y.hom : Y.left ⟶ S)) (by
    have : IsFinite (X.hom : X.left ⟶ S) := X.prop.1
    have : IsFinite (Y.hom : Y.left ⟶ S) := Y.prop.1
    have : Etale (X.hom : X.left ⟶ S) := X.prop.2
    have : Etale (Y.hom : Y.left ⟶ S) := Y.prop.2
    exact ⟨inferInstance, etale_coprod_desc _ _⟩)

/-- The sum of two étale coverings, as a binary cofan. -/
noncomputable def FEt.coprodCofan (X Y : FEt S) : BinaryCofan X Y :=
  BinaryCofan.mk (P := FEt.coprodObj X Y)
    (MorphismProperty.Over.homMk coprod.inl (coprod.inl_desc _ _))
    (MorphismProperty.Over.homMk coprod.inr (coprod.inr_desc _ _))

/-- The sum of two étale coverings is a coproduct in `FEt S`. -/
noncomputable def FEt.coprodCofanIsColimit (X Y : FEt S) : IsColimit (FEt.coprodCofan X Y) := by
  apply isColimitOfReflects (MorphismProperty.Over.forget _ ⊤ S ⋙ Over.forget S)
  refine (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm ?_
  exact coprodIsCoprod X.left Y.left

section Topology

variable {S : Scheme.{u}}

/-- The structure morphism of an étale covering. -/
abbrev FEt.toBase (X : FEt S) : X.left ⟶ S := X.hom

instance (X : FEt S) : IsFinite X.toBase := X.prop.1
instance (X : FEt S) : Etale X.toBase := X.prop.2

lemma FEt.isClosedMap (X : FEt S) : IsClosedMap X.toBase := X.toBase.isClosedMap

lemma FEt.isOpenMap (X : FEt S) : IsOpenMap X.toBase := X.toBase.isOpenMap

/-- The image of an étale covering is open and closed; over a connected base a nonempty
covering is surjective. -/
lemma FEt.range_eq_univ [ConnectedSpace S] (X : FEt S) [Nonempty X.left] :
    Set.range X.toBase = Set.univ :=
  IsClopen.eq_univ ⟨(FEt.isClosedMap X).isClosed_range, (FEt.isOpenMap X).isOpen_range⟩
    (Set.range_nonempty _)

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- Over a connected base, an étale covering without geometric points over a given geometric
point is empty. -/
theorem FEt.isEmpty_of_isEmpty_fiber [ConnectedSpace S] (s : Spec (CommRingCat.of Ω) ⟶ S)
    (X : FEt S) (h : IsEmpty ((FEt.fiber Ω s).obj X)) : IsEmpty X.left := by
  by_contra hne
  rw [not_isEmpty_iff] at hne
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
  obtain ⟨x, hx⟩ : s pt ∈ Set.range X.toBase := by
    rw [FEt.range_eq_univ X]
    trivial
  let P := (FEt.pullback s).obj X
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x pt hx
  let E := specEquivalence (CommRingCat.of Ω)
  let A := (E.inverse.obj P).unop
  let i : Spec (CommRingCat.of A) ≅ P.left :=
    (MorphismProperty.Over.forget _ ⊤ _ ⋙ Over.forget _).mapIso (E.counitIso.app P)
  have : Nonempty (PrimeSpectrum A) := ⟨i.inv z⟩
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp this
  obtain ⟨y⟩ := nonempty_algHom_of_nontrivial (R := Ω) (A := A) Ω
  exact h.false y

/-- The restriction of an étale covering to an open and closed subset. -/
noncomputable def FEt.restrict (X : FEt S) (U : X.left.Opens) (hU : IsClosed (U : Set X.left)) :
    FEt S :=
  MorphismProperty.Over.mk ⊤ (U.ι ≫ X.toBase) (by
    have : IsClosedImmersion U.ι :=
      IsClosedImmersion.of_isPreimmersion _ (by simpa using hU)
    exact ⟨inferInstance, inferInstance⟩)

/-- The inclusion of the restriction of an étale covering to an open and closed subset. -/
noncomputable def FEt.restrictι (X : FEt S) (U : X.left.Opens) (hU : IsClosed (U : Set X.left)) :
    FEt.restrict X U hU ⟶ X :=
  MorphismProperty.Over.homMk U.ι rfl

/-- The underlying map of a morphism of étale coverings is finite and étale. -/
instance (X Y : FEt S) (f : X ⟶ Y) : IsFinite f.left := by
  have : f.left ≫ Y.toBase = X.toBase := MorphismProperty.Over.w f
  have : IsFinite (f.left ≫ Y.toBase) := by rw [this]; infer_instance
  exact IsFinite.of_comp f.left Y.toBase

instance (X Y : FEt S) (f : X ⟶ Y) : Etale f.left := by
  have : f.left ≫ Y.toBase = X.toBase := MorphismProperty.Over.w f
  have : Etale (f.left ≫ Y.toBase) := by rw [this]; infer_instance
  exact Etale.of_comp f.left Y.toBase

end Topology

section FiberPoints

variable {S : Scheme.{u}} (Ω : Type u) [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)

/-- The fiber `F_s(X)` is the set of geometric points of `X` over `s`. -/
noncomputable def FEt.fiberEquiv (X : FEt S) :
    (FEt.fiber Ω s).obj X ≃ (Over.mk s ⟶ (MorphismProperty.Over.forget _ ⊤ S).obj X) :=
  ((FEt.fiberInclIso Ω s).app X).toEquiv

lemma FEt.fiberEquiv_w {X : FEt S} (x : (FEt.fiber Ω s).obj X) :
    (FEt.fiberEquiv Ω s X x).left ≫ X.toBase = s :=
  Over.w (FEt.fiberEquiv Ω s X x)

lemma geometricPoints_map_apply {W : Scheme.{u}} (t : W ⟶ S) {X Y : FEt S} (f : X ⟶ Y)
    (a : (geometricPoints t).obj X) :
    (geometricPoints t).map f a = a ≫ (MorphismProperty.Over.forget _ ⊤ S).map f :=
  rfl

variable [IsSepClosed Ω]

/-- Over a connected base, an étale covering without geometric points over `s̄` is empty. -/
theorem FEt.isEmpty_of_isEmpty_geometricPoints [ConnectedSpace S] (X : FEt S)
    (h : IsEmpty ((geometricPoints s).obj X)) : IsEmpty X.left :=
  FEt.isEmpty_of_isEmpty_fiber Ω s X ((FEt.fiberEquiv Ω s X).isEmpty_congr.mpr h)

/-- V.3.7, surjectivity part: over a connected base, a morphism of étale coverings which is
surjective on geometric points over `s̄` is surjective. -/
theorem FEt.surjective_of_surjective_geometricPoints [ConnectedSpace S] {X Y : FEt S}
    (f : X ⟶ Y) (h : Function.Surjective ((geometricPoints s).map f)) :
    Surjective f.left := by
  let V : Y.left.Opens := ⟨(Set.range f.left)ᶜ, f.left.isClosedMap.isClosed_range.isOpen_compl⟩
  have hV : IsClosed (V : Set Y.left) := f.left.isOpenMap.isOpen_range.isClosed_compl
  have hW : IsEmpty (FEt.restrict Y V hV).left := by
    refine FEt.isEmpty_of_isEmpty_geometricPoints Ω s _ ⟨fun w ↦ ?_⟩
    obtain ⟨x, hx⟩ := h ((geometricPoints s).map (FEt.restrictι Y V hV) w)
    obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
    have h₁ : (w.left ≫ V.ι) pt ∈ (V : Set Y.left) := by
      rw [← Scheme.Opens.range_ι V]
      exact ⟨w.left pt, rfl⟩
    have h₂ : (x.left ≫ f.left) pt ∈ Set.range f.left := ⟨_, rfl⟩
    have h₃ : x.left ≫ f.left = w.left ≫ V.ι := congr_arg (fun a ↦ Over.Hom.left a) hx
    rw [h₃] at h₂
    exact h₁ h₂
  refine ⟨fun y ↦ ?_⟩
  by_contra hy
  exact hW.false (⟨y, hy⟩ : V)

/-- V.3.7, injectivity part: over a connected base, a morphism of étale coverings which is
injective on geometric points over `s̄` is a monomorphism of schemes. -/
theorem FEt.mono_of_injective_geometricPoints [ConnectedSpace S] {X Y : FEt S}
    (f : X ⟶ Y) (h : Function.Injective ((geometricPoints s).map f)) :
    Mono f.left := by
  let g := f.left
  have hg : g ≫ Y.toBase = X.toBase := MorphismProperty.Over.w f
  let Δ := pullback.diagonal g
  let Q : FEt S := MorphismProperty.Over.mk ⊤ (pullback.fst g g ≫ X.toBase)
    ⟨inferInstance, inferInstance⟩
  let V : Q.left.Opens := ⟨(Set.range Δ)ᶜ, Δ.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hV : IsClosed (V : Set Q.left) := Δ.isOpenEmbedding.isOpen_range.isClosed_compl
  have hW : IsEmpty (FEt.restrict Q V hV).left := by
    refine FEt.isEmpty_of_isEmpty_geometricPoints Ω s _ ⟨fun w ↦ ?_⟩
    let w' : Over.mk s ⟶ (MorphismProperty.Over.forget _ ⊤ S).obj (FEt.restrict Q V hV) := w
    let k : Spec (CommRingCat.of Ω) ⟶ Limits.pullback g g := w'.left ≫ V.ι
    have hw : k ≫ pullback.fst g g ≫ X.toBase = s := (Category.assoc _ _ _).symm.trans (Over.w w')
    let a : (geometricPoints s).obj X :=
      Over.homMk (k ≫ pullback.fst g g) (by
        change (k ≫ pullback.fst g g) ≫ X.toBase = s
        rw [Category.assoc]
        exact hw)
    let b : (geometricPoints s).obj X :=
      Over.homMk (k ≫ pullback.snd g g) (by
        change (k ≫ pullback.snd g g) ≫ X.toBase = s
        rw [← hg, Category.assoc, ← pullback.condition_assoc, hg]
        exact hw)
    have hab : a = b := h (by
      apply Over.OverMorphism.ext
      change (k ≫ pullback.fst g g) ≫ g = (k ≫ pullback.snd g g) ≫ g
      rw [Category.assoc, Category.assoc, pullback.condition])
    have hab' : k ≫ pullback.fst g g = k ≫ pullback.snd g g :=
      congr_arg (fun c ↦ Over.Hom.left c) hab
    have hΔ : k = (k ≫ pullback.fst g g) ≫ Δ := by
      apply pullback.hom_ext
      · simp [Δ]
      · simp [Δ, hab']
    obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
    have h₁ : k pt ∈ (V : Set Q.left) := by
      rw [← Scheme.Opens.range_ι V]
      exact ⟨w'.left pt, rfl⟩
    apply h₁
    rw [hΔ]
    exact ⟨_, rfl⟩
  have : Surjective Δ := ⟨fun z ↦ by
    by_contra hz
    exact hW.false (⟨z, hz⟩ : V)⟩
  have : IsIso Δ := (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, this⟩
  exact (pullback.isIso_diagonal_iff g).mp this

/-- V.3.7: over a connected base, a morphism of étale coverings inducing a bijection on the
geometric points over one geometric point is an isomorphism. -/
theorem FEt.isIso_of_bijective_geometricPoints [ConnectedSpace S] {X Y : FEt S} (f : X ⟶ Y)
    (h : Function.Bijective ((geometricPoints s).map f)) : IsIso f := by
  have := FEt.mono_of_injective_geometricPoints Ω s f h.1
  have := FEt.surjective_of_surjective_geometricPoints Ω s f h.2
  have : IsIso f.left := Flat.isIso_of_surjective_of_mono f.left
  have : IsIso ((MorphismProperty.Over.forget _ ⊤ S ⋙ Over.forget S).map f) := this
  exact isIso_of_reflects_iso f (MorphismProperty.Over.forget _ ⊤ S ⋙ Over.forget S)

/-- (G 6) for étale coverings of a connected scheme: the fiber functor reflects
isomorphisms. -/
lemma FEt.fiber_reflectsIsomorphisms [ConnectedSpace S] :
    (FEt.fiber Ω s).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    have : IsIso ((FEt.fiber Ω s ⋙ FintypeCat.incl).map f) :=
      inferInstanceAs (IsIso (FintypeCat.incl.map ((FEt.fiber Ω s).map f)))
    have : IsIso ((geometricPoints s).map f) :=
      (NatIso.isIso_map_iff (FEt.fiberInclIso Ω s) f).mp this
    exact FEt.isIso_of_bijective_geometricPoints Ω s f
      ((isIso_iff_bijective _).mp this)

end FiberPoints

section DirectSummand

variable {S : Scheme.{u}}

instance :
    (MorphismProperty.Over.forget finiteEtaleHom ⊤ S ⋙ Over.forget S).PreservesMonomorphisms :=
  inferInstance

/-- V.3.5, V.3.6 (G 3) for étale coverings of any scheme: a monomorphism of étale coverings is
the inclusion of a direct summand (an open and closed subscheme). -/
theorem FEt.monoInducesIsoOnDirectSummand {X Y : FEt S} (i : X ⟶ Y) [Mono i] :
    ∃ (Z : FEt S) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  have : Mono i.left := inferInstanceAs
    (Mono ((MorphismProperty.Over.forget finiteEtaleHom ⊤ S ⋙ Over.forget S).map i))
  have : IsOpenImmersion i.left := IsOpenImmersion.of_flat_of_mono i.left
  let V : Y.left.Opens := ⟨(Set.range i.left)ᶜ, i.left.isClosedMap.isClosed_range.isOpen_compl⟩
  have hV : IsClosed (V : Set Y.left) := i.left.isOpenMap.isOpen_range.isClosed_compl
  refine ⟨FEt.restrict Y V hV, FEt.restrictι Y V hV, ⟨?_⟩⟩
  apply isColimitOfReflects (MorphismProperty.Over.forget _ ⊤ S ⋙ Over.forget S)
  refine (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm ?_
  refine (AlgebraicGeometry.nonempty_isColimit_binaryCofanMk_of_isCompl i.left V.ι ?_).some
  rw [Scheme.Opens.opensRange_ι]
  constructor
  · rw [disjoint_iff]
    ext y
    simp [V, Scheme.Hom.opensRange]
  · rw [codisjoint_iff]
    ext y
    simp [V, Scheme.Hom.opensRange]

end DirectSummand

section Coproducts

variable {S : Scheme.{u}}

/-- The empty étale covering. -/
noncomputable def FEt.empty (S : Scheme.{u}) : FEt S :=
  MorphismProperty.Over.mk ⊤ (Scheme.emptyTo S) ⟨inferInstance, inferInstance⟩

/-- The empty covering is initial. -/
noncomputable def FEt.emptyIsInitial : IsInitial (FEt.empty S) :=
  IsInitial.ofUniqueHom
    (fun X ↦ MorphismProperty.Over.homMk (Scheme.emptyTo X.left)
      (AlgebraicGeometry.emptyIsInitial.hom_ext _ _))
    (fun X f ↦ MorphismProperty.Over.Hom.ext (by
      have h : ∀ g h : (∅ : Scheme.{u}) ⟶ X.left, g = h := fun g h ↦
        AlgebraicGeometry.emptyIsInitial.hom_ext g h
      exact h _ _))

instance : HasInitial (FEt S) := FEt.emptyIsInitial.hasInitial

instance (X Y : FEt S) : HasColimit (pair X Y) := ⟨⟨⟨_, FEt.coprodCofanIsColimit X Y⟩⟩⟩

instance : HasBinaryCoproducts (FEt S) := hasBinaryCoproducts_of_hasColimit_pair _

/-- V.7 (G 2), sums: the category of étale coverings of a scheme has finite coproducts. -/
instance : HasFiniteCoproducts (FEt S) := hasFiniteCoproducts_of_has_binary_and_initial

variable (Ω : Type u) [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)

lemma FEt.isEmpty_geometricPoints_empty : IsEmpty ((geometricPoints s).obj (FEt.empty S)) := by
  refine ⟨fun a ↦ ?_⟩
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
  let a' : Over.mk s ⟶ (MorphismProperty.Over.forget _ ⊤ S).obj (FEt.empty S) := a
  exact (a'.left pt : (∅ : Scheme.{u})).elim

instance : PreservesColimit (Functor.empty.{0} (FEt S)) (geometricPoints s) := by
  refine preservesColimit_of_preserves_colimit_cocone FEt.emptyIsInitial ?_
  refine (isColimitMapCoconeEmptyCoconeEquiv (geometricPoints s) _).symm ?_
  have := FEt.isEmpty_geometricPoints_empty Ω s
  exact ((Types.initial_iff_empty _).mpr this).some

instance (X Y : FEt S) : PreservesColimit (pair X Y) (geometricPoints s) := by
  refine preservesColimit_of_preserves_colimit_cocone (FEt.coprodCofanIsColimit X Y) ?_
  refine (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm ?_
  let T := FEt.coprodObj X Y
  refine ((Types.binaryCofan_isColimit_iff _).mpr ⟨?_, ?_, ⟨?_, ?_⟩⟩).some
  · intro a b hab
    let a' : Over.mk s ⟶ (MorphismProperty.Over.forget _ ⊤ S).obj X := a
    let b' : Over.mk s ⟶ (MorphismProperty.Over.forget _ ⊤ S).obj X := b
    have : a'.left ≫ coprod.inl = b'.left ≫ coprod.inl :=
      congr_arg (fun c : Over.mk s ⟶ (MorphismProperty.Over.forget _ ⊤ S).obj T ↦ c.left) hab
    exact Over.OverMorphism.ext ((cancel_mono _).mp this)
  · intro a b hab
    let a' : Over.mk s ⟶ (MorphismProperty.Over.forget _ ⊤ S).obj Y := a
    let b' : Over.mk s ⟶ (MorphismProperty.Over.forget _ ⊤ S).obj Y := b
    have : a'.left ≫ coprod.inr = b'.left ≫ coprod.inr :=
      congr_arg (fun c : Over.mk s ⟶ (MorphismProperty.Over.forget _ ⊤ S).obj T ↦ c.left) hab
    exact Over.OverMorphism.ext ((cancel_mono _).mp this)
  · rw [Set.disjoint_iff]
    rintro c ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
    let a' : Over.mk s ⟶ (MorphismProperty.Over.forget _ ⊤ S).obj X := a
    let b' : Over.mk s ⟶ (MorphismProperty.Over.forget _ ⊤ S).obj Y := b
    have : b'.left ≫ coprod.inr = a'.left ≫ coprod.inl :=
      congr_arg (fun c : Over.mk s ⟶ (MorphismProperty.Over.forget _ ⊤ S).obj T ↦ c.left) hb
    have h := congr_arg (fun g ↦ g pt) this
    simp only [Scheme.Hom.comp_apply] at h
    exact AlgebraicGeometry.inr_ne_inl _ _ _ _ h
  · refine codisjoint_iff.mpr (Set.eq_univ_of_forall fun c ↦ ?_)
    obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
    let c' : Over.mk s ⟶ (MorphismProperty.Over.forget _ ⊤ S).obj T := c
    let c'' : Spec (CommRingCat.of Ω) ⟶ X.left ⨿ Y.left := c'.left
    have hc' : c'' ≫ coprod.desc X.toBase Y.toBase = s := Over.w c'
    have hsub : ∀ x : Spec (CommRingCat.of Ω), x = pt := fun x ↦ Subsingleton.elim x pt
    have hc : c'' pt ∈ Set.range (coprod.inl : X.left ⟶ X.left ⨿ Y.left) ∪
        Set.range (coprod.inr : Y.left ⟶ X.left ⨿ Y.left) := by
      exact Set.eq_univ_iff_forall.mp (isCompl_range_inl_inr X.left Y.left).sup_eq_top (c'' pt)
    rcases hc with h | h
    · have H : Set.range c'' ⊆ Set.range (coprod.inl : X.left ⟶ X.left ⨿ Y.left) := by
        rintro _ ⟨x, rfl⟩; rwa [hsub x]
      let l := IsOpenImmersion.lift (coprod.inl : X.left ⟶ X.left ⨿ Y.left) c'' H
      have hl : l ≫ coprod.inl = c'' := IsOpenImmersion.lift_fac _ _ _
      let a : (geometricPoints s).obj X := Over.homMk l (by
        change l ≫ X.toBase = s
        rw [← hc', ← hl, Category.assoc, coprod.inl_desc])
      left
      refine ⟨a, ?_⟩
      apply Over.OverMorphism.ext
      exact hl
    · have H : Set.range c'' ⊆ Set.range (coprod.inr : Y.left ⟶ X.left ⨿ Y.left) := by
        rintro _ ⟨x, rfl⟩; rwa [hsub x]
      let l := IsOpenImmersion.lift (coprod.inr : Y.left ⟶ X.left ⨿ Y.left) c'' H
      have hl : l ≫ coprod.inr = c'' := IsOpenImmersion.lift_fac _ _ _
      let a : (geometricPoints s).obj Y := Over.homMk l (by
        change l ≫ Y.toBase = s
        rw [← hc', ← hl, Category.assoc, coprod.inr_desc])
      right
      refine ⟨a, ?_⟩
      apply Over.OverMorphism.ext
      exact hl

end Coproducts


section Exactness

variable {S : Scheme.{u}} (Ω : Type u) [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)

instance : PreservesColimitsOfShape (Discrete WalkingPair) (geometricPoints s) where
  preservesColimit {K} := preservesColimit_of_iso_diagram _ (diagramIsoPair K).symm

instance : PreservesColimitsOfShape (Discrete.{0} PEmpty) (geometricPoints s) where
  preservesColimit {K} :=
    preservesColimit_of_iso_diagram _ (Functor.emptyExt (Functor.empty.{0} (FEt S)) K)

instance : PreservesFiniteCoproducts (geometricPoints s) :=
  ⟨fun n ↦ PreservesFiniteCoproducts.of_preserves_binary_and_initial _ (Fin n)⟩

/-- V.7 (G 5), sums: the fiber functor at a geometric point commutes with finite sums. -/
instance : PreservesFiniteCoproducts (FEt.fiber Ω s) := by
  refine ⟨fun n ↦ ?_⟩
  have : PreservesColimitsOfShape (Discrete (Fin n)) (FEt.fiber Ω s ⋙ FintypeCat.incl) :=
    preservesColimitsOfShape_of_natIso (FEt.fiberInclIso Ω s).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (FEt.fiber Ω s) FintypeCat.incl

end Exactness

section Epimorphisms

variable {S : Scheme.{u}}

/-- An étale covering is the sum of its restrictions to complementary open and closed
subsets. -/
noncomputable def FEt.restrictIsColimit (Y : FEt S) (U V : Y.left.Opens)
    (hU : IsClosed (U : Set Y.left)) (hV : IsClosed (V : Set Y.left)) (h : IsCompl U V) :
    IsColimit (BinaryCofan.mk (FEt.restrictι Y U hU) (FEt.restrictι Y V hV)) := by
  apply isColimitOfReflects (MorphismProperty.Over.forget _ ⊤ S ⋙ Over.forget S)
  refine (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm ?_
  refine (AlgebraicGeometry.nonempty_isColimit_binaryCofanMk_of_isCompl U.ι V.ι ?_).some
  simpa only [Scheme.Opens.opensRange_ι] using h

/-- V.7: an epimorphism of étale coverings is surjective. -/
theorem FEt.surjective_of_epi {X Y : FEt S} (f : X ⟶ Y) [Epi f] : Surjective f.left := by
  let U : Y.left.Opens := ⟨Set.range f.left, f.left.isOpenMap.isOpen_range⟩
  have hU : IsClosed (U : Set Y.left) := f.left.isClosedMap.isClosed_range
  let V : Y.left.Opens := ⟨(Set.range f.left)ᶜ, f.left.isClosedMap.isClosed_range.isOpen_compl⟩
  have hV : IsClosed (V : Set Y.left) := f.left.isOpenMap.isOpen_range.isClosed_compl
  have hUV : IsCompl U V := by
    constructor
    · rw [disjoint_iff]
      ext y
      simp [U, V]
    · rw [codisjoint_iff]
      ext y
      simp [U, V]
  let hc := FEt.restrictIsColimit Y U V hU hV hUV
  let c := FEt.coprodCofan Y Y
  obtain ⟨g₁, hg₁l, hg₁r⟩ := BinaryCofan.IsColimit.desc' hc (FEt.restrictι Y U hU ≫ c.inl)
    (FEt.restrictι Y V hV ≫ c.inl)
  obtain ⟨g₂, hg₂l, hg₂r⟩ := BinaryCofan.IsColimit.desc' hc (FEt.restrictι Y U hU ≫ c.inl)
    (FEt.restrictι Y V hV ≫ c.inr)
  simp only [BinaryCofan.mk_inl, BinaryCofan.mk_inr] at hg₁l hg₁r hg₂l hg₂r
  let l := IsOpenImmersion.lift U.ι f.left (by rw [Scheme.Opens.range_ι]; rfl)
  have hl : l ≫ U.ι = f.left := IsOpenImmersion.lift_fac _ _ _
  let f' : X ⟶ FEt.restrict Y U hU := MorphismProperty.Over.homMk l (by
    change l ≫ U.ι ≫ Y.toBase = X.toBase
    rw [reassoc_of% hl]
    exact MorphismProperty.Over.w f)
  have hf' : f' ≫ FEt.restrictι Y U hU = f := MorphismProperty.Over.Hom.ext hl
  have h₁ : f ≫ (g₁ : Y ⟶ c.pt) = f ≫ g₂ := by
    rw [← hf']
    exact (Category.assoc _ _ _).trans ((congr_arg (f' ≫ ·) (hg₁l.trans hg₂l.symm)).trans
      (Category.assoc _ _ _).symm)
  have h₂ : (g₁ : Y ⟶ c.pt) = g₂ := (cancel_epi f).mp h₁
  have h₃ : FEt.restrictι Y V hV ≫ c.inl = FEt.restrictι Y V hV ≫ c.inr :=
    hg₁r.symm.trans ((congr_arg (FEt.restrictι Y V hV ≫ ·) h₂).trans hg₂r)
  refine ⟨fun y ↦ ?_⟩
  by_contra hy
  have h₄ := congr_arg (fun φ ↦ φ.left (⟨y, hy⟩ : V)) h₃
  change (V.ι ≫ coprod.inl) _ = (V.ι ≫ coprod.inr) _ at h₄
  exact AlgebraicGeometry.inl_ne_inr _ _ _ _ h₄

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)

/-- A surjective morphism of étale coverings is surjective on geometric points. -/
theorem FEt.surjective_geometricPoints_of_surjective {X Y : FEt S} (f : X ⟶ Y)
    (hf : Surjective f.left) : Function.Surjective ((geometricPoints s).map f) := by
  intro y
  let y' : Spec (CommRingCat.of Ω) ⟶ Y.left := y.left
  have hy : y' ≫ Y.toBase = s := Over.w y
  let P : FEt (Spec (CommRingCat.of Ω)) :=
    MorphismProperty.Over.mk ⊤ (pullback.snd f.left y') ⟨inferInstance, inferInstance⟩
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
  obtain ⟨x, hx⟩ := hf.surj (y' pt)
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x pt hx
  have hne : ¬ IsEmpty ((geometricPoints (𝟙 (Spec (CommRingCat.of Ω)))).obj P) := fun h ↦
    (FEt.isEmpty_of_isEmpty_geometricPoints Ω (𝟙 _) P h).false z
  obtain ⟨a⟩ := not_isEmpty_iff.mp hne
  let a' : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶
    (MorphismProperty.Over.forget _ ⊤ _).obj P := a
  let σ : Spec (CommRingCat.of Ω) ⟶ Limits.pullback f.left y' := a'.left
  have hσ : σ ≫ pullback.snd f.left y' = 𝟙 _ := Over.w a'
  have hw : f.left ≫ Y.toBase = X.toBase := MorphismProperty.Over.w f
  have h₁ : (σ ≫ pullback.fst f.left y') ≫ f.left = y' := by
    rw [Category.assoc, pullback.condition, reassoc_of% hσ]
  have h₂ : (σ ≫ pullback.fst f.left y') ≫ X.toBase = s := by
    rw [← hw, ← Category.assoc, h₁, hy]
  exact ⟨Over.homMk (σ ≫ pullback.fst f.left y') h₂, Over.OverMorphism.ext h₁⟩

/-- V.7 (G 5), epimorphisms: the fiber functor at a geometric point sends epimorphisms of
étale coverings to surjections. -/
instance : (FEt.fiber Ω s).PreservesEpimorphisms where
  preserves {X Y} f _ := by
    have h : Epi ((geometricPoints s).map f) := (epi_iff_surjective _).mpr
      (FEt.surjective_geometricPoints_of_surjective Ω s f (FEt.surjective_of_epi f))
    have : Epi ((FEt.fiber Ω s ⋙ FintypeCat.incl).map f) := by
      rw [← NatIso.naturality_2 (FEt.fiberInclIso Ω s) f]
      infer_instance
    exact FintypeCat.incl.epi_of_epi_map this

instance : PreservesLimitsOfShape WalkingCospan (FEt.fiber Ω s) :=
  inferInstanceAs (PreservesLimitsOfShape _ (FEt.pullback s ⋙ geometricFiber _ _))

instance : PreservesLimitsOfShape (Discrete PEmpty.{1}) (FEt.fiber Ω s) :=
  inferInstanceAs (PreservesLimitsOfShape _ (FEt.pullback s ⋙ geometricFiber _ _))

end Epimorphisms


section GaloisCategory

/-- V.7, axiom (G 2) for quotients, for the étale coverings of a scheme `S`: `FEt S` has
quotients by finite groups, and the fiber functors at geometric points commute with them.
It holds for every scheme (`FEt.hasQuotients` in `SGA.SGA1.ExposeV.QuotientHasQuotients`, from
the quotient `X/G = Spec_S (f_* 𝒪_X)^G` of V.1 and its compatibility with base change); here it is
proved for `S = Spec R` with `R` connected (`FEt.hasQuotients_spec`). -/
class FEt.HasQuotients (S : Scheme.{u}) : Prop where
  hasColimitsOfShape (G : Type u) [Group G] [Finite G] : HasColimitsOfShape (SingleObj G) (FEt S)
  preservesColimitsOfShape (G : Type u) [Group G] [Finite G] (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) :
    PreservesColimitsOfShape (SingleObj G) (FEt.fiber Ω s)

/-- V.1, V.7: every scheme satisfies (G 2) for quotients of étale coverings by finite groups.
Proved in `SGA.SGA1.ExposeV.QuotientHasQuotients` (`FEt.hasQuotientsStatement`), from the quotient
`X/G` of a finite étale `S`-scheme and its compatibility with base change. -/
def FEt.HasQuotientsStatement : Prop := ∀ S : Scheme.{u}, FEt.HasQuotients S

/-- (G 2) for quotients holds for `Spec R`, `R` connected. -/
instance FEt.hasQuotients_spec (R : CommRingCat.{u}) [ConnectedSpace (PrimeSpectrum R)] :
    FEt.HasQuotients (Spec R) where
  hasColimitsOfShape G _ _ := PreGaloisCategory.hasQuotientsByFiniteGroups G
  preservesColimitsOfShape G _ _ _ _ _ _ := FiberFunctor.preservesQuotientsByFiniteGroups G

variable {S : Scheme.{u}} [FEt.HasQuotients S]

/-- V.7, (G 1)–(G 3) for the étale coverings of a scheme `S` satisfying (G 2) for
quotients. -/
instance FEt.preGaloisCategory : PreGaloisCategory (FEt S) where
  hasQuotientsByFiniteGroups G _ _ := FEt.HasQuotients.hasColimitsOfShape G
  monoInducesIsoOnDirectSummand i _ := FEt.monoInducesIsoOnDirectSummand i

variable [ConnectedSpace S] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ S)

/-- V.7, (G 4)–(G 6): over a connected base, the functor of geometric points over a
geometric point `s̄ : Spec Ω ⟶ S` (`Ω` separably closed) is a fiber functor. -/
instance FEt.fiber_fiberFunctor : FiberFunctor (FEt.fiber Ω s) where
  preservesQuotientsByFiniteGroups G _ _ :=
    FEt.HasQuotients.preservesColimitsOfShape G Ω s
  reflectsIsos := FEt.fiber_reflectsIsomorphisms Ω s

/-- V.7: the étale coverings of a connected scheme form a Galois category (given (G 2) for
quotients, which holds for every `S` by `FEt.hasQuotients` in
`SGA.SGA1.ExposeV.QuotientHasQuotients`). -/
instance FEt.galoisCategory : GaloisCategory (FEt S) where
  hasFiberFunctor := by
    obtain ⟨x⟩ : Nonempty S := inferInstance
    let φ : S.residueField x ⟶ CommRingCat.of (AlgebraicClosure (S.residueField x)) :=
      CommRingCat.ofHom (algebraMap (S.residueField x) (AlgebraicClosure (S.residueField x)))
    exact ⟨FEt.fiber _ (Spec.map φ ≫ S.fromSpecResidueField x), inferInstance⟩

open scoped FintypeCatDiscrete in
/-- V.7: over a connected base, the étale coverings are equivalent to the finite sets with a
continuous action of `π₁(S, s̄)`. -/
noncomputable def FEt.equivContActionOfHasQuotients :
    FEt S ≌ ContAction FintypeCat (etaleFundamentalGroup Ω s) :=
  (functorToContAction (FEt.fiber Ω s)).asEquivalence

end GaloisCategory

end SGA.SGA1.ExposeV
