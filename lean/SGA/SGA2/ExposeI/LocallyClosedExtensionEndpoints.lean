/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.OuterOpenExtensionComposition

/-! # Single-witness endpoints of the arbitrary-coefficient sequence (17)

Both ends use the original locally closed extension functor on genuine
single support witnesses. The comparisons with the earlier composite
sequence are proved from actual open–closed and open–open composition.
The arrows retain the original open counit and closed unit.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI
variable {X : TopCat.{u}}

/-- Equal opens have their canonical actual subspace isomorphism. -/
def openExtensionEqSpaceIso {U V : Opens X} (h : U = V) :
    (Opens.toTopCat X).obj U ≅ (Opens.toTopCat X).obj V :=
  eqToIso (congrArg (Opens.toTopCat X).obj h)

/-- Transport of coefficients along equality of opens preserves the actual
extension functor. This is equality elimination, with no assumed witness comparison. -/
def openExtensionEqIso {U V : Opens X} (h : U = V) :
    Sheaf.pushforward AddCommGrpCat.{u} (openExtensionEqSpaceIso h).hom ⋙ iBang_open V ≅
      iBang_open U := by
  subst V
  exact Iso.refl _

/-- The open complement in the support is the inverse image of the complement
of the genuine closed part in the original neighbourhood. -/
theorem nestedDifferenceOpen_eq (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    T.compl = closedSupportOpenPart (X := (Opens.toTopCat X).obj W.V)
      W.ZV (nestedClosedPart W T).compl := by
  ext x
  change x ∉ (T : Set (W.ZV : Set W.V)) ↔
    x.val ∉ Subtype.val '' (T : Set (W.ZV : Set W.V))
  constructor
  · intro hx
    rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    exact hx (this ▸ hy)
  · intro hx hxt
    exact hx ⟨x, hxt, rfl⟩

/-- The difference is closed in the complement of the smaller closed support
inside the original open neighbourhood. -/
def nestedDifferenceNeighbourhoodWitness (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) : LocallyClosedIn ((Opens.toTopCat X).obj W.V) :=
  LocallyClosedIn.ofOpenClosed (nestedClosedPart W T).compl W.ZV

/-- A genuine single ambient witness for the open difference. -/
def nestedDifferenceExtensionWitness (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) : LocallyClosedIn X :=
  outerOpenExtensionWitness W.V (nestedDifferenceNeighbourhoodWitness W T)

/-- Original difference coefficients are transported only by the actual
homeomorphisms which flatten the nested inclusions. -/
def nestedDifferenceExtensionSpaceIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    (Opens.toTopCat (TopCat.of (W.ZV : Set W.V))).obj T.compl ≅
      TopCat.of ((nestedDifferenceExtensionWitness W T).ZV :
        Set (nestedDifferenceExtensionWitness W T).V) :=
  openExtensionEqSpaceIso (X := TopCat.of (W.ZV : Set W.V)) (nestedDifferenceOpen_eq W T) ≪≫
    openClosedExtensionSpaceIso (X := (Opens.toTopCat X).obj W.V)
      W.ZV (nestedClosedPart W T).compl ≪≫
    outerOpenExtensionSpaceIso W.V (nestedDifferenceNeighbourhoodWitness W T)

/-- **I.1, (13), the open difference:** actual extension along the single
witness is the original composite open extension followed by `i_!`. -/
def locallyClosedDifferenceExtensionCompIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    Sheaf.pushforward AddCommGrpCat.{u} (nestedDifferenceExtensionSpaceIso W T).hom ⋙
        iBang_locallyClosed (nestedDifferenceExtensionWitness W T) ≅
      iBang_open (X := TopCat.of (W.ZV : Set W.V)) T.compl ⋙ iBang_locallyClosed W :=
  isoWhiskerLeft
      (Sheaf.pushforward AddCommGrpCat.{u}
          (openExtensionEqSpaceIso (X := TopCat.of (W.ZV : Set W.V))
            (nestedDifferenceOpen_eq W T)).hom ⋙
        Sheaf.pushforward AddCommGrpCat.{u}
          (openClosedExtensionSpaceIso (X := (Opens.toTopCat X).obj W.V)
            W.ZV (nestedClosedPart W T).compl).hom)
      (outerOpenLocallyClosedExtensionCompIso W.V (nestedDifferenceNeighbourhoodWitness W T)) ≪≫
    isoWhiskerLeft
      (Sheaf.pushforward AddCommGrpCat.{u}
        (openExtensionEqSpaceIso (X := TopCat.of (W.ZV : Set W.V))
          (nestedDifferenceOpen_eq W T)).hom)
      (isoWhiskerRight
        (openClosedExtensionCompIso (X := (Opens.toTopCat X).obj W.V)
          W.ZV (nestedClosedPart W T).compl) (iBang_open W.V)) ≪≫
    isoWhiskerRight
      (openExtensionEqIso (X := TopCat.of (W.ZV : Set W.V)) (nestedDifferenceOpen_eq W T))
      (iBang_locallyClosed W)

/-- The new single witness has literally the required difference support. -/
theorem nestedDifferenceExtensionWitness_asSet (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    (nestedDifferenceExtensionWitness W T).asSet =
      W.asSet \ (nestedClosedSupportWitness W T).asSet := by
  rw [nestedDifferenceExtensionWitness, outerOpenExtensionWitness_asSet,
    nestedDifferenceNeighbourhoodWitness, LocallyClosedIn.ofOpenClosed_asSet]
  ext x
  constructor
  · rintro ⟨y, ⟨hyT, hyW⟩, rfl⟩
    refine ⟨⟨y, hyW, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzy⟩
    have : z = y := Subtype.ext hzy
    exact hyT (this ▸ hz)
  · rintro ⟨⟨y, hyW, rfl⟩, hyT⟩
    exact ⟨y, ⟨fun hy => hyT ⟨y, hy, rfl⟩, hyW⟩, rfl⟩

/-- The newly flattened witness is the same actual difference subset used
by the previous support/cohomology sequence. -/
theorem nestedDifferenceExtensionWitness_sameSet (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    (nestedDifferenceExtensionWitness W T).asSet = (nestedDifferenceSupportWitness W T).asSet :=
  (nestedDifferenceExtensionWitness_asSet W T).trans
    (nestedDifferenceSupportWitness_asSet W T).symm

/-- The actual single-witness left endpoint, for arbitrary coefficient sheaves. -/
def locallyClosedExtensionLeftIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))) :
    (iBang_locallyClosed (nestedDifferenceExtensionWitness W T)).obj
      ((Sheaf.pushforward AddCommGrpCat.{u} (nestedDifferenceExtensionSpaceIso W T).hom).obj
        (restrictToOpen G T.compl)) ≅ (locallyClosedExtensionSequence W T G).X₁ :=
  (locallyClosedDifferenceExtensionCompIso W T).app (restrictToOpen G T.compl)

/-- The actual single-witness right endpoint, using ordinary restriction of `G`
to the closed subset and only its canonical subspace transport. -/
def locallyClosedExtensionRightIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))) :
    (iBang_locallyClosed (nestedClosedSupportWitness W T)).obj
      ((Sheaf.pushforward AddCommGrpCat.{u} (nestedClosedExtensionSpaceIso W T).hom).obj
        ((Sheaf.pullback AddCommGrpCat.{u}
          (closedInclusion (X := TopCat.of (W.ZV : Set W.V)) T)).obj G)) ≅
      (locallyClosedExtensionSequence W T G).X₃ :=
  (locallyClosedClosedExtensionCompIso W T).app _

/-- The original counit and unit maps, expressed with genuine single-witness
extensions of the restricted arbitrary coefficient sheaves. -/
def locallyClosedSingleExtensionSequence (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk
    ((locallyClosedExtensionLeftIso W T G).hom ≫ (locallyClosedExtensionSequence W T G).f)
    ((locallyClosedExtensionSequence W T G).g ≫ (locallyClosedExtensionRightIso W T G).inv)
    (by simp [Category.assoc])

/-- Both original canonical arrows are preserved by the endpoint comparisons. -/
def locallyClosedSingleExtensionSequenceIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))) :
    locallyClosedSingleExtensionSequence W T G ≅ locallyClosedExtensionSequence W T G :=
  ShortComplex.isoMk (locallyClosedExtensionLeftIso W T G) (Iso.refl _)
    (locallyClosedExtensionRightIso W T G)
    (by simp [locallyClosedSingleExtensionSequence])
    (by simp [locallyClosedSingleExtensionSequence])

/-- **I.1, (17), arbitrary coefficients:** the short exact sequence has
actual single-witness locally closed extension functors at all three terms. -/
theorem locallyClosedSingleExtensionSequence_shortExact (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))) :
    (locallyClosedSingleExtensionSequence W T G).ShortExact :=
  ShortComplex.shortExact_of_iso (locallyClosedSingleExtensionSequenceIso W T G).symm
    (locallyClosedExtensionSequence_shortExact W T G)

/-- The left arrow is the actual original open counit, after the proved
single-witness comparison. -/
theorem locallyClosedSingleExtensionSequence_f (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))) :
    (locallyClosedSingleExtensionSequence W T G).f =
      (locallyClosedExtensionLeftIso W T G).hom ≫
        (iBang_locallyClosed W).map
          ((openExtensionByZeroAdjunction (X := TopCat.of (W.ZV : Set W.V))
            T.compl).counit.app G) := rfl

/-- The right arrow is the original ordinary closed pullback/direct-image
unit, after the proved single-witness comparison. -/
theorem locallyClosedSingleExtensionSequence_g (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))) :
    (locallyClosedSingleExtensionSequence W T G).g =
      (iBang_locallyClosed W).map
        ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (closedInclusion (X := TopCat.of (W.ZV : Set W.V)) T)).unit.app G) ≫
        (locallyClosedExtensionRightIso W T G).inv := rfl

/-- The single-witness sequence, naturally in arbitrary coefficients. -/
def locallyClosedSingleExtensionSequenceFunctor (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V)) ⥤
      ShortComplex (Sheaf AddCommGrpCat.{u} X) where
  obj G := locallyClosedSingleExtensionSequence W T G
  map {G H} f := (locallyClosedSingleExtensionSequenceIso W T G).hom ≫
    (locallyClosedExtensionSequenceFunctor W T).map f ≫
      (locallyClosedSingleExtensionSequenceIso W T H).inv
  map_id G := by
    rw [CategoryTheory.Functor.map_id]
    exact (congrArg (fun f => (locallyClosedSingleExtensionSequenceIso W T G).hom ≫ f)
      (Category.id_comp (locallyClosedSingleExtensionSequenceIso W T G).inv)).trans
        (locallyClosedSingleExtensionSequenceIso W T G).hom_inv_id
  map_comp f g := by simp [Category.assoc]

/-- The comparison of short exact sequences is itself natural in coefficients. -/
def locallyClosedSingleExtensionSequenceFunctorIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    locallyClosedSingleExtensionSequenceFunctor W T ≅ locallyClosedExtensionSequenceFunctor W T :=
  NatIso.ofComponents (locallyClosedSingleExtensionSequenceIso W T)
    (fun f => by simp [locallyClosedSingleExtensionSequenceFunctor, Category.assoc])

/-- The actual restriction, transport, and extension coefficient functor
on the difference support. -/
def locallyClosedDifferenceCoefficientFunctor (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V)) ⥤ Sheaf AddCommGrpCat.{u} X :=
  iShriek_open (X := TopCat.of (W.ZV : Set W.V)) T.compl ⋙
    Sheaf.pushforward AddCommGrpCat.{u} (nestedDifferenceExtensionSpaceIso W T).hom ⋙
      iBang_locallyClosed (nestedDifferenceExtensionWitness W T)

/-- The actual closed restriction, transport, and extension coefficient functor. -/
def locallyClosedClosedCoefficientFunctor (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V)) ⥤ Sheaf AddCommGrpCat.{u} X :=
  Sheaf.pullback AddCommGrpCat.{u} (closedInclusion (X := TopCat.of (W.ZV : Set W.V)) T) ⋙
    Sheaf.pushforward AddCommGrpCat.{u} (nestedClosedExtensionSpaceIso W T).hom ⋙
      iBang_locallyClosed (nestedClosedSupportWitness W T)

private theorem conjugate_coefficient_map {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (f : A ⟶ B) :
    e.hom.app A ≫ G.map f ≫ e.inv.app B = F.map f := by
  rw [← Category.assoc, ← e.hom.naturality]
  simp

private def differenceCoefficientIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    locallyClosedDifferenceCoefficientFunctor W T ≅
      iShriek_open (X := TopCat.of (W.ZV : Set W.V)) T.compl ⋙
        iBang_open (X := TopCat.of (W.ZV : Set W.V)) T.compl ⋙ iBang_locallyClosed W :=
  isoWhiskerLeft (iShriek_open (X := TopCat.of (W.ZV : Set W.V)) T.compl)
    (locallyClosedDifferenceExtensionCompIso W T)

private def closedCoefficientIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    locallyClosedClosedCoefficientFunctor W T ≅
      Sheaf.pullback AddCommGrpCat.{u} (closedInclusion (X := TopCat.of (W.ZV : Set W.V)) T) ⋙
        iBang_closed (X := TopCat.of (W.ZV : Set W.V)) T ⋙ iBang_locallyClosed W :=
  isoWhiskerLeft
    (Sheaf.pullback AddCommGrpCat.{u} (closedInclusion (X := TopCat.of (W.ZV : Set W.V)) T))
    (locallyClosedClosedExtensionCompIso W T)

/-- The coefficient map on the single-witness left endpoint is the literal
restriction, transport, and extension of the given sheaf morphism. -/
theorem locallyClosedSingleExtensionSequence_map_τ₁ (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    {G H : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))} (f : G ⟶ H) :
    ((locallyClosedSingleExtensionSequenceFunctor W T).map f).τ₁ =
      (locallyClosedDifferenceCoefficientFunctor W T).map f :=
  conjugate_coefficient_map (differenceCoefficientIso W T) f

/-- The middle coefficient map is the original `i_!` applied to the given morphism. -/
theorem locallyClosedSingleExtensionSequence_map_τ₂ (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    {G H : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))} (f : G ⟶ H) :
    ((locallyClosedSingleExtensionSequenceFunctor W T).map f).τ₂ =
      (iBang_locallyClosed W).map f := by
  change 𝟙 _ ≫ (iBang_locallyClosed W).map f ≫ 𝟙 _ = _
  simp

/-- The right coefficient map is the literal ordinary closed restriction,
subspace transport, and single-witness extension of the given morphism. -/
theorem locallyClosedSingleExtensionSequence_map_τ₃ (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    {G H : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))} (f : G ⟶ H) :
    ((locallyClosedSingleExtensionSequenceFunctor W T).map f).τ₃ =
      (locallyClosedClosedCoefficientFunctor W T).map f :=
  conjugate_coefficient_map (closedCoefficientIso W T) f

end SGA.SGA2.ExposeI
