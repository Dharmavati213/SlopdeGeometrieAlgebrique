/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.NestedSupportedSheafSequence

/-!
# I.1.9 for an arbitrary original locally closed support

The actual ambient functor of the original witness is retained. Proved
witness-independence comparisons transport the actual inclusion/restriction
sequence from the closed-hull presentation. Closed subsets may be given
directly in the literal support subspace, with no additional support data.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- The actual original supported sheaf agrees with its closed-hull presentation. -/
def locallyClosedSupportedSheafClosedHullIso (W : LocallyClosedIn X) :
    underlineGammaLocallyClosedFunctor (LocallyClosedIn.ofOpenClosed W.V W.closedHull) ≅
      underlineGammaLocallyClosedFunctor W :=
  underlineGammaLocallyClosedIndependenceIso
    ((LocallyClosedIn.ofOpenClosed_asSet W.V W.closedHull).trans W.inter_closedHull)

/-- Actual support inclusion for the original locally closed supported sheaves. -/
def locallyClosedNestedSheafInclusion (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    underlineGammaLocallyClosedFunctor (nestedClosedSupportWitness W T) ⟶
      underlineGammaLocallyClosedFunctor W :=
  (locallyClosedSupportedSheafClosedHullIso (nestedClosedSupportWitness W T)).inv ≫
    openClosedSupportedSheafInclusion (nestedSupportClosedHulls_le W T) W.V ≫
      (locallyClosedSupportedSheafClosedHullIso W).hom

/-- Actual restriction to the original locally closed difference. -/
def locallyClosedNestedSheafRestriction (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    underlineGammaLocallyClosedFunctor W ⟶
      underlineGammaLocallyClosedFunctor (nestedDifferenceSupportWitness W T) :=
  (locallyClosedSupportedSheafClosedHullIso W).inv ≫
    openClosedSupportedSheafRestriction (nestedClosedSupportWitness W T).closedHull
      W.closedHull W.V

/-- The original nested supported-sheaf maps have zero composite. -/
theorem locallyClosedNestedSheaf_comp (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    locallyClosedNestedSheafInclusion W T ≫ locallyClosedNestedSheafRestriction W T = 0 := by
  simp only [locallyClosedNestedSheafInclusion, locallyClosedNestedSheafRestriction,
    Category.assoc, Iso.hom_inv_id_assoc, openClosedSupportedSheaf_comp, comp_zero]

/-- The actual general nested supported-sheaf functors form a short complex. -/
def locallyClosedNestedSheafFunctorSequence (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (locallyClosedNestedSheafInclusion W T)
    (locallyClosedNestedSheafRestriction W T) (locallyClosedNestedSheaf_comp W T)

/-- Genuine witness independence identifies the actual functor short complexes. -/
def locallyClosedNestedSheafFunctorSequenceIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    openClosedSupportedSheafFunctorSequence (nestedSupportClosedHulls_le W T) W.V ≅
      locallyClosedNestedSheafFunctorSequence W T :=
  ShortComplex.isoMk
    (locallyClosedSupportedSheafClosedHullIso (nestedClosedSupportWitness W T))
    (locallyClosedSupportedSheafClosedHullIso W) (Iso.refl _)
    (by simp [openClosedSupportedSheafFunctorSequence, locallyClosedNestedSheafFunctorSequence,
      locallyClosedNestedSheafInclusion])
    (by simp [openClosedSupportedSheafFunctorSequence, locallyClosedNestedSheafFunctorSequence,
      locallyClosedNestedSheafRestriction])

/-- The original general nested sequence on a coefficient sheaf. -/
def locallyClosedNestedSheafSequence (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  (locallyClosedNestedSheafFunctorSequence W T).map
    ((evaluation (Sheaf AddCommGrpCat.{u} X) (Sheaf AddCommGrpCat.{u} X)).obj F)

/-- The objectwise comparison preserves both original sheaf maps. -/
def locallyClosedNestedSheafSequenceIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) (F : Sheaf AddCommGrpCat.{u} X) :
    openClosedSupportedSheafSequence (nestedSupportClosedHulls_le W T) W.V F ≅
      locallyClosedNestedSheafSequence W T F :=
  (((evaluation (Sheaf AddCommGrpCat.{u} X)
    (Sheaf AddCommGrpCat.{u} X)).obj F).mapShortComplex).mapIso
      (locallyClosedNestedSheafFunctorSequenceIso W T)

/-- **I.1.9:** exactness for the original arbitrary locally closed support. -/
theorem locallyClosedNestedSheafSequence_exact (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) (F : Sheaf AddCommGrpCat.{u} X) :
    (locallyClosedNestedSheafSequence W T F).Exact :=
  (ShortComplex.exact_iff_of_iso (locallyClosedNestedSheafSequenceIso W T F)).mp
    (openClosedSupportedSheafSequence_exact (nestedSupportClosedHulls_le W T) W.V F)

/-- The original sequence starts with a monomorphism, without flasqueness. -/
theorem locallyClosedNestedSheafInclusion_mono (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) (F : Sheaf AddCommGrpCat.{u} X) :
    Mono ((locallyClosedNestedSheafInclusion W T).app F) :=
  ((ShortComplex.exact_and_mono_f_iff_of_iso (locallyClosedNestedSheafSequenceIso W T F)).mp
    ⟨openClosedSupportedSheafSequence_exact (nestedSupportClosedHulls_le W T) W.V F,
      openClosedSupportedSheafInclusion_mono (nestedSupportClosedHulls_le W T) W.V F⟩).2

/-- **I.1.9, flasque surjectivity:** the actual original sequence is short exact. -/
theorem locallyClosedNestedSheafSequence_shortExact (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    (locallyClosedNestedSheafSequence W T F).ShortExact :=
  ShortComplex.shortExact_of_iso (locallyClosedNestedSheafSequenceIso W T F)
    (openClosedSupportedSheafSequence_shortExact (nestedSupportClosedHulls_le W T) W.V F)

/-- **I.1.9**, with a closed subset of the literal ambient support space. -/
theorem nestedClosedSubspaceSheafSequence_exact (W : LocallyClosedIn X)
    (T : Closeds W.asSet) (F : Sheaf AddCommGrpCat.{u} X) :
    (locallyClosedNestedSheafSequence W (nestedClosedSubspace W T) F).Exact :=
  locallyClosedNestedSheafSequence_exact W (nestedClosedSubspace W T) F

/-- **I.1.9**, including flasque surjectivity, for a literal closed subspace. -/
theorem nestedClosedSubspaceSheafSequence_shortExact (W : LocallyClosedIn X)
    (T : Closeds W.asSet) (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    (locallyClosedNestedSheafSequence W (nestedClosedSubspace W T) F).ShortExact :=
  locallyClosedNestedSheafSequence_shortExact W (nestedClosedSubspace W T) F

end SGA.SGA2.ExposeI
