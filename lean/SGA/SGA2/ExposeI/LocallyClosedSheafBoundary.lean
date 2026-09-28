/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.SupportedSheafStalkBoundary

/-!
# Boundary support for original locally closed supported sheaves

SGA 2, I.2.7 for locally closed supports: all degrees have literal stalk
support inside the closure, and positive degrees inside the boundary.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

private def intersectionWhiskerIso {U V : Opens X} (hUV : U ≤ V) :
    (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openIntersectionFunctor V).op ⋙
      (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openIntersectionFunctor U).op ≅
    (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openIntersectionFunctor U).op := by
  let e : (openIntersectionFunctor U).op ⋙ (openIntersectionFunctor V).op ≅
      (openIntersectionFunctor U).op := NatIso.ofComponents
    (fun A ↦ eqToIso (congrArg op (show V ⊓ (U ⊓ A.unop) = U ⊓ A.unop from
      inf_eq_right.mpr (inf_le_left.trans hUV)))) (fun _ ↦ Subsingleton.elim _ _)
  exact (whiskeringLeft _ _ AddCommGrpCat.{u}).mapIso e

/-- Within its open witness, a locally closed support has the same original
supported sheaf as its ambient closure. -/
def locallyClosedSupportedRestrictionIso (W : LocallyClosedIn X)
    (U : Opens X) (hU : U ≤ W.V) :
    underlineGammaLocallyClosedFunctor W ⋙ iShriek_open U ≅
      underlineGammaZFunctor W.closedHull ⋙ iShriek_open U := by
  let ff := ((fullyFaithfulSheafToPresheaf
    (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u}).comp
      (fullyFaithfulOpenPresheafPushforward U)).whiskeringRight
        (Sheaf AddCommGrpCat.{u} X)
  apply ff.preimageIso
  exact isoWhiskerLeft (underlineGammaLocallyClosedFunctor W)
      (openRestrictionSectionsFunctorIso U) ≪≫
    isoWhiskerRight (underlineGammaLocallyClosedPresheafFunctorIso W)
      ((whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openIntersectionFunctor U).op) ≪≫
    isoWhiskerRight
      (locallyClosedAmbientPresheafIso W W.closedHull W.closedSupportOnOpen_closedHull)
      ((whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openIntersectionFunctor U).op) ≪≫
    isoWhiskerLeft (gammaZSectionsPresheafFunctor W.closedHull) (intersectionWhiskerIso hU) ≪≫
    (isoWhiskerRight (underlineGammaZPresheafFunctorIso W.closedHull)
      ((whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openIntersectionFunctor U).op)).symm ≪≫
    (isoWhiskerLeft (underlineGammaZFunctor W.closedHull)
      (openRestrictionSectionsFunctorIso U)).symm

/-- The comparison within the witness persists in every original derived degree. -/
def derivedLocallyClosedSupportedRestrictionIso (W : LocallyClosedIn X)
    (U : Opens X) (hU : U ≤ W.V) (n : ℕ) :
    derivedUnderlineGammaLocallyClosed W n ⋙ iShriek_open U ≅
      derivedUnderlineGammaZ W.closedHull n ⋙ iShriek_open U := by
  letI := (openExtensionByZeroAdjunction U).isRightAdjoint
  letI : (iShriek_open U).PreservesHomology := inferInstance
  exact (rightDerivedPostcomposeIso (underlineGammaLocallyClosedFunctor W)
    (iShriek_open U) n).symm ≪≫
      rightDerivedFunctorIso (locallyClosedSupportedRestrictionIso W U hU) n ≪≫
        rightDerivedPostcomposeIso (underlineGammaZFunctor W.closedHull) (iShriek_open U) n

/-- Supported sections on an open disjoint from a closed support are zero. -/
theorem gammaZSections_eq_bot_of_le_compl (F : Sheaf AddCommGrpCat.{u} X)
    (Z : Closeds X) (U : Opens X) (hU : U ≤ Z.compl) : gammaZSections F Z U = ⊥ := by
  have hi : IsIso (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U)) :=
    ⟨⟨homOfLE (le_inf le_rfl hU), Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  have : IsIso (restrictToComplement F Z U) := by
    change IsIso (F.presheaf.map (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U)).op)
    infer_instance
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  change (restrictToComplement F Z U).hom x = 0 at hx
  exact ((AddCommGrpCat.mono_iff_injective (restrictToComplement F Z U)).mp inferInstance)
    (by simpa only [map_zero] using hx)

/-- The original locally closed supported sheaf is zero away from its closure. -/
theorem underlineGammaLocallyClosed_restrict_isZero_of_le_compl (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) (hU : U ≤ W.closedHull.compl) :
    IsZero (restrictToOpen ((underlineGammaLocallyClosedFunctor W).obj F) U) := by
  apply IsZero.of_iso _ ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).app _)
  apply IsZero.of_full_of_faithful_of_isZero
    (sheafToPresheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u})
  apply Functor.isZero
  intro A
  let B := U.isOpenEmbedding.functor.obj A.unop
  let e := (underlineGammaLocallyClosedSectionsEquiv W F B).trans
    (locallyClosedAmbientSectionsEquiv W W.closedHull W.closedSupportOnOpen_closedHull F B)
  change IsZero (((underlineGammaLocallyClosedFunctor W).obj F).presheaf.obj (op B))
  apply IsZero.of_iso (Y := AddCommGrpCat.of (gammaZSections F W.closedHull (W.V ⊓ B)))
    _ e.toAddCommGrpIso
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  have hB : W.V ⊓ B ≤ W.closedHull.compl := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx.2
    exact hU y.property
  rw [gammaZSections_eq_bot_of_le_compl F W.closedHull (W.V ⊓ B) hB]
  infer_instance

/-- All original derived locally closed supported sheaves vanish off the closure. -/
theorem derivedUnderlineGammaLocallyClosed_restrict_isZero_of_le_compl
    (W : LocallyClosedIn X) (F : Sheaf AddCommGrpCat.{u} X)
    (U : Opens X) (hU : U ≤ W.closedHull.compl) (n : ℕ) :
    IsZero (restrictToOpen ((derivedUnderlineGammaLocallyClosed W n).obj F) U) := by
  have := (openExtensionByZeroAdjunction U).isRightAdjoint
  have : (iShriek_open U).PreservesHomology := inferInstance
  have hz : IsZero
      (((underlineGammaLocallyClosedFunctor W ⋙ iShriek_open U).rightDerived n).obj F) := by
    apply IsZero.of_iso _ ((injectiveResolution F).isoRightDerivedObj
      (underlineGammaLocallyClosedFunctor W ⋙ iShriek_open U) n)
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact underlineGammaLocallyClosed_restrict_isZero_of_le_compl W _ U hU
  exact hz.of_iso ((rightDerivedPostcomposeIso (underlineGammaLocallyClosedFunctor W)
    (iShriek_open U) n).app F).symm

/-- Positive original derived sheaves vanish on every open inside the support. -/
theorem derivedUnderlineGammaLocallyClosed_restrict_isZero_of_subset
    (W : LocallyClosedIn X) (F : Sheaf AddCommGrpCat.{u} X)
    (U : Opens X) (hU : (U : Set X) ⊆ W.asSet) (n : ℕ) :
    IsZero (restrictToOpen ((derivedUnderlineGammaLocallyClosed W (n + 1)).obj F) U) := by
  have hUV : U ≤ W.V := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hU hx
    exact y.property
  have hUZ : (U : Set X) ⊆ W.closedHull := fun _ hx ↦ subset_closure (hU hx)
  exact (derivedUnderlineGammaZ_restrict_isZero_of_subset W.closedHull F U hUZ n).of_iso
    ((derivedLocallyClosedSupportedRestrictionIso W U hUV (n + 1)).app F)

/-- Every actual stalk outside the closure of a locally closed support is zero. -/
theorem derivedUnderlineGammaLocallyClosed_stalk_isZero_of_not_mem_closure
    (W : LocallyClosedIn X) (F : Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (x : X) (hx : x ∉ closure W.asSet) :
    IsZero (((derivedUnderlineGammaLocallyClosed W n).obj F).presheaf.stalk x) :=
  sheafStalk_isZero_of_restrict_isZero _ W.closedHull.compl
    (derivedUnderlineGammaLocallyClosed_restrict_isZero_of_le_compl W F _ le_rfl n) x hx

/-- Every positive actual stalk in the interior of the locally closed support is zero. -/
theorem derivedUnderlineGammaLocallyClosed_stalk_isZero_of_mem_interior
    (W : LocallyClosedIn X) (F : Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (x : X) (hx : x ∈ interior W.asSet) :
    IsZero (((derivedUnderlineGammaLocallyClosed W (n + 1)).obj F).presheaf.stalk x) :=
  sheafStalk_isZero_of_restrict_isZero _ ⟨interior W.asSet, isOpen_interior⟩
    (derivedUnderlineGammaLocallyClosed_restrict_isZero_of_subset W F _ interior_subset n) x hx

/-- **I.2.7, locally closed support:** literal stalk support lies in the closure. -/
theorem derivedUnderlineGammaLocallyClosed_stalkSupport_subset_closure
    (W : LocallyClosedIn X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    {x : X | ¬ IsZero (((derivedUnderlineGammaLocallyClosed W n).obj F).presheaf.stalk x)} ⊆
      closure W.asSet := by
  classical
  intro x hx
  by_contra h
  exact hx (derivedUnderlineGammaLocallyClosed_stalk_isZero_of_not_mem_closure W F n x h)

/-- **I.2.7, locally closed support:** positive literal stalk support lies in the boundary. -/
theorem derivedUnderlineGammaLocallyClosed_stalkSupport_subset_frontier
    (W : LocallyClosedIn X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    {x : X | ¬ IsZero (((derivedUnderlineGammaLocallyClosed W (n + 1)).obj F).presheaf.stalk x)} ⊆
      frontier W.asSet := by
  intro x hx
  exact ⟨derivedUnderlineGammaLocallyClosed_stalkSupport_subset_closure W F (n + 1) hx,
    fun hi ↦ hx (derivedUnderlineGammaLocallyClosed_stalk_isZero_of_mem_interior W F n x hi)⟩

end SGA.SGA2.ExposeI
