/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.DerivedSupportedSheaves
import SGA.SGA2.ExposeI.RightDerivedPrecomposition
import SGA.SGA2.ExposeI.LocallyClosedIndependence
import SGA.SGA2.ExposeI.OpenSupportedSections

/-!
# Original ambient supported sheaves for locally closed supports

The functor is the actual composite of open restriction, the original closed
support kernel, and open pushforward. Its original right-derived functors are
identified with sheafifications of locally supported cohomology presheaves.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology
open CategoryTheory.Functor
open scoped ConcreteCategory

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- The original locally closed support kernel on the witness, pushed to `X`. -/
def underlineGammaLocallyClosedFunctor (W : LocallyClosedIn X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X :=
  iShriek_open W.V ⋙ underlineGammaZFunctor (X := (Opens.toTopCat X).obj W.V) W.ZV ⋙
    Sheaf.pushforward AddCommGrpCat.{u} W.V.inclusion'

/-- This construction preserves the previously defined sheaf on the witness. -/
theorem underlineGammaLocallyClosedFunctor_obj (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (underlineGammaLocallyClosedFunctor W).obj F =
      (Sheaf.pushforward AddCommGrpCat.{u} W.V.inclusion').obj
        (underlineGamma_locallyClosed W F) := rfl

instance underlineGammaLocallyClosedFunctor_additive (W : LocallyClosedIn X) :
    (underlineGammaLocallyClosedFunctor W).Additive := by
  dsimp [underlineGammaLocallyClosedFunctor]
  infer_instance

instance underlineGammaLocallyClosedFunctor_preservesFiniteLimits (W : LocallyClosedIn X) :
    PreservesFiniteLimits (underlineGammaLocallyClosedFunctor W) := by
  let := (openExtensionByZeroAdjunction W.V).isRightAdjoint
  dsimp [underlineGammaLocallyClosedFunctor]
  infer_instance

/-- Sections of the ambient sheaf are the original supported sections on the
preimage open inside the witness. -/
def underlineGammaLocallyClosedSectionsEquiv (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    ((underlineGammaLocallyClosedFunctor W).obj F).presheaf.obj (op U) ≃+
      gammaZSections (restrictToOpen F W.V) W.ZV ((Opens.map W.V.inclusion').obj U) :=
  underlineGammaZSectionsEquiv (restrictToOpen F W.V) W.ZV _

theorem underlineGammaLocallyClosedSectionsEquiv_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (U : Opens X)
    (s : ((underlineGammaLocallyClosedFunctor W).obj F).presheaf.obj (op U)) :
    underlineGammaLocallyClosedSectionsEquiv W G U
      (((underlineGammaLocallyClosedFunctor W).map f).hom.app (op U) s) =
        gammaZSectionsMap ((iShriek_open W.V).map f) W.ZV _
          (underlineGammaLocallyClosedSectionsEquiv W F U s) :=
  underlineGammaZSectionsEquiv_naturality ((iShriek_open W.V).map f) W.ZV _ s

theorem underlineGammaLocallyClosedSectionsEquiv_restrict (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) {U V : Opens X} (i : V ⟶ U)
    (s : ((underlineGammaLocallyClosedFunctor W).obj F).presheaf.obj (op U)) :
    underlineGammaLocallyClosedSectionsEquiv W F V
      (((underlineGammaLocallyClosedFunctor W).obj F).presheaf.map i.op s) =
        gammaZSectionsRestriction (restrictToOpen F W.V) W.ZV ((Opens.map W.V.inclusion').map i)
          (underlineGammaLocallyClosedSectionsEquiv W F U s) :=
  underlineGammaZSectionsEquiv_restrict (restrictToOpen F W.V) W.ZV _ s

/-- The concrete locally supported-section presheaf, with its actual
restriction maps and functorial coefficient maps. -/
def gammaLocallyClosedSectionsPresheafFunctor (W : LocallyClosedIn X) :
    Sheaf AddCommGrpCat.{u} X ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  iShriek_open W.V ⋙ gammaZSectionsPresheafFunctor (X := (Opens.toTopCat X).obj W.V) W.ZV ⋙
    (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Opens.map W.V.inclusion').op

instance gammaLocallyClosedSectionsPresheafFunctor_additive (W : LocallyClosedIn X) :
    (gammaLocallyClosedSectionsPresheafFunctor W).Additive := by
  let : ((whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Opens.map W.V.inclusion').op).Additive :=
    ⟨rfl⟩
  dsimp [gammaLocallyClosedSectionsPresheafFunctor]
  infer_instance

/-- The actual ambient sheaf has the concrete supported-section presheaf. -/
def underlineGammaLocallyClosedPresheafFunctorIso (W : LocallyClosedIn X) :
    underlineGammaLocallyClosedFunctor W ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
        gammaLocallyClosedSectionsPresheafFunctor W :=
  isoWhiskerLeft (iShriek_open W.V)
    (isoWhiskerRight (underlineGammaZPresheafFunctorIso (X := (Opens.toTopCat X).obj W.V) W.ZV)
      ((whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Opens.map W.V.inclusion').op))

/-- The original right-derived ambient locally closed support functor. -/
def derivedUnderlineGammaLocallyClosed (W : LocallyClosedIn X) (n : ℕ) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X :=
  (underlineGammaLocallyClosedFunctor W).rightDerived n

def derivedUnderlineGammaLocallyClosedZeroIso (W : LocallyClosedIn X) :
    derivedUnderlineGammaLocallyClosed W 0 ≅ underlineGammaLocallyClosedFunctor W :=
  (underlineGammaLocallyClosedFunctor W).rightDerivedZeroIsoSelf

/-- The local cohomology presheaf is derived before sheafification. -/
def locallyClosedCohomologyPresheafFunctor (W : LocallyClosedIn X) (n : ℕ) :
    Sheaf AddCommGrpCat.{u} X ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (gammaLocallyClosedSectionsPresheafFunctor W).rightDerived n

/-- Presheaf cohomology on each ambient open is the original derived supported
sections on its preimage in the witness. -/
def locallyClosedCohomologyPresheafEvalIso (W : LocallyClosedIn X) (U : Opens X) (n : ℕ) :
    locallyClosedCohomologyPresheafFunctor W n ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
        iShriek_open W.V ⋙ derivedGammaZSections (X := (Opens.toTopCat X).obj W.V)
          W.ZV ((Opens.map W.V.inclusion').obj U) n := by
  letI := (openExtensionByZeroAdjunction W.V).isRightAdjoint
  letI : (iShriek_open W.V).PreservesHomology := inferInstance
  exact (rightDerivedPostcomposeIso (gammaLocallyClosedSectionsPresheafFunctor W)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) n).symm ≪≫
      rightDerivedPrecomposeIso (iShriek_open W.V)
        (gammaZSectionsFunctor (X := (Opens.toTopCat X).obj W.V)
          W.ZV ((Opens.map W.V.inclusion').obj U)) n

/-- The original derived ambient sheaves are the sheafifications of local
supported cohomology, naturally in arbitrary coefficients. -/
def locallyClosedCohomologySheafificationIso (W : LocallyClosedIn X) (n : ℕ) :
    locallyClosedCohomologyPresheafFunctor W n ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
        derivedUnderlineGammaLocallyClosed W n := by
  letI := abelianSheafToPresheaf_additive (X := X)
  letI : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive :=
    inferInstance
  letI : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesHomology :=
    inferInstance
  exact
  isoWhiskerRight
    (rightDerivedFunctorIso (underlineGammaLocallyClosedPresheafFunctorIso W) n).symm
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ≪≫
  rightDerivedExactRetractionIso (underlineGammaLocallyClosedFunctor W)
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (asIso (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).counit) n

/-- Local cohomology presheaves vanish in positive degrees on flasque sheaves. -/
theorem locallyClosedCohomologyPresheaf_isZero_of_isFlasque (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (n : ℕ) :
    IsZero ((locallyClosedCohomologyPresheafFunctor W (n + 1)).obj F) := by
  have : IsFlasque (restrictToOpen F W.V) :=
    isFlasque_pullback_of_isOpenEmbedding W.V.isOpenEmbedding F
  apply Functor.isZero
  intro U
  exact (derivedGammaZSections_isZero_of_isFlasque W.ZV
    ((Opens.map W.V.inclusion').obj U.unop) (restrictToOpen F W.V) n).of_iso
      ((locallyClosedCohomologyPresheafEvalIso W U.unop (n + 1)).app F)

/-- All positive original ambient locally closed supported sheaves of a
flasque coefficient sheaf vanish. -/
theorem derivedUnderlineGammaLocallyClosed_isZero_of_isFlasque (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (n : ℕ) :
    IsZero ((derivedUnderlineGammaLocallyClosed W (n + 1)).obj F) :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map_isZero
    (locallyClosedCohomologyPresheaf_isZero_of_isFlasque W F n)).of_iso
      ((locallyClosedCohomologySheafificationIso W (n + 1)).app F).symm

/-- Ambient sections can be computed with any ambient closed set whose
restriction to the witness is the prescribed closed support. -/
def locallyClosedAmbientSectionsEquiv (W : LocallyClosedIn X)
    (Z : Closeds X) (hZ : closedSupportOnOpen Z W.V = W.ZV)
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    gammaZSections (restrictToOpen F W.V) W.ZV ((Opens.map W.V.inclusion').obj U) ≃+
      gammaZSections F Z (W.V ⊓ U) :=
  (AddEquiv.addSubgroupCongr (congrArg
    (fun D => gammaZSections (restrictToOpen F W.V) D ((Opens.map W.V.inclusion').obj U))
    hZ.symm)).trans (restrictToOpenGammaZSectionsEquiv Z W.V U F)

theorem locallyClosedAmbientSectionsEquiv_val (W : LocallyClosedIn X)
    (Z : Closeds X) (hZ : closedSupportOnOpen Z W.V = W.ZV)
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X)
    (s : gammaZSections (restrictToOpen F W.V) W.ZV ((Opens.map W.V.inclusion').obj U)) :
    (locallyClosedAmbientSectionsEquiv W Z hZ F U s).val =
      (((openRestrictionSectionsFunctorIso W.V).app F).hom.app (op U)) s.val := by
  change (restrictToOpenGammaZSectionsEquiv Z W.V U F _).val = _
  exact restrictToOpenGammaZSectionsEquiv_val Z W.V U F _

theorem locallyClosedAmbientSectionsEquiv_naturality (W : LocallyClosedIn X)
    (Z : Closeds X) (hZ : closedSupportOnOpen Z W.V = W.ZV)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (U : Opens X)
    (s : gammaZSections (restrictToOpen F W.V) W.ZV ((Opens.map W.V.inclusion').obj U)) :
    locallyClosedAmbientSectionsEquiv W Z hZ G U
        (gammaZSectionsMap ((iShriek_open W.V).map f) W.ZV _ s) =
      gammaZSectionsMap f Z (W.V ⊓ U) (locallyClosedAmbientSectionsEquiv W Z hZ F U s) := by
  apply Subtype.ext
  rw [locallyClosedAmbientSectionsEquiv_val, gammaZSectionsMap_apply,
    gammaZSectionsMap_apply, locallyClosedAmbientSectionsEquiv_val]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k => k.app (op U))
      ((openRestrictionSectionsFunctorIso W.V).hom.naturality f)) s.val

theorem locallyClosedAmbientSectionsEquiv_restrict (W : LocallyClosedIn X)
    (Z : Closeds X) (hZ : closedSupportOnOpen Z W.V = W.ZV)
    (F : Sheaf AddCommGrpCat.{u} X) {U U' : Opens X} (i : U' ⟶ U)
    (s : gammaZSections (restrictToOpen F W.V) W.ZV ((Opens.map W.V.inclusion').obj U)) :
    locallyClosedAmbientSectionsEquiv W Z hZ F U'
        (gammaZSectionsRestriction (restrictToOpen F W.V) W.ZV
          ((Opens.map W.V.inclusion').map i) s) =
      gammaZSectionsRestriction F Z ((openIntersectionFunctor W.V).map i)
        (locallyClosedAmbientSectionsEquiv W Z hZ F U s) := by
  apply Subtype.ext
  rw [locallyClosedAmbientSectionsEquiv_val]
  change _ = F.presheaf.map _ (locallyClosedAmbientSectionsEquiv W Z hZ F U s).val
  rw [locallyClosedAmbientSectionsEquiv_val]
  exact ConcreteCategory.congr_hom
    (((openRestrictionSectionsFunctorIso W.V).app F).hom.naturality i.op) s.val

/-- The ambient closed-support description is natural in both opens and
coefficient sheaves, not only an objectwise identification of groups. -/
def locallyClosedAmbientPresheafIso (W : LocallyClosedIn X)
    (Z : Closeds X) (hZ : closedSupportOnOpen Z W.V = W.ZV) :
    gammaLocallyClosedSectionsPresheafFunctor W ≅
      gammaZSectionsPresheafFunctor Z ⋙
        (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openIntersectionFunctor W.V).op :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun U => (locallyClosedAmbientSectionsEquiv W Z hZ F U.unop).toAddCommGrpIso)
      (fun i => by ext s; exact locallyClosedAmbientSectionsEquiv_restrict W Z hZ F i.unop s))
    (fun f => by
      apply NatTrans.ext
      funext U
      ext s
      exact locallyClosedAmbientSectionsEquiv_naturality W Z hZ f U.unop s)

private theorem inf_relativeCover {Z : Closeds X} {V' V : Opens X}
    (hcover : V ≤ V' ⊔ (V ⊓ Z.compl)) (U : Opens X) :
    V ⊓ U ≤ (V' ⊓ U) ⊔ ((V ⊓ U) ⊓ Z.compl) := by
  intro x hx
  rcases hcover hx.1 with hy | hy
  · exact Or.inl ⟨hy, hx.2⟩
  · exact Or.inr ⟨hx, hy.2⟩

/-- Relative excision on intersections is natural in every ambient open. -/
def gammaZIntersectionRestrictionIso {Z : Closeds X} {V' V : Opens X}
    (hV : V' ≤ V) (hcover : V ≤ V' ⊔ (V ⊓ Z.compl)) :
    gammaZSectionsPresheafFunctor Z ⋙
      (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openIntersectionFunctor V).op ≅
    gammaZSectionsPresheafFunctor Z ⋙
      (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openIntersectionFunctor V').op :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun U => (gammaZSections_restrict_addEquiv_of_cover F
        (inf_le_inf_right U.unop hV) (inf_relativeCover hcover U.unop)).toAddCommGrpIso)
      (fun i => by
        ext s
        apply Subtype.ext
        change F.presheaf.map _ (F.presheaf.map _ s.val) =
          F.presheaf.map _ (F.presheaf.map _ s.val)
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          ← Functor.map_comp, ← Functor.map_comp]
        rfl))
    (fun f => by
      apply NatTrans.ext
      funext U
      ext s
      exact gammaZSections_restrict_addEquiv_of_cover_naturality
        (inf_le_inf_right U.unop hV) (inf_relativeCover hcover U.unop) f s)

/-- Independence of arbitrary witnesses as an isomorphism of presheaf-valued
functors, including all restriction and coefficient maps. -/
def locallyClosedSectionsPresheafIndependenceIso {W W' : LocallyClosedIn X}
    (h : W.asSet = W'.asSet) :
    gammaLocallyClosedSectionsPresheafFunctor W ≅ gammaLocallyClosedSectionsPresheafFunctor W' := by
  have hZ : closedSupportOnOpen W.closedHull W'.V = W'.ZV := by
    rw [LocallyClosedIn.closedHull_eq_of_asSet_eq h]
    exact W'.closedSupportOnOpen_closedHull
  have hc : W'.V ≤ (W.V ⊓ W'.V) ⊔ (W'.V ⊓ W.closedHull.compl) := by
    rw [LocallyClosedIn.closedHull_eq_of_asSet_eq h, inf_comm W.V W'.V]
    exact LocallyClosedIn.inter_cover h.symm
  exact locallyClosedAmbientPresheafIso W W.closedHull W.closedSupportOnOpen_closedHull ≪≫
    gammaZIntersectionRestrictionIso inf_le_left (LocallyClosedIn.inter_cover h) ≪≫
    (gammaZIntersectionRestrictionIso inf_le_right hc).symm ≪≫
    (locallyClosedAmbientPresheafIso W' W.closedHull hZ).symm

/-- The actual ambient locally closed support sheaf is independent of the
chosen witness, naturally in arbitrary coefficient sheaves. -/
def underlineGammaLocallyClosedIndependenceIso {W W' : LocallyClosedIn X}
    (h : W.asSet = W'.asSet) :
    underlineGammaLocallyClosedFunctor W ≅ underlineGammaLocallyClosedFunctor W' :=
  ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).whiskeringRight
    (Sheaf AddCommGrpCat.{u} X)).preimageIso
    (underlineGammaLocallyClosedPresheafFunctorIso W ≪≫
      locallyClosedSectionsPresheafIndependenceIso h ≪≫
        (underlineGammaLocallyClosedPresheafFunctorIso W').symm)

/-- Independence of the original derived ambient sheaves in every degree. -/
def derivedUnderlineGammaLocallyClosedIndependenceIso {W W' : LocallyClosedIn X}
    (h : W.asSet = W'.asSet) (n : ℕ) :
    derivedUnderlineGammaLocallyClosed W n ≅ derivedUnderlineGammaLocallyClosed W' n :=
  rightDerivedFunctorIso (underlineGammaLocallyClosedIndependenceIso h) n

/-- The local cohomology presheaves are likewise independent in every degree. -/
def locallyClosedCohomologyPresheafIndependenceIso {W W' : LocallyClosedIn X}
    (h : W.asSet = W'.asSet) (n : ℕ) :
    locallyClosedCohomologyPresheafFunctor W n ≅ locallyClosedCohomologyPresheafFunctor W' n :=
  rightDerivedFunctorIso (locallyClosedSectionsPresheafIndependenceIso h) n

end SGA.SGA2.ExposeI
