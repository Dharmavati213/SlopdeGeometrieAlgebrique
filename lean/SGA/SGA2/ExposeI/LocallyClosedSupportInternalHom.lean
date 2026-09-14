/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.InternalHomIntersection
import SGA.SGA2.ExposeI.LocallyClosedSupportedSheaves

/-! # Internal Hom and sheaf Ext for an arbitrary locally closed support

The source is the original extension-by-zero object `zZX_locallyClosed W`.
The target is the original ambient locally closed supported-section functor.
We prove their natural comparison on every open, then derive this actual
sheaf-valued natural isomorphism in every degree.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat
open CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI
variable {X : TopCat.{u}}

/-- Supported sections of the genuine intersection sheaf are the ordinary
supported sections on the intersection. -/
def intersectionGammaZSectionsEquiv (F : Sheaf AddCommGrpCat.{u} X)
    (Z : Closeds X) (V U : Opens X) :
    gammaZSections (intersectionSectionsSheaf F U) Z V ≃+
      gammaZSections F Z (V ⊓ U) :=
  kerAddEquivOfCommSq (restrictToComplement (intersectionSectionsSheaf F U) Z V).hom
    (restrictToComplement F Z (V ⊓ U)).hom (AddEquiv.refl _)
    (F.obj.mapIso (eqToIso (congrArg op
      (inf_right_comm V Z.compl U)))).addCommGroupIsoToAddEquiv
    (fun s => by
      change (F.obj.map _ ≫ F.obj.map _) s = F.obj.map _ s
      apply ConcreteCategory.congr_hom
      rw [← F.obj.map_comp]
      congr 1)

theorem intersectionGammaZSectionsEquiv_val (F : Sheaf AddCommGrpCat.{u} X)
    (Z : Closeds X) (V U : Opens X)
    (s : gammaZSections (intersectionSectionsSheaf F U) Z V) :
    (intersectionGammaZSectionsEquiv F Z V U s).val = s.val := rfl

theorem intersectionGammaZSectionsEquiv_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (Z : Closeds X) (V U : Opens X)
    (s : gammaZSections (intersectionSectionsSheaf F U) Z V) :
    intersectionGammaZSectionsEquiv G Z V U
        (gammaZSectionsMap (intersectionSectionsSheafMap f U) Z V s) =
      gammaZSectionsMap f Z (V ⊓ U) (intersectionGammaZSectionsEquiv F Z V U s) :=
  Subtype.ext rfl

theorem intersectionGammaZSectionsEquiv_restrict (F : Sheaf AddCommGrpCat.{u} X)
    (Z : Closeds X) (V : Opens X) {U U' : Opens X} (i : U' ⟶ U)
    (s : gammaZSections (intersectionSectionsSheaf F U) Z V) :
    intersectionGammaZSectionsEquiv F Z V U'
        (gammaZSectionsMap (intersectionSectionsSheafRestrict F i) Z V s) =
      gammaZSectionsRestriction F Z ((openIntersectionFunctor V).map i)
        (intersectionGammaZSectionsEquiv F Z V U s) :=
  Subtype.ext rfl

/-- Local Hom from the original support object, expressed as ambient
supported sections on the intersection with the witness. -/
def locallyClosedInternalHomAmbientEquiv (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    (abelianSheafHom (Opens.grothendieckTopology X) (zZX_locallyClosed W) F).obj.obj
      (op U) ≃+ gammaZSections F W.closedHull (W.V ⊓ U) :=
  (internalHomIntersectionEquiv (zZX_locallyClosed W) F U).trans
    ((locallyClosedSupportHomEquiv W (intersectionSectionsSheaf F U)).trans
      ((locallyClosedGammaAmbientEquiv W W.closedHull W.closedSupportOnOpen_closedHull
        (intersectionSectionsSheaf F U)).trans
        (intersectionGammaZSectionsEquiv F W.closedHull W.V U)))

theorem locallyClosedInternalHomAmbientEquiv_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (U : Opens X)
    (φ : (abelianSheafHom (Opens.grothendieckTopology X) (zZX_locallyClosed W) F).obj.obj
      (op U)) :
    locallyClosedInternalHomAmbientEquiv W G U
        ((abelianSheafHomMap (Opens.grothendieckTopology X) (zZX_locallyClosed W) f).hom.app
          (op U) φ) =
      gammaZSectionsMap f W.closedHull (W.V ⊓ U)
        (locallyClosedInternalHomAmbientEquiv W F U φ) := by
  dsimp only [locallyClosedInternalHomAmbientEquiv, AddEquiv.trans_apply]
  rw [internalHomIntersectionEquiv_naturality, locallyClosedSupportHomEquiv_naturality,
    locallyClosedGammaAmbientEquiv_naturality, intersectionGammaZSectionsEquiv_naturality]

theorem locallyClosedInternalHomAmbientEquiv_restrict (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) {U U' : Opens X} (i : U' ⟶ U)
    (φ : (abelianSheafHom (Opens.grothendieckTopology X) (zZX_locallyClosed W) F).obj.obj
      (op U)) :
    locallyClosedInternalHomAmbientEquiv W F U'
        ((abelianSheafHom (Opens.grothendieckTopology X) (zZX_locallyClosed W) F).obj.map
          i.op φ) =
      gammaZSectionsRestriction F W.closedHull ((openIntersectionFunctor W.V).map i)
        (locallyClosedInternalHomAmbientEquiv W F U φ) := by
  dsimp only [locallyClosedInternalHomAmbientEquiv, AddEquiv.trans_apply]
  rw [internalHomIntersectionEquiv_restrict, locallyClosedSupportHomEquiv_naturality,
    locallyClosedGammaAmbientEquiv_naturality, intersectionGammaZSectionsEquiv_restrict]

/-- The sectionwise comparison respects both coefficient morphisms and all
open restrictions. -/
def locallyClosedInternalHomAmbientPresheafIso (W : LocallyClosedIn X) :
    abelianSheafHomFunctor (Opens.grothendieckTopology X) (zZX_locallyClosed W) ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
    gammaZSectionsPresheafFunctor W.closedHull ⋙
      (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openIntersectionFunctor W.V).op :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun U => (locallyClosedInternalHomAmbientEquiv W F U.unop).toAddCommGrpIso)
      (fun i => by
        ext φ
        exact locallyClosedInternalHomAmbientEquiv_restrict W F i.unop φ))
    (fun f => by
      apply NatTrans.ext
      funext U
      ext φ
      exact locallyClosedInternalHomAmbientEquiv_naturality W f U.unop φ)

/-- **I.1.6, arbitrary locally closed support:** internal Hom from the
original integer support sheaf is the original ambient supported-section
sheaf, naturally in the coefficient sheaf. -/
def locallyClosedSupportInternalHomFunctorIso (W : LocallyClosedIn X) :
    abelianSheafHomFunctor (Opens.grothendieckTopology X) (zZX_locallyClosed W) ≅
      underlineGammaLocallyClosedFunctor W :=
  ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).whiskeringRight
    (Sheaf AddCommGrpCat.{u} X)).preimageIso
    (locallyClosedInternalHomAmbientPresheafIso W ≪≫
      (locallyClosedAmbientPresheafIso W W.closedHull W.closedSupportOnOpen_closedHull).symm ≪≫
      (underlineGammaLocallyClosedPresheafFunctorIso W).symm)

/-- **I.2.3 bis, arbitrary locally closed support, sheaf-valued:** the
original right-derived internal Hom agrees in every degree with the original
right-derived ambient locally closed supported-section functor. -/
def locallyClosedSupportInternalSheafExtIso (W : LocallyClosedIn X) (n : ℕ) :
    internalSheafExtFunctor (Opens.grothendieckTopology X) (zZX_locallyClosed W) n ≅
      derivedUnderlineGammaLocallyClosed W n := by
  letI : (underlineGammaLocallyClosedFunctor W).Additive := inferInstance
  exact rightDerivedFunctorIso (locallyClosedSupportInternalHomFunctorIso W) n

end SGA.SGA2.ExposeI
