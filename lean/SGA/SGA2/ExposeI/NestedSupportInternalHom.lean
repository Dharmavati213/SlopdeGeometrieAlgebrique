/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.InternalHomPrecomposition
import SGA.SGA2.ExposeI.LocallyClosedSupportInternalHom
import SGA.SGA2.ExposeI.NestedSupportObjects
import SGA.SGA2.ExposeI.NestedSupportedSheafSequence

/-! # I.1.10: internal Hom recovers the actual nested supported-sheaf arrows

The integer-support arrows and the ambient supported-sheaf arrows were
constructed independently from their original sections. Their actual maps
are identified here by natural isomorphisms, not only their objects.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI
variable {X : TopCat.{u}}

private theorem representingHomIso_naturality
    {C : Type*} [Category.{u} C] [Preadditive C] {A : C}
    {T : C ⥤ AddCommGrpCat.{u}} (e : preadditiveCoyoneda.obj (op A) ≅ T)
    {F G : C} (g : F ⟶ G) (f : A ⟶ F) :
    (e.app G).addCommGroupIsoToAddEquiv (f ≫ g) =
      T.map g ((e.app F).addCommGroupIsoToAddEquiv f) :=
  ConcreteCategory.congr_hom (C := AddCommGrpCat.{u}) (e.hom.naturality g) f

private theorem square_of_map_comparisons
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D) [T.Faithful]
    {A₁ A₂ B₁ B₂ : C} (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂)
    (e₁ : A₁ ⟶ B₁) (e₂ : A₂ ⟶ B₂) {P₁ P₂ : D}
    (f₁ : T.obj A₁ ⟶ P₁) (f₂ : T.obj A₂ ⟶ P₂)
    (g₁ : T.obj B₁ ⟶ P₁) (g₂ : T.obj B₂ ⟶ P₂) [Mono g₂] (p : P₁ ⟶ P₂)
    (he₁ : T.map e₁ ≫ g₁ = f₁) (he₂ : T.map e₂ ≫ g₂ = f₂)
    (ha : T.map a ≫ f₂ = f₁ ≫ p) (hb : T.map b ≫ g₂ = g₁ ≫ p) :
    a ≫ e₂ = e₁ ≫ b := by
  apply T.map_injective
  apply (cancel_mono g₂).mp
  rw [T.map_comp, T.map_comp, Category.assoc, he₂, ha, Category.assoc, hb,
    ← Category.assoc, he₁]

theorem openClosedSupportHomEquiv_naturality (Z : Closeds X) (V : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (g : F ⟶ G)
    (f : zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V Z) ⟶ F) :
    openClosedSupportHomEquiv Z V G (f ≫ g) =
      gammaZSectionsMap g Z V (openClosedSupportHomEquiv Z V F f) :=
  representingHomIso_naturality (openClosedSupportHomFunctorIso Z V) g f

/-- I.1.6 on an open/closed presentation, with the original global Hom
representation used to define the nested integer-support arrows. -/
def openClosedInternalHomSectionsEquiv (Z : Closeds X) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    (abelianSheafHom (Opens.grothendieckTopology X)
      (zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V Z)) F).obj.obj (op U) ≃+
        gammaZSections F Z (V ⊓ U) :=
  (internalHomIntersectionEquiv _ F U).trans
    ((openClosedSupportHomEquiv Z V (intersectionSectionsSheaf F U)).trans
      (intersectionGammaZSectionsEquiv F Z V U))

theorem openClosedInternalHomSectionsEquiv_naturality (Z : Closeds X) (V : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (U : Opens X)
    (φ : (abelianSheafHom (Opens.grothendieckTopology X)
      (zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V Z)) F).obj.obj (op U)) :
    openClosedInternalHomSectionsEquiv Z V G U
        ((abelianSheafHomMap (Opens.grothendieckTopology X) _ f).hom.app (op U) φ) =
      gammaZSectionsMap f Z (V ⊓ U) (openClosedInternalHomSectionsEquiv Z V F U φ) := by
  dsimp only [openClosedInternalHomSectionsEquiv, AddEquiv.trans_apply]
  rw [internalHomIntersectionEquiv_naturality, openClosedSupportHomEquiv_naturality,
    intersectionGammaZSectionsEquiv_naturality]

theorem openClosedInternalHomSectionsEquiv_restrict (Z : Closeds X) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) {U U' : Opens X} (i : U' ⟶ U)
    (φ : (abelianSheafHom (Opens.grothendieckTopology X)
      (zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V Z)) F).obj.obj (op U)) :
    openClosedInternalHomSectionsEquiv Z V F U'
        ((abelianSheafHom (Opens.grothendieckTopology X)
          (zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V Z)) F).obj.map i.op φ) =
      gammaZSectionsRestriction F Z ((openIntersectionFunctor V).map i)
        (openClosedInternalHomSectionsEquiv Z V F U φ) := by
  dsimp only [openClosedInternalHomSectionsEquiv, AddEquiv.trans_apply]
  rw [internalHomIntersectionEquiv_restrict, openClosedSupportHomEquiv_naturality,
    intersectionGammaZSectionsEquiv_restrict]

def openClosedInternalHomPresheafIso (Z : Closeds X) (V : Opens X) :
    abelianSheafHomFunctor (Opens.grothendieckTopology X)
        (zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V Z)) ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
        gammaIntersectionPresheafFunctor Z V :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun U => (openClosedInternalHomSectionsEquiv Z V F U.unop).toAddCommGrpIso)
      (fun i => by ext φ; exact openClosedInternalHomSectionsEquiv_restrict Z V F i.unop φ))
    (fun f => by
      apply NatTrans.ext
      funext U
      ext φ
      exact openClosedInternalHomSectionsEquiv_naturality Z V f U.unop φ)

/-- Local precomposition by the actual support-object restriction induces
exactly inclusion of the original supported-section presheaves. -/
theorem nestedSupportObjectRestriction_internalHom_sections {A B : Closeds X}
    (h : A ≤ B) (V : Opens X) :
    whiskerRight (abelianSheafHomPrecomp (Opens.grothendieckTopology X)
        (nestedSupportObjectRestriction h V))
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ≫
      (openClosedInternalHomPresheafIso B V).hom =
        (openClosedInternalHomPresheafIso A V).hom ≫ nestedSupportedPresheafInclusion h V := by
  ext F U φ
  change openClosedInternalHomSectionsEquiv B V F U.unop
      (((abelianSheafHomPrecomp _ (nestedSupportObjectRestriction h V)).app F).hom.app U φ) =
    nestedSupportSectionsInclusion h (V ⊓ U.unop) F
      (openClosedInternalHomSectionsEquiv A V F U.unop φ)
  dsimp only [openClosedInternalHomSectionsEquiv, AddEquiv.trans_apply]
  rw [internalHomIntersectionEquiv_precomp, nestedSupportObjectRestriction_sections]
  exact Subtype.ext rfl

/-- Local precomposition by the actual support-object inclusion induces
exactly the original restriction to the difference support. -/
theorem nestedSupportObjectInclusion_internalHom_sections (A B : Closeds X)
    (V : Opens X) :
    whiskerRight (abelianSheafHomPrecomp (Opens.grothendieckTopology X)
        (nestedSupportObjectInclusion A B V))
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ≫
      (openClosedInternalHomPresheafIso B (V ⊓ A.compl)).hom =
        (openClosedInternalHomPresheafIso B V).hom ≫ nestedSupportedPresheafRestriction A B V := by
  ext F U φ
  change openClosedInternalHomSectionsEquiv B (V ⊓ A.compl) F U.unop
      (((abelianSheafHomPrecomp _ (nestedSupportObjectInclusion A B V)).app F).hom.app U φ) =
    gammaZSectionsRestriction F B (homOfLE (inf_le_inf_right U.unop inf_le_left))
      (openClosedInternalHomSectionsEquiv B V F U.unop φ)
  dsimp only [openClosedInternalHomSectionsEquiv, AddEquiv.trans_apply]
  rw [internalHomIntersectionEquiv_precomp, nestedSupportObjectInclusion_sections]
  exact Subtype.ext rfl

/-- The original sheaf-valued Hom/support comparison for an arbitrary
open/closed presentation, with the section comparison fixed above. -/
def openClosedInternalHomFunctorIso (Z : Closeds X) (V : Opens X) :
    abelianSheafHomFunctor (Opens.grothendieckTopology X)
      (zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V Z)) ≅
        underlineGammaLocallyClosedFunctor (LocallyClosedIn.ofOpenClosed V Z) :=
  ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).whiskeringRight
    (Sheaf AddCommGrpCat.{u} X)).preimageIso
    (openClosedInternalHomPresheafIso Z V ≪≫ (openClosedSupportedPresheafIso Z V).symm)

theorem openClosedInternalHomFunctorIso_sections (Z : Closeds X) (V : Opens X) :
    whiskerRight (openClosedInternalHomFunctorIso Z V).hom
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ≫
      (openClosedSupportedPresheafIso Z V).hom = (openClosedInternalHomPresheafIso Z V).hom := by
  change (((whiskeringRight _ _ _).obj
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).map
      (openClosedInternalHomFunctorIso Z V).hom) ≫ _ = _
  dsimp only [openClosedInternalHomFunctorIso, Functor.FullyFaithful.preimageIso]
  rw [Functor.FullyFaithful.map_preimage]
  simp

/-- **I.1.10, first map:** internal Hom of the actual support-object
restriction is exactly the original supported-sheaf inclusion. -/
theorem nestedSupportObjectRestriction_internalHom {A B : Closeds X}
    (h : A ≤ B) (V : Opens X) :
    abelianSheafHomPrecomp (Opens.grothendieckTopology X) (nestedSupportObjectRestriction h V) ≫
        (openClosedInternalHomFunctorIso B V).hom =
      (openClosedInternalHomFunctorIso A V).hom ≫ openClosedSupportedSheafInclusion h V := by
  exact square_of_map_comparisons
    ((whiskeringRight _ _ _).obj
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    _ _ _ _ (openClosedInternalHomPresheafIso A V).hom
    (openClosedInternalHomPresheafIso B V).hom (openClosedSupportedPresheafIso A V).hom
    (openClosedSupportedPresheafIso B V).hom (nestedSupportedPresheafInclusion h V)
    (openClosedInternalHomFunctorIso_sections A V) (openClosedInternalHomFunctorIso_sections B V)
    (nestedSupportObjectRestriction_internalHom_sections h V)
    (openClosedSupportedSheafInclusion_sections h V)

/-- **I.1.10, second map:** internal Hom of the actual support-object
inclusion is exactly the original supported-sheaf restriction. -/
theorem nestedSupportObjectInclusion_internalHom (A B : Closeds X) (V : Opens X) :
    abelianSheafHomPrecomp (Opens.grothendieckTopology X) (nestedSupportObjectInclusion A B V) ≫
        (openClosedInternalHomFunctorIso B (V ⊓ A.compl)).hom =
      (openClosedInternalHomFunctorIso B V).hom ≫ openClosedSupportedSheafRestriction A B V := by
  exact square_of_map_comparisons
    ((whiskeringRight _ _ _).obj
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    _ _ _ _ (openClosedInternalHomPresheafIso B V).hom
    (openClosedInternalHomPresheafIso B (V ⊓ A.compl)).hom (openClosedSupportedPresheafIso B V).hom
    (openClosedSupportedPresheafIso B (V ⊓ A.compl)).hom (nestedSupportedPresheafRestriction A B V)
    (openClosedInternalHomFunctorIso_sections B V)
    (openClosedInternalHomFunctorIso_sections B (V ⊓ A.compl))
    (nestedSupportObjectInclusion_internalHom_sections A B V)
    (openClosedSupportedSheafRestriction_sections A B V)

/-- The short complex obtained by actual contravariant internal Hom from
the proved integer-support sequence. -/
def nestedSupportInternalHomSequence {A B : Closeds X} (h : A ≤ B) (V : Opens X) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk
    (abelianSheafHomPrecomp (Opens.grothendieckTopology X) (nestedSupportObjectRestriction h V))
    (abelianSheafHomPrecomp (Opens.grothendieckTopology X) (nestedSupportObjectInclusion A B V))
    (by rw [← abelianSheafHomPrecomp_comp, nestedSupportObject_comp,
      abelianSheafHomPrecomp_zero])

/-- **I.1.10:** applying actual internal Hom to the genuine integer-support
sequence gives the actual I.1.9 supported-sheaf sequence, including its maps. -/
def nestedSupportInternalHomSequenceIso {A B : Closeds X} (h : A ≤ B) (V : Opens X) :
    nestedSupportInternalHomSequence h V ≅ openClosedSupportedSheafFunctorSequence h V :=
  ShortComplex.isoMk (openClosedInternalHomFunctorIso A V)
    (openClosedInternalHomFunctorIso B V) (openClosedInternalHomFunctorIso B (V ⊓ A.compl))
    (nestedSupportObjectRestriction_internalHom h V).symm
    (nestedSupportObjectInclusion_internalHom A B V).symm

end SGA.SGA2.ExposeI
