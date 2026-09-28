/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.ClosedSupportAdjunction
import SGA.SGA2.ExposeI.DerivedSupportedSheaves

/-!
# Acyclic-resolution inputs for supported local-to-global cohomology

The original supported-sheaf functor sends injective coefficients to flasque
sheaves, hence to sheaves acyclic for ordinary global sections. For an actual
injective resolution `I` of `F`, the homology of global sections of
`underlineGammaZ(I)` is the existing Ext-defined supported cohomology `H_Z`.

These are genuine compositional inputs for I.2.6, not a construction of its
spectral sequence, its E₂ identification, or its convergence filtration.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X Y : TopCat.{u}}

instance abelianSheafSections_additive (U : (Opens X)ᵒᵖ) :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj U).Additive where
  map_add := rfl

/-- Ordinary direct image along any continuous map preserves flasque abelian
sheaves: its restriction maps are restrictions on inverse-image opens. -/
theorem isFlasque_pushforward (f : Y ⟶ X) (F : Sheaf AddCommGrpCat.{u} Y)
    [IsFlasque F] : IsFlasque ((Sheaf.pushforward AddCommGrpCat.{u} f).obj F) where
  epi i := inferInstanceAs (Epi (F.presheaf.map ((Opens.map f).op.map i)))

/-- The original supported-section kernel of an injective sheaf is flasque.
This uses the genuine closed extraordinary inverse image and its adjunction,
not an acyclicity assumption on the support functor. -/
theorem isFlasque_underlineGammaZ_of_injective (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] : IsFlasque (underlineGammaZ F Z) := by
  have : IsFlasque ((iUpperShriek_closed Z).obj F) := isFlasque_of_injective _
  have : IsFlasque ((iUpperShriek_closed Z ⋙ iBang_closed Z).obj F) :=
    isFlasque_pushforward (closedInclusion Z) _
  exact isFlasque_of_iso ((closedSupportPushforwardIso Z).app F).symm

/-- The supported-sheaf functor sends injectives to objects acyclic for
ordinary global sections, the key Grothendieck-composition hypothesis. -/
theorem H_underlineGammaZ_pos_subsingleton_of_injective (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] (p : ℕ) :
    Subsingleton (H (underlineGammaZ F Z) (p + 1)) := by
  have := isFlasque_underlineGammaZ_of_injective Z F
  exact H_pos_subsingleton_of_isFlasque _ p

/-- The supported kernel of an injective is acyclic even on every open
subspace, for actual ordinary sheaf cohomology. -/
theorem H_underlineGammaZ_restrict_pos_subsingleton_of_injective (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] (U : Opens X) (p : ℕ) :
    Subsingleton (H (restrictToOpen (underlineGammaZ F Z) U) (p + 1)) := by
  have := isFlasque_underlineGammaZ_of_injective Z F
  exact H_pos_restrict_subsingleton_of_isFlasque _ U p

/-- The actual complex of supported sheaves attached to a chosen injective
resolution; it is the complex computing the original derived support functor. -/
def supportedSheafResolution (Z : Closeds X) {F : Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ :=
  ((underlineGammaZFunctor Z).mapHomologicalComplex _).obj I.cocomplex

/-- Each term of the supported resolution is flasque. -/
theorem supportedSheafResolution_isFlasque (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (q : ℕ) :
    IsFlasque ((supportedSheafResolution Z I).X q) :=
  isFlasque_underlineGammaZ_of_injective Z (I.cocomplex.X q)

/-- Every term of the supported resolution is globally acyclic. -/
theorem supportedSheafResolution_acyclic (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (p q : ℕ) :
    Subsingleton (H ((supportedSheafResolution Z I).X q) (p + 1)) :=
  H_underlineGammaZ_pos_subsingleton_of_injective Z (I.cocomplex.X q) p

/-- Homology of the supported resolution is the original derived supported
sheaf, not a replacement sheaf model. -/
def supportedSheafResolutionHomologyIso (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (q : ℕ) :
    (supportedSheafResolution Z I).homology q ≅ (derivedUnderlineGammaZ Z q).obj F :=
  (I.isoRightDerivedObj (underlineGammaZFunctor Z) q).symm

/-- Global sections of the actual supported resolution. -/
def supportedGlobalSectionsComplex (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (op (⊤ : Opens X))).mapHomologicalComplex _).obj (supportedSheafResolution Z I)

/-- The composite of the original support functor and actual global sections
has the existing Ext-defined supported cohomology as its right-derived functors. -/
instance supportedGlobalSections_additive (Z : Closeds X) :
    (underlineGammaZFunctor Z ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X))).Additive where
  map_add {_F _G} f g :=
    congrArg (fun k => k.hom.app (op (⊤ : Opens X)))
      ((underlineGammaZFunctor Z).map_add (f := f) (g := g))

def derivedSupportedGlobalSectionsIsoH_Z (Z : Closeds X) (n : ℕ) :
    (underlineGammaZFunctor Z ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X))).rightDerived n ≅ Abelian.extFunctorObj (zZX_closed Z) n :=
  rightDerivedFunctorIso (underlineGammaZSectionsFunctorIso Z ⊤) n ≪≫
    derivedGammaZSectionsIsoH_Z Z n

/-- Global sections of the supported resolution compute the actual `H_Z`.
This supplies the abutment-complex comparison needed by a local-to-global
spectral-sequence construction. -/
def supportedGlobalSectionsComplexHomologyIso (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    (supportedGlobalSectionsComplex Z I).homology n ≅ AddCommGrpCat.of (H_Z Z F n) :=
  (I.isoRightDerivedObj (underlineGammaZFunctor Z ⋙
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : Opens X))) n).symm ≪≫
    (derivedSupportedGlobalSectionsIsoH_Z Z n).app F

/-- The abutment-complex comparison commutes with every compatible map of
actual injective resolutions. -/
@[reassoc]
lemma supportedGlobalSectionsComplexHomologyIso_hom_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    homologyMap (((underlineGammaZFunctor Z ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X))).mapHomologicalComplex _).map φ) n ≫
      (supportedGlobalSectionsComplexHomologyIso Z J n).hom =
    (supportedGlobalSectionsComplexHomologyIso Z I n).hom ≫
      AddCommGrpCat.ofHom (H_Z_map Z f n) := by
  simp only [supportedGlobalSectionsComplexHomologyIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  rw [← Category.assoc]
  erw [← InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ hφ
    (underlineGammaZFunctor Z ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X))) n]
  rw [Category.assoc]
  exact congrArg (fun k =>
    (I.isoRightDerivedObj (underlineGammaZFunctor Z ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X))) n).inv ≫ k)
      ((derivedSupportedGlobalSectionsIsoH_Z Z n).hom.naturality f)

end SGA.SGA2.ExposeI
