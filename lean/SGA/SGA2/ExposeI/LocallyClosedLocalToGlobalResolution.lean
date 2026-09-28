/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedSupportedSheaves
import SGA.SGA2.ExposeI.SupportedSheafInjective
import SGA.SGA2.ExposeI.LocalToGlobalResolution

/-!
# Ambient resolution inputs for general locally closed local-to-global cohomology

The unchanged ambient support functor preserves injectives: open restriction,
closed supported sections, and ordinary open direct image all do. Its actual
global sections are the previously defined locally supported-section functor.
Consequently the global-sections complex of its image of an injective resolution
computes Ext from the original locally closed support sheaf on the ambient space.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex
open CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- The original ambient locally closed support functor preserves injectives. -/
instance underlineGammaLocallyClosedFunctor_preservesInjectiveObjects (W : LocallyClosedIn X) :
    (underlineGammaLocallyClosedFunctor W).PreservesInjectiveObjects := by
  dsimp [underlineGammaLocallyClosedFunctor]
  infer_instance

/-- Actual global sections of the ambient supported sheaf are the original
locally closed supported sections. -/
def underlineGammaLocallyClosedGlobalSectionsIso (W : LocallyClosedIn X) :
    underlineGammaLocallyClosedFunctor W ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op (⊤ : Opens X)) ≅
        gammaLocallyClosedFunctor W :=
  NatIso.ofComponents
    (fun F => (underlineGammaLocallyClosedSectionsEquiv W F ⊤).toAddCommGrpIso)
    (fun f => by ext s; exact underlineGammaLocallyClosedSectionsEquiv_naturality W f ⊤ s)

/-- The actual ambient supported complex attached to an injective resolution. -/
def locallyClosedSupportedSheafResolution (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ :=
  ((underlineGammaLocallyClosedFunctor W).mapHomologicalComplex _).obj I.cocomplex

instance locallyClosedSupportedSheafResolution_injective (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (q : ℕ) :
    Injective ((locallyClosedSupportedSheafResolution W I).X q) := by
  change Injective ((underlineGammaLocallyClosedFunctor W).obj (I.cocomplex.X q))
  infer_instance

theorem locallyClosedSupportedSheafResolution_isFlasque (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (q : ℕ) :
    IsFlasque ((locallyClosedSupportedSheafResolution W I).X q) :=
  isFlasque_of_injective _

/-- Cohomology of the actual ambient complex is the original ambient
right-derived locally closed supported sheaf. -/
def locallyClosedSupportedSheafResolutionHomologyIso (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (q : ℕ) :
    (locallyClosedSupportedSheafResolution W I).homology q ≅
      (derivedUnderlineGammaLocallyClosed W q).obj F :=
  (I.isoRightDerivedObj (underlineGammaLocallyClosedFunctor W) q).symm

/-- The actual ambient global-sections complex of the supported resolution. -/
def locallyClosedSupportedGlobalSectionsComplex (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (op (⊤ : Opens X))).mapHomologicalComplex _).obj
      (locallyClosedSupportedSheafResolution W I)

instance locallyClosedSupportedGlobalSections_additive (W : LocallyClosedIn X) :
    (underlineGammaLocallyClosedFunctor W ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X))).Additive where
  map_add {_F _G} f g :=
    congrArg (fun k => k.hom.app (op (⊤ : Opens X)))
      ((underlineGammaLocallyClosedFunctor W).map_add (f := f) (g := g))

/-- Deriving actual global sections of the ambient supported sheaf gives
Ext from the original locally closed integer support sheaf. -/
def derivedLocallyClosedSupportedGlobalSectionsIsoExt (W : LocallyClosedIn X) (n : ℕ) :
    (underlineGammaLocallyClosedFunctor W ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X))).rightDerived n ≅
      Abelian.extFunctorObj (zZX_locallyClosed W) n :=
  rightDerivedFunctorIso (underlineGammaLocallyClosedGlobalSectionsIso W) n ≪≫
    derivedGammaLocallyClosedIsoExt W n

/-- The genuine global-sections homology comparison with the previously
defined ambient Ext support groups. -/
def locallyClosedSupportedGlobalSectionsComplexHomologyIso (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    (locallyClosedSupportedGlobalSectionsComplex W I).homology n ≅
      AddCommGrpCat.of (H_locallyClosed W F n) :=
  (I.isoRightDerivedObj (underlineGammaLocallyClosedFunctor W ⋙
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : Opens X))) n).symm ≪≫
    (derivedLocallyClosedSupportedGlobalSectionsIsoExt W n).app F

end SGA.SGA2.ExposeI
