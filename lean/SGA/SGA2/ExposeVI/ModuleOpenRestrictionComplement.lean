/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleOpenRestrictionExt
import SGA.SGA2.ExposeVI.ModuleSupportIndependence

/-!
# The ordinary Ext endpoints of VI.1.9

Support on an open gives ordinary Ext in the actual module category of
that open. Together with the existing full-space and closed-support
comparisons, these are the endpoint identifications for the closed/open
supported Ext sequence. Arbitrary presentations with the same support are
covered by the proved independence of locally closed support witnesses.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)
    (F : SheafOfModules.{u} R) (U : Opens X)

/-- With full support, local supported Hom is the original local Hom group. -/
def moduleFullSupportHomSectionsIso :
    moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        ExposeI.gammaZSectionsFunctor (⊤ : Closeds X) U ≅
      (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⋙
          (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U) :=
  NatIso.ofComponents
    (fun G => (ExposeI.gammaZTopSectionsEquiv
      (moduleSheafHomAb (Opens.grothendieckTopology X) F G) U).toAddCommGrpIso)
    (fun f => by ext φ; rfl)

/-- Open-supported Hom is naturally the ordinary Hom of the actual restrictions. -/
def moduleLocallyClosedSupportedHomOpenIso :
    moduleLocallyClosedSupportedHomFunctor R F (ExposeI.LocallyClosedIn.ofOpenClosed U ⊤) ≅
      moduleOpenRestriction R U ⋙ preadditiveCoyoneda.obj (op (F.over U)) :=
  moduleLocallyClosedSupportedHomGammaIso R F _ ≪≫
    Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
      (ExposeI.gammaZSectionsLocallyClosedIso (⊤ : Closeds X) U) ≪≫
    moduleFullSupportHomSectionsIso R F U ≪≫ moduleHomSectionsRestrictionIso R F U

/-- The open term of **VI.1.9** is ordinary Ext in the actual module category
on `U`, in every degree and naturally in the coefficient module sheaf. -/
def moduleLocallyClosedSupportedExtOpenIso (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F
        (ExposeI.LocallyClosedIn.ofOpenClosed U ⊤) n ≅
      moduleOpenRestriction R U ⋙ Abelian.extFunctorObj (F.over U) n :=
  ExposeI.rightDerivedFunctorIso (moduleLocallyClosedSupportedHomOpenIso R F U) n ≪≫
    ExposeI.rightDerivedPrecomposeIso (moduleOpenRestriction R U)
      (preadditiveCoyoneda.obj (op (F.over U))) n ≪≫
    Functor.isoWhiskerLeft (moduleOpenRestriction R U)
      (ExposeI.rightDerivedCoyonedaNatIsoExt (F.over U) n)

/-- Any locally closed witness of an open support gives its actual ordinary Ext. -/
def moduleLocallyClosedSupportedExtOpenIsoOfAsSet
    {W : ExposeI.LocallyClosedIn X} (h : W.asSet = (U : Set X)) (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F W n ≅
      moduleOpenRestriction R U ⋙ Abelian.extFunctorObj (F.over U) n :=
  moduleLocallyClosedSupportedExtIndependenceIso R F
    (h.trans (by simp [ExposeI.LocallyClosedIn.ofOpenClosed_asSet])) n ≪≫
      moduleLocallyClosedSupportedExtOpenIso R F U n

/-- Any locally closed witness of a closed support gives the original
closed-supported module Ext functor. -/
def moduleLocallyClosedSupportedExtClosedIsoOfAsSet
    {W : ExposeI.LocallyClosedIn X} (Z : Closeds X)
    (h : W.asSet = (Z : Set X)) (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F W n ≅ moduleSupportedExtFunctor R F Z n :=
  moduleLocallyClosedSupportedExtIndependenceIso R F
    (h.trans (by simp [ExposeI.LocallyClosedIn.ofOpenClosed_asSet])) n ≪≫
      moduleLocallyClosedSupportedExtClosedIso R F Z n

/-- The underlying groups for the open term are the genuine Ext groups. -/
def moduleLocallyClosedSupportedExtOpenEquiv (G : SheafOfModules.{u} R) (n : ℕ) :
    (moduleLocallyClosedSupportedExtFunctor R F
      (ExposeI.LocallyClosedIn.ofOpenClosed U ⊤) n).obj G ≃+
        Abelian.Ext (F.over U) (G.over U) n :=
  ((moduleLocallyClosedSupportedExtOpenIso R F U n).app G).addCommGroupIsoToAddEquiv

end SGA.SGA2.ExposeVI
