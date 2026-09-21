/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleLocallyClosedSupportedSheafInjective
import SGA.SGA2.ExposeVI.ModuleOpenRestrictionExt
import SGA.SGA2.ExposeVI.LocallyClosedExtSequences

/-!
# SGA 2, VI.1.4.3 for arbitrary locally closed supports

The original locally supported Hom functor naturally factors through the
actual locally supported coefficient module sheaf. This follows from the
closed local-Hom factorization and the actual open restriction/direct-image
adjunction. The coefficient maps on both sides are the original maps.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (F : SheafOfModules.{u} R)

/-- The closed local-Hom factorization as a natural comparison on the actual open module site. -/
def moduleSupportedLocalHomFunctorIso (Z : Closeds X) (U : Opens X) :
    moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        ExposeI.gammaZSectionsFunctor Z U ≅
      moduleGammaZSheafFunctor R Z ⋙ moduleOpenRestriction R U ⋙
        preadditiveCoyoneda.obj (op (F.over U)) :=
  NatIso.ofComponents (fun G ↦
    ((moduleSupportedLocalHomEquiv R F G Z U).trans
      (moduleLocalHomSheafOverAddEquiv R F (moduleGammaZSheaf R Z G) U)).toAddCommGrpIso)
    (fun a ↦ by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro φ
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro V
      ext x
      rfl)

/-- Open-site Hom is ambient Hom into actual open direct image. -/
def moduleOpenHomDirectImageIso (U : Opens X) :
    preadditiveCoyoneda.obj (op (F.over U)) ≅
      moduleOpenDirectImage R U ⋙ preadditiveCoyoneda.obj (op F) :=
  NatIso.ofComponents (fun G ↦
    ((moduleOpenRestrictionDirectImageAdjunction R U).homAddEquiv F G).toAddCommGrpIso)
    (fun a ↦ by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro φ
      exact (moduleOpenRestrictionDirectImageAdjunction R U).homEquiv_naturality_right φ a)

/-- **VI.1.4.3:** locally supported local linear Hom is naturally Hom into the
original locally supported coefficient module sheaf. -/
def moduleLocallyClosedHomGammaFactorIso (W : ExposeI.LocallyClosedIn X) :
    moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        ExposeI.gammaLocallyClosedFunctor W ≅
      moduleGammaLocallyClosedSheafFunctor R W ⋙ preadditiveCoyoneda.obj (op F) :=
  Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
      (ExposeI.gammaLocallyClosedAmbientIso W W.closedHull W.closedSupportOnOpen_closedHull) ≪≫
    moduleSupportedLocalHomFunctorIso R F W.closedHull W.V ≪≫
    Functor.isoWhiskerLeft (moduleGammaZSheafFunctor R W.closedHull ⋙ moduleOpenRestriction R W.V)
      (moduleOpenHomDirectImageIso R F W.V) ≪≫
    Functor.isoWhiskerRight (moduleGammaLocallyClosedFunctorCompositeIso R W).symm
      (preadditiveCoyoneda.obj (op F))

/-- The additive Hom equivalence of VI.1.4.3 for an arbitrary locally closed witness. -/
def moduleLocallyClosedSupportedHomEquiv (G : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) :
    W.gamma (moduleSheafHomAb (Opens.grothendieckTopology X) F G) ≃+
      (F ⟶ moduleGammaLocallyClosedSheaf R W G) :=
  ((moduleLocallyClosedHomGammaFactorIso R F W).app G).addCommGroupIsoToAddEquiv

/-- The actual VI.1.1 locally supported Hom functor has the VI.1.4.3 factorization. -/
def moduleLocallyClosedSupportedHomFunctorIso (W : ExposeI.LocallyClosedIn X) :
    moduleLocallyClosedSupportedHomFunctor R F W ≅
      moduleGammaLocallyClosedSheafFunctor R W ⋙ preadditiveCoyoneda.obj (op F) :=
  moduleLocallyClosedSupportedHomGammaIso R F W ≪≫ moduleLocallyClosedHomGammaFactorIso R F W

/-- The actual locally closed supported-Hom factorization after derivation in module sheaves. -/
def moduleLocallyClosedSupportedExtViaSupportedSheafIso (W : ExposeI.LocallyClosedIn X) (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F W n ≅
      (moduleGammaLocallyClosedSheafFunctor R W ⋙ preadditiveCoyoneda.obj (op F)).rightDerived n :=
  ExposeI.rightDerivedFunctorIso (moduleLocallyClosedSupportedHomFunctorIso R F W) n

end SGA.SGA2.ExposeVI
