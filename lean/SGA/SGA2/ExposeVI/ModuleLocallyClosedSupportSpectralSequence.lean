/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleEndofunctorSpectralAbutment
import SGA.SGA2.ExposeVI.ModuleLocallyClosedSupportedHom

/-!
# SGA 2, VI.1.6.3 for arbitrary locally closed support

The actual module-valued locally supported functor is applied to the original
module-injective resolution. Its proved preservation of injectives gives
the genuine derived-Hom abutment. Canonical truncations supply all pages and
differentials, original module Ext against the original derived locally
supported module sheaves as E₂, and a finite exhaustive filtration whose
graded quotients are the actual stable pages.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (W : ExposeI.LocallyClosedIn X)

/-- The actual locally supported module complex, on the original ambient injective resolution. -/
abbrev moduleLocallyClosedSupportResolutionInt {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) :=
  moduleEndofunctorResolutionInt R (moduleGammaLocallyClosedSheafFunctor R W) I

/-- The genuine derived locally supported module object. -/
abbrev moduleLocallyClosedSupportDerivedObject {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) :=
  moduleEndofunctorDerivedObject R (moduleGammaLocallyClosedSheafFunctor R W) I

/-- Its cohomology is the unchanged original derived locally supported module sheaf. -/
abbrev moduleLocallyClosedSupportDerivedHomologyIso {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (q : ℕ) :=
  moduleEndofunctorDerivedHomologyIso R (moduleGammaLocallyClosedSheafFunctor R W) I q

variable (F : SheafOfModules.{u} R)

/-- The actual abelian spectral object of locally supported derived module Hom. -/
abbrev moduleLocallyClosedSupportAbelianSpectralObject {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) :=
  moduleEndofunctorAbelianSpectralObject R (moduleGammaLocallyClosedSheafFunctor R W) F I

/-- **VI.1.6.3, locally closed:** all actual pages, differentials and next-page homology. -/
abbrev moduleLocallyClosedSupportSpectralSequence {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) :=
  moduleEndofunctorSpectralSequence R (moduleGammaLocallyClosedSheafFunctor R W) F I

/-- **VI.1.6.3, locally closed E₂:** actual module Ext against actual derived support modules. -/
def moduleLocallyClosedSupportSpectralSequenceE2Equiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (p q : ℕ) :
    ((moduleLocallyClosedSupportSpectralSequence R W F I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      Abelian.Ext F ((derivedModuleGammaLocallyClosedSheaf R W q).obj G) p :=
  moduleEndofunctorSpectralSequenceE2Equiv R (moduleGammaLocallyClosedSheafFunctor R W) F I p q

/-- The actual total interval group of locally supported derived module Hom. -/
abbrev moduleLocallyClosedSupportSpectralTotal {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℤ) :=
  moduleEndofunctorSpectralTotal R (moduleGammaLocallyClosedSheafFunctor R W) F I n

/-- **VI.1.6.3, locally closed abutment:** the original locally supported module Ext functor. -/
def moduleLocallyClosedSupportSpectralAbutmentEquiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleLocallyClosedSupportSpectralTotal R W F I n ≃+
      (moduleLocallyClosedSupportedExtFunctor R F W n).obj G :=
  let e := ((moduleLocallyClosedSupportedExtViaSupportedSheafIso R F W n).app G).symm
  (moduleEndofunctorSpectralDerivedCompositeEquiv R
    (moduleGammaLocallyClosedSheafFunctor R W) F I n).trans e.addCommGroupIsoToAddEquiv

/-- The finite increasing filtration of the actual total group identified with supported Ext. -/
abbrev moduleLocallyClosedSupportSpectralFiniteFiltration {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :=
  moduleEndofunctorSpectralFiniteFiltration R (moduleGammaLocallyClosedSheafFunctor R W) F I n

@[simp]
theorem moduleLocallyClosedSupportSpectralFiniteFiltration_zero {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleLocallyClosedSupportSpectralFiniteFiltration R W F I n 0 = ⊥ :=
  moduleEndofunctorSpectralFiniteFiltration_zero R
    (moduleGammaLocallyClosedSheafFunctor R W) F I n

@[simp]
theorem moduleLocallyClosedSupportSpectralFiniteFiltration_last {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleLocallyClosedSupportSpectralFiniteFiltration R W F I n (Fin.last (n + 1)) = ⊤ :=
  moduleEndofunctorSpectralFiniteFiltration_last R
    (moduleGammaLocallyClosedSheafFunctor R W) F I n

/-- Genuine consecutive quotients of the locally supported total filtration. -/
abbrev moduleLocallyClosedSupportSpectralGradedPiece {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n q : ℤ) :=
  moduleEndofunctorSpectralGradedPiece R (moduleGammaLocallyClosedSheafFunctor R W) F I n q

/-- **VI.1.6.3, locally closed convergence:** stable pages are the actual graded quotients. -/
def moduleLocallyClosedSupportSpectralStablePageIsoGraded {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) (q : Fin (n + 1)) (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((moduleLocallyClosedSupportSpectralSequence R W F I).page r).X ((n : ℤ) - q, q) ≅
      moduleLocallyClosedSupportSpectralGradedPiece R W F I n q :=
  moduleEndofunctorSpectralStablePageIsoGraded R
    (moduleGammaLocallyClosedSheafFunctor R W) F I n q r hr

/-- Actual resolution maps act on all pages and commute with the original next-page homology. -/
abbrev moduleLocallyClosedSupportSpectralSequenceMap
    {G H : SheafOfModules.{u} R} {I : InjectiveResolution G} {J : InjectiveResolution H}
    (α : I.cocomplex ⟶ J.cocomplex) :=
  moduleEndofunctorSpectralSequenceMap R (moduleGammaLocallyClosedSheafFunctor R W) F α

/-- **VI.1.6.3, locally closed spectral functor:** the original coefficient maps on all pages. -/
abbrev moduleLocallyClosedSupportSpectralSequenceFunctor :=
  moduleEndofunctorSpectralSequenceFunctor R (moduleGammaLocallyClosedSheafFunctor R W) F

/-- Canonical change of module-injective resolution for the entire locally supported sequence. -/
abbrev moduleLocallyClosedSupportSpectralSequenceResolutionIso {G : SheafOfModules.{u} R}
    (I J : InjectiveResolution G) :=
  moduleEndofunctorSpectralSequenceResolutionIso R
    (moduleGammaLocallyClosedSheafFunctor R W) F I J

end SGA.SGA2.ExposeVI
