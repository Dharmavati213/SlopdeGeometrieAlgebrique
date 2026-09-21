/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleSheafExtSpectralFunctor
import SGA.SGA2.ExposeVI.ModuleSheafExtSpectralNaturality
import SGA.SGA2.ExposeVI.ModuleLocallyClosedSheafExtSpectralSequence
import SGA.SGA2.ExposeVI.LocallyClosedSpectralE2Comparison
import SGA.SGA2.ExposeVI.ModuleSupportedSheafExtSpectralSequence
import SGA.SGA2.ExposeVI.SheafFunctorSpectralNaturality
import SGA.SGA2.ExposeVI.ModuleSupportSpectralAbutment
import SGA.SGA2.ExposeVI.ModuleSupportSpectralNaturality
import SGA.SGA2.ExposeVI.ModuleSupportIndependence

/-!
# SGA 2, VI.1.6: spectral functors abutting to supported Ext

The initial terms are supported cohomology of sheaf Ext and ordinary
cohomology of supported sheaf Ext, and Ext against derived supported modules.
These are genuine spectral functors on
module sheaves, with all pages and differentials, proved E₂ identifications,
and finite convergence to the original supported Ext. The constructions use
the actual module-injective resolutions and VI.1.5 Hom flasqueness.

The first and second sequences allow arbitrary locally closed support. The
third sequence is constructed for closed support.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- **VI.1.6.1 initial term:** supported cohomology of sheaf Ext. -/
abbrev VI_1_6_1_E2 (F G : SheafOfModules.{u} R) (Z : Closeds X) (p q : ℕ) :=
  ExposeI.H_Z Z ((moduleSheafExtAbFunctor R F q).obj G) p

/-- **VI.1.6.1 initial term for every locally closed support.** -/
abbrev VI_1_6_1_locallyClosed_E2 (F G : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) (p q : ℕ) :=
  ExposeI.H_locallyClosed W ((moduleSheafExtAbFunctor R F q).obj G) p

/-- **VI.1.6.2 initial term:** ordinary cohomology of supported sheaf Ext. -/
abbrev VI_1_6_2_E2 (F G : SheafOfModules.{u} R) (W : ExposeI.LocallyClosedIn X)
    (p q : ℕ) :=
  ExposeI.H ((moduleLocallyClosedSheafExtFunctor R F W q).obj G) p

/-- **VI.1.6.3 initial term:** module Ext against the original derived supported module. -/
abbrev VI_1_6_3_E2 (F G : SheafOfModules.{u} R) (Z : Closeds X) (p q : ℕ) :=
  Abelian.Ext F ((derivedModuleGammaZSheaf R Z q).obj G) p

/-- **VI.1.6 abutment:** the original supported Ext groups. -/
abbrev VI_1_6_abutment (F G : SheafOfModules.{u} R) (Z : Closeds X) (n : ℕ) :=
  (moduleSupportedExtFunctor R F Z n).obj G

/-- Positive supported Ext vanishes on actual injective coefficient module sheaves. -/
theorem VI_1_6_1_deg0_isZero_succ_of_injective (F G : SheafOfModules.{u} R)
    [Injective G] (Z : Closeds X) (p : ℕ) :
    IsZero ((moduleSupportedExtFunctor R F Z (p + 1)).obj G) :=
  moduleSupportedExt_isZero_of_injective R F G Z p

/-- **VI.1.6.1:** the actual spectral sequence of supported cohomology of sheaf Ext. -/
def VI_1_6_1_grothendieck (F : SheafOfModules.{u} R) (Z : Closeds X)
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  moduleSheafExtSpectralSequence R F Z I

/-- The initial terms of the actual VI.1.6.1 sequence. -/
def VI_1_6_1_grothendieck_E2 (F : SheafOfModules.{u} R) (Z : Closeds X)
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) (p q : ℕ) :
    ((VI_1_6_1_grothendieck R F Z I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      VI_1_6_1_E2 R F G Z p q :=
  moduleSheafExtSpectralSequenceE2Equiv R F Z I p q

/-- **VI.1.6.1 for arbitrary locally closed support:** actual pages and differentials. -/
def VI_1_6_1_locallyClosed_grothendieck (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  moduleLocallyClosedSheafExtSpectralSequence R F W I

/-- Ambient locally supported cohomology gives the actual E₂ terms of VI.1.6.1. -/
def VI_1_6_1_locallyClosed_grothendieck_E2 (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) {G : SheafOfModules.{u} R} (I : InjectiveResolution G)
    (p q : ℕ) :
    ((VI_1_6_1_locallyClosed_grothendieck R F W I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      VI_1_6_1_locallyClosed_E2 R F G W p q :=
  moduleLocallyClosedSheafExtSpectralSequenceE2Equiv R F W I p q

/-- The total is the unchanged original locally supported module Ext group. -/
def VI_1_6_1_locallyClosed_grothendieck_abutment (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) {G : SheafOfModules.{u} R} (I : InjectiveResolution G)
    (n : ℕ) :
    moduleLocallyClosedSheafExtSpectralTotal R F W I n ≃+
      (moduleLocallyClosedSupportedExtFunctor R F W n).obj G :=
  moduleLocallyClosedSheafExtSpectralAbutmentEquiv R F W I n

/-- **VI.1.6.2:** ordinary cohomology of supported sheaf Ext from a module resolution. -/
def VI_1_6_2_grothendieck (F : SheafOfModules.{u} R) (W : ExposeI.LocallyClosedIn X)
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  moduleSupportedSheafExtSpectralSequence R F W I

/-- The initial terms of the actual VI.1.6.2 sequence. -/
def VI_1_6_2_grothendieck_E2 (F : SheafOfModules.{u} R) (W : ExposeI.LocallyClosedIn X)
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) (p q : ℕ) :
    ((VI_1_6_2_grothendieck R F W I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      VI_1_6_2_E2 R F G W p q :=
  moduleSupportedSheafExtSpectralSequenceE2Equiv R F W I p q

/-- **VI.1.6.3:** the actual module Ext spectral sequence of the supported resolution. -/
def VI_1_6_3_grothendieck (F : SheafOfModules.{u} R) (Z : Closeds X)
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  moduleSupportSpectralSequence R Z F I

/-- The initial terms of the actual VI.1.6.3 sequence. -/
def VI_1_6_3_grothendieck_E2 (F : SheafOfModules.{u} R) (Z : Closeds X)
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) (p q : ℕ) :
    ((VI_1_6_3_grothendieck R F Z I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      VI_1_6_3_E2 R F G Z p q :=
  moduleSupportSpectralSequenceE2Equiv R Z F I p q

/-- The actual VI.1.6.1 total is original supported Ext. -/
def VI_1_6_1_grothendieck_abutment (F : SheafOfModules.{u} R) (Z : Closeds X)
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) (n : ℕ) :
    moduleSheafExtSpectralTotal R F Z I n ≃+ VI_1_6_abutment R F G Z n :=
  moduleSheafExtSpectralAbutmentEquiv R F Z I n

/-- For closed support, VI.1.6.2 abuts to exactly the same original supported Ext functor. -/
def VI_1_6_2_grothendieck_abutment (F : SheafOfModules.{u} R) (Z : Closeds X)
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) (n : ℕ) :
    moduleSupportedSheafExtSpectralTotal R F (ExposeI.LocallyClosedIn.ofOpenClosed ⊤ Z) I n ≃+
      VI_1_6_abutment R F G Z n :=
  (moduleSupportedSheafExtSpectralAbutmentEquiv R F _ I n).trans
    ((moduleLocallyClosedSupportedExtClosedIso R F Z n).app G).addCommGroupIsoToAddEquiv

/-- The actual VI.1.6.3 total is the unchanged original supported Ext functor. -/
def VI_1_6_3_grothendieck_abutment (F : SheafOfModules.{u} R) (Z : Closeds X)
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) (n : ℕ) :
    moduleSupportSpectralTotal R Z F I n ≃+ VI_1_6_abutment R F G Z n :=
  moduleSupportSpectralAbutmentEquiv R Z F I n

end SGA.SGA2.ExposeVI
