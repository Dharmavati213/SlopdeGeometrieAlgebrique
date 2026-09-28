/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.SupportedHomFlasque
import SGA.SGA2.ExposeVI.SheafFunctorSpectralFunctor
import SGA.SGA2.ExposeI.OpenDerivedSupportedSheaves
import SGA.SGA2.ExposeI.LocalToGlobalTotalCohomology

/-!
# SGA 2, VI.1.6.2: ordinary cohomology of actual supported sheaf Ext

The original locally supported Hom functor is applied to a module-injective
resolution. Its flasque terms give the genuine truncation spectral sequence
with E₂ equal to ordinary cohomology of actual supported sheaf Ext and total
equal to the original locally supported Ext. The construction retains all
coefficient maps, a finite exhaustive filtration, and stable-page quotients.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- Full supported sections are the actual global-section functor, naturally. -/
def gammaZTopSectionsFunctorIso :
    ExposeI.gammaZSectionsFunctor (⊤ : Closeds X) ⊤ ≅
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X)) :=
  NatIso.ofComponents (fun A ↦ (ExposeI.gammaZTopSectionsEquiv A ⊤).toAddCommGrpIso)
    (by intro A B f; ext s; rfl)

/-- Supported cohomology with full support is original ordinary sheaf cohomology. -/
def supportedCohomologyTopEquiv (A : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    ExposeI.H_Z (⊤ : Closeds X) A n ≃+ ExposeI.H A n := by
  letI : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (op (⊤ : Opens X))).Additive := ExposeI.abelianSheafSections_additive _
  exact ((ExposeI.derivedGammaZSectionsIsoH_Z (⊤ : Closeds X) n).symm ≪≫
    ExposeI.rightDerivedFunctorIso (gammaZTopSectionsFunctorIso (X := X)) n ≪≫
    (ExposeI.rightDerivedFunctorIso (ExposeI.constantZHomFunctorIso (X := X)) n).symm ≪≫
    ExposeI.rightDerivedCoyonedaNatIsoExt (ExposeI.constantZ X) n).app A
      |>.addCommGroupIsoToAddEquiv

variable (R : Sheaf RingCat.{u} X) (F : SheafOfModules.{u} R) (W : ExposeI.LocallyClosedIn X)

/-- The actual integer-indexed complex of locally supported local linear Hom. -/
abbrev moduleSupportedSheafHomResolutionInt {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) :=
  sheafFunctorResolutionInt (moduleLocallyClosedSheafHomFunctor R F W) I

/-- The terms are flasque by the original VI.1.5 Hom flasqueness and supported gluing. -/
instance {G : SheafOfModules.{u} R} (I : InjectiveResolution G) (n : ℤ) :
    ExposeI.IsFlasque ((moduleSupportedSheafHomResolutionInt R F W I).X n) :=
  moduleLocallyClosedSheafHom_isFlasque_of_injective R F (I.cochainComplex.X n) W

/-- **VI.1.6.2:** the actual spectral sequence, including all differentials and page homology. -/
abbrev moduleSupportedSheafExtSpectralSequence {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) :=
  sheafFunctorSpectralSequence (moduleLocallyClosedSheafHomFunctor R F W) ⊤ I

/-- **VI.1.6.2, E₂:** ordinary cohomology of the original supported sheaf Ext. -/
def moduleSupportedSheafExtSpectralSequenceE2Equiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (p q : ℕ) :
    ((moduleSupportedSheafExtSpectralSequence R F W I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      ExposeI.H ((moduleLocallyClosedSheafExtFunctor R F W q).obj G) p :=
  (sheafFunctorSpectralSequenceE2Equiv (moduleLocallyClosedSheafHomFunctor R F W) ⊤ I p q).trans
    (supportedCohomologyTopEquiv _ p)

/-- The genuine total interval group. -/
abbrev moduleSupportedSheafExtSpectralTotal {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℤ) :=
  sheafFunctorSpectralTotal (moduleLocallyClosedSheafHomFunctor R F W) ⊤ I n

/-- **VI.1.6.2, abutment:** the original locally supported Ext from VI.1.1. -/
def moduleSupportedSheafExtSpectralAbutmentEquiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleSupportedSheafExtSpectralTotal R F W I n ≃+
      (moduleLocallyClosedSupportedExtFunctor R F W n).obj G := by
  letI : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (op (⊤ : Opens X))).Additive := ExposeI.abelianSheafSections_additive _
  exact (sheafFunctorSpectralAbutmentEquiv
    (moduleLocallyClosedSheafHomFunctor R F W) ⊤ I n).trans
    ((ExposeI.rightDerivedFunctorIso
      (Functor.isoWhiskerLeft (moduleLocallyClosedSheafHomFunctor R F W)
        gammaZTopSectionsFunctorIso) n).app G).addCommGroupIsoToAddEquiv

/-- The genuine finite image filtration of the actual total group. -/
abbrev moduleSupportedSheafExtSpectralFiniteFiltration {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :=
  sheafFunctorSpectralFiniteFiltration (moduleLocallyClosedSheafHomFunctor R F W) ⊤ I n

@[simp]
theorem moduleSupportedSheafExtSpectralFiniteFiltration_zero {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleSupportedSheafExtSpectralFiniteFiltration R F W I n 0 = ⊥ :=
  sheafFunctorSpectralFiniteFiltration_zero _ ⊤ I n

@[simp]
theorem moduleSupportedSheafExtSpectralFiniteFiltration_last {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleSupportedSheafExtSpectralFiniteFiltration R F W I n (Fin.last (n + 1)) = ⊤ :=
  sheafFunctorSpectralFiniteFiltration_last _ ⊤ I n

/-- Genuine consecutive quotients of the canonical total filtration. -/
abbrev moduleSupportedSheafExtSpectralGradedPiece {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n q : ℤ) :=
  sheafFunctorSpectralGradedPiece (moduleLocallyClosedSheafHomFunctor R F W) ⊤ I n q

/-- **VI.1.6.2, finite convergence:** stable pages are actual total-filtration quotients. -/
def moduleSupportedSheafExtSpectralStablePageIsoGraded {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) (q : Fin (n + 1)) (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((moduleSupportedSheafExtSpectralSequence R F W I).page r).X ((n : ℤ) - q, q) ≅
      moduleSupportedSheafExtSpectralGradedPiece R F W I n q :=
  sheafFunctorSpectralStablePageIsoGraded (moduleLocallyClosedSheafHomFunctor R F W) ⊤ I n q r hr

/-- **VI.1.6.2, spectral functor:** the genuine maps of all original page complexes. -/
abbrev moduleSupportedSheafExtSpectralSequenceFunctor :=
  sheafFunctorSpectralSequenceFunctor (moduleLocallyClosedSheafHomFunctor R F W) ⊤

/-- Canonical change of resolution for the entire VI.1.6.2 sequence. -/
abbrev moduleSupportedSheafExtSpectralSequenceResolutionIso {G : SheafOfModules.{u} R}
    (I J : InjectiveResolution G) :=
  sheafFunctorSpectralSequenceResolutionIso (moduleLocallyClosedSheafHomFunctor R F W) ⊤ I J

end SGA.SGA2.ExposeVI
