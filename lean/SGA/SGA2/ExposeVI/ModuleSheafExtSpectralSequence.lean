/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSheafHomSpectralPresentation
import SGA.SGA2.ExposeVI.ModuleHomInjectiveFlasque
import SGA.SGA2.ExposeVI.SheafFunctorSpectralSequence

/-!
# SGA 2, VI.1.6.1: supported cohomology of actual module sheaf Ext

The genuine truncation construction is applied to the actual sheaf of local
linear maps from `F` into a module-injective resolution of `G`. Its actual
E₂ terms are supported cohomology of the original sheaf Ext, and VI.1.5
identifies its finitely filtered total with the original supported Ext.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (F : SheafOfModules.{u} R)

/-- The actual integer-indexed complex of sheaves of local linear maps. -/
abbrev moduleSheafHomResolutionInt {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :=
  sheafFunctorResolutionInt (moduleSheafHomTopFunctor R F) I

/-- VI.1.5 applies to every term of the actual module-injective resolution. -/
instance {G : SheafOfModules.{u} R} (I : InjectiveResolution G) (n : ℤ) :
    ExposeI.IsFlasque ((moduleSheafHomResolutionInt R F I).X n) :=
  moduleSheafHomAb_isFlasque_of_injective R F (I.cochainComplex.X n)

/-- The actual derived object of local linear Hom on the module resolution. -/
abbrev moduleSheafHomDerivedObject {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :=
  sheafFunctorDerivedObject (moduleSheafHomTopFunctor R F) I

/-- Its cohomology sheaves are the original right-derived sheaf Hom values. -/
abbrev moduleSheafHomDerivedHomologyIso {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (q : ℕ) :=
  sheafFunctorDerivedHomologyIso (moduleSheafHomTopFunctor R F) I q

/-- All genuine canonical truncations and distinguished interval triangles. -/
abbrev moduleSheafExtTriangulatedSpectralObject {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) :=
  sheafFunctorSpectralTriangulatedSpectralObject
    (moduleSheafHomTopFunctor R F) I

/-- Derived Hom from the original integer support sheaf. -/
abbrev moduleSheafExtDerivedSupportedHom (Z : Closeds X) := sheafFunctorDerivedSupportedHom Z

variable (Z : Closeds X)

/-- The genuine abelian spectral object for VI.1.6.1. -/
abbrev moduleSheafExtAbelianSpectralObject {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) :=
  sheafFunctorSpectralAbelianSpectralObject
    (moduleSheafHomTopFunctor R F) Z I

/-- **VI.1.6.1:** all actual pages, differentials and next-page homology isomorphisms. -/
abbrev moduleSheafExtSpectralSequence {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) :=
  sheafFunctorSpectralSequence (moduleSheafHomTopFunctor R F) Z I

/-- The one-degree interval is the actual sheaf Ext in its original degree. -/
abbrev moduleSheafExtE2TruncationIso {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (q : ℕ) :=
  sheafFunctorSpectralE2TruncationIso
    (moduleSheafHomTopFunctor R F) I q

/-- **VI.1.6.1, E₂:** terms of the constructed page are supported cohomology of sheaf Ext. -/
def moduleSheafExtSpectralSequenceE2Equiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (p q : ℕ) :
    ((moduleSheafExtSpectralSequence R F Z I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      ExposeI.H_Z Z ((moduleSheafExtAbFunctor R F q).obj G) p :=
  sheafFunctorSpectralSequenceE2ComparedEquiv (moduleSheafHomTopFunctor R F) Z
    (moduleSheafExtAbFunctor R F q) q (moduleSheafHomTopRightDerivedIso R F q) I p

/-- The genuine total interval group, with its canonical image filtration. -/
abbrev moduleSheafExtSpectralTotal {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℤ) :=
  sheafFunctorSpectralTotal (moduleSheafHomTopFunctor R F) Z I n

/-- **VI.1.6.1, abutment:** flasque Hom terms compute original supported Ext. -/
def moduleSheafExtSpectralAbutmentEquiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleSheafExtSpectralTotal R F Z I n ≃+ (moduleSupportedExtFunctor R F Z n).obj G :=
  sheafFunctorSpectralAbutmentEquiv
    (moduleSheafHomTopFunctor R F) Z I n

/-- The finite increasing filtration of the actual total group. -/
abbrev moduleSheafExtSpectralFiniteFiltration {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :=
  sheafFunctorSpectralFiniteFiltration
    (moduleSheafHomTopFunctor R F) Z I n

@[simp]
theorem moduleSheafExtSpectralFiniteFiltration_zero {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleSheafExtSpectralFiniteFiltration R F Z I n 0 = ⊥ :=
  sheafFunctorSpectralFiniteFiltration_zero _ Z I n

@[simp]
theorem moduleSheafExtSpectralFiniteFiltration_last {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleSheafExtSpectralFiniteFiltration R F Z I n (Fin.last (n + 1)) = ⊤ :=
  sheafFunctorSpectralFiniteFiltration_last _ Z I n

/-- Genuine consecutive quotients of the actual total filtration. -/
abbrev moduleSheafExtSpectralGradedPiece {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n q : ℤ) :=
  sheafFunctorSpectralGradedPiece
    (moduleSheafHomTopFunctor R F) Z I n q

/-- **VI.1.6.1, finite convergence:** the stable pages are actual graded quotients. -/
def moduleSheafExtSpectralStablePageIsoGraded {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) (q : Fin (n + 1)) (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((moduleSheafExtSpectralSequence R F Z I).page r).X ((n : ℤ) - q, q) ≅
      moduleSheafExtSpectralGradedPiece R F Z I n q :=
  sheafFunctorSpectralStablePageIsoGraded
    (moduleSheafHomTopFunctor R F) Z I n q r hr

end SGA.SGA2.ExposeVI
