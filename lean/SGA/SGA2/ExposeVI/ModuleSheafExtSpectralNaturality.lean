/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSheafExtSpectralFunctor
import SGA.SGA2.ExposeVI.SheafFunctorSpectralNaturality

/-!
# SGA 2, VI.1.6.1: original E₂ and abutment coefficient maps

The spectral construction's E₂ and total comparisons retain the unchanged
original sheaf Ext and supported Ext coefficient maps. The proof includes
the explicit comparison between the site and topological sheaf presentations.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (F : SheafOfModules.{u} R)
  (Z : Closeds X) {G H : SheafOfModules.{u} R}
  {I : InjectiveResolution G} {J : InjectiveResolution H}

-- Specialize the proved constructions without unfolding the complete spectral-page data.
attribute [local irreducible] sheafFunctorSpectralSequence
  sheafFunctorSpectralSequenceMap sheafFunctorSpectralSequenceE2ComparedEquiv

/-- The unchanged comparison used by `moduleSheafExtSpectralSequenceE2Equiv` carries
the actual coefficient page map to the original sheaf Ext cohomology map. -/
theorem moduleSheafExtSpectralSequenceE2Equiv_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p q : ℕ)
    (x : ((moduleSheafExtSpectralSequence R F Z I).page 2).X ((p : ℤ), (q : ℤ))) :
    sheafFunctorSpectralSequenceE2ComparedEquiv (moduleSheafHomTopFunctor R F) Z
        (moduleSheafExtAbFunctor R F q) q (moduleSheafHomTopRightDerivedIso R F q) J p
        (((sheafFunctorSpectralSequenceMap
          (moduleSheafHomTopFunctor R F) Z α).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      ExposeI.H_Z_map Z ((moduleSheafExtAbFunctor R F q).map a) p
        (sheafFunctorSpectralSequenceE2ComparedEquiv (moduleSheafHomTopFunctor R F) Z
          (moduleSheafExtAbFunctor R F q) q (moduleSheafHomTopRightDerivedIso R F q) I p x) :=
  sheafFunctorSpectralSequenceE2ComparedEquiv_naturality (moduleSheafHomTopFunctor R F) Z
    (moduleSheafExtAbFunctor R F q) q (moduleSheafHomTopRightDerivedIso R F q)
    (X := X) (C := SheafOfModules.{u} R) (G := G) (H := H) (I := I) (J := J) a α hα p x

/-- The unchanged original total-interval coefficient map. -/
abbrev moduleSheafExtSpectralTotalMap (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ) :=
  sheafFunctorSpectralTotalMap (moduleSheafHomTopFunctor R F) Z α n

/-- The total comparison retains the actual original supported Ext coefficient map. -/
theorem moduleSheafExtSpectralAbutmentEquiv_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (n : ℕ)
    (x : moduleSheafExtSpectralTotal R F Z I n) :
    moduleSheafExtSpectralAbutmentEquiv R F Z J n
        (moduleSheafExtSpectralTotalMap R F Z α n x) =
      (moduleSupportedExtFunctor R F Z n).map a
        (moduleSheafExtSpectralAbutmentEquiv R F Z I n x) :=
  sheafFunctorSpectralAbutmentEquiv_naturality (moduleSheafHomTopFunctor R F) Z a α hα n x

end SGA.SGA2.ExposeVI
