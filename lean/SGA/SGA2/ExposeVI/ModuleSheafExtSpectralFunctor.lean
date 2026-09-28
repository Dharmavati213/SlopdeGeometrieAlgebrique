/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSheafExtSpectralSequence
import SGA.SGA2.ExposeVI.SheafFunctorSpectralFunctor

/-!
# SGA 2, VI.1.6.1: the actual coefficient spectral functor

The generic coefficient construction is applied to the original local linear
Hom functor. Actual resolution maps induce maps on every page and commute
with differentials and next-page homology. Homotopies prove independence of
lifts and canonical change of injective resolution.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (F : SheafOfModules.{u} R)
  {G H : SheafOfModules.{u} R} {I : InjectiveResolution G} {J : InjectiveResolution H}

/-- The actual map of the local linear Hom resolution complexes. -/
abbrev moduleSheafHomResolutionIntMap (a : I.cocomplex ⟶ J.cocomplex) :=
  sheafFunctorResolutionIntMap (moduleSheafHomTopFunctor R F) a

/-- The actual localized map on derived local linear Hom. -/
abbrev moduleSheafHomDerivedObjectMap (a : I.cocomplex ⟶ J.cocomplex) :=
  sheafFunctorDerivedObjectMap (moduleSheafHomTopFunctor R F) a

variable (Z : Closeds X)

/-- The original coefficient map on the genuine truncation spectral objects. -/
abbrev moduleSheafExtAbelianSpectralObjectMap (a : I.cocomplex ⟶ J.cocomplex) :=
  sheafFunctorSpectralAbelianSpectralObjectMap
    (moduleSheafHomTopFunctor R F) Z a

/-- The actual map of all page complexes and homology-to-next-page isomorphisms. -/
abbrev moduleSheafExtSpectralSequenceMap (a : I.cocomplex ⟶ J.cocomplex) :=
  sheafFunctorSpectralSequenceMap (moduleSheafHomTopFunctor R F) Z a

/-- Coefficient maps computed on arbitrary chosen module-injective resolutions. -/
abbrev moduleSheafExtSpectralSequenceCoefficientMap (a : G ⟶ H)
    (I : InjectiveResolution G) (J : InjectiveResolution H) :=
  sheafFunctorSpectralSequenceCoefficientMap
    (moduleSheafHomTopFunctor R F) Z a I J

/-- **VI.1.6.1, spectral functor:** genuine functoriality of the entire spectral sequence. -/
abbrev moduleSheafExtSpectralSequenceFunctor :=
  sheafFunctorSpectralSequenceFunctor (moduleSheafHomTopFunctor R F) Z

/-- Canonical change of resolution, as an isomorphism of the entire spectral sequence. -/
abbrev moduleSheafExtSpectralSequenceResolutionIso (I J : InjectiveResolution G) :=
  sheafFunctorSpectralSequenceResolutionIso
    (moduleSheafHomTopFunctor R F) Z I J

end SGA.SGA2.ExposeVI
