/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.SpectralSequenceCoefficientMaps
import SGA.SGA2.ExposeI.SpectralSequenceFirstPageExt

/-! # Functor laws for the original spectral-object coefficient maps -/

noncomputable section

open CategoryTheory Limits ComposableArrows
open CategoryTheory.Abelian.SpectralObject

namespace SGA.SGA2.ExposeI.SpectralObjectCoefficientMaps

variable {C : Type*} [Category C] [Abelian C]

unseal Abelian.SpectralObject.spectralSequence in
@[simp]
theorem spectralSequenceMap_id (S : Abelian.SpectralObject C EInt) :
    spectralSequenceMap (𝟙 S) coreE₂Cohomological = 𝟙 S.E₂SpectralSequence := by
  apply spectralSequence_hom_ext_firstPage_f
  intro pq
  change ShortComplex.homologyMap (𝟙 _) = 𝟙 _
  exact ShortComplex.homologyMap_id _

unseal Abelian.SpectralObject.spectralSequence in
@[reassoc]
theorem spectralSequenceMap_comp {S T U : Abelian.SpectralObject C EInt}
    (a : S ⟶ T) (b : T ⟶ U) :
    spectralSequenceMap (a ≫ b) coreE₂Cohomological =
      spectralSequenceMap a coreE₂Cohomological ≫
        spectralSequenceMap b coreE₂Cohomological := by
  apply spectralSequence_hom_ext_firstPage_f
  intro pq
  change ShortComplex.homologyMap
      (shortComplexMap a _ _ _ _ _ _ _ _ ≫ shortComplexMap b _ _ _ _ _ _ _ _) = _
  exact ShortComplex.homologyMap_comp _ _

/-- The existing E₂ spectral-sequence construction with its original coefficient maps. -/
def spectralObjectE2Functor :
    Abelian.SpectralObject C EInt ⥤ E₂CohomologicalSpectralSequence C where
  obj S := S.E₂SpectralSequence
  map a := spectralSequenceMap a coreE₂Cohomological
  map_id := spectralSequenceMap_id
  map_comp := spectralSequenceMap_comp

end SGA.SGA2.ExposeI.SpectralObjectCoefficientMaps
