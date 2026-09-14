/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalSpectralFunctoriality
import SGA.SGA2.ExposeI.SpectralSequenceCoefficientMaps

/-! # Actual coefficient morphisms of the supported local-to-global spectral sequence -/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Every actual map of injective resolutions induces a morphism of the
original supported truncation spectral sequences. This morphism respects
all page differentials and the existing homology-to-next-page isomorphisms. -/
def supportedTruncationSpectralSequenceMap (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    supportedTruncationSpectralSequence Z I ⟶ supportedTruncationSpectralSequence Z J :=
  SpectralObjectCoefficientMaps.spectralSequenceMap
    (supportedAbelianSpectralObjectMap Z φ) Abelian.SpectralObject.coreE₂Cohomological

/-- The induced maps commute with each original page differential. -/
@[reassoc]
theorem supportedTruncationSpectralSequenceMap_d (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (r : ℤ) (hr : 2 ≤ r) (pq pq' : ℤ × ℤ) :
    ((supportedTruncationSpectralSequenceMap Z φ).hom r hr).f pq ≫
        ((supportedTruncationSpectralSequence Z J).page r hr).d pq pq' =
      ((supportedTruncationSpectralSequence Z I).page r hr).d pq pq' ≫
        ((supportedTruncationSpectralSequenceMap Z φ).hom r hr).f pq' :=
  ((supportedTruncationSpectralSequenceMap Z φ).hom r hr).comm pq pq'

/-- The induced maps commute with each original homology-to-next-page
isomorphism, in every bidegree. -/
@[reassoc]
theorem supportedTruncationSpectralSequenceMap_next (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (r r' : ℤ) (hr : 2 ≤ r) (hrr' : r + 1 = r')
    (pq : ℤ × ℤ) :
    HomologicalComplex.homologyMap ((supportedTruncationSpectralSequenceMap Z φ).hom r hr) pq ≫
        ((supportedTruncationSpectralSequence Z J).iso r r' pq hrr' hr).hom =
      ((supportedTruncationSpectralSequence Z I).iso r r' pq hrr' hr).hom ≫
        ((supportedTruncationSpectralSequenceMap Z φ).hom r' (by lia)).f pq :=
  (supportedTruncationSpectralSequenceMap Z φ).comm r r' pq hrr' hr

end SGA.SGA2.ExposeI
