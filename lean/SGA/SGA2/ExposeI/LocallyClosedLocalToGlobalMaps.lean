/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedLocalToGlobalConvergence
import SGA.SGA2.ExposeI.LocalToGlobalSpectralFunctoriality
import SGA.SGA2.ExposeI.SpectralSequenceCoefficientMaps

/-! # Actual coefficient maps of ambient locally closed local-to-global spectral sequences -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex
open ComposableArrows

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

attribute [local instance] supportedE2_hasDerivedCategory

/-- Coefficient maps on the original ambient Ext-defined locally closed support groups. -/
def H_locallyClosed_map (W : LocallyClosedIn X) {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) : H_locallyClosed W F n →+ H_locallyClosed W G n :=
  (Abelian.Ext.mk₀ f).postcomp (zZX_locallyClosed W) (add_zero n)

/-- Apply the original support functor to a chain map of resolutions. -/
def locallyClosedSupportedSheafResolutionMap (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    locallyClosedSupportedSheafResolution W I ⟶ locallyClosedSupportedSheafResolution W J :=
  ((underlineGammaLocallyClosedFunctor W).mapHomologicalComplex _).map φ

/-- The actual integer-indexed supported chain map. -/
def locallyClosedSupportedSheafResolutionIntMap (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    locallyClosedSupportedSheafResolutionInt W I ⟶ locallyClosedSupportedSheafResolutionInt W J :=
  HomologicalComplex.extendMap (locallyClosedSupportedSheafResolutionMap W φ)
    ComplexShape.embeddingUpNat

/-- The induced morphism of the actual supported derived objects. -/
def locallyClosedSupportedDerivedObjectMap (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    locallyClosedSupportedDerivedObject W I ⟶ locallyClosedSupportedDerivedObject W J :=
  DerivedCategory.Q.map (locallyClosedSupportedSheafResolutionIntMap W φ)

/-- The actual coefficient morphism of the full supported triangulated
spectral objects, obtained from the canonical truncation functor. -/
def locallyClosedTriangulatedSpectralObjectMap (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    locallyClosedLocalToGlobalTriangulatedSpectralObject W I ⟶
      locallyClosedLocalToGlobalTriangulatedSpectralObject W J :=
  (DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} X)).spectralObjectFunctor.map
    (locallyClosedSupportedDerivedObjectMap W φ)

/-- The actual coefficient morphism of the full supported abelian spectral
objects. It preserves all connecting maps in all degrees and intervals. -/
def locallyClosedAbelianSpectralObjectMap (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    locallyClosedLocalToGlobalAbelianSpectralObject W I ⟶
      locallyClosedLocalToGlobalAbelianSpectralObject W J :=
  homologicalSpectralObjectMap (locallyClosedTriangulatedSpectralObjectMap W φ)
    supportedDerivedGlobalHom

/-- On the total interval, the spectral-object map is actual postcomposition
with the shifted supported derived morphism. -/
theorem locallyClosedAbelianSpectralObjectMap_total_apply (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℤ)
    (x : (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X) ⟶
      (locallyClosedSupportedDerivedObject W I)⟦n⟧) :
    ((locallyClosedAbelianSpectralObjectMap W φ).hom n).app
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) x =
      x ≫ (locallyClosedSupportedDerivedObjectMap W φ)⟦n⟧' := rfl

/-- Every actual map of injective resolutions induces a morphism of the
original supported truncation spectral sequences. This morphism respects
all page differentials and the existing homology-to-next-page isomorphisms. -/
def locallyClosedTruncationSpectralSequenceMap (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    locallyClosedTruncationSpectralSequence W I ⟶ locallyClosedTruncationSpectralSequence W J :=
  SpectralObjectCoefficientMaps.spectralSequenceMap
    (locallyClosedAbelianSpectralObjectMap W φ) Abelian.SpectralObject.coreE₂Cohomological

/-- The induced maps commute with each original page differential. -/
@[reassoc]
theorem locallyClosedTruncationSpectralSequenceMap_d (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (r : ℤ) (hr : 2 ≤ r) (pq pq' : ℤ × ℤ) :
    ((locallyClosedTruncationSpectralSequenceMap W φ).hom r hr).f pq ≫
        ((locallyClosedTruncationSpectralSequence W J).page r hr).d pq pq' =
      ((locallyClosedTruncationSpectralSequence W I).page r hr).d pq pq' ≫
        ((locallyClosedTruncationSpectralSequenceMap W φ).hom r hr).f pq' :=
  ((locallyClosedTruncationSpectralSequenceMap W φ).hom r hr).comm pq pq'

/-- The induced maps commute with each original homology-to-next-page
isomorphism, in every bidegree. -/
@[reassoc]
theorem locallyClosedTruncationSpectralSequenceMap_next (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (r r' : ℤ) (hr : 2 ≤ r) (hrr' : r + 1 = r')
    (pq : ℤ × ℤ) :
    HomologicalComplex.homologyMap ((locallyClosedTruncationSpectralSequenceMap W φ).hom r hr) pq ≫
        ((locallyClosedTruncationSpectralSequence W J).iso r r' pq hrr' hr).hom =
      ((locallyClosedTruncationSpectralSequence W I).iso r r' pq hrr' hr).hom ≫
        ((locallyClosedTruncationSpectralSequenceMap W φ).hom r' (by lia)).f pq :=
  (locallyClosedTruncationSpectralSequenceMap W φ).comm r r' pq hrr' hr

end SGA.SGA2.ExposeI
