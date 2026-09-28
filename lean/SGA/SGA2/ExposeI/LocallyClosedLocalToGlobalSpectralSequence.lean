/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedLocalToGlobalResolution
import SGA.SGA2.ExposeI.LocalToGlobalE2

/-!
# The actual ambient local-to-global spectral sequence for locally closed support

The unchanged ambient support functor is applied to an injective resolution.
Its integer extension is K-injective and connective. Canonical truncations and
derived Hom from the ambient constant sheaf construct the genuine spectral
object and all pages. The actual E₂ terms are ordinary cohomology on X of the
original ambient derived locally closed supported sheaves.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex
open ComposableArrows

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Extend the actual nonnegative supported resolution by zero in negative
degrees. -/
def locallyClosedSupportedSheafResolutionInt (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ :=
  (locallyClosedSupportedSheafResolution W I).extend ComplexShape.embeddingUpNat

instance locallyClosedSupportedSheafResolutionInt_isStrictlyGE (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    (locallyClosedSupportedSheafResolutionInt W I).IsStrictlyGE 0 := by
  dsimp [locallyClosedSupportedSheafResolutionInt]
  infer_instance

/-- The integer-indexed supported resolution is genuinely K-injective. -/
instance locallyClosedSupportedSheafResolutionInt_isKInjective (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    (locallyClosedSupportedSheafResolutionInt W I).IsKInjective := by
  dsimp [locallyClosedSupportedSheafResolutionInt]
  infer_instance

attribute [local instance] supportedE2_hasDerivedCategory

/-- The actual supported resolution as an object of the constructed derived
category, with no assumed localization or derived-category model. -/
def locallyClosedSupportedDerivedObject (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    DerivedCategory (Sheaf AddCommGrpCat.{u} X) :=
  DerivedCategory.Q.obj (locallyClosedSupportedSheafResolutionInt W I)

instance locallyClosedSupportedDerivedObject_isGE (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    (locallyClosedSupportedDerivedObject W I).IsGE 0 := by
  dsimp [locallyClosedSupportedDerivedObject]
  infer_instance

/-- The cohomology sheaves of the actual supported derived object are exactly
the original right-derived supported sheaves. -/
def locallyClosedSupportedDerivedObjectHomologyIso (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (q : ℕ) :
    (DerivedCategory.homologyFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).obj
        (locallyClosedSupportedDerivedObject W I) ≅
      (derivedUnderlineGammaLocallyClosed W q).obj F :=
  (DerivedCategory.homologyFunctorFactors (Sheaf AddCommGrpCat.{u} X)
    (q : ℤ)).app (locallyClosedSupportedSheafResolutionInt W I) ≪≫
      (locallyClosedSupportedSheafResolution W I).extendHomologyIso ComplexShape.embeddingUpNat
        (j := q) (j' := (q : ℤ)) rfl ≪≫
      locallyClosedSupportedSheafResolutionHomologyIso W I q

/-- Negative cohomology of the supported derived object vanishes. -/
theorem locallyClosedSupportedDerivedObject_negative_isZero (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (q : ℤ) (hq : q < 0) :
    IsZero ((DerivedCategory.homologyFunctor (Sheaf AddCommGrpCat.{u} X) q).obj
      (locallyClosedSupportedDerivedObject W I)) :=
  DerivedCategory.isZero_of_isGE _ 0 q hq

/-- The genuine triangulated spectral object given by all canonical
truncations of the actual supported derived object. -/
def locallyClosedLocalToGlobalTriangulatedSpectralObject (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    Triangulated.SpectralObject (DerivedCategory (Sheaf AddCommGrpCat.{u} X)) EInt :=
  (DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} X)).spectralObject
    (locallyClosedSupportedDerivedObject W I)

/-- The canonical triangles of the supported truncation spectral object are
distinguished, proved by the t-structure construction. -/
theorem locallyClosedLocalToGlobalTriangulatedSpectralObject_distinguished (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    {a b c : EInt} (f : a ⟶ b) (g : b ⟶ c) :
    (locallyClosedLocalToGlobalTriangulatedSpectralObject W I).triangle f g ∈
      distTriang (DerivedCategory (Sheaf AddCommGrpCat.{u} X)) :=
  (locallyClosedLocalToGlobalTriangulatedSpectralObject W I).triangle_distinguished f g


/-- The actual ambient abelian spectral object from canonical truncations. -/
def locallyClosedLocalToGlobalAbelianSpectralObject (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    Abelian.SpectralObject AddCommGrpCat.{u + 1} EInt :=
  homologicalSpectralObject (locallyClosedLocalToGlobalTriangulatedSpectralObject W I)
    supportedDerivedGlobalHom

/-- The genuine ambient spectral sequence, including all differential and
next-page data, for arbitrary locally closed support. -/
def locallyClosedTruncationSpectralSequence (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  (locallyClosedLocalToGlobalAbelianSpectralObject W I).E₂SpectralSequence

/-- The single-degree truncation interval is the single complex of the
original ambient locally closed derived supported sheaf. -/
def locallyClosedE2TruncationIso (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (q : ℕ) :
    (locallyClosedLocalToGlobalTriangulatedSpectralObject W I).ω₁.obj
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) by
          exact WithBotTop.coe_le_coe.mpr (by lia)))) ≅
      (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).obj
        ((derivedUnderlineGammaLocallyClosed W q).obj F) :=
  derivedSingleDegreeTruncationIsoSingle (locallyClosedSupportedDerivedObject W I) (q : ℤ) ≪≫
    (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).mapIso
      (locallyClosedSupportedDerivedObjectHomologyIso W I q)

/-- The shifted single-degree truncation in the actual E₂ computation. -/
def locallyClosedE2TotalShiftIso (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (p q : ℕ) :=
  (shiftFunctor (DerivedCategory (Sheaf AddCommGrpCat.{u} X))
    ((p : ℤ) + (q : ℤ))).mapIso (locallyClosedE2TruncationIso W I q) ≪≫
      supportedSingleTotalShiftIso ((derivedUnderlineGammaLocallyClosed W q).obj F)
        (p : ℤ) (q : ℤ)

/-- The actual first-page interval isomorphism. -/
def locallyClosedE2FirstPageIso (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (p q : ℕ) :=
  (locallyClosedLocalToGlobalAbelianSpectralObject W I).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂Cohomological ((p : ℤ), (q : ℤ))
    (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl

/-- **I.2.6, locally closed E₂:** the actual terms are ordinary cohomology
on the ambient X of the original ambient derived supported sheaves. -/
def locallyClosedTruncationSpectralSequenceE2Equiv (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (p q : ℕ) :
    ((locallyClosedTruncationSpectralSequence W I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      H ((derivedUnderlineGammaLocallyClosed W q).obj F) p := by
  let eHom := (preadditiveCoyoneda.obj
    (op ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj
      (constantZ X)))).mapIso (locallyClosedE2TotalShiftIso W I p q)
  exact (locallyClosedE2FirstPageIso W I p q).addCommGroupIsoToAddEquiv.trans
    (eHom.addCommGroupIsoToAddEquiv.trans
      (supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaLocallyClosed W q).obj F) p))

end SGA.SGA2.ExposeI
