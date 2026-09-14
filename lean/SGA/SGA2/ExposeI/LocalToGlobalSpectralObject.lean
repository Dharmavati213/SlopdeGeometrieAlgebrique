/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalResolution
import SGA.SGA2.ExposeI.SupportedSheafInjective
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject

/-!
# The genuine truncation spectral object of the supported resolution

The actual supported resolution is termwise injective. Its extension by zero
to integer degrees is K-injective and determines an object of the constructed
derived category. Its cohomology sheaves are the original `derivedUnderlineGammaZ`.
The canonical t-structure gives a genuine triangulated spectral object of its
truncations, with actual distinguished triangles.

The companion `LocalToGlobalSpectralSequence` applies cohomological derived
Hom and constructs all pages and differentials. `LocalToGlobalE2` identifies
the actual E₂ terms; `LocalToGlobalConvergence` supplies the finite abutment
filtration and convergence. Full coefficient compatibility of E₂ and page
morphisms remains separate from these objectwise constructions.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Each term of the actual supported resolution is injective. -/
instance supportedSheafResolution_injective (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (q : ℕ) :
    Injective ((supportedSheafResolution Z I).X q) := by
  change Injective ((underlineGammaZFunctor Z).obj (I.cocomplex.X q))
  infer_instance

/-- Extend the actual nonnegative supported resolution by zero in negative
degrees. -/
def supportedSheafResolutionInt (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ :=
  (supportedSheafResolution Z I).extend ComplexShape.embeddingUpNat

instance supportedSheafResolutionInt_isStrictlyGE (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    (supportedSheafResolutionInt Z I).IsStrictlyGE 0 := by
  dsimp [supportedSheafResolutionInt]
  infer_instance

/-- The integer-indexed supported resolution is genuinely K-injective. -/
instance supportedSheafResolutionInt_isKInjective (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    (supportedSheafResolutionInt Z I).IsKInjective := by
  dsimp [supportedSheafResolutionInt]
  infer_instance

local instance supportedSheaves_hasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

/-- The actual supported resolution as an object of the constructed derived
category, with no assumed localization or derived-category model. -/
def supportedDerivedObject (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    DerivedCategory (Sheaf AddCommGrpCat.{u} X) :=
  DerivedCategory.Q.obj (supportedSheafResolutionInt Z I)

instance supportedDerivedObject_isGE (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    (supportedDerivedObject Z I).IsGE 0 := by
  dsimp [supportedDerivedObject]
  infer_instance

/-- The cohomology sheaves of the actual supported derived object are exactly
the original right-derived supported sheaves. -/
def supportedDerivedObjectHomologyIso (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (q : ℕ) :
    (DerivedCategory.homologyFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).obj
        (supportedDerivedObject Z I) ≅ (derivedUnderlineGammaZ Z q).obj F :=
  (DerivedCategory.homologyFunctorFactors (Sheaf AddCommGrpCat.{u} X)
    (q : ℤ)).app (supportedSheafResolutionInt Z I) ≪≫
      (supportedSheafResolution Z I).extendHomologyIso ComplexShape.embeddingUpNat
        (j := q) (j' := (q : ℤ)) rfl ≪≫
      supportedSheafResolutionHomologyIso Z I q

/-- Negative cohomology of the supported derived object vanishes. -/
theorem supportedDerivedObject_negative_isZero (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (q : ℤ) (hq : q < 0) :
    IsZero ((DerivedCategory.homologyFunctor (Sheaf AddCommGrpCat.{u} X) q).obj
      (supportedDerivedObject Z I)) :=
  DerivedCategory.isZero_of_isGE _ 0 q hq

/-- The genuine triangulated spectral object given by all canonical
truncations of the actual supported derived object. -/
def supportedLocalToGlobalTriangulatedSpectralObject (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    Triangulated.SpectralObject (DerivedCategory (Sheaf AddCommGrpCat.{u} X)) EInt :=
  (DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} X)).spectralObject
    (supportedDerivedObject Z I)

/-- The canonical triangles of the supported truncation spectral object are
distinguished, proved by the t-structure construction. -/
theorem supportedLocalToGlobalTriangulatedSpectralObject_distinguished (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    {a b c : EInt} (f : a ⟶ b) (g : b ⟶ c) :
    (supportedLocalToGlobalTriangulatedSpectralObject Z I).triangle f g ∈
      distTriang (DerivedCategory (Sheaf AddCommGrpCat.{u} X)) :=
  (supportedLocalToGlobalTriangulatedSpectralObject Z I).triangle_distinguished f g

end SGA.SGA2.ExposeI
