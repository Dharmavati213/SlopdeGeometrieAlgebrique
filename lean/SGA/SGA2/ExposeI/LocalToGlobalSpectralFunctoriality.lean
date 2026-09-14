/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalTotalCohomology

/-!
# Coefficient morphisms of the actual supported spectral objects

An actual chain map of resolutions induces maps of supported complexes,
their derived objects, and the full triangulated and abelian spectral
objects. In particular these maps commute with all connecting morphisms.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex
open ComposableArrows

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

section

variable {C A ι : Type*} [Category C] [Category A] [Category ι]
  [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [Abelian A]

/-- Apply a homological functor to an actual map of triangulated spectral
objects. Compatibility with connecting maps follows from triangle naturality. -/
def homologicalSpectralObjectMap {S T : Triangulated.SpectralObject C ι}
    (φ : S ⟶ T) (P : C ⥤ A) [P.IsHomological] [P.ShiftSequence ℤ] :
    homologicalSpectralObject S P ⟶ homologicalSpectralObject T P where
  hom n := Functor.whiskerRight φ.hom (P.shift n)
  comm n m h i j k f g := by
    let ψ : S.triangle f g ⟶ T.triangle f g :=
      { hom₁ := φ.hom.app (mk₁ f)
        hom₂ := φ.hom.app (mk₁ (f ≫ g))
        hom₃ := φ.hom.app (mk₁ g)
        comm₁ := φ.hom.naturality _
        comm₂ := φ.hom.naturality _
        comm₃ := φ.comm f g }
    exact (P.homologySequenceδ_naturality (S.triangle f g) (T.triangle f g) ψ n m h).symm

/-- The genuine bridge from triangulated to abelian spectral objects is a
functor, not just a construction on objects. -/
def homologicalSpectralObjectFunctor (P : C ⥤ A) [P.IsHomological] [P.ShiftSequence ℤ] :
    Triangulated.SpectralObject C ι ⥤ Abelian.SpectralObject A ι where
  obj S := homologicalSpectralObject S P
  map φ := homologicalSpectralObjectMap φ P
  map_id S := by
    apply Abelian.SpectralObject.Hom.ext
    funext n
    ext D
    simp [homologicalSpectralObjectMap]
    rfl
  map_comp φ ψ := by
    apply Abelian.SpectralObject.Hom.ext
    funext n
    ext D
    simp [homologicalSpectralObjectMap]

end

variable {X : TopCat.{u}}

local instance supportedFunctoriality_hasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

/-- Apply the original support functor to a chain map of resolutions. -/
def supportedSheafResolutionMap (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    supportedSheafResolution Z I ⟶ supportedSheafResolution Z J :=
  ((underlineGammaZFunctor Z).mapHomologicalComplex _).map φ

/-- The actual integer-indexed supported chain map. -/
def supportedSheafResolutionIntMap (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    supportedSheafResolutionInt Z I ⟶ supportedSheafResolutionInt Z J :=
  HomologicalComplex.extendMap (supportedSheafResolutionMap Z φ) ComplexShape.embeddingUpNat

/-- The induced morphism of the actual supported derived objects. -/
def supportedDerivedObjectMap (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    supportedDerivedObject Z I ⟶ supportedDerivedObject Z J :=
  DerivedCategory.Q.map (supportedSheafResolutionIntMap Z φ)

/-- The actual coefficient morphism of the full supported triangulated
spectral objects, obtained from the canonical truncation functor. -/
def supportedTriangulatedSpectralObjectMap (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    supportedLocalToGlobalTriangulatedSpectralObject Z I ⟶
      supportedLocalToGlobalTriangulatedSpectralObject Z J :=
  (DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} X)).spectralObjectFunctor.map
    (supportedDerivedObjectMap Z φ)

/-- The actual coefficient morphism of the full supported abelian spectral
objects. It preserves all connecting maps in all degrees and intervals. -/
def supportedAbelianSpectralObjectMap (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    supportedLocalToGlobalAbelianSpectralObject Z I ⟶
      supportedLocalToGlobalAbelianSpectralObject Z J :=
  homologicalSpectralObjectMap (supportedTriangulatedSpectralObjectMap Z φ)
    supportedDerivedGlobalHom

/-- On the total interval, the spectral-object map is actual postcomposition
with the shifted supported derived morphism. -/
theorem supportedAbelianSpectralObjectMap_total_apply (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℤ)
    (x : (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X) ⟶
      (supportedDerivedObject Z I)⟦n⟧) :
    ((supportedAbelianSpectralObjectMap Z φ).hom n).app
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) x =
      x ≫ (supportedDerivedObjectMap Z φ)⟦n⟧' := rfl

end SGA.SGA2.ExposeI
