/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalFirstQuadrant
import SGA.SGA2.ExposeI.HomComplexSingleComparison
import SGA.SGA2.ExposeI.FlasqueVanishingCriterion

/-!
# The total cohomology of the actual supported spectral object

K-injectivity of the supported resolution identifies its actual derived Hom
with the cohomology of its global-sections complex, hence with the original
Ext-defined supported cohomology `H_Z`. The total interval of the constructed
spectral object therefore has precisely the required groups.

This file gives the total-group comparison. The companion
`LocalToGlobalConvergence` constructs the finite abutment filtration and
stable-page associated-graded comparison; `LocalToGlobalTotalNaturality`
proves compatibility with actual coefficient maps of resolutions.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex
open ComposableArrows

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

local instance supportedTotal_hasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

/-- The original constant integer sheaf represents actual global sections,
as an additive natural isomorphism. -/
def constantZHomFunctorIso :
    preadditiveCoyoneda.obj (op (constantZ X)) ≅
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X)) :=
  NatIso.ofComponents (fun F => (constantZHomEquiv F).toAddCommGrpIso)
    (by intro F G f; ext g; rfl)

/-- The genuine Hom complex of the supported integer resolution is the
extension by zero of its actual global-sections complex. -/
def supportedHomComplexIsoGlobalSections (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X))
        (supportedSheafResolutionInt Z I) ≅
      (supportedGlobalSectionsComplex Z I).extend ComplexShape.embeddingUpNat := by
  letI : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : Opens X))).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact homComplexFromSingleIso (constantZ X) (supportedSheafResolutionInt Z I) ≪≫
    (NatIso.mapHomologicalComplex (constantZHomFunctorIso (X := X)) (ComplexShape.up ℤ)).app
      (supportedSheafResolutionInt Z I) ≪≫
    mapExtendIso
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X))) ComplexShape.embeddingUpNat (supportedSheafResolution Z I)

/-- Actual derived global Hom of the supported derived object identifies
additively with the original `H_Z`, including its smaller universe. -/
def supportedDerivedTotalHomEquivH_Z (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    (((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X)) ⟶
      (supportedDerivedObject Z I)⟦(n : ℤ)⟧) ≃+ H_Z Z F n :=
  (homComplexHomologyDerivedHomEquiv
    ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X))
    (supportedSheafResolutionInt Z I) (n : ℤ)).symm.trans
      (((homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (n : ℤ)).mapIso
          (supportedHomComplexIsoGlobalSections Z I) ≪≫
        (supportedGlobalSectionsComplex Z I).extendHomologyIso ComplexShape.embeddingUpNat
          (j := n) (j' := (n : ℤ)) rfl ≪≫
        supportedGlobalSectionsComplexHomologyIso Z I n).addCommGroupIsoToAddEquiv)

/-- The total interval of the actual constructed spectral object has exactly
the original supported cohomology as its cohomology groups. -/
def supportedSpectralObjectTotalEquivH_Z (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    ((supportedLocalToGlobalAbelianSpectralObject Z I).H (n : ℤ)).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) ≃+ H_Z Z F n :=
  supportedDerivedTotalHomEquivH_Z Z I n

end SGA.SGA2.ExposeI
