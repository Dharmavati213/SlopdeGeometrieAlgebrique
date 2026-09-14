/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedLocalToGlobalSpectralSequence
import SGA.SGA2.ExposeI.LocalToGlobalTotalCohomology
import SGA.SGA2.ExposeI.SpectralObjectConvergence

/-!
# Genuine convergence for arbitrary locally closed support on the ambient space

The actual ambient supported complex is connective and K-injective. Its derived
global Hom computes the original Ext-defined locally closed support cohomology.
First-quadrant vanishing gives a finite filtration of that total group and
identifies genuine stable pages with its actual associated-graded cokernels.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex
open ComposableArrows

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

attribute [local instance] supportedE2_hasDerivedCategory

/-- First-quadrant support for the actual spectral object, not an additional
assumption on its pages. -/
instance locallyClosedLocalToGlobalAbelianSpectralObject_isFirstQuadrant (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    (locallyClosedLocalToGlobalAbelianSpectralObject W I).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    let t := DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} X)
    have h := t.isZero_eTruncLT_obj_obj (locallyClosedSupportedDerivedObject W I) 0 j hj
    have h' := (t.eTruncGE.obj i).map_isZero h
    exact ((supportedDerivedGlobalHom (X := X)).shift n).map_isZero h'
  isZero₂ i j hij n hi := by
    let t := DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} X)
    have hni : ((n + 1 : ℤ) : EInt) ≤ i := by
      induction i using WithBotTop.rec with
      | bot => simp at hi
      | coe i =>
        simp only [WithBotTop.coe_le_coe, WithBotTop.coe_lt_coe] at *
        lia
      | top => exact le_top
    have hge := t.isGE_eTruncGE_obj_obj (n + 1) i hni
      ((t.eTruncLT.obj j).obj (locallyClosedSupportedDerivedObject W I))
    have hshift := t.isGE_shift
      ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj (locallyClosedSupportedDerivedObject W I)))
      (n + 1) n 1 (by lia)
    change IsZero (AddCommGrpCat.of
      (((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X)) ⟶
        ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj
          (locallyClosedSupportedDerivedObject W I)))⟦n⟧))
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact ⟨fun f g => (t.zero f 0 1).trans (t.zero g 0 1).symm⟩

/-- On every page Eᵣ with r ≥ 2, negative second degree vanishes. -/
theorem locallyClosedTruncationSpectralSequence_isZero_of_second_neg (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hq : q < 0) :
    IsZero (((locallyClosedTruncationSpectralSequence W I).page r).X (p, q)) :=
  Abelian.SpectralObject.isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr _
    ((locallyClosedLocalToGlobalAbelianSpectralObject W I).isZero₁_of_isFirstQuadrant
      _ _ _ (by simp; lia) _)

/-- On every page Eᵣ with r ≥ 2, negative first degree vanishes. -/
theorem locallyClosedTruncationSpectralSequence_isZero_of_first_neg (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hp : p < 0) :
    IsZero (((locallyClosedTruncationSpectralSequence W I).page r).X (p, q)) :=
  Abelian.SpectralObject.isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr _
    ((locallyClosedLocalToGlobalAbelianSpectralObject W I).isZero₂_of_isFirstQuadrant
      _ _ _ _ (by simp; lia))

/-- The genuine Hom complex of the supported integer resolution is the
extension by zero of its actual global-sections complex. -/
def locallyClosedSupportedHomComplexIsoGlobalSections (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    CochainComplex.HomComplex
        ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X))
        (locallyClosedSupportedSheafResolutionInt W I) ≅
      (locallyClosedSupportedGlobalSectionsComplex W I).extend ComplexShape.embeddingUpNat := by
  letI : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : Opens X))).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact homComplexFromSingleIso (constantZ X) (locallyClosedSupportedSheafResolutionInt W I) ≪≫
    (NatIso.mapHomologicalComplex (constantZHomFunctorIso (X := X)) (ComplexShape.up ℤ)).app
      (locallyClosedSupportedSheafResolutionInt W I) ≪≫
    mapExtendIso
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X))) ComplexShape.embeddingUpNat (locallyClosedSupportedSheafResolution W I)

/-- Actual derived global Hom of the supported derived object identifies
additively with the original `H_locallyClosed`, including its smaller universe. -/
def locallyClosedDerivedTotalHomEquiv (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    (((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X)) ⟶
      (locallyClosedSupportedDerivedObject W I)⟦(n : ℤ)⟧) ≃+ H_locallyClosed W F n :=
  (homComplexHomologyDerivedHomEquiv
    ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X))
    (locallyClosedSupportedSheafResolutionInt W I) (n : ℤ)).symm.trans
      (((homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (n : ℤ)).mapIso
          (locallyClosedSupportedHomComplexIsoGlobalSections W I) ≪≫
        (locallyClosedSupportedGlobalSectionsComplex W I).extendHomologyIso
          ComplexShape.embeddingUpNat
          (j := n) (j' := (n : ℤ)) rfl ≪≫
        locallyClosedSupportedGlobalSectionsComplexHomologyIso W I n).addCommGroupIsoToAddEquiv)

/-- The total interval of the actual constructed spectral object has exactly
the original supported cohomology as its cohomology groups. -/
def locallyClosedSpectralObjectTotalEquiv (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    ((locallyClosedLocalToGlobalAbelianSpectralObject W I).H (n : ℤ)).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) ≃+ H_locallyClosed W F n :=
  locallyClosedDerivedTotalHomEquiv W I n


/-- The actual finite filtration of the total group, identified above with
original ambient locally closed support Ext. -/
def locallyClosedCohomologyFiniteFiltration (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    Fin (n + 2) →o Subobject (SpectralObjectConvergence.total
      (locallyClosedLocalToGlobalAbelianSpectralObject W I) n) :=
  SpectralObjectConvergence.finiteFiltration _ n

@[simp] theorem locallyClosedCohomologyFiniteFiltration_zero (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    locallyClosedCohomologyFiniteFiltration W I n 0 = ⊥ :=
  SpectralObjectConvergence.finiteFiltration_zero _ n

@[simp] theorem locallyClosedCohomologyFiniteFiltration_last (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    locallyClosedCohomologyFiniteFiltration W I n (Fin.last (n + 1)) = ⊤ :=
  SpectralObjectConvergence.finiteFiltration_last _ n

/-- **I.2.6, locally closed convergence:** actual stable pages are the
genuine graded cokernels of the finite filtration of the original Ext total
group, with the single uniform bound r ≥ n + 2. -/
def locallyClosedLocalToGlobalStablePageIsoGraded (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ)
    (q : Fin (n + 1)) (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((locallyClosedTruncationSpectralSequence W I).page r).X ((n : ℤ) - q, q) ≅
      SpectralObjectConvergence.gradedPiece
        (locallyClosedLocalToGlobalAbelianSpectralObject W I) n q :=
  SpectralObjectConvergence.stablePageIsoGradedTotal _ n q r hr

end SGA.SGA2.ExposeI
