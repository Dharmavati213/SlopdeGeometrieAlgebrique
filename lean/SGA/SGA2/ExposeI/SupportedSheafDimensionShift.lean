/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.SupportedSheafSequence
import SGA.SGA2.ExposeI.DerivedSupportedSheaves
import SGA.SGA2.ExposeI.RightDerivedPrecomposition
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Dimension shifting for the original supported sheaves

The genuine short exact sequence on an injective resolution identifies
positive derived complement pushforward with the next derived supported
sheaf. The comparison is obtained from the connecting homomorphism of the
actual short exact sequence of complexes.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- A map of coefficient complexes induces a map of supported-sheaf sequences. -/
def supportedSheafComplexSequenceMap (Z : Closeds X)
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ} (φ : K ⟶ L) :
    supportedSheafComplexSequence Z K ⟶ supportedSheafComplexSequence Z L where
  τ₁ := ((underlineGammaZFunctor Z).mapHomologicalComplex _).map φ
  τ₂ := ((𝟭 (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex _).map φ
  τ₃ := ((complementPushforwardFunctor Z).mapHomologicalComplex _).map φ
  comm₁₂ := ((supportedSheafInclusion Z).mapHomologicalComplex _).naturality φ
  comm₂₃ := ((complementPushforwardUnit Z).mapHomologicalComplex _).naturality φ

/-- The connecting isomorphism computed on a chosen injective resolution. -/
def supportedSheafResolutionShiftIso (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    (((complementPushforwardFunctor Z).mapHomologicalComplex _).obj I.cocomplex).homology
        (n + 1) ≅
      (((underlineGammaZFunctor Z).mapHomologicalComplex _).obj I.cocomplex).homology
        (n + 2) :=
  (supportedSheafComplexSequence_shortExact Z I).δIso (n + 1) (n + 2) (by simp)
    (I.cocomplex_exactAt_succ n).isZero_homology
    (I.cocomplex_exactAt_succ (n + 1)).isZero_homology

@[reassoc]
theorem supportedSheafResolutionShiftIso_hom_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (J : InjectiveResolution G) (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) :
    (supportedSheafResolutionShiftIso Z I n).hom ≫
        HomologicalComplex.homologyMap
          (((underlineGammaZFunctor Z).mapHomologicalComplex _).map φ) (n + 2) =
      HomologicalComplex.homologyMap
          (((complementPushforwardFunctor Z).mapHomologicalComplex _).map φ) (n + 1) ≫
        (supportedSheafResolutionShiftIso Z J n).hom :=
  HomologicalComplex.HomologySequence.δ_naturality (supportedSheafComplexSequenceMap Z φ)
    (supportedSheafComplexSequence_shortExact Z I)
    (supportedSheafComplexSequence_shortExact Z J) (n + 1) (n + 2) (by simp)

/-- Positive right-derived complement pushforward computes the next original
right-derived supported sheaf. -/
def derivedSupportedSheafShiftObjIso (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    ((complementPushforwardFunctor Z).rightDerived (n + 1)).obj F ≅
      (derivedUnderlineGammaZ Z (n + 2)).obj F :=
  (injectiveResolution F).isoRightDerivedObj (complementPushforwardFunctor Z) (n + 1) ≪≫
    supportedSheafResolutionShiftIso Z (injectiveResolution F) n ≪≫
      ((injectiveResolution F).isoRightDerivedObj (underlineGammaZFunctor Z) (n + 2)).symm

@[reassoc]
theorem derivedSupportedSheafShiftObjIso_hom_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ) :
    ((complementPushforwardFunctor Z).rightDerived (n + 1)).map f ≫
        (derivedSupportedSheafShiftObjIso Z G n).hom =
      (derivedSupportedSheafShiftObjIso Z F n).hom ≫
        (derivedUnderlineGammaZ Z (n + 2)).map f := by
  let I := injectiveResolution F
  let J := injectiveResolution G
  let φ := InjectiveResolution.desc f J I
  have hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero f J I
  simp only [derivedSupportedSheafShiftObjIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc,
    InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ hφ
      (complementPushforwardFunctor Z) (n + 1), Category.assoc]
  erw [← supportedSheafResolutionShiftIso_hom_naturality_assoc Z I J φ n]
  erw [← InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ hφ
    (underlineGammaZFunctor Z) (n + 2)]
  rfl

/-- The dimension-shift comparison is natural in coefficient sheaves. -/
def derivedSupportedSheafShiftIso (Z : Closeds X) (n : ℕ) :
    (complementPushforwardFunctor Z).rightDerived (n + 1) ≅
      derivedUnderlineGammaZ Z (n + 2) :=
  NatIso.ofComponents (fun F ↦ derivedSupportedSheafShiftObjIso Z F n)
    (fun f ↦ derivedSupportedSheafShiftObjIso_hom_naturality Z f n)

/-- Restriction to the complement may be performed before or after deriving
the complement-pushforward composite. -/
def derivedComplementPushforwardIso (Z : Closeds X) (n : ℕ) :
    (complementPushforwardFunctor Z).rightDerived n ≅
      Sheaf.pullback AddCommGrpCat.{u} (complementInclusion Z) ⋙
        (Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)).rightDerived n := by
  letI := (openExtensionByZeroAdjunction Z.compl).isRightAdjoint
  letI : (Sheaf.pullback AddCommGrpCat.{u} (complementInclusion Z)).PreservesHomology := by
    change (iShriek_open Z.compl).PreservesHomology
    infer_instance
  letI : (Sheaf.pullback AddCommGrpCat.{u} (complementInclusion Z)).PreservesInjectiveObjects :=
    iShriek_open_preservesInjectiveObjects Z.compl
  exact rightDerivedPrecomposeIso
    (Sheaf.pullback AddCommGrpCat.{u} (complementInclusion Z))
    (Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)) n

/-- **I.2.11, degrees at least two:** the original derived supported-sheaf
functor is naturally derived complement pushforward, shifted by one. -/
def derivedSupportedSheafHigherIso (Z : Closeds X) (n : ℕ) :
    derivedUnderlineGammaZ Z (n + 2) ≅
      Sheaf.pullback AddCommGrpCat.{u} (complementInclusion Z) ⋙
        (Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)).rightDerived (n + 1) :=
  (derivedSupportedSheafShiftIso Z n).symm ≪≫ derivedComplementPushforwardIso Z (n + 1)

/-- The existing higher-degree model is the actual original derived sheaf. -/
def derivedSupportedSheafHigherModelIso (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (derivedUnderlineGammaZ Z (n + 2)).obj F ≅ sheafH_Z_n Z F (n + 2) :=
  (derivedSupportedSheafHigherIso Z n).app F

end SGA.SGA2.ExposeI
