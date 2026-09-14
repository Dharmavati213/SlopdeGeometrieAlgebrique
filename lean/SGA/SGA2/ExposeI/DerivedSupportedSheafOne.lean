/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.SupportedSheafSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # The original first derived supported sheaf is the complement-unit cokernel -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

section ResolutionZero

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- A left exact functor on an injective resolution recovers its value as
zeroth homology. -/
def resolutionZeroHomologyIso (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P]
    {X : C} (I : InjectiveResolution X) :
    P.obj X ≅ ((P.mapHomologicalComplex _).obj I.cocomplex).homology 0 :=
  asIso (I.toRightDerivedZero' P) ≪≫
    CochainComplex.isoHomologyπ₀ ((P.mapHomologicalComplex _).obj I.cocomplex)

/-- The degree-zero comparison commutes with natural transformations of
left exact coefficient functors. -/
@[reassoc]
lemma resolutionZeroHomologyIso_hom_natTrans
    {P Q : C ⥤ D} [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteLimits Q]
    (α : P ⟶ Q) {X : C} (I : InjectiveResolution X) :
    α.app X ≫ (resolutionZeroHomologyIso Q I).hom =
      (resolutionZeroHomologyIso P I).hom ≫
        homologyMap ((α.mapHomologicalComplex _).app I.cocomplex) 0 := by
  have h : α.app X ≫ I.toRightDerivedZero' Q =
      I.toRightDerivedZero' P ≫
        cyclesMap ((α.mapHomologicalComplex _).app I.cocomplex) 0 := by
    apply (cancel_mono (iCycles _ 0)).mp
    simp only [Category.assoc, InjectiveResolution.toRightDerivedZero'_comp_iCycles,
      cyclesMap_i, InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
    exact (α.naturality (I.ι.f 0)).symm
  simp only [resolutionZeroHomologyIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← Category.assoc, h, Category.assoc]
  congr 1
  exact (homologyπ_naturality _ 0).symm

/-- Naturality of the degree-zero comparison for a map of resolutions. -/
@[reassoc]
lemma resolutionZeroHomologyIso_hom_naturality
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P]
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    P.map f ≫ (resolutionZeroHomologyIso P J).hom =
      (resolutionZeroHomologyIso P I).hom ≫
        homologyMap ((P.mapHomologicalComplex _).map φ) 0 := by
  simp only [resolutionZeroHomologyIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← Category.assoc, InjectiveResolution.toRightDerivedZero'_naturality f I J φ hφ,
    Category.assoc]
  congr 1
  exact (homologyπ_naturality _ 0).symm

end ResolutionZero

variable {X : TopCat.{u}}

instance complementPushforwardFunctor_preservesFiniteLimits (Z : Closeds X) :
    PreservesFiniteLimits (complementPushforwardFunctor Z) := by
  dsimp [complementPushforwardFunctor, complementInclusion]
  let := (openExtensionByZeroAdjunction Z.compl).isRightAdjoint
  let := (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} Z.compl.inclusion').isRightAdjoint
  infer_instance

/-- The first connecting morphism, from the original complement pushforward
to the original first derived supported sheaf. -/
def supportedSheafOneConnecting (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    (complementPushforwardFunctor Z).obj F ⟶
      ((underlineGammaZFunctor Z).rightDerived 1).obj F :=
  (resolutionZeroHomologyIso (complementPushforwardFunctor Z) (injectiveResolution F)).hom ≫
    (supportedSheafComplexSequence_shortExact Z (injectiveResolution F)).δ 0 1 (by simp) ≫
      ((injectiveResolution F).isoRightDerivedObj (underlineGammaZFunctor Z) 1).inv

instance supportedSheafOneConnecting_epi (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    Epi (supportedSheafOneConnecting Z F) := by
  have := (supportedSheafComplexSequence_shortExact Z (injectiveResolution F)).epi_δ
    0 1 (by simp) ((injectiveResolution F).cocomplex_exactAt_succ 0).isZero_homology
  dsimp [supportedSheafOneConnecting]
  infer_instance

/-- The original complement unit is killed by the first connecting morphism. -/
@[reassoc (attr := simp)]
lemma toComplementPushforward_comp_supportedSheafOneConnecting (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    toComplementPushforward F Z ≫ supportedSheafOneConnecting Z F = 0 := by
  dsimp only [supportedSheafOneConnecting]
  rw [← Category.assoc, ← Category.assoc]
  erw [resolutionZeroHomologyIso_hom_natTrans (complementPushforwardUnit Z)
    (injectiveResolution F)]
  rw [Category.assoc, Category.assoc]
  erw [(supportedSheafComplexSequence_shortExact Z (injectiveResolution F)).comp_δ_assoc
    0 1 (by simp)]
  simp

/-- The first derived supported-sheaf sequence, using the original unit. -/
def supportedSheafOneSequence (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (toComplementPushforward F Z) (supportedSheafOneConnecting Z F)
    (toComplementPushforward_comp_supportedSheafOneConnecting Z F)

/-- Exactness at the original complement pushforward. -/
lemma supportedSheafOneSequence_exact (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    (supportedSheafOneSequence Z F).Exact := by
  let I := injectiveResolution F
  let hS := supportedSheafComplexSequence_shortExact Z I
  let T := ShortComplex.mk _ _ (hS.comp_δ 0 1 (by simp))
  have e : supportedSheafOneSequence Z F ≅ T :=
    ShortComplex.isoMk (resolutionZeroHomologyIso (𝟭 _) I)
      (resolutionZeroHomologyIso (complementPushforwardFunctor Z) I)
      (I.isoRightDerivedObj (underlineGammaZFunctor Z) 1)
      (resolutionZeroHomologyIso_hom_natTrans (complementPushforwardUnit Z) I).symm
      (by
        dsimp [supportedSheafOneSequence, supportedSheafOneConnecting, T, hS, I]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  exact (ShortComplex.exact_iff_of_iso e).mpr (hS.homology_exact₃ 0 1 (by simp))

/-- The cokernel of the original complement unit identifies with the original
first right-derived supported sheaf. -/
def cokernelToDerivedSupportedSheafOneIso (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    cokernel (toComplementPushforward F Z) ≅
      ((underlineGammaZFunctor Z).rightDerived 1).obj F := by
  let S := supportedSheafOneSequence Z F
  have : Epi S.g := supportedSheafOneConnecting_epi Z F
  have : IsIso (cokernel.desc S.f S.g S.zero) := by
    have : Mono (cokernel.desc S.f S.g S.zero) :=
      (supportedSheafOneSequence_exact Z F).mono_cokernelDesc
    have : Epi (cokernel.desc S.f S.g S.zero) :=
      epi_of_epi_fac (cokernel.π_desc S.f S.g S.zero)
    exact isIso_of_mono_of_epi _
  exact asIso (cokernel.desc S.f S.g S.zero)

/-- The original first derived supported sheaf is the existing cokernel model. -/
def derivedSupportedSheafOneObjIso (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    ((underlineGammaZFunctor Z).rightDerived 1).obj F ≅
      cokernel (toComplementPushforward F Z) :=
  (cokernelToDerivedSupportedSheafOneIso Z F).symm

private def oneComplexSequenceMap (Z : Closeds X)
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ} (φ : K ⟶ L) :
    supportedSheafComplexSequence Z K ⟶ supportedSheafComplexSequence Z L where
  τ₁ := ((underlineGammaZFunctor Z).mapHomologicalComplex _).map φ
  τ₂ := ((𝟭 (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex _).map φ
  τ₃ := ((complementPushforwardFunctor Z).mapHomologicalComplex _).map φ
  comm₁₂ := ((supportedSheafInclusion Z).mapHomologicalComplex _).naturality φ
  comm₂₃ := ((complementPushforwardUnit Z).mapHomologicalComplex _).naturality φ

@[reassoc]
private lemma oneResolutionδ_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (J : InjectiveResolution G) (φ : I.cocomplex ⟶ J.cocomplex) :
    (supportedSheafComplexSequence_shortExact Z I).δ 0 1 (by simp) ≫
        homologyMap (((underlineGammaZFunctor Z).mapHomologicalComplex _).map φ) 1 =
      homologyMap (((complementPushforwardFunctor Z).mapHomologicalComplex _).map φ) 0 ≫
        (supportedSheafComplexSequence_shortExact Z J).δ 0 1 (by simp) :=
  HomologicalComplex.HomologySequence.δ_naturality (oneComplexSequenceMap Z φ)
    (supportedSheafComplexSequence_shortExact Z I)
    (supportedSheafComplexSequence_shortExact Z J) 0 1 (by simp)

/-- Naturality of the first connecting morphism in the coefficient sheaf. -/
@[reassoc]
lemma supportedSheafOneConnecting_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    (complementPushforwardFunctor Z).map f ≫ supportedSheafOneConnecting Z G =
      supportedSheafOneConnecting Z F ≫ ((underlineGammaZFunctor Z).rightDerived 1).map f := by
  let I := injectiveResolution F
  let J := injectiveResolution G
  let φ := InjectiveResolution.desc f J I
  have hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero f J I
  simp only [supportedSheafOneConnecting, Category.assoc]
  rw [← Category.assoc,
    resolutionZeroHomologyIso_hom_naturality (complementPushforwardFunctor Z) f I J φ hφ,
    Category.assoc]
  rw [← oneResolutionδ_naturality_assoc Z I J φ]
  erw [← InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ hφ
    (underlineGammaZFunctor Z) 1]

/-- Naturality of the cokernel-to-derived comparison for the actual induced
cokernel map. -/
@[reassoc]
lemma cokernelToDerivedSupportedSheafOneIso_hom_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    cokernel.map (toComplementPushforward F Z) (toComplementPushforward G Z)
        f ((complementPushforwardFunctor Z).map f)
        ((complementPushforwardUnit Z).naturality f).symm ≫
      (cokernelToDerivedSupportedSheafOneIso Z G).hom =
    (cokernelToDerivedSupportedSheafOneIso Z F).hom ≫
      ((underlineGammaZFunctor Z).rightDerived 1).map f :=
  cokernel.map_desc _ _ _ _ _ _ _ _ _ _ (supportedSheafOneConnecting_naturality Z f).symm

/-- Naturality of the original first derived supported-sheaf model comparison. -/
@[reassoc]
lemma derivedSupportedSheafOneObjIso_hom_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    ((underlineGammaZFunctor Z).rightDerived 1).map f ≫
        (derivedSupportedSheafOneObjIso Z G).hom =
      (derivedSupportedSheafOneObjIso Z F).hom ≫
        cokernel.map (toComplementPushforward F Z) (toComplementPushforward G Z)
          f ((complementPushforwardFunctor Z).map f)
          ((complementPushforwardUnit Z).naturality f).symm := by
  apply (cancel_epi (cokernelToDerivedSupportedSheafOneIso Z F).hom).mp
  simp only [derivedSupportedSheafOneObjIso, Iso.symm_hom, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]
  rw [← cokernelToDerivedSupportedSheafOneIso_hom_naturality Z f, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end SGA.SGA2.ExposeI
