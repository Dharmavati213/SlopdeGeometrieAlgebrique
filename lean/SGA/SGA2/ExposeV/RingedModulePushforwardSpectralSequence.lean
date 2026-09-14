/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RingedModuleGlobalAction
import SGA.SGA2.ExposeI.LocalToGlobalE2

/-!
# SGA 2, V.3.2: actual additive spectral-sequence pages and their E₂ identification

Apply derived Hom from the original closed-support integer sheaf to the
canonical truncations of the underlying additive direct-image resolution.
This constructs all pages and differentials of a genuine spectral sequence.
Its E₂ groups are the original supported cohomology of the actual higher
module direct images. The underlying derived object retains its global
structure-ring action. The companion files `RingedModuleSpectralModuleLift`,
`RingedModuleSpectralE2Linear` and `RingedModuleSpectralAbutment` lift the actual
spectral sequence to modules and identify its E₂ and abutment module-linearly.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat
open ComposableArrows

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {R : Sheaf RingCat.{u} X} {S : Sheaf RingCat.{u} Y}
  (φ : S ⟶ (Sheaf.pushforward RingCat f).obj R)

local instance : (SheafOfModules.toSheaf.{u} S).Additive := inferInstance

local instance : (SheafOfModules.toSheaf.{u} S).PreservesHomology :=
  ((Functor.exact_tfae (SheafOfModules.toSheaf.{u} S)).out 1 3).mp
    (fun _ hT ↦ moduleToSheaf_map_shortExact S hT)

local instance : (ringedModulePushforward f φ ⋙ SheafOfModules.toSheaf S).Additive := by
  infer_instance

/-- The actual integer-indexed module direct image of a module-injective resolution. -/
def ringedModulePushforwardResolutionInt {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) : CochainComplex (SheafOfModules.{u} S) ℤ :=
  ((ringedModulePushforward f φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex

/-- The underlying additive direct-image complex, with its actual module-linear differentials. -/
def ringedModulePushforwardAdditiveResolutionInt {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) : CochainComplex (Sheaf AddCommGrpCat.{u} Y) ℤ :=
  ((SheafOfModules.toSheaf S).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (ringedModulePushforwardResolutionInt f φ I)

instance {M : SheafOfModules.{u} R} (I : InjectiveResolution M) :
    (ringedModulePushforwardAdditiveResolutionInt f φ I).IsStrictlyGE 0 := by
  dsimp [ringedModulePushforwardAdditiveResolutionInt, ringedModulePushforwardResolutionInt]
  infer_instance

/-- Every term of the actual additive direct-image resolution is flasque. -/
instance {M : SheafOfModules.{u} R} (I : InjectiveResolution M) (n : ℤ) :
    ExposeI.IsFlasque ((ringedModulePushforwardAdditiveResolutionInt f φ I).X n) :=
  ringedModulePushforward_injective_isFlasque f φ (I.cochainComplex.X n)

local instance : HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} Y) :=
  HasDerivedCategory.standard _

/-- The actual derived additive object of the module direct-image resolution. -/
def ringedModulePushforwardDerivedObject {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) : DerivedCategory (Sheaf AddCommGrpCat.{u} Y) :=
  DerivedCategory.Q.obj (ringedModulePushforwardAdditiveResolutionInt f φ I)

instance {M : SheafOfModules.{u} R} (I : InjectiveResolution M) :
    (ringedModulePushforwardDerivedObject f φ I).IsGE 0 := by
  dsimp [ringedModulePushforwardDerivedObject]
  infer_instance

/-- The derived direct-image object retains the actual action of `Γ(Y,S)`. -/
def ringedModulePushforwardDerivedScalarRingHom {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) :
    S.obj.obj (op (⊤ : Opens Y)) →+* End (ringedModulePushforwardDerivedObject f φ I) :=
  moduleUnderlyingDerivedGlobalScalarRingHom S (ringedModulePushforwardResolutionInt f φ I)

/-- Its cohomology sheaves underlie the original module higher direct images. -/
def ringedModulePushforwardDerivedObjectHomologyIso {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (q : ℕ) :
    (DerivedCategory.homologyFunctor (Sheaf AddCommGrpCat.{u} Y) (q : ℤ)).obj
        (ringedModulePushforwardDerivedObject f φ I) ≅
      (SheafOfModules.toSheaf S).obj ((derivedRingedModulePushforward f φ q).obj M) :=
  (DerivedCategory.homologyFunctorFactors (Sheaf AddCommGrpCat.{u} Y) (q : ℤ)).app
      (ringedModulePushforwardAdditiveResolutionInt f φ I) ≪≫
    ExposeI.injectiveResolutionIntHomologyIso
      (ringedModulePushforward f φ ⋙ SheafOfModules.toSheaf S) I q ≪≫
    (ExposeI.rightDerivedPostcomposeIso (ringedModulePushforward f φ)
      (SheafOfModules.toSheaf S) q).app M

variable (Z : Closeds Y)

/-- Canonical truncations of the actual derived module direct image. -/
def ringedModulePushforwardTriangulatedSpectralObject {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) :
    Triangulated.SpectralObject (DerivedCategory (Sheaf AddCommGrpCat.{u} Y)) EInt :=
  (DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} Y)).spectralObject
    (ringedModulePushforwardDerivedObject f φ I)

/-- Derived supported Hom from the unchanged integer support object. -/
def ringedDerivedSupportedHom :
    DerivedCategory (Sheaf AddCommGrpCat.{u} Y) ⥤ AddCommGrpCat.{u + 1} :=
  preadditiveCoyoneda.obj
    (op ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) 0).obj
      (ExposeI.zZX_closed Z)))

instance : (ringedDerivedSupportedHom Z).IsHomological := by
  dsimp [ringedDerivedSupportedHom]
  infer_instance

instance : (ringedDerivedSupportedHom Z).ShiftSequence ℤ := by
  dsimp [ringedDerivedSupportedHom]
  infer_instance

/-- The genuine additive spectral object for the direct-image truncations and supported Hom. -/
def ringedModulePushforwardAbelianSpectralObject {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) : Abelian.SpectralObject AddCommGrpCat.{u + 1} EInt :=
  ExposeI.homologicalSpectralObject (ringedModulePushforwardTriangulatedSpectralObject f φ I)
    (ringedDerivedSupportedHom Z)

/-- The actual additive spectral sequence, including all pages, differentials and page homology. -/
def ringedModulePushforwardAdditiveSpectralSequence {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) : E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  (ringedModulePushforwardAbelianSpectralObject f φ Z I).E₂SpectralSequence

/-- Its single-degree interval is the single complex of the original higher module direct image. -/
def ringedModulePushforwardE2TruncationIso {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (q : ℕ) :
    (ringedModulePushforwardTriangulatedSpectralObject f φ I).ω₁.obj
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) by
          exact WithBotTop.coe_le_coe.mpr (by lia)))) ≅
      (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) (q : ℤ)).obj
        ((SheafOfModules.toSheaf S).obj ((derivedRingedModulePushforward f φ q).obj M)) :=
  ExposeI.derivedSingleDegreeTruncationIsoSingle (ringedModulePushforwardDerivedObject f φ I)
      (q : ℤ) ≪≫
    (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) (q : ℤ)).mapIso
      (ringedModulePushforwardDerivedObjectHomologyIso f φ I q)

/-- **V.3.2, underlying E₂ groups:** the actual page terms are the original supported
cohomology of the actual higher module direct images. -/
def ringedModulePushforwardAdditiveSpectralSequenceE2Equiv {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (p q : ℕ) :
    ((ringedModulePushforwardAdditiveSpectralSequence f φ Z I).page 2).X
        ((p : ℤ), (q : ℤ)) ≃+
      ExposeI.H_Z Z
        ((SheafOfModules.toSheaf S).obj ((derivedRingedModulePushforward f φ q).obj M)) p := by
  let eFirst :=
    (ringedModulePushforwardAbelianSpectralObject f φ Z I).spectralSequenceFirstPageXIso
      Abelian.SpectralObject.coreE₂Cohomological
      ((p : ℤ), (q : ℤ)) (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl
  let eShift := (shiftFunctor (DerivedCategory (Sheaf AddCommGrpCat.{u} Y))
      ((p : ℤ) + (q : ℤ))).mapIso (ringedModulePushforwardE2TruncationIso f φ I q) ≪≫
    ExposeI.supportedSingleTotalShiftIso
      ((SheafOfModules.toSheaf S).obj ((derivedRingedModulePushforward f φ q).obj M))
      (p : ℤ) (q : ℤ)
  let eHom := (ringedDerivedSupportedHom Z).mapIso eShift
  exact eFirst.addCommGroupIsoToAddEquiv.trans
    (eHom.addCommGroupIsoToAddEquiv.trans (Abelian.Ext.homAddEquiv
      (X := ExposeI.zZX_closed Z)
      (Y := (SheafOfModules.toSheaf S).obj ((derivedRingedModulePushforward f φ q).obj M))
      (n := p)).symm)

/-- The same actual E₂ page agrees additively with the previously constructed
module-valued supported cohomology of the original higher module direct images.
Scalar compatibility of this unchanged comparison is proved in
`RingedModuleSpectralE2Linear`. -/
def ringedModulePushforwardE2ModuleAddEquiv {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (p q : ℕ) :
    ((ringedModulePushforwardAdditiveSpectralSequence f φ Z I).page 2).X
        ((p : ℤ), (q : ℤ)) ≃+
      (forget₂ (ModuleCat (S.obj.obj (op (⊤ : Opens Y)))) AddCommGrpCat).obj
        ((derivedModuleGammaZSections S Z ⊤ p).obj
          ((derivedRingedModulePushforward f φ q).obj M)) :=
  (ringedModulePushforwardAdditiveSpectralSequenceE2Equiv f φ Z I p q).trans
    (derivedModuleGammaZSectionsObjIsoH_Z S Z
      ((derivedRingedModulePushforward f φ q).obj M) p).symm.addCommGroupIsoToAddEquiv

end SGA.SGA2.ExposeV
