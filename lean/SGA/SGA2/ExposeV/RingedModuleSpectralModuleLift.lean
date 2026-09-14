/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RingedModulePushforwardSpectralSequence
import SGA.SGA2.ExposeV.SpectralSequenceModuleComparison
import SGA.SGA2.ExposeI.TruncationSpectralObjectAdditive

/-!
# SGA 2, V.3.2: the actual spectral sequence with its retained module structures

The original global scalar action on the direct-image resolution induces a
ring action on its canonical truncation spectral object. Its lift to modules
therefore gives genuine module-valued pages, differentials, and next-page
homology isomorphisms. The canonical additive comparison identifies the whole
spectral sequence with the previous additive construction. The companion files
`RingedModuleSpectralE2Linear` and `RingedModuleSpectralAbutment` prove linearity
of the original E₂ cohomology comparison and identify the stated abutment.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {R : Sheaf RingCat.{u} X} {S : Sheaf RingCat.{u} Y}
  (φ : S ⟶ (Sheaf.pushforward RingCat f).obj R) (Z : Closeds Y)

local instance : HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} Y) :=
  HasDerivedCategory.standard _

/-- The actual canonical-truncation and supported-Hom functor retains full scalar ring actions. -/
def ringedModulePushforwardSpectralScalarRingHom {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) :
    S.obj.obj (op (⊤ : Opens Y)) →+*
      End (ringedModulePushforwardAbelianSpectralObject f φ Z I) :=
  (additiveEndRingHom
    (ExposeI.truncationAbelianSpectralObjectFunctor
      (DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} Y))
      (ringedDerivedSupportedHom Z)) (ringedModulePushforwardDerivedObject f φ I)).comp
    (ringedModulePushforwardDerivedScalarRingHom f φ I)

/-- The genuine module-valued spectral object retains the original global structure-ring action. -/
def ringedModulePushforwardModuleSpectralObject {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) :
    Abelian.SpectralObject (ModuleCat.{u + 1} (S.obj.obj (op (⊤ : Opens Y)))) EInt :=
  spectralObjectModuleLift (ringedModulePushforwardAbelianSpectralObject f φ Z I)
    (ringedModulePushforwardSpectralScalarRingHom f φ Z I)

/-- **V.3.2, module-valued construction:** every page, differential and successive
homology isomorphism is a genuine module object or module-linear map over `Γ(Y,S)`. -/
def ringedModulePushforwardModuleSpectralSequence {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) :
    E₂CohomologicalSpectralSequence (ModuleCat.{u + 1} (S.obj.obj (op (⊤ : Opens Y)))) :=
  (ringedModulePushforwardModuleSpectralObject f φ Z I).E₂SpectralSequence

/-- The module-valued pages have the original additive terms through canonical homology maps. -/
def ringedModulePushforwardModulePageXForgetIso {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    (forget₂ (ModuleCat (S.obj.obj (op (⊤ : Opens Y)))) AddCommGrpCat).obj
        (((ringedModulePushforwardModuleSpectralSequence f φ Z I).page r hr).X pq) ≅
      (((ringedModulePushforwardAdditiveSpectralSequence f φ Z I).page r hr).X pq) :=
  spectralObjectModulePageXForgetIso (ringedModulePushforwardAbelianSpectralObject f φ Z I)
    (ringedModulePushforwardSpectralScalarRingHom f φ Z I) r hr pq

/-- The module spectral sequence forgets to the entire original additive sequence. -/
def ringedModulePushforwardModuleSpectralSequenceForgetIso {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) :
    moduleSpectralSequenceForget (ringedModulePushforwardModuleSpectralSequence f φ Z I) ≅
      ringedModulePushforwardAdditiveSpectralSequence f φ Z I :=
  spectralObjectModuleForgetIso (ringedModulePushforwardAbelianSpectralObject f φ Z I)
    (ringedModulePushforwardSpectralScalarRingHom f φ Z I)
    Abelian.SpectralObject.coreE₂Cohomological

/-- The actual module-valued E₂ terms agree additively with the original module-supported
cohomology of the original higher module direct images. The companion
`RingedModuleSpectralE2Linear` proves scalar compatibility of this unchanged map. -/
def ringedModulePushforwardModuleE2AddEquiv {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (p q : ℕ) :
    (forget₂ (ModuleCat (S.obj.obj (op (⊤ : Opens Y)))) AddCommGrpCat).obj
        (((ringedModulePushforwardModuleSpectralSequence f φ Z I).page 2).X
          ((p : ℤ), (q : ℤ))) ≃+
      (forget₂ (ModuleCat (S.obj.obj (op (⊤ : Opens Y)))) AddCommGrpCat).obj
        ((derivedModuleGammaZSections S Z ⊤ p).obj
          ((derivedRingedModulePushforward f φ q).obj M)) :=
  (ringedModulePushforwardModulePageXForgetIso f φ Z I 2 (by lia)
      ((p : ℤ), (q : ℤ))).addCommGroupIsoToAddEquiv.trans
    (ringedModulePushforwardE2ModuleAddEquiv f φ Z I p q)

end SGA.SGA2.ExposeV
