/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedExt
import SGA.SGA2.ExposeI.LocalToGlobalE2
import SGA.SGA2.ExposeI.InjectiveResolutionIntCohomology
import SGA.SGA2.ExposeI.SpectralObjectConvergence

/-!
# SGA 2, VI.1.6.3: Ext against the actual derived supported module sheaves

Canonical truncations of the genuine supported module-injective resolution
give a spectral sequence in the derived category of module sheaves. Its E₂
terms are module Ext against the original right-derived supported module
sheaves. The connective resolution gives first-quadrant support and a finite
exhaustive total filtration. Identifying its total with original supported
Ext uses injective preservation and is supplied in the companion file.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat ComposableArrows

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (Z : Closeds X)

/-- The original right-derived closed-support functor in module sheaves. -/
def derivedModuleGammaZSheaf (q : ℕ) : SheafOfModules.{u} R ⥤ SheafOfModules.{u} R :=
  (moduleGammaZSheafFunctor R Z).rightDerived q

/-- The actual complex obtained by applying module support to a module-injective resolution. -/
def moduleSupportResolutionInt {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    CochainComplex (SheafOfModules.{u} R) ℤ :=
  ((moduleGammaZSheafFunctor R Z).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex

instance {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    (moduleSupportResolutionInt R Z I).IsStrictlyGE 0 := by
  dsimp [moduleSupportResolutionInt]
  infer_instance

local instance : HasDerivedCategory.{u + 1} (SheafOfModules.{u} R) :=
  HasDerivedCategory.standard _

/-- The actual derived module-support object. -/
def moduleSupportDerivedObject {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    DerivedCategory (SheafOfModules.{u} R) :=
  DerivedCategory.Q.obj (moduleSupportResolutionInt R Z I)

instance {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    (moduleSupportDerivedObject R Z I).IsGE 0 := by
  dsimp [moduleSupportDerivedObject]
  infer_instance

/-- Its module cohomology is the original right-derived module-support functor. -/
def moduleSupportDerivedHomologyIso {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (q : ℕ) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} R) (q : ℤ)).obj
        (moduleSupportDerivedObject R Z I) ≅ (derivedModuleGammaZSheaf R Z q).obj G :=
  (DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} R) (q : ℤ)).app
      (moduleSupportResolutionInt R Z I) ≪≫
    ExposeI.injectiveResolutionIntHomologyIso (moduleGammaZSheafFunctor R Z) I q

/-- All canonical truncation intervals and their actual distinguished triangles. -/
def moduleSupportTriangulatedSpectralObject {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) :
    Triangulated.SpectralObject (DerivedCategory (SheafOfModules.{u} R)) EInt :=
  (DerivedCategory.TStructure.t (C := SheafOfModules.{u} R)).spectralObject
    (moduleSupportDerivedObject R Z I)

variable (F : SheafOfModules.{u} R)

/-- Derived Hom from the original coefficient module sheaf. -/
def moduleSupportDerivedHom : DerivedCategory (SheafOfModules.{u} R) ⥤ AddCommGrpCat.{u + 1} :=
  preadditiveCoyoneda.obj
    (op ((DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).obj F))

instance : (moduleSupportDerivedHom R F).IsHomological := by
  dsimp [moduleSupportDerivedHom]
  infer_instance

instance : (moduleSupportDerivedHom R F).ShiftSequence ℤ := by
  dsimp [moduleSupportDerivedHom]
  infer_instance

/-- The genuine abelian spectral object in VI.1.6.3. -/
def moduleSupportAbelianSpectralObject {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) : Abelian.SpectralObject AddCommGrpCat.{u + 1} EInt :=
  ExposeI.homologicalSpectralObject (moduleSupportTriangulatedSpectralObject R Z I)
    (moduleSupportDerivedHom R F)

/-- **VI.1.6.3:** the actual pages, differentials and next-page homology isomorphisms. -/
def moduleSupportSpectralSequence {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) : E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  (moduleSupportAbelianSpectralObject R Z F I).E₂SpectralSequence

/-- The actual one-degree interval is the original module-support cohomology sheaf. -/
def moduleSupportE2TruncationIso {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (q : ℕ) :
    (moduleSupportTriangulatedSpectralObject R Z I).ω₁.obj
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} R) (q : ℤ)).obj
        ((derivedModuleGammaZSheaf R Z q).obj G) :=
  ExposeI.derivedSingleDegreeTruncationIsoSingle (moduleSupportDerivedObject R Z I) (q : ℤ) ≪≫
    (DerivedCategory.singleFunctor (SheafOfModules.{u} R) (q : ℤ)).mapIso
      (moduleSupportDerivedHomologyIso R Z I q)

/-- The actual shift comparison for a module sheaf placed in one degree. -/
def moduleSupportSingleTotalShiftIso (A : SheafOfModules.{u} R) (p q : ℤ) :
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} R) q).obj A)⟦p + q⟧ ≅
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).obj A)⟦p⟧ :=
  ((DerivedCategory.singleFunctors (SheafOfModules.{u} R)).shiftIso
    (p + q) (-p) q (by lia)).app A ≪≫
    (((DerivedCategory.singleFunctors (SheafOfModules.{u} R)).shiftIso
      p (-p) 0 (by lia)).app A).symm

/-- The total shift puts the original module-support cohomology in the Hom degree. -/
def moduleSupportE2TotalShiftIso {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (p q : ℕ) :=
  (shiftFunctor (DerivedCategory (SheafOfModules.{u} R)) ((p : ℤ) + q)).mapIso
      (moduleSupportE2TruncationIso R Z I q) ≪≫
    moduleSupportSingleTotalShiftIso R ((derivedModuleGammaZSheaf R Z q).obj G) p q

/-- The original single-interval first-page comparison. -/
def moduleSupportE2FirstPageIso {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (p q : ℕ) :=
  (moduleSupportAbelianSpectralObject R Z F I).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂Cohomological ((p : ℤ), (q : ℤ))
    (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl

/-- **VI.1.6.3, E₂:** actual module Ext against the actual derived supported coefficient. -/
def moduleSupportSpectralSequenceE2Equiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (p q : ℕ) :
    ((moduleSupportSpectralSequence R Z F I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      Abelian.Ext F ((derivedModuleGammaZSheaf R Z q).obj G) p := by
  let eHom := (moduleSupportDerivedHom R F).mapIso (moduleSupportE2TotalShiftIso R Z I p q)
  exact (moduleSupportE2FirstPageIso R Z F I p q).addCommGroupIsoToAddEquiv.trans
    (eHom.addCommGroupIsoToAddEquiv.trans (Abelian.Ext.homAddEquiv
      (X := F) (Y := (derivedModuleGammaZSheaf R Z q).obj G) (n := p)).symm)

/-- Connectiveness and module-category t-structure orthogonality give first-quadrant support. -/
instance moduleSupportAbelianSpectralObject_isFirstQuadrant
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    (moduleSupportAbelianSpectralObject R Z F I).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    let t := DerivedCategory.TStructure.t (C := SheafOfModules.{u} R)
    have h := t.isZero_eTruncLT_obj_obj (moduleSupportDerivedObject R Z I) 0 j hj
    have h' := (t.eTruncGE.obj i).map_isZero h
    exact ((moduleSupportDerivedHom R F).shift n).map_isZero h'
  isZero₂ i j hij n hi := by
    let t := DerivedCategory.TStructure.t (C := SheafOfModules.{u} R)
    have hni : ((n + 1 : ℤ) : EInt) ≤ i := by
      induction i using WithBotTop.rec with
      | bot => simp at hi
      | coe i =>
        simp only [WithBotTop.coe_le_coe, WithBotTop.coe_lt_coe] at *
        lia
      | top => exact le_top
    have hge := t.isGE_eTruncGE_obj_obj (n + 1) i hni
      ((t.eTruncLT.obj j).obj (moduleSupportDerivedObject R Z I))
    have hshift := t.isGE_shift
      ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj
        (moduleSupportDerivedObject R Z I))) (n + 1) n 1 (by lia)
    change IsZero (AddCommGrpCat.of
      (((DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).obj F) ⟶
        ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj
          (moduleSupportDerivedObject R Z I)))⟦n⟧))
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact ⟨fun a b ↦ (t.zero a 0 1).trans (t.zero b 0 1).symm⟩

/-- The actual total interval group of VI.1.6.3. -/
def moduleSupportSpectralTotal {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℤ) : AddCommGrpCat.{u + 1} :=
  ExposeI.SpectralObjectConvergence.total (moduleSupportAbelianSpectralObject R Z F I) n

/-- The genuine finite increasing filtration on actual total cohomology. -/
def moduleSupportSpectralFiniteFiltration {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    Fin (n + 2) →o Subobject (moduleSupportSpectralTotal R Z F I n) :=
  ExposeI.SpectralObjectConvergence.finiteFiltration (moduleSupportAbelianSpectralObject R Z F I) n

@[simp]
theorem moduleSupportSpectralFiniteFiltration_zero {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleSupportSpectralFiniteFiltration R Z F I n 0 = ⊥ :=
  ExposeI.SpectralObjectConvergence.finiteFiltration_zero _ n

@[simp]
theorem moduleSupportSpectralFiniteFiltration_last {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleSupportSpectralFiniteFiltration R Z F I n (Fin.last (n + 1)) = ⊤ :=
  ExposeI.SpectralObjectConvergence.finiteFiltration_last _ n

/-- The actual consecutive quotients of the canonical filtration. -/
def moduleSupportSpectralGradedPiece {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n q : ℤ) : AddCommGrpCat.{u + 1} :=
  ExposeI.SpectralObjectConvergence.gradedPiece (moduleSupportAbelianSpectralObject R Z F I) n q

/-- The stable actual page terms are the genuine finite-filtration quotients. -/
def moduleSupportSpectralStablePageIsoGraded {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) (q : Fin (n + 1)) (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((moduleSupportSpectralSequence R Z F I).page r).X ((n : ℤ) - q, q) ≅
      moduleSupportSpectralGradedPiece R Z F I n q :=
  ExposeI.SpectralObjectConvergence.stablePageIsoGradedTotal
    (moduleSupportAbelianSpectralObject R Z F I) n q r hr

end SGA.SGA2.ExposeVI
