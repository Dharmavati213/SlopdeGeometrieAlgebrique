/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportSpectralSequence

/-!
# The module Ext spectral sequence of an additive endofunctor

Map an actual injective module resolution by an additive endofunctor, take
all canonical truncations, and apply derived module Hom. This constructs
all pages and differentials, with genuine module Ext of the original derived
values as E₂. Connectiveness gives a finite exhaustive filtration and stable
page quotients. Applications supply their proved injective-preservation and
Hom identifications for the total comparison.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat ComposableArrows

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)
  (T : SheafOfModules.{u} R ⥤ SheafOfModules.{u} R) [T.Additive]

/-- The actual complex obtained by applying the given functor to a module-injective resolution. -/
def moduleEndofunctorResolutionInt {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    CochainComplex (SheafOfModules.{u} R) ℤ :=
  (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex

instance {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    (moduleEndofunctorResolutionInt R T I).IsStrictlyGE 0 := by
  dsimp [moduleEndofunctorResolutionInt]
  infer_instance

local instance moduleEndofunctorSpectralHasDerivedCategory :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u} R) :=
  HasDerivedCategory.standard _

/-- The actual derived mapped module object. -/
def moduleEndofunctorDerivedObject {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    DerivedCategory (SheafOfModules.{u} R) :=
  DerivedCategory.Q.obj (moduleEndofunctorResolutionInt R T I)

instance {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    (moduleEndofunctorDerivedObject R T I).IsGE 0 := by
  dsimp [moduleEndofunctorDerivedObject]
  infer_instance

/-- Its module cohomology is the original right-derived mapped module functor. -/
def moduleEndofunctorDerivedHomologyIso {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (q : ℕ) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} R) (q : ℤ)).obj
        (moduleEndofunctorDerivedObject R T I) ≅ (T.rightDerived q).obj G :=
  (DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} R) (q : ℤ)).app
      (moduleEndofunctorResolutionInt R T I) ≪≫
    ExposeI.injectiveResolutionIntHomologyIso T I q

/-- All canonical truncation intervals and their actual distinguished triangles. -/
def moduleEndofunctorTriangulatedSpectralObject {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) :
    Triangulated.SpectralObject (DerivedCategory (SheafOfModules.{u} R)) EInt :=
  (DerivedCategory.TStructure.t (C := SheafOfModules.{u} R)).spectralObject
    (moduleEndofunctorDerivedObject R T I)

variable (F : SheafOfModules.{u} R)

/-- The genuine abelian spectral object of the mapped resolution. -/
def moduleEndofunctorAbelianSpectralObject {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) : Abelian.SpectralObject AddCommGrpCat.{u + 1} EInt :=
  ExposeI.homologicalSpectralObject (moduleEndofunctorTriangulatedSpectralObject R T I)
    (moduleSupportDerivedHom R F)

/-- All actual pages, differentials and next-page homology isomorphisms. -/
def moduleEndofunctorSpectralSequence {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) : E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  (moduleEndofunctorAbelianSpectralObject R T F I).E₂SpectralSequence

/-- The actual one-degree interval is the original mapped module cohomology sheaf. -/
def moduleEndofunctorE2TruncationIso {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (q : ℕ) :
    (moduleEndofunctorTriangulatedSpectralObject R T I).ω₁.obj
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} R) (q : ℤ)).obj
        ((T.rightDerived q).obj G) :=
  ExposeI.derivedSingleDegreeTruncationIsoSingle (moduleEndofunctorDerivedObject R T I) (q : ℤ) ≪≫
    (DerivedCategory.singleFunctor (SheafOfModules.{u} R) (q : ℤ)).mapIso
      (moduleEndofunctorDerivedHomologyIso R T I q)

/-- The total shift puts the original mapped module cohomology in the Hom degree. -/
def moduleEndofunctorE2TotalShiftIso {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (p q : ℕ) :=
  (shiftFunctor (DerivedCategory (SheafOfModules.{u} R)) ((p : ℤ) + q)).mapIso
      (moduleEndofunctorE2TruncationIso R T I q) ≪≫
    moduleSupportSingleTotalShiftIso R ((T.rightDerived q).obj G) p q

/-- The original single-interval first-page comparison. -/
def moduleEndofunctorE2FirstPageIso {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (p q : ℕ) :=
  (moduleEndofunctorAbelianSpectralObject R T F I).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂Cohomological ((p : ℤ), (q : ℤ))
    (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl

/-- The actual E₂ page: actual module Ext against the actual derived coefficient. -/
def moduleEndofunctorSpectralSequenceE2Equiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (p q : ℕ) :
    ((moduleEndofunctorSpectralSequence R T F I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      Abelian.Ext F ((T.rightDerived q).obj G) p := by
  let eHom := (moduleSupportDerivedHom R F).mapIso (moduleEndofunctorE2TotalShiftIso R T I p q)
  exact (moduleEndofunctorE2FirstPageIso R T F I p q).addCommGroupIsoToAddEquiv.trans
    (eHom.addCommGroupIsoToAddEquiv.trans (Abelian.Ext.homAddEquiv
      (X := F) (Y := (T.rightDerived q).obj G) (n := p)).symm)

/-- Connectiveness and module-category t-structure orthogonality give first-quadrant support. -/
instance moduleEndofunctorAbelianSpectralObject_isFirstQuadrant
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    (moduleEndofunctorAbelianSpectralObject R T F I).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    let t := DerivedCategory.TStructure.t (C := SheafOfModules.{u} R)
    have h := t.isZero_eTruncLT_obj_obj (moduleEndofunctorDerivedObject R T I) 0 j hj
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
      ((t.eTruncLT.obj j).obj (moduleEndofunctorDerivedObject R T I))
    have hshift := t.isGE_shift
      ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj
        (moduleEndofunctorDerivedObject R T I))) (n + 1) n 1 (by lia)
    change IsZero (AddCommGrpCat.of
      (((DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).obj F) ⟶
        ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj
          (moduleEndofunctorDerivedObject R T I)))⟦n⟧))
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact ⟨fun a b ↦ (t.zero a 0 1).trans (t.zero b 0 1).symm⟩

/-- The actual total interval group of the mapped resolution. -/
def moduleEndofunctorSpectralTotal {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℤ) : AddCommGrpCat.{u + 1} :=
  ExposeI.SpectralObjectConvergence.total (moduleEndofunctorAbelianSpectralObject R T F I) n

/-- The genuine finite increasing filtration on actual total cohomology. -/
def moduleEndofunctorSpectralFiniteFiltration {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    Fin (n + 2) →o Subobject (moduleEndofunctorSpectralTotal R T F I n) :=
  ExposeI.SpectralObjectConvergence.finiteFiltration
    (moduleEndofunctorAbelianSpectralObject R T F I) n

@[simp]
theorem moduleEndofunctorSpectralFiniteFiltration_zero {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleEndofunctorSpectralFiniteFiltration R T F I n 0 = ⊥ :=
  ExposeI.SpectralObjectConvergence.finiteFiltration_zero _ n

@[simp]
theorem moduleEndofunctorSpectralFiniteFiltration_last {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleEndofunctorSpectralFiniteFiltration R T F I n (Fin.last (n + 1)) = ⊤ :=
  ExposeI.SpectralObjectConvergence.finiteFiltration_last _ n

/-- The actual consecutive quotients of the canonical filtration. -/
def moduleEndofunctorSpectralGradedPiece {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n q : ℤ) : AddCommGrpCat.{u + 1} :=
  ExposeI.SpectralObjectConvergence.gradedPiece (moduleEndofunctorAbelianSpectralObject R T F I) n q

/-- The stable actual page terms are the genuine finite-filtration quotients. -/
def moduleEndofunctorSpectralStablePageIsoGraded {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) (q : Fin (n + 1)) (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((moduleEndofunctorSpectralSequence R T F I).page r).X ((n : ℤ) - q, q) ≅
      moduleEndofunctorSpectralGradedPiece R T F I n q :=
  ExposeI.SpectralObjectConvergence.stablePageIsoGradedTotal
    (moduleEndofunctorAbelianSpectralObject R T F I) n q r hr

end SGA.SGA2.ExposeVI
