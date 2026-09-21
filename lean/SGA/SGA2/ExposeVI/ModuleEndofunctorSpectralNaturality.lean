/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleEndofunctorSpectralFunctor
import SGA.SGA2.ExposeVI.ModuleSupportSpectralNaturality
import SGA.SGA2.ExposeI.DerivedTruncationNaturality
import SGA.SGA2.ExposeI.LocalToGlobalE2Naturality
import SGA.SGA2.ExposeI.SpectralObjectConvergenceNaturality

/-!
# Naturality of the original module-endofunctor E₂ comparison

Actual coefficient spectral maps act on the original E₂ groups by module
Ext of the original right-derived functor maps. All comparisons retain
the existing truncation, first-page, shift and Ext identifications.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat ComposableArrows

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)
  (T : SheafOfModules.{u} R ⥤ SheafOfModules.{u} R) [T.Additive]
  (F : SheafOfModules.{u} R)

local instance moduleEndofunctorNaturalityHasDerivedCategory : HasDerivedCategory.{u + 1} (SheafOfModules.{u} R) :=
  HasDerivedCategory.standard _

variable {G H : SheafOfModules.{u} R} {I : InjectiveResolution G} {J : InjectiveResolution H}

/-- The original derived-homology comparison retains every augmented coefficient lift. -/
@[reassoc]
theorem moduleEndofunctorDerivedHomologyIso_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (q : ℕ) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} R) (q : ℤ)).map
        (moduleEndofunctorDerivedObjectMap R T α) ≫ (moduleEndofunctorDerivedHomologyIso R T J q).hom =
      (moduleEndofunctorDerivedHomologyIso R T I q).hom ≫ (T.rightDerived q).map a := by
  have hQ := (DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} R)
    (q : ℤ)).hom.naturality (moduleEndofunctorResolutionIntMap R T α)
  simp only [Functor.comp_map] at hQ
  dsimp only [moduleEndofunctorDerivedHomologyIso, Iso.trans_hom, Iso.app_hom]
  erw [← Category.assoc, hQ, Category.assoc]
  exact congrArg
    (fun f ↦ (DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} R)
      (q : ℤ)).hom.app (moduleEndofunctorResolutionInt R T I) ≫ f)
    (ExposeI.injectiveResolutionIntHomologyIso_naturality
      T a I J α hα q)

/-- The normalized one-degree truncation comparison retains the original derived map. -/
@[reassoc]
theorem moduleEndofunctorE2TruncationIso_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (q : ℕ) :
    ExposeI.derivedSingleDegreeTruncationMap (q : ℤ) (moduleEndofunctorDerivedObjectMap R T α) ≫
        (moduleEndofunctorE2TruncationIso R T J q).hom =
      (moduleEndofunctorE2TruncationIso R T I q).hom ≫
        (DerivedCategory.singleFunctor (SheafOfModules.{u} R) (q : ℤ)).map
          ((T.rightDerived q).map a) := by
  dsimp only [moduleEndofunctorE2TruncationIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [ExposeI.derivedSingleDegreeTruncationIsoSingle_naturality_assoc,
    ← Functor.map_comp, moduleEndofunctorDerivedHomologyIso_naturality R T a α hα, Functor.map_comp]
  simp only [Category.assoc]

/-- The original shifted E₂ comparison is natural in the actual coefficient map. -/
@[reassoc]
theorem moduleEndofunctorE2TotalShiftIso_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p q : ℕ) :
    (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
        (moduleEndofunctorDerivedObjectMap R T α))⟦(p : ℤ) + (q : ℤ)⟧' ≫
        (moduleEndofunctorE2TotalShiftIso R T J p q).hom =
      (moduleEndofunctorE2TotalShiftIso R T I p q).hom ≫
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).map
          ((T.rightDerived q).map a))⟦(p : ℤ)⟧' := by
  dsimp only [moduleEndofunctorE2TotalShiftIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc, moduleEndofunctorE2TruncationIso_naturality R T a α hα,
    Functor.map_comp_assoc, moduleSupportSingleTotalShiftIso_naturality]
  simp only [Category.assoc]


/-- The actual interval map is postcomposition by the original truncation map. -/
theorem moduleEndofunctorSpectralIntervalMap_apply
    (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ) (q : ℕ)
    (x : (DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).obj (F) ⟶
      (ExposeI.derivedSingleDegreeTruncation (moduleEndofunctorDerivedObject R T I) (q : ℤ))⟦n⟧) :
    ((moduleEndofunctorAbelianSpectralObjectMap R T F α).hom n).app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))) x =
      x ≫ (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
        (moduleEndofunctorDerivedObjectMap R T α))⟦n⟧' := rfl

section

set_option maxHeartbeats 800000 in
-- Comparing the original first-page map expands the spectral-object page construction.
/-- The original first-page comparison commutes with actual page coefficient maps. -/
theorem moduleEndofunctorE2FirstPageIso_naturality_apply
    (α : I.cocomplex ⟶ J.cocomplex) (p q : ℕ)
    (x : ((moduleEndofunctorSpectralSequence R T F I).page 2).X ((p : ℤ), (q : ℤ))) :
    (moduleEndofunctorE2FirstPageIso R T F J p q).hom
        (((moduleEndofunctorSpectralSequenceMap R T F α).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      (moduleEndofunctorE2FirstPageIso R T F I p q).hom x ≫
        (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
          (moduleEndofunctorDerivedObjectMap R T α))⟦(p : ℤ) + (q : ℤ)⟧' := by
  have hm : ((moduleEndofunctorSpectralSequenceMap R T F α).hom 2).f ((p : ℤ), (q : ℤ)) ≫
        (moduleEndofunctorE2FirstPageIso R T F J p q).hom =
      (moduleEndofunctorE2FirstPageIso R T F I p q).hom ≫
        ((moduleEndofunctorAbelianSpectralObjectMap R T F α).hom
          ((p : ℤ) + (q : ℤ))).app
          (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
            WithBotTop.coe_le_coe.mpr (by lia)))) :=
    ExposeI.SpectralObjectCoefficientMaps.firstPageMap_hom
      (moduleEndofunctorAbelianSpectralObjectMap R T F α)
      Abelian.SpectralObject.coreE₂Cohomological ((p : ℤ), (q : ℤ))
      (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl
  have h := ConcreteCategory.congr_hom hm x
  simp only [ConcreteCategory.comp_apply] at h
  erw [moduleEndofunctorSpectralIntervalMap_apply] at h
  exact h

end

/-- The original E₂ equivalence has precisely its declared first-page and shift factors. -/
theorem moduleEndofunctorSpectralSequenceE2Equiv_apply (I : InjectiveResolution G) (p q : ℕ)
    (x : ((moduleEndofunctorSpectralSequence R T F I).page 2).X ((p : ℤ), (q : ℤ))) :
    moduleEndofunctorSpectralSequenceE2Equiv R T F I p q x =
      Abelian.Ext.homAddEquiv.symm
        ((moduleEndofunctorE2FirstPageIso R T F I p q).hom x ≫
          (moduleEndofunctorE2TotalShiftIso R T I p q).hom) := rfl

/-- Supported Ext in the original sheaf category retains the original derived Hom map. -/
private theorem moduleEndofunctorExtHomEquiv_naturality
    {A B : SheafOfModules.{u} R} (a : A ⟶ B) (p : ℕ)
    (x : (DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).obj (F) ⟶
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).obj A)⟦(p : ℤ)⟧) :
    Abelian.Ext.homAddEquiv.symm
        (x ≫ ((DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).map a)⟦(p : ℤ)⟧') =
      (Abelian.extFunctorObj F p).map a (Abelian.Ext.homAddEquiv.symm x) := by
  apply (Abelian.Ext.homAddEquiv (X := F) (Y := B) (n := p)).injective
  change (Abelian.Ext.homAddEquiv.symm _).hom =
    ((Abelian.Ext.homAddEquiv.symm x).comp (Abelian.Ext.mk₀ a) (add_zero p)).hom
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  change Abelian.Ext.homAddEquiv (Abelian.Ext.homAddEquiv.symm _) =
    Abelian.Ext.homAddEquiv (Abelian.Ext.homAddEquiv.symm x) ≫ _
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The genuine E₂ page morphism is supported cohomology of the original derived map. -/
theorem moduleEndofunctorSpectralSequenceE2Equiv_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p q : ℕ)
    (x : ((moduleEndofunctorSpectralSequence R T F I).page 2).X ((p : ℤ), (q : ℤ))) :
    moduleEndofunctorSpectralSequenceE2Equiv R T F J p q
        (((moduleEndofunctorSpectralSequenceMap R T F α).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      (Abelian.extFunctorObj F p).map ((T.rightDerived q).map a)
        (moduleEndofunctorSpectralSequenceE2Equiv R T F I p q x) := by
  rw [moduleEndofunctorSpectralSequenceE2Equiv_apply,
    moduleEndofunctorSpectralSequenceE2Equiv_apply,
    moduleEndofunctorE2FirstPageIso_naturality_apply,
    Category.assoc, moduleEndofunctorE2TotalShiftIso_naturality R T a α hα,
    ← Category.assoc]
  exact moduleEndofunctorExtHomEquiv_naturality R F _ p _

/-- The actual map on the total interval, hence on its canonical image filtration. -/
def moduleEndofunctorSpectralTotalMap (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ) :
    moduleEndofunctorSpectralTotal R T F I n ⟶ moduleEndofunctorSpectralTotal R T F J n :=
  ExposeI.SpectralObjectConvergence.totalMap (moduleEndofunctorAbelianSpectralObjectMap R T F α) n


end SGA.SGA2.ExposeVI
