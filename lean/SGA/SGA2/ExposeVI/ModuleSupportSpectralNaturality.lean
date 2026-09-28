/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportSpectralAbutment
import SGA.SGA2.ExposeI.DerivedTruncationNaturality
import SGA.SGA2.ExposeI.LocalToGlobalE2Naturality
import SGA.SGA2.ExposeI.SpectralObjectConvergenceNaturality

/-!
# SGA 2, VI.1.6.3: naturality of the original E₂ identification

The actual coefficient spectral maps act on E₂ by the original module Ext
maps of the original derived supported-coefficient maps. Every comparison
uses the unchanged truncation, first-page, shift and Ext isomorphisms.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat ComposableArrows

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (Z : Closeds X)
  (F : SheafOfModules.{u} R)

local instance : HasDerivedCategory.{u + 1} (SheafOfModules.{u} R) :=
  HasDerivedCategory.standard _

variable {G H : SheafOfModules.{u} R} {I : InjectiveResolution G} {J : InjectiveResolution H}

/-- The original derived-homology comparison retains every augmented coefficient lift. -/
@[reassoc]
theorem moduleSupportDerivedHomologyIso_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (q : ℕ) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} R) (q : ℤ)).map
        (moduleSupportDerivedObjectMap R Z α) ≫ (moduleSupportDerivedHomologyIso R Z J q).hom =
      (moduleSupportDerivedHomologyIso R Z I q).hom ≫ (derivedModuleGammaZSheaf R Z q).map a := by
  have hQ := (DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} R)
    (q : ℤ)).hom.naturality (moduleSupportResolutionIntMap R Z α)
  simp only [Functor.comp_map] at hQ
  dsimp only [moduleSupportDerivedHomologyIso, Iso.trans_hom, Iso.app_hom]
  erw [← Category.assoc, hQ, Category.assoc]
  exact congrArg
    (fun f ↦ (DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} R)
      (q : ℤ)).hom.app (moduleSupportResolutionInt R Z I) ≫ f)
    (ExposeI.injectiveResolutionIntHomologyIso_naturality
      (moduleGammaZSheafFunctor R Z) a I J α hα q)

/-- The normalized one-degree truncation comparison retains the original derived map. -/
@[reassoc]
theorem moduleSupportE2TruncationIso_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (q : ℕ) :
    ExposeI.derivedSingleDegreeTruncationMap (q : ℤ) (moduleSupportDerivedObjectMap R Z α) ≫
        (moduleSupportE2TruncationIso R Z J q).hom =
      (moduleSupportE2TruncationIso R Z I q).hom ≫
        (DerivedCategory.singleFunctor (SheafOfModules.{u} R) (q : ℤ)).map
          ((derivedModuleGammaZSheaf R Z q).map a) := by
  dsimp only [moduleSupportE2TruncationIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [ExposeI.derivedSingleDegreeTruncationIsoSingle_naturality_assoc,
    ← Functor.map_comp, moduleSupportDerivedHomologyIso_naturality R Z a α hα, Functor.map_comp]
  simp only [Category.assoc]

/-- Shifting single module sheaves retains every original coefficient morphism. -/
@[reassoc]
theorem moduleSupportSingleTotalShiftIso_naturality {A B : SheafOfModules.{u} R}
    (a : A ⟶ B) (p q : ℤ) :
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} R) q).map a)⟦p + q⟧' ≫
        (moduleSupportSingleTotalShiftIso R B p q).hom =
      (moduleSupportSingleTotalShiftIso R A p q).hom ≫
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).map a)⟦p⟧' := by
  let e := (DerivedCategory.singleFunctors (SheafOfModules.{u} R)).shiftIso
    (p + q) (-p) q (by lia) ≪≫
      ((DerivedCategory.singleFunctors (SheafOfModules.{u} R)).shiftIso
        p (-p) 0 (by lia)).symm
  exact e.hom.naturality a

/-- The original shifted E₂ comparison is natural in the actual coefficient map. -/
@[reassoc]
theorem moduleSupportE2TotalShiftIso_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p q : ℕ) :
    (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
        (moduleSupportDerivedObjectMap R Z α))⟦(p : ℤ) + (q : ℤ)⟧' ≫
        (moduleSupportE2TotalShiftIso R Z J p q).hom =
      (moduleSupportE2TotalShiftIso R Z I p q).hom ≫
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).map
          ((derivedModuleGammaZSheaf R Z q).map a))⟦(p : ℤ)⟧' := by
  dsimp only [moduleSupportE2TotalShiftIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc, moduleSupportE2TruncationIso_naturality R Z a α hα,
    Functor.map_comp_assoc, moduleSupportSingleTotalShiftIso_naturality]
  simp only [Category.assoc]


/-- The actual interval map is postcomposition by the original truncation map. -/
theorem moduleSupportSpectralIntervalMap_apply
    (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ) (q : ℕ)
    (x : (DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).obj (F) ⟶
      (ExposeI.derivedSingleDegreeTruncation (moduleSupportDerivedObject R Z I) (q : ℤ))⟦n⟧) :
    ((moduleSupportAbelianSpectralObjectMap R Z F α).hom n).app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))) x =
      x ≫ (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
        (moduleSupportDerivedObjectMap R Z α))⟦n⟧' := rfl

section

set_option maxHeartbeats 800000 in
-- Comparing the original first-page map expands the spectral-object page construction.
/-- The original first-page comparison commutes with actual page coefficient maps. -/
theorem moduleSupportE2FirstPageIso_naturality_apply
    (α : I.cocomplex ⟶ J.cocomplex) (p q : ℕ)
    (x : ((moduleSupportSpectralSequence R Z F I).page 2).X ((p : ℤ), (q : ℤ))) :
    (moduleSupportE2FirstPageIso R Z F J p q).hom
        (((moduleSupportSpectralSequenceMap R Z F α).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      (moduleSupportE2FirstPageIso R Z F I p q).hom x ≫
        (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
          (moduleSupportDerivedObjectMap R Z α))⟦(p : ℤ) + (q : ℤ)⟧' := by
  have hm : ((moduleSupportSpectralSequenceMap R Z F α).hom 2).f ((p : ℤ), (q : ℤ)) ≫
        (moduleSupportE2FirstPageIso R Z F J p q).hom =
      (moduleSupportE2FirstPageIso R Z F I p q).hom ≫
        ((moduleSupportAbelianSpectralObjectMap R Z F α).hom
          ((p : ℤ) + (q : ℤ))).app
          (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
            WithBotTop.coe_le_coe.mpr (by lia)))) :=
    ExposeI.SpectralObjectCoefficientMaps.firstPageMap_hom
      (moduleSupportAbelianSpectralObjectMap R Z F α)
      Abelian.SpectralObject.coreE₂Cohomological ((p : ℤ), (q : ℤ))
      (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl
  have h := ConcreteCategory.congr_hom hm x
  simp only [ConcreteCategory.comp_apply] at h
  erw [moduleSupportSpectralIntervalMap_apply] at h
  exact h

end

/-- The original E₂ equivalence has precisely its declared first-page and shift factors. -/
theorem moduleSupportSpectralSequenceE2Equiv_apply (I : InjectiveResolution G) (p q : ℕ)
    (x : ((moduleSupportSpectralSequence R Z F I).page 2).X ((p : ℤ), (q : ℤ))) :
    moduleSupportSpectralSequenceE2Equiv R Z F I p q x =
      Abelian.Ext.homAddEquiv.symm
        ((moduleSupportE2FirstPageIso R Z F I p q).hom x ≫
          (moduleSupportE2TotalShiftIso R Z I p q).hom) := rfl

/-- Supported Ext in the original sheaf category retains the original derived Hom map. -/
private theorem moduleSupportExtHomEquiv_naturality
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
theorem moduleSupportSpectralSequenceE2Equiv_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p q : ℕ)
    (x : ((moduleSupportSpectralSequence R Z F I).page 2).X ((p : ℤ), (q : ℤ))) :
    moduleSupportSpectralSequenceE2Equiv R Z F J p q
        (((moduleSupportSpectralSequenceMap R Z F α).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      (Abelian.extFunctorObj F p).map ((derivedModuleGammaZSheaf R Z q).map a)
        (moduleSupportSpectralSequenceE2Equiv R Z F I p q x) := by
  rw [moduleSupportSpectralSequenceE2Equiv_apply,
    moduleSupportSpectralSequenceE2Equiv_apply,
    moduleSupportE2FirstPageIso_naturality_apply,
    Category.assoc, moduleSupportE2TotalShiftIso_naturality R Z a α hα,
    ← Category.assoc]
  exact moduleSupportExtHomEquiv_naturality R F _ p _

/-- The actual map on the total interval, hence on its canonical image filtration. -/
def moduleSupportSpectralTotalMap (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ) :
    moduleSupportSpectralTotal R Z F I n ⟶ moduleSupportSpectralTotal R Z F J n :=
  ExposeI.SpectralObjectConvergence.totalMap (moduleSupportAbelianSpectralObjectMap R Z F α) n


end SGA.SGA2.ExposeVI
