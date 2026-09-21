/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RingedModuleSpectralCoefficientFunctor
import SGA.SGA2.ExposeV.RingedModuleSpectralE2Linear

/-!
# V.3.2: naturality of the original E₂ comparison

The original first-page, normalized truncation, total-shift and Ext comparison
maps intertwine the actual coefficient morphisms. In particular the E₂ maps
are the original supported-cohomology maps of the original higher module
direct-image coefficient maps.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat ComposableArrows

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {R : Sheaf RingCat.{u} X} {S : Sheaf RingCat.{u} Y}
  (φ : S ⟶ (Sheaf.pushforward RingCat f).obj R) (Z : Closeds Y)

local instance e2NaturalityHasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} Y) :=
  HasDerivedCategory.standard _

variable {M N : SheafOfModules.{u} R} {I : InjectiveResolution M} {J : InjectiveResolution N}

/-- On the single-degree interval, the actual coefficient map is postcomposition. -/
theorem ringedModulePushforwardSpectralIntervalMap_apply
    (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ) (q : ℕ)
    (x : (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) 0).obj (ExposeI.zZX_closed Z) ⟶
      (ExposeI.derivedSingleDegreeTruncation (ringedModulePushforwardDerivedObject f φ I)
        (q : ℤ))⟦n⟧) :
    ((ringedModulePushforwardAbelianSpectralObjectMap f φ Z α).hom n).app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))) x =
      x ≫ (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
        (ringedModulePushforwardDerivedObjectMap f φ α))⟦n⟧' := by
  change ((ringedDerivedSupportedHom Z).shift n).map
    (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
      (ringedModulePushforwardDerivedObjectMap f φ α)) x = _
  rfl

set_option maxHeartbeats 800000 in
-- The same named first-page maps occur with two different resolution coefficient objects.
/-- The original first-page comparison is natural in every actual resolution map. -/
theorem ringedModulePushforwardE2FirstPageIso_naturality_apply
    (α : I.cocomplex ⟶ J.cocomplex) (p q : ℕ)
    (x : ((ringedModulePushforwardAdditiveSpectralSequence f φ Z I).page 2).X
      ((p : ℤ), (q : ℤ))) :
    (ringedModulePushforwardE2FirstPageIso f φ Z J p q).hom
        (((ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
          (ringedModulePushforwardAbelianSpectralObjectMap f φ Z α)
          Abelian.SpectralObject.coreE₂Cohomological).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      (ringedModulePushforwardE2FirstPageIso f φ Z I p q).hom x ≫
        (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
          (ringedModulePushforwardDerivedObjectMap f φ α))⟦(p : ℤ) + (q : ℤ)⟧' := by
  have hm :
      ((ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
        (ringedModulePushforwardAbelianSpectralObjectMap f φ Z α)
        Abelian.SpectralObject.coreE₂Cohomological).hom 2).f ((p : ℤ), (q : ℤ)) ≫
          (ringedModulePushforwardE2FirstPageIso f φ Z J p q).hom =
        (ringedModulePushforwardE2FirstPageIso f φ Z I p q).hom ≫
          ((ringedModulePushforwardAbelianSpectralObjectMap f φ Z α).hom
            ((p : ℤ) + (q : ℤ))).app
            (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
              WithBotTop.coe_le_coe.mpr (by lia)))) :=
    ExposeI.SpectralObjectCoefficientMaps.firstPageMap_hom
      (ringedModulePushforwardAbelianSpectralObjectMap f φ Z α)
      Abelian.SpectralObject.coreE₂Cohomological ((p : ℤ), (q : ℤ))
      (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl
  have h := ConcreteCategory.congr_hom hm x
  simp only [ConcreteCategory.comp_apply] at h
  erw [ringedModulePushforwardSpectralIntervalMap_apply] at h
  exact h

/-- The original total-shift comparison retains the original higher-direct-image map. -/
@[reassoc]
theorem ringedModulePushforwardE2TotalShiftIso_naturality
    (a : M ⟶ N) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p q : ℕ) :
    (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
        (ringedModulePushforwardDerivedObjectMap f φ α))⟦(p : ℤ) + (q : ℤ)⟧' ≫
        (ringedModulePushforwardE2TotalShiftIso f φ J p q).hom =
      (ringedModulePushforwardE2TotalShiftIso f φ I p q).hom ≫
        ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) 0).map
          ((SheafOfModules.toSheaf S).map ((derivedRingedModulePushforward f φ q).map a)))
            ⟦(p : ℤ)⟧' := by
  dsimp only [ringedModulePushforwardE2TotalShiftIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc, ringedModulePushforwardE2TruncationIso_naturality f φ a α hα,
    Functor.map_comp_assoc, ExposeI.supportedSingleTotalShiftIso_naturality]
  simp only [Category.assoc]

/-- The original additive E₂ comparison intertwines the original higher-direct-image
coefficient maps. -/
theorem ringedModulePushforwardAdditiveSpectralSequenceE2Equiv_naturality
    (a : M ⟶ N) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p q : ℕ)
    (x : ((ringedModulePushforwardAdditiveSpectralSequence f φ Z I).page 2).X
      ((p : ℤ), (q : ℤ))) :
    ringedModulePushforwardAdditiveSpectralSequenceE2Equiv f φ Z J p q
        (((ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
          (ringedModulePushforwardAbelianSpectralObjectMap f φ Z α)
          Abelian.SpectralObject.coreE₂Cohomological).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      ExposeI.H_Z_map Z ((SheafOfModules.toSheaf S).map
        ((derivedRingedModulePushforward f φ q).map a)) p
        (ringedModulePushforwardAdditiveSpectralSequenceE2Equiv f φ Z I p q x) := by
  rw [ringedModulePushforwardAdditiveSpectralSequenceE2Equiv_apply,
    ringedModulePushforwardAdditiveSpectralSequenceE2Equiv_apply,
    ringedModulePushforwardE2FirstPageIso_naturality_apply,
    Category.assoc, ringedModulePushforwardE2TotalShiftIso_naturality f φ a α hα,
    ← Category.assoc]
  exact supportedExtHomAddEquiv_naturality Z _ p _

/-- The original page-forgetful comparison is natural on the native module carriers. -/
theorem ringedModulePushforwardModulePageXForgetIso_naturality_apply
    (α : I.cocomplex ⟶ J.cocomplex) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (x : ((ringedModulePushforwardModuleSpectralSequence f φ Z I).page r hr).X pq) :
    (ringedModulePushforwardModulePageXForgetIso f φ Z J r hr pq).hom
        (((ringedModulePushforwardModuleSpectralSequenceMap f φ Z α).hom r hr).f pq x) =
      ((ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
        (ringedModulePushforwardAbelianSpectralObjectMap f φ Z α)
        Abelian.SpectralObject.coreE₂Cohomological).hom r hr).f pq
        ((ringedModulePushforwardModulePageXForgetIso f φ Z I r hr pq).hom x) := by
  have h := ConcreteCategory.congr_hom
    (ringedModulePushforwardModulePageXForgetIso_naturality f φ Z α r hr pq) x
  simp only [ConcreteCategory.comp_apply] at h
  exact h

private theorem moduleCohomologyIsoH_Z_inv_naturality_apply
    {A B : SheafOfModules.{u} S} (a : A ⟶ B) (p : ℕ)
    (x : ExposeI.H_Z Z ((SheafOfModules.toSheaf S).obj A) p) :
    (derivedModuleGammaZSectionsObjIsoH_Z S Z B p).inv
        (ExposeI.H_Z_map Z ((SheafOfModules.toSheaf S).map a) p x) =
      ((derivedModuleGammaZSections S Z ⊤ p).map a)
        ((derivedModuleGammaZSectionsObjIsoH_Z S Z A p).inv x) := by
  have hm := (derivedModuleGammaZSectionsIsoH_Z S Z p).inv.naturality a
  simp only [CategoryTheory.Functor.comp_map] at hm
  have h := ConcreteCategory.congr_hom hm x
  simp only [ConcreteCategory.comp_apply] at h
  exact h

set_option maxHeartbeats 800000 in
-- Unfold the unchanged composite once, outside the coefficient-naturality proof.
set_option maxRecDepth 2048 in
/-- The original linear E₂ equivalence has exactly the preexisting comparison factors. -/
theorem ringedModulePushforwardModuleE2LinearEquiv_apply
    (I : InjectiveResolution M) (p q : ℕ)
    (x : ((ringedModulePushforwardModuleSpectralSequence f φ Z I).page 2).X
      ((p : ℤ), (q : ℤ))) :
    ringedModulePushforwardModuleE2LinearEquiv f φ Z I p q x =
      (derivedModuleGammaZSectionsObjIsoH_Z S Z
        ((derivedRingedModulePushforward f φ q).obj M) p).inv
        (ringedModulePushforwardAdditiveSpectralSequenceE2Equiv f φ Z I p q
          ((ringedModulePushforwardModulePageXForgetIso f φ Z I 2 (by lia)
            ((p : ℤ), (q : ℤ))).hom x)) := rfl

set_option maxHeartbeats 800000 in
-- The canonical page and supported-cohomology comparisons use their native module carriers.
/-- The actual module-linear E₂ identification is natural for all compatible coefficient lifts. -/
theorem ringedModulePushforwardModuleE2LinearEquiv_naturality
    (a : M ⟶ N) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p q : ℕ)
    (x : ((ringedModulePushforwardModuleSpectralSequence f φ Z I).page 2).X
      ((p : ℤ), (q : ℤ))) :
    ringedModulePushforwardModuleE2LinearEquiv f φ Z J p q
        (((ringedModulePushforwardModuleSpectralSequenceMap f φ Z α).hom 2).f
          ((p : ℤ), (q : ℤ)) x) =
      ((derivedModuleGammaZSections S Z ⊤ p).map ((derivedRingedModulePushforward f φ q).map a))
        (ringedModulePushforwardModuleE2LinearEquiv f φ Z I p q x) := by
  rw [ringedModulePushforwardModuleE2LinearEquiv_apply,
    ringedModulePushforwardModuleE2LinearEquiv_apply,
    ringedModulePushforwardModulePageXForgetIso_naturality_apply,
    ringedModulePushforwardAdditiveSpectralSequenceE2Equiv_naturality f φ Z a α hα]
  exact moduleCohomologyIsoH_Z_inv_naturality_apply Z
    ((derivedRingedModulePushforward f φ q).map a) p _

set_option maxHeartbeats 800000 in
-- Specialize the original page map to the canonical resolution lift.
set_option maxRecDepth 2048 in
/-- V.3.2's coefficient functor has the original module-supported higher-direct-image maps on E₂. -/
theorem ringedModulePushforwardModuleSpectralSequenceCoefficientMap_E2
    (a : M ⟶ N) (I : InjectiveResolution M) (J : InjectiveResolution N) (p q : ℕ)
    (x : ((ringedModulePushforwardModuleSpectralSequence f φ Z I).page 2).X
      ((p : ℤ), (q : ℤ))) :
    ringedModulePushforwardModuleE2LinearEquiv f φ Z J p q
        (((ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z a I J).hom 2).f
          ((p : ℤ), (q : ℤ)) x) =
      ((derivedModuleGammaZSections S Z ⊤ p).map ((derivedRingedModulePushforward f φ q).map a))
        (ringedModulePushforwardModuleE2LinearEquiv f φ Z I p q x) := by
  dsimp only [ringedModulePushforwardModuleSpectralSequenceCoefficientMap]
  have h := ringedModulePushforwardModuleE2LinearEquiv_naturality f φ Z a
    (InjectiveResolution.desc a J I) (InjectiveResolution.desc_commutes_zero a J I) p q x
  exact h

end SGA.SGA2.ExposeV
