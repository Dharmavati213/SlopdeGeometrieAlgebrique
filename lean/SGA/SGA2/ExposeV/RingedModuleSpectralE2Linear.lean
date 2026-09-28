/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.RingedModuleSpectralE2Scalars
import SGA.SGA2.ExposeV.RingedModuleCohomologyScalars
import SGA.SGA2.ExposeV.SpectralObjectModuleScalars
import SGA.SGA2.ExposeV.RingedModuleSpectralModuleLift
import SGA.SGA2.ExposeI.LocalToGlobalE2Naturality

/-!
# V.3.2: the original E₂ identification is module-linear

The canonical page-forgetful comparison, first-page computation, normalized
truncation, and original supported-cohomology comparison all retain the
same scalar action. Their original composite therefore identifies the
module-valued E₂ page with module-supported cohomology of the actual higher
module direct image, with no commutativity or flatness hypothesis.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat ComposableArrows

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {R : Sheaf RingCat.{u} X} {S : Sheaf RingCat.{u} Y}
  (φ : S ⟶ (Sheaf.pushforward RingCat f).obj R) (Z : Closeds Y)

local instance e2LinearHasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} Y) :=
  HasDerivedCategory.standard _

/-- The unchanged first-page isomorphism used by the original E₂ comparison. -/
def ringedModulePushforwardE2FirstPageIso {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (p q : ℕ) :
    ((ringedModulePushforwardAdditiveSpectralSequence f φ Z I).page 2).X ((p : ℤ), (q : ℤ)) ≅
      AddCommGrpCat.of
        ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) 0).obj (ExposeI.zZX_closed Z) ⟶
          (ExposeI.derivedSingleDegreeTruncation (ringedModulePushforwardDerivedObject f φ I)
            (q : ℤ))⟦(p : ℤ) + (q : ℤ)⟧) :=
  (ringedModulePushforwardAbelianSpectralObject f φ Z I).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂Cohomological
    ((p : ℤ), (q : ℤ)) (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl

/-- The unchanged truncation and shift isomorphism used by the original E₂ comparison. -/
def ringedModulePushforwardE2TotalShiftIso {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (p q : ℕ) :
    (ExposeI.derivedSingleDegreeTruncation (ringedModulePushforwardDerivedObject f φ I)
        (q : ℤ))⟦(p : ℤ) + (q : ℤ)⟧ ≅
      ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) 0).obj
        ((SheafOfModules.toSheaf S).obj ((derivedRingedModulePushforward f φ q).obj M)))⟦(p : ℤ)⟧ :=
  (shiftFunctor (DerivedCategory (Sheaf AddCommGrpCat.{u} Y))
      ((p : ℤ) + (q : ℤ))).mapIso (ringedModulePushforwardE2TruncationIso f φ I q) ≪≫
    ExposeI.supportedSingleTotalShiftIso
      ((SheafOfModules.toSheaf S).obj ((derivedRingedModulePushforward f φ q).obj M))
      (p : ℤ) (q : ℤ)

set_option maxHeartbeats 800000 in
-- Identifying the original inline factors unfolds both spectral-page and derived-Hom structures.
/-- The original E₂ equivalence written using exactly its original factors. -/
theorem ringedModulePushforwardAdditiveSpectralSequenceE2Equiv_apply
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M) (p q : ℕ)
    (x : ((ringedModulePushforwardAdditiveSpectralSequence f φ Z I).page 2).X
      ((p : ℤ), (q : ℤ))) :
    ringedModulePushforwardAdditiveSpectralSequenceE2Equiv f φ Z I p q x =
      (Abelian.Ext.homAddEquiv (X := ExposeI.zZX_closed Z)
        (Y := (SheafOfModules.toSheaf S).obj ((derivedRingedModulePushforward f φ q).obj M))
        (n := p)).symm
        ((ringedModulePushforwardE2FirstPageIso f φ Z I p q).hom x ≫
          (ringedModulePushforwardE2TotalShiftIso f φ I p q).hom) := by
  simp only [ringedModulePushforwardAdditiveSpectralSequenceE2Equiv, AddEquiv.trans_apply]
  rfl

/-- The retained scalar endomorphism on the original single-degree interval is postcomposition. -/
theorem ringedModulePushforwardSpectralIntervalScalar_apply
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M) (n : ℤ) (q : ℕ)
    (r : S.obj.obj (op (⊤ : Opens Y)))
    (x : (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) 0).obj (ExposeI.zZX_closed Z) ⟶
      (ExposeI.derivedSingleDegreeTruncation (ringedModulePushforwardDerivedObject f φ I)
        (q : ℤ))⟦n⟧) :
    ((ringedModulePushforwardSpectralScalarRingHom f φ Z I r).hom n).app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))) x =
      x ≫ (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
        (ringedModulePushforwardDerivedScalarRingHom f φ I r))⟦n⟧' := by
  change ((ringedDerivedSupportedHom Z).shift n).map
    (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
      (ringedModulePushforwardDerivedScalarRingHom f φ I r)) x = _
  rfl

set_option maxHeartbeats 800000 in
-- The two presentations use the same first-page isomorphism and concrete-category coercions.
/-- The original first-page computation retains the actual scalar truncation map. -/
theorem ringedModulePushforwardE2FirstPageIso_scalar_apply
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M) (p q : ℕ)
    (r : S.obj.obj (op (⊤ : Opens Y)))
    (x : ((ringedModulePushforwardAdditiveSpectralSequence f φ Z I).page 2).X
      ((p : ℤ), (q : ℤ))) :
    (ringedModulePushforwardE2FirstPageIso f φ Z I p q).hom
        (((ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
          (ringedModulePushforwardSpectralScalarRingHom f φ Z I r)
          Abelian.SpectralObject.coreE₂Cohomological).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      (ringedModulePushforwardE2FirstPageIso f φ Z I p q).hom x ≫
        (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
          (ringedModulePushforwardDerivedScalarRingHom f φ I r))⟦(p : ℤ) + (q : ℤ)⟧' := by
  have hm :
      ((ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
        (ringedModulePushforwardSpectralScalarRingHom f φ Z I r)
        Abelian.SpectralObject.coreE₂Cohomological).hom 2).f ((p : ℤ), (q : ℤ)) ≫
          (ringedModulePushforwardE2FirstPageIso f φ Z I p q).hom =
        (ringedModulePushforwardE2FirstPageIso f φ Z I p q).hom ≫
          ((ringedModulePushforwardSpectralScalarRingHom f φ Z I r).hom
            ((p : ℤ) + (q : ℤ))).app
            (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
              WithBotTop.coe_le_coe.mpr (by lia)))) :=
    ExposeI.SpectralObjectCoefficientMaps.firstPageMap_hom
      (ringedModulePushforwardSpectralScalarRingHom f φ Z I r)
      Abelian.SpectralObject.coreE₂Cohomological ((p : ℤ), (q : ℤ))
      (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl
  have h := ConcreteCategory.congr_hom hm x
  simp only [ConcreteCategory.comp_apply] at h
  erw [ringedModulePushforwardSpectralIntervalScalar_apply] at h
  exact h

/-- The original total-shift comparison intertwines the actual scalar maps. -/
@[reassoc]
theorem ringedModulePushforwardE2TotalShiftIso_scalar
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M) (p q : ℕ)
    (r : S.obj.obj (op (⊤ : Opens Y))) :
    (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
        (ringedModulePushforwardDerivedScalarRingHom f φ I r))⟦(p : ℤ) + (q : ℤ)⟧' ≫
        (ringedModulePushforwardE2TotalShiftIso f φ I p q).hom =
      (ringedModulePushforwardE2TotalShiftIso f φ I p q).hom ≫
        ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) 0).map
          (moduleUnderlyingGlobalScalarHom S ((derivedRingedModulePushforward f φ q).obj M) r))
            ⟦(p : ℤ)⟧' := by
  dsimp only [ringedModulePushforwardE2TotalShiftIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc, ringedModulePushforwardE2TruncationIso_scalar,
    Functor.map_comp_assoc, ExposeI.supportedSingleTotalShiftIso_naturality]
  simp only [Category.assoc]

/-- The derived-Hom description of supported cohomology respects coefficient maps. -/
theorem supportedExtHomAddEquiv_naturality
    {A B : Sheaf AddCommGrpCat.{u} Y} (a : A ⟶ B) (p : ℕ)
    (x : (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) 0).obj (ExposeI.zZX_closed Z) ⟶
      ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) 0).obj A)⟦(p : ℤ)⟧) :
    Abelian.Ext.homAddEquiv.symm
        (x ≫ ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) 0).map a)⟦(p : ℤ)⟧') =
      ExposeI.H_Z_map Z a p (Abelian.Ext.homAddEquiv.symm x) := by
  apply (Abelian.Ext.homAddEquiv (X := ExposeI.zZX_closed Z) (Y := B) (n := p)).injective
  change (Abelian.Ext.homAddEquiv.symm _).hom =
    ((Abelian.Ext.homAddEquiv.symm x).comp (Abelian.Ext.mk₀ a) (add_zero p)).hom
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  change Abelian.Ext.homAddEquiv (Abelian.Ext.homAddEquiv.symm _) =
    Abelian.Ext.homAddEquiv (Abelian.Ext.homAddEquiv.symm x) ≫ _
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The unchanged additive E₂ comparison intertwines the actual retained scalar maps. -/
theorem ringedModulePushforwardAdditiveSpectralSequenceE2Equiv_scalar
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M) (p q : ℕ)
    (r : S.obj.obj (op (⊤ : Opens Y)))
    (x : ((ringedModulePushforwardAdditiveSpectralSequence f φ Z I).page 2).X
      ((p : ℤ), (q : ℤ))) :
    ringedModulePushforwardAdditiveSpectralSequenceE2Equiv f φ Z I p q
        (((ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
          (ringedModulePushforwardSpectralScalarRingHom f φ Z I r)
          Abelian.SpectralObject.coreE₂Cohomological).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      ExposeI.H_Z_map Z
        (moduleUnderlyingGlobalScalarHom S ((derivedRingedModulePushforward f φ q).obj M) r) p
        (ringedModulePushforwardAdditiveSpectralSequenceE2Equiv f φ Z I p q x) := by
  rw [ringedModulePushforwardAdditiveSpectralSequenceE2Equiv_apply,
    ringedModulePushforwardAdditiveSpectralSequenceE2Equiv_apply,
    ringedModulePushforwardE2FirstPageIso_scalar_apply,
    Category.assoc, ringedModulePushforwardE2TotalShiftIso_scalar, ← Category.assoc]
  exact supportedExtHomAddEquiv_naturality Z _ p _

/-- The unchanged page-forgetful comparison carries native scalar multiplication
to the retained scalar endomorphism of the original additive page. -/
theorem ringedModulePushforwardModulePageXForgetIso_scalar_apply
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M)
    (k : ℤ) (hk : 2 ≤ k) (pq : ℤ × ℤ)
    (r : S.obj.obj (op (⊤ : Opens Y)))
    (x : ((ringedModulePushforwardModuleSpectralSequence f φ Z I).page k hk).X pq) :
    (ringedModulePushforwardModulePageXForgetIso f φ Z I k hk pq).hom
        (r • x : ((ringedModulePushforwardModuleSpectralSequence f φ Z I).page k hk).X pq) =
      ((ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
        (ringedModulePushforwardSpectralScalarRingHom f φ Z I r)
        Abelian.SpectralObject.coreE₂Cohomological).hom k hk).f pq
        ((ringedModulePushforwardModulePageXForgetIso f φ Z I k hk pq).hom x) := by
  have hm :
      (((ringedModulePushforwardModuleSpectralSequence f φ Z I).page k hk).X pq).smul r ≫
          (ringedModulePushforwardModulePageXForgetIso f φ Z I k hk pq).hom =
        (ringedModulePushforwardModulePageXForgetIso f φ Z I k hk pq).hom ≫
          ((ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
            (ringedModulePushforwardSpectralScalarRingHom f φ Z I r)
            Abelian.SpectralObject.coreE₂Cohomological).hom k hk).f pq :=
    spectralObjectModulePageXForgetIso_scalar
      (ringedModulePushforwardAbelianSpectralObject f φ Z I)
      (ringedModulePushforwardSpectralScalarRingHom f φ Z I) k hk pq r
  have h := ConcreteCategory.congr_hom hm x
  simp only [ConcreteCategory.comp_apply] at h
  exact h

set_option maxHeartbeats 800000 in
-- Both terms retain the named module-page and additive-page carriers.
/-- The original page comparison followed by the original additive E₂ computation
intertwines the native module scalar and the original supported-cohomology scalar. -/
theorem ringedModulePushforwardModuleE2ToH_Z_smul
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M) (p q : ℕ)
    (r : S.obj.obj (op (⊤ : Opens Y)))
    (x : ((ringedModulePushforwardModuleSpectralSequence f φ Z I).page 2).X
      ((p : ℤ), (q : ℤ))) :
    ringedModulePushforwardAdditiveSpectralSequenceE2Equiv f φ Z I p q
        ((ringedModulePushforwardModulePageXForgetIso f φ Z I 2 (by lia)
          ((p : ℤ), (q : ℤ))).hom (r • x :
            ((ringedModulePushforwardModuleSpectralSequence f φ Z I).page 2).X
              ((p : ℤ), (q : ℤ)))) =
      ExposeI.H_Z_map Z
        (moduleUnderlyingGlobalScalarHom S ((derivedRingedModulePushforward f φ q).obj M) r) p
        (ringedModulePushforwardAdditiveSpectralSequenceE2Equiv f φ Z I p q
          ((ringedModulePushforwardModulePageXForgetIso f φ Z I 2 (by lia)
            ((p : ℤ), (q : ℤ))).hom x)) := by
  rw [ringedModulePushforwardModulePageXForgetIso_scalar_apply]
  exact ringedModulePushforwardAdditiveSpectralSequenceE2Equiv_scalar f φ Z I p q r
    ((ringedModulePushforwardModulePageXForgetIso f φ Z I 2 (by lia)
      ((p : ℤ), (q : ℤ))).hom x)

-- This is only a carrier-type annotation of the existing equivalence. It keeps scalar
-- inference on the actual modules instead of on their forgotten additive groups.
private def moduleE2OriginalAddEquiv {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (p q : ℕ) :
    ((ringedModulePushforwardModuleSpectralSequence f φ Z I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      (derivedModuleGammaZSections S Z ⊤ p).obj ((derivedRingedModulePushforward f φ q).obj M) :=
  ringedModulePushforwardModuleE2AddEquiv f φ Z I p q

set_option maxHeartbeats 800000 in
-- Expand the original composite once, separately from its scalar-compatibility proof.
set_option maxRecDepth 2048 in
private theorem moduleE2OriginalAddEquiv_apply {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (p q : ℕ)
    (x : ((ringedModulePushforwardModuleSpectralSequence f φ Z I).page 2).X
      ((p : ℤ), (q : ℤ))) :
    moduleE2OriginalAddEquiv f φ Z I p q x =
      (derivedModuleGammaZSectionsObjIsoH_Z S Z
        ((derivedRingedModulePushforward f φ q).obj M) p).inv
        (ringedModulePushforwardAdditiveSpectralSequenceE2Equiv f φ Z I p q
          ((ringedModulePushforwardModulePageXForgetIso f φ Z I 2 (by lia)
            ((p : ℤ), (q : ℤ))).hom x)) := rfl

set_option maxHeartbeats 800000 in
-- The original composite passes through the page-forgetful and cohomology-forgetful isomorphisms.
set_option maxRecDepth 2048 in
/-- The original module-valued E₂ additive equivalence is scalar-compatible. -/
theorem ringedModulePushforwardModuleE2AddEquiv_smul
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M) (p q : ℕ)
    (r : S.obj.obj (op (⊤ : Opens Y)))
    (x : ((ringedModulePushforwardModuleSpectralSequence f φ Z I).page 2).X
      ((p : ℤ), (q : ℤ))) :
    moduleE2OriginalAddEquiv f φ Z I p q (r • x) =
      r • moduleE2OriginalAddEquiv f φ Z I p q x := by
  rw [moduleE2OriginalAddEquiv_apply, moduleE2OriginalAddEquiv_apply,
    ringedModulePushforwardModuleE2ToH_Z_smul]
  exact derivedModuleGammaZSectionsObjIsoH_Z_inv_scalar_apply S Z
    ((derivedRingedModulePushforward f φ q).obj M) r p
    (ringedModulePushforwardAdditiveSpectralSequenceE2Equiv f φ Z I p q
      ((ringedModulePushforwardModulePageXForgetIso f φ Z I 2 (by lia)
        ((p : ℤ), (q : ℤ))).hom x))

set_option maxHeartbeats 800000 in
-- The scalar field compares the original additive equivalence with its native module carriers.
set_option maxRecDepth 2048 in
/-- **V.3.2, module-valued E₂:** the actual page is module-linearly the original
supported cohomology of the original higher module direct image. -/
def ringedModulePushforwardModuleE2LinearEquiv {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (p q : ℕ) :
    ((ringedModulePushforwardModuleSpectralSequence f φ Z I).page 2).X ((p : ℤ), (q : ℤ))
      ≃ₗ[S.obj.obj (op (⊤ : Opens Y))]
        (derivedModuleGammaZSections S Z ⊤ p).obj ((derivedRingedModulePushforward f φ q).obj M) :=
  (moduleE2OriginalAddEquiv f φ Z I p q).toLinearEquiv
    (ringedModulePushforwardModuleE2AddEquiv_smul f φ Z I p q)

/-- The linear equivalence has exactly the original additive comparison, not a new conjugate. -/
@[simp]
theorem ringedModulePushforwardModuleE2LinearEquiv_toAddEquiv {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (p q : ℕ) :
    (ringedModulePushforwardModuleE2LinearEquiv f φ Z I p q).toAddEquiv =
      ringedModulePushforwardModuleE2AddEquiv f φ Z I p q := rfl

end SGA.SGA2.ExposeV
