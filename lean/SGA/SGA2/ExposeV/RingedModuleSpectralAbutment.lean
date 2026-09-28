/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.RingedModuleSpectralFiltration
import SGA.SGA2.ExposeV.ModuleComplexScalarHomology
import SGA.SGA2.ExposeI.FlasqueComplexDerivedHom
import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# V.3.2: the actual module-valued spectral abutment

The original supported-section complex of the direct-image resolution computes
the canonical total object by the flasque derived-Hom comparison. Naturality
for additive cochain maps proves compatibility with the retained global
scalars. The original composite-derived comparison then identifies this total
module with source supported cohomology restricted along the prescribed ring map.
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

/-- The original module-valued supported-section complex of the direct-image resolution. -/
def ringedModulePushforwardSupportedComplex {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) :
    CochainComplex (ModuleCat.{u} (S.obj.obj (op (⊤ : Opens Y)))) ℤ :=
  ((moduleGammaZSectionsFunctor S Z ⊤).mapHomologicalComplex _).obj
    (ringedModulePushforwardResolutionInt f φ I)

/-- The actual supported-section homology computes the original spectral total group. -/
def ringedModulePushforwardSupportedHomologyTotalAddEquiv {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (n : ℤ) :
    (ringedModulePushforwardSupportedComplex f φ Z I).homology n ≃+
      ringedModulePushforwardSpectralTotal f φ Z I n :=
  (ExposeI.complexHomologyMapIso
    (forget₂ (ModuleCat (S.obj.obj (op (⊤ : Opens Y)))) AddCommGrpCat) (ComplexShape.up ℤ)
    (ringedModulePushforwardSupportedComplex f φ Z I) n).symm.addCommGroupIsoToAddEquiv.trans
      (ExposeI.flasqueGammaComplexDerivedHomEquiv Z
        (ringedModulePushforwardAdditiveResolutionInt f φ I) 0 n)

set_option maxHeartbeats 800000 in
-- Comparing the original actions unfolds the truncation, localization and module lifts.
/-- The comparison retains the original scalar actions, including for noncommutative rings. -/
theorem ringedModulePushforwardSupportedHomologyTotalAddEquiv_smul
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M) (n : ℤ)
    (r : S.obj.obj (op (⊤ : Opens Y)))
    (x : (ringedModulePushforwardSupportedComplex f φ Z I).homology n) :
    ringedModulePushforwardSupportedHomologyTotalAddEquiv f φ Z I n (r • x) =
      r • ringedModulePushforwardSupportedHomologyTotalAddEquiv f φ Z I n x := by
  let K := ringedModulePushforwardAdditiveResolutionInt f φ I
  let P := ringedModulePushforwardSupportedComplex f φ Z I
  let e := ExposeI.complexHomologyMapIso
    (forget₂ (ModuleCat (S.obj.obj (op (⊤ : Opens Y)))) AddCommGrpCat) (ComplexShape.up ℤ) P n
  change ExposeI.flasqueGammaComplexDerivedHomEquiv Z K 0 n (e.inv (r • x)) =
    ExposeI.flasqueGammaComplexDerivedHomEquiv Z K 0 n (e.inv x) ≫
      (DerivedCategory.Q.map
        (moduleUnderlyingComplexGlobalScalar S (ringedModulePushforwardResolutionInt f φ I) r))⟦n⟧'
  rw [← moduleComplexAdditiveScalar_homology_apply P r n x]
  erw [← moduleGammaComplex_globalScalar S Z (ringedModulePushforwardResolutionInt f φ I) r]
  exact ExposeI.flasqueGammaComplexDerivedHomEquiv_naturality Z (K := K) (L := K)
    (moduleUnderlyingComplexGlobalScalar S (ringedModulePushforwardResolutionInt f φ I) r) 0 n _

/-- Supported-complex homology and the actual filtered total module agree module-linearly. -/
def ringedModulePushforwardSupportedHomologyTotalLinearEquiv {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (n : ℤ) :
    (ringedModulePushforwardSupportedComplex f φ Z I).homology n ≃ₗ[S.obj.obj (op (⊤ : Opens Y))]
      ringedModulePushforwardSpectralTotal f φ Z I n where
  __ := ringedModulePushforwardSupportedHomologyTotalAddEquiv f φ Z I n
  map_smul' r x := ringedModulePushforwardSupportedHomologyTotalAddEquiv_smul f φ Z I n r x

/-- The actual module-supported complex computes the original source cohomology
with precisely the restriction of scalars prescribed in V.3.2. -/
def ringedModulePushforwardSupportedHomologyIsoSource {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (n : ℕ) :
    (ringedModulePushforwardSupportedComplex f φ Z I).homology (n : ℤ) ≅
      (ModuleCat.restrictScalars (ringedGlobalRingHom f φ)).obj
        ((derivedModuleGammaZSections R (Z.preimage f.hom.continuous) ⊤ n).obj M) :=
  ExposeI.injectiveResolutionIntHomologyIso
      (ringedModulePushforward f φ ⋙ moduleGammaZSectionsFunctor S Z ⊤) I n ≪≫
    (ringedModuleSupportedGlobalRightDerivedIso f φ Z n).app M

/-- **V.3.2, abutment:** the actual filtered total module is the original
source supported cohomology with its actual restricted global scalars. -/
def ringedModulePushforwardSpectralAbutmentLinearEquiv {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (n : ℕ) :
    ringedModulePushforwardSpectralTotal f φ Z I n ≃ₗ[S.obj.obj (op (⊤ : Opens Y))]
      (ModuleCat.restrictScalars (ringedGlobalRingHom f φ)).obj
        ((derivedModuleGammaZSections R (Z.preimage f.hom.continuous) ⊤ n).obj M) :=
  (ringedModulePushforwardSupportedHomologyTotalLinearEquiv f φ Z I n).symm.trans
    (ringedModulePushforwardSupportedHomologyIsoSource f φ Z I n).toLinearEquiv

/-- The genuine finite submodule filtration on the original smaller-universe
source cohomology, transported by the proved module-linear abutment comparison. -/
def ringedModulePushforwardSourceFiniteFiltration {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (n : ℕ) :
    Fin (n + 2) →o Submodule (S.obj.obj (op (⊤ : Opens Y)))
      ((ModuleCat.restrictScalars (ringedGlobalRingHom f φ)).obj
        ((derivedModuleGammaZSections R (Z.preimage f.hom.continuous) ⊤ n).obj M)) :=
  let e := (ModuleCat.subobjectModule.{u + 1, u}
    (ringedModulePushforwardSpectralTotal f φ Z I n)).trans
      (Submodule.orderIsoMapComap
        (ringedModulePushforwardSpectralAbutmentLinearEquiv f φ Z I n))
  e.toOrderEmbedding.toOrderHom.comp
    (ringedModulePushforwardSpectralFiniteFiltration f φ Z I n)

@[simp]
theorem ringedModulePushforwardSourceFiniteFiltration_zero {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (n : ℕ) :
    ringedModulePushforwardSourceFiniteFiltration f φ Z I n 0 = ⊥ := by
  let e := (ModuleCat.subobjectModule.{u + 1, u}
    (ringedModulePushforwardSpectralTotal f φ Z I n)).trans
      (Submodule.orderIsoMapComap
        (ringedModulePushforwardSpectralAbutmentLinearEquiv f φ Z I n))
  change e (ringedModulePushforwardSpectralFiniteFiltration f φ Z I n 0) = ⊥
  rw [ringedModulePushforwardSpectralFiniteFiltration_zero]
  apply le_antisymm _ bot_le
  simpa only [OrderIso.apply_symm_apply] using e.monotone (bot_le : ⊥ ≤ e.symm ⊥)

@[simp]
theorem ringedModulePushforwardSourceFiniteFiltration_last {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (n : ℕ) :
    ringedModulePushforwardSourceFiniteFiltration f φ Z I n (Fin.last (n + 1)) = ⊤ := by
  let e := (ModuleCat.subobjectModule.{u + 1, u}
    (ringedModulePushforwardSpectralTotal f φ Z I n)).trans
      (Submodule.orderIsoMapComap
        (ringedModulePushforwardSpectralAbutmentLinearEquiv f φ Z I n))
  change e (ringedModulePushforwardSpectralFiniteFiltration f φ Z I n (Fin.last (n + 1))) = ⊤
  rw [ringedModulePushforwardSpectralFiniteFiltration_last]
  apply le_antisymm le_top
  simpa only [OrderIso.apply_symm_apply] using e.monotone (le_top : e.symm ⊤ ≤ ⊤)

end SGA.SGA2.ExposeV
