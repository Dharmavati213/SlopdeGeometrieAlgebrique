/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.QuasiCoherentSupportedModulesAffine

/-!
# The affine torsion/support comparison preserves the original maps

The comparison is the canonical map induced by the original torsion
inclusion, and is natural in every coefficient module. Its maps to sections
on principal opens are genuine localization maps of ideal-power torsion.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : CommRingCat.{u}} (I : Ideal R) (hI : I.FG) (M : ModuleCat.{u} R)

/-- On original tilde sections, the comparison is exactly the original torsion inclusion. -/
theorem affineSupportedModuleSheafIsoTorsion_toOpen_val (U : (Spec R).Opens)
    (x : ExposeII.powerTorsion I M) :
    ((affineSupportedModuleSheafIsoTorsion I hI M).hom.val.app (op U)
      ((tilde.toOpen (ModuleCat.of R (ExposeII.powerTorsion I M)) U) x)).val =
        tilde.toOpen M U x.val := by
  let H := affineSupportedModuleSheaf I M
  let e : ModuleCat.of R (ExposeII.powerTorsion I M) ≅ (moduleSpecΓFunctor (R := R)).obj H :=
    (affineSupportedModuleGlobalEquiv I hI M).toModuleIso
  have h₁ := ConcreteCategory.congr_hom (tilde.toOpen_map_app e.hom U) x
  have h₂ := ConcreteCategory.congr_hom (H.toOpen_fromTildeΓ_app U) (e.hom x)
  change (H.fromTildeΓ.val.app (op U)
      ((tilde.map e.hom).val.app (op U)
        ((tilde.toOpen (ModuleCat.of R (ExposeII.powerTorsion I M)) U) x))).val = _
  change (tilde.map e.hom).val.app (op U)
      ((tilde.toOpen (ModuleCat.of R (ExposeII.powerTorsion I M)) U) x) =
    (tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj H) U) (e.hom x) at h₁
  rw [h₁]
  change H.fromTildeΓ.val.app (op U)
      ((tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj H) U) (e.hom x)) =
    H.val.map U.leTop.op (e.hom x) at h₂
  rw [h₂]
  exact ConcreteCategory.congr_hom (tilde.toOpen_res M ⊤ U U.leTop) x.val

/-- The support comparison composes to the literal tilde of the original torsion inclusion. -/
@[reassoc]
theorem affineSupportedModuleSheafIsoTorsion_hom_ι :
    (affineSupportedModuleSheafIsoTorsion I hI M).hom ≫
        moduleGammaZSheafι (Spec R).ringCatSheaf (ExposeII.affineSupportClosed I) (tilde M) =
      tilde.map (ModuleCat.ofHom (ExposeII.powerTorsion I M).subtype) := by
  apply (tilde.adjunction (R := R)).homEquiv _ (tilde M) |>.injective
  ext x
  change ((affineSupportedModuleSheafIsoTorsion I hI M).hom.val.app (op ⊤)
      ((tilde.toOpen (ModuleCat.of R (ExposeII.powerTorsion I M)) ⊤) x)).val =
    (tilde.map (ModuleCat.ofHom (ExposeII.powerTorsion I M).subtype)).val.app (op ⊤)
      ((tilde.toOpen (ModuleCat.of R (ExposeII.powerTorsion I M)) ⊤) x)
  rw [affineSupportedModuleSheafIsoTorsion_toOpen_val]
  exact (ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (ModuleCat.ofHom (ExposeII.powerTorsion I M).subtype) ⊤) x).symm

/-- The comparison retains the original coefficient maps on torsion and supported sections. -/
theorem affineSupportedModuleSheafIsoTorsion_naturality {N : ModuleCat.{u} R} (a : M ⟶ N) :
    tilde.map ((ExposeII.powerTorsionFunctor I).map a) ≫
        (affineSupportedModuleSheafIsoTorsion I hI N).hom =
      (affineSupportedModuleSheafIsoTorsion I hI M).hom ≫
        moduleGammaZSheafMap (Spec R).ringCatSheaf
          (ExposeII.affineSupportClosed I) (tilde.map a) := by
  apply (cancel_mono
    (moduleGammaZSheafι (Spec R).ringCatSheaf (ExposeII.affineSupportClosed I) (tilde N))).mp
  rw [Category.assoc, Category.assoc, moduleGammaZSheafMap_comp_ι,
    affineSupportedModuleSheafIsoTorsion_hom_ι, affineSupportedModuleSheafIsoTorsion_hom_ι_assoc,
    ← tilde.map_comp, ← tilde.map_comp]
  rfl

/-- The actual affine closed-supported module functor is naturally tilde of torsion. -/
def affineSupportedModuleSheafFunctorIsoTorsion :
    ExposeII.powerTorsionFunctor I ⋙ tilde.functor R ≅
      tilde.functor R ⋙
        moduleGammaZSheafFunctor (Spec R).ringCatSheaf (ExposeII.affineSupportClosed I) :=
  NatIso.ofComponents (fun M ↦ affineSupportedModuleSheafIsoTorsion I hI M)
    (fun a ↦ affineSupportedModuleSheafIsoTorsion_naturality I hI _ a)

/-- The original map from torsion elements to supported sections on an open. -/
def affineTorsionToSupportedOpen (U : (Spec R).Opens) :
    ModuleCat.of R (ExposeII.powerTorsion I M) ⟶
      (modulesSpecToSheaf.obj (affineSupportedModuleSheaf I M)).presheaf.obj (op U) :=
  (affineSupportedModuleGlobalEquiv I hI M).toModuleIso.hom ≫
    (modulesSpecToSheaf.obj (affineSupportedModuleSheaf I M)).presheaf.map U.leTop.op

/-- Ideal-power torsion localizes through the actual supported-section restriction map. -/
instance affineTorsionToSupportedOpen_isLocalized (f : R) :
    IsLocalizedModule (.powers f)
      (affineTorsionToSupportedOpen I hI M (PrimeSpectrum.basicOpen f)).hom :=
  (IsLocalizedModule.comp_iff_of_bijective_right (.powers f)
    (affineSupportedModuleGlobalEquiv I hI M).toLinearMap
      (affineSupportedModuleGlobalEquiv I hI M).bijective).mpr
        (affineSupportedModuleSheaf_isLocalizing I hI M f)

/-- Supported sections on a principal open are the localization of the original torsion module. -/
def affineTorsionLocalizationEquivSupportedSections (f : R) :
    LocalizedModule (.powers f) (ExposeII.powerTorsion I M) ≃ₗ[R]
      Γ(affineSupportedModuleSheaf I M, PrimeSpectrum.basicOpen f) := by
  let : IsLocalizedModule (.powers f)
      (affineTorsionToSupportedOpen I hI M (PrimeSpectrum.basicOpen f)).hom :=
    affineTorsionToSupportedOpen_isLocalized I hI M f
  exact IsLocalizedModule.linearEquiv (.powers f)
    (LocalizedModule.mkLinearMap (.powers f) (ExposeII.powerTorsion I M))
      (affineTorsionToSupportedOpen I hI M (PrimeSpectrum.basicOpen f)).hom

end SGA.SGA2.ExposeVI
