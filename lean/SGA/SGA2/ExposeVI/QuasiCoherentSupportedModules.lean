/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.QuasiCoherentSupportedModulesAffine
import SGA.SGA2.ExposeVI.QuasiCoherentSupportedModulesRestriction
import SGA.SGA2.ExposeVI.CoherentInternalHom
import SGA.SGA2.ExposeVI.ModuleSheafExtLinear

/-!
# Quasi-coherence of genuine closed-supported module sheaves

On a locally noetherian scheme, the original module sheaf of sections
supported in a closed subset preserves quasi-coherence. The proof uses the
proved affine torsion/sheaf comparison and the original open-restriction
maps, then descends across actual affine opens. This is a degree-zero
statement; no higher supported-cohomology quasi-coherence is used.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- On a noetherian affine, actual closed-supported sections of a quasi-coherent module
form a quasi-coherent module sheaf. -/
theorem affineModuleGammaZ_isQuasicoherent {R : CommRingCat.{u}} [IsNoetherianRing R]
    (Z : Closeds (Spec R)) (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (schemeModuleGammaZ Z M).IsQuasicoherent := by
  obtain ⟨I, hI⟩ :=
    (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (show Set (PrimeSpectrum R) from
      (Z : Set (Spec R)))).mp Z.isClosed
  have hZ : ExposeII.affineSupportClosed I = Z := SetLike.coe_injective hI.symm
  subst Z
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  let e := (moduleGammaZSheafFunctor (Spec R).ringCatSheaf (ExposeII.affineSupportClosed I)).mapIso
    (asIso M.fromTildeΓ)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
    (affineSupportedModuleSheaf_isQuasicoherent I (IsNoetherian.noetherian I)
      ((moduleSpecΓFunctor (R := R)).obj M))

/-- **II.3, closed support in degree zero:** the actual supported-module sheaf
of a quasi-coherent module is quasi-coherent on a locally noetherian scheme. -/
theorem schemeModuleGammaZ_isQuasicoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (Z : Closeds X) (M : X.Modules) [M.IsQuasicoherent] :
    (schemeModuleGammaZ Z M).IsQuasicoherent := by
  obtain ⟨κ, hκ, hκcover⟩ :=
    Opens.isBasis_iff_cover.mp X.isBasis_affineOpens (⊤ : X.Opens)
  let U : κ → X.Opens := fun i ↦ i.val
  have hcov : IsOpenCover U := by
    change (⨆ i : κ, i.val) = ⊤
    rw [← sSup_eq_iSup']
    exact hκcover.symm
  apply schemeModule_isQuasicoherent_of_restrict_cover (schemeModuleGammaZ Z M) U hcov
  intro i
  let hU : IsAffineOpen (U i) := hκ i.property
  have : IsNoetherianRing Γ(X, U i) := IsLocallyNoetherian.component_noetherian ⟨U i, hU⟩
  have hlocal := affineModuleGammaZ_isQuasicoherent
    (schemeClosedSupportPreimage hU.fromSpec Z) (M.restrict hU.fromSpec)
  have : ((schemeModuleGammaZ Z M).restrict hU.fromSpec).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, U i)).ringCatSheaf).prop_of_iso
      (schemeModuleGammaZRestrictionIso hU.fromSpec Z M).symm hlocal
  let e : (schemeModuleGammaZ Z M).restrict (U i).ι ≅
      ((schemeModuleGammaZ Z M).restrict hU.fromSpec).restrict hU.isoSpec.hom :=
    (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec.symm).app _ ≪≫
      (Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app _
  exact (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).prop_of_iso e.symm
    (by infer_instance)

/-- The original closed-support coefficient functor preserves quasi-coherence in degree zero. -/
instance moduleGammaZSheafFunctor_obj_isQuasicoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (Z : Closeds X) (M : X.Modules) [M.IsQuasicoherent] :
    ((moduleGammaZSheafFunctor X.ringCatSheaf Z).obj M).IsQuasicoherent :=
  schemeModuleGammaZ_isQuasicoherent Z M

/-- **VI.2.1, closed support in degree zero:** actual supported Hom is quasi-coherent
for coherent source and quasi-coherent target. -/
theorem coherent_closedSupportedHom_isQuasicoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F G : X.Modules) [F.IsFinitePresentation] [G.IsQuasicoherent] (Z : Closeds X) :
    ((moduleClosedSheafHomFunctor X.sheaf F Z).obj G).IsQuasicoherent := by
  let : (schemeModuleInternalHom F G).IsQuasicoherent :=
    coherent_internalHom_isQuasicoherent F G
  exact schemeModuleGammaZ_isQuasicoherent Z (schemeModuleInternalHom F G)

/-- The literal degree-zero module-valued supported sheaf Ext of VI.1.1 is quasi-coherent. -/
theorem coherent_closedSheafExtZero_isQuasicoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F G : X.Modules) [F.IsFinitePresentation] [G.IsQuasicoherent] (Z : Closeds X) :
    ((moduleClosedSheafExtFunctor X.sheaf F Z 0).obj G).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((moduleClosedSheafExtZeroIso X.sheaf F Z).app G).symm
      (coherent_closedSupportedHom_isQuasicoherent F G Z)

end SGA.SGA2.ExposeVI
