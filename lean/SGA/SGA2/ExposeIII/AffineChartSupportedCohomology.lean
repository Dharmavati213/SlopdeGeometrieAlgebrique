/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.CoherentHartogs
import SGA.SGA2.ExposeIII.AffineDepth
import SGA.SGA2.ExposeIII.HomeomorphismSupportedCohomology

/-!
# Supported cohomology on genuine affine charts of scheme modules

Actual module restriction is compared with ordinary abelian sheaf pullback.
The genuine affine-chart homeomorphism then transports supported cohomology
in every degree, without a supplied chart or sheaf-comparison hypothesis.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat AlgebraicGeometry Abelian
open SGA.SGA2.ExposeI SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}}

/-- A genuine module-sheaf isomorphism gives an isomorphism of its actual
underlying abelian sheaves. -/
def schemeModuleAbSheafIso {M N : X.Modules} (e : M ≅ N) :
    schemeModuleAbSheaf M ≅ schemeModuleAbSheaf N :=
  (SheafOfModules.toSheaf X.ringCatSheaf).mapIso e

/-- Module restriction along an open immersion has exactly ordinary
abelian sheaf pullback as its underlying sheaf. -/
def schemeModuleAbSheafRestrictIso (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules) :
    schemeModuleAbSheaf (M.restrict f) ≅
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base).obj (schemeModuleAbSheaf M) :=
  ((f.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).app (schemeModuleAbSheaf M)).symm

/-- Restriction and actual abelian direct image under a scheme isomorphism
recover the original underlying abelian sheaf. -/
def schemeModuleAbSheafPushforwardRestrictIso (e : Y ≅ X) (M : X.Modules) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base).obj
      (schemeModuleAbSheaf (M.restrict e.hom)) ≅ schemeModuleAbSheaf M := by
  have : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base).IsEquivalence :=
    homeomorphismSheafPushforward_isEquivalence (Scheme.forgetToTop.mapIso e)
  exact (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base).mapIso
      (schemeModuleAbSheafRestrictIso e.hom M) ≪≫
    (asIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} e.hom.base).unit.app
      (schemeModuleAbSheaf M))).symm

/-- The actual inverse image of a closed support on a canonical affine chart. -/
def affineChartSupport (Z : Closeds X) {U : X.Opens} (hU : IsAffineOpen U) :
    Closeds (Spec Γ(X, U)) := Z.preimage hU.fromSpec.continuous

/-- The actual supported cohomology of the restriction to an affine open
is the actual supported cohomology of the canonical affine coefficient sheaf. -/
def affineChartSupportedCohomologyEquiv (M : X.Modules) (Z : Closeds X)
    (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    H_Z (closedSupportOnOpen Z U) (restrictToOpen (schemeModuleAbSheaf M) U) n ≃+
      H_Z (affineChartSupport Z hU) (schemeModuleAbSheaf (M.restrict hU.fromSpec)) n := by
  let e := hU.isoSpec.symm
  let F := M.restrict U.ι
  let N := F.restrict e.hom
  let ZU := closedSupportOnOpen Z U
  let e₁ := (extFunctorObj (zZX_closed ZU) n).mapIso
    (schemeModuleAbSheafRestrictIso U.ι M)
  let e₂ := (extFunctorObj (zZX_closed ZU) n).mapIso
    (schemeModuleAbSheafPushforwardRestrictIso e F)
  let e₃ := (homeomorphismSupportedCohomologyFunctorIso
    (Scheme.forgetToTop.mapIso e) ZU n).app (schemeModuleAbSheaf N)
  let e₄ := (extFunctorObj (zZX_closed (affineChartSupport Z hU)) n).mapIso
    (schemeModuleAbSheafIso ((Scheme.Modules.restrictFunctorComp e.hom U.ι).app M).symm)
  exact (e₁.symm ≪≫ e₂.symm ≪≫ e₃ ≪≫ e₄).addCommGroupIsoToAddEquiv

variable {R : CommRingCat.{u}} [IsNoetherianRing R]

/-- For an actual quasi-coherent affine module with finite canonical
coefficients, all lower supported-cohomology groups test literal stalk depth. -/
theorem affineQuasicoherent_H_Z_vanishes_iff_stalkDepth
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R (affineModuleCoefficients M)] (I : Ideal R) (n : ℕ) :
    (∀ i < n, Subsingleton (H_Z (affineSupportClosed I) (schemeModuleAbSheaf M) i)) ↔
      ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
        (n : ℕ∞) ≤ moduleStalkDepth M p := by
  have he (i : ℕ) :
      Subsingleton (H_Z (affineSupportClosed I)
        (affineTildeAbSheaf (affineModuleCoefficients M)) i) ↔
      Subsingleton (H_Z (affineSupportClosed I) (schemeModuleAbSheaf M) i) := by
    let e := (extFunctorObj (zZX_closed (affineSupportClosed I)) i).mapIso
      (schemeModuleAbSheafIso (affineQuasicoherentPresentationIso M))
    exact e.addCommGroupIsoToAddEquiv.subsingleton_congr
  simp_rw [← he, ← localDepth_affineModuleCoefficients]
  exact affine_H_Z_vanishes_iff_localDepth I (affineModuleCoefficients M) n

variable [IsLocallyNoetherian X]

/-- The all-degree affine-chart criterion, with literal ambient stalk depth
and actual supported cohomology on the open subspace. -/
theorem affineChart_H_Z_vanishes_iff_stalkDepth
    (M : X.Modules) [M.IsFinitePresentation] (Z : Closeds X)
    (U : X.Opens) (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) (affineModuleCoefficients (M.restrict hU.fromSpec))] (n : ℕ) :
    (∀ i < n, Subsingleton
      (H_Z (closedSupportOnOpen Z U) (restrictToOpen (schemeModuleAbSheaf M) U) i)) ↔
      ∀ x : X, x ∈ U → x ∈ Z → (n : ℕ∞) ≤ moduleStalkDepth M x := by
  let R := Γ(X, U)
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let f : Spec R ⟶ X := hU.fromSpec
  let N := M.restrict f
  let Z' : Closeds (PrimeSpectrum R) := affineChartSupport Z hU
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (Z' : Set (PrimeSpectrum R))).mp
    Z'.isClosed
  have hZI : Z' = affineSupportClosed I := Closeds.ext hI
  have he (i : ℕ) :
      Subsingleton
        (H_Z (closedSupportOnOpen Z U) (restrictToOpen (schemeModuleAbSheaf M) U) i) ↔
      Subsingleton (H_Z (affineSupportClosed I) (schemeModuleAbSheaf N) i) := by
    rw [← hZI]
    exact (affineChartSupportedCohomologyEquiv M Z U hU i).subsingleton_congr
  simp_rw [he]
  rw [affineQuasicoherent_H_Z_vanishes_iff_stalkDepth N I n]
  have (p : PrimeSpectrum R) :
      Module.Finite ((Spec R).presheaf.stalk p) (schemeModuleStalk N p) :=
    affineQuasicoherentStalkFinite N p
  constructor
  · intro h x hx hxZ
    have hxrange : x ∈ Set.range f := hU.range_fromSpec.symm ▸ hx
    obtain ⟨p, rfl⟩ := hxrange
    rw [← moduleStalkDepth_restrict f M p]
    apply h p
    rw [← hI]
    exact hxZ
  · intro h p hp
    rw [moduleStalkDepth_restrict f M p]
    apply h (f p)
    · exact (show Set.range f ⊆ (U : Set X) from hU.range_fromSpec.le) ⟨p, rfl⟩
    · rw [← hI] at hp
      exact hp

end SGA.SGA2.ExposeIII
