/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.AffineChartSupportedCohomology
import SGA.SGA2.ExposeIII.HomeomorphismCohomology
import SGA.SGA2.ExposeII.AffineCohomologyVanishing

/-!
# Vanishing on actual affine opens

Transport through the genuine canonical affine chart identifies ordinary
cohomology of the original restricted abelian sheaf with that of an actual
associated sheaf. No presentation or acyclicity is supplied as a hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat AlgebraicGeometry Abelian
open SGA.SGA2.ExposeI SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- Original ordinary cohomology on an affine open agrees with cohomology
of the actual module restricted to its canonical spectrum chart. -/
def affineChartCohomologyEquiv (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    H (restrictToOpen (schemeModuleAbSheaf M) U) n ≃+
      H (schemeModuleAbSheaf (M.restrict hU.fromSpec)) n := by
  let e := hU.isoSpec.symm
  let F := M.restrict U.ι
  let N := F.restrict e.hom
  let e₁ := (extFunctorObj (constantZ ((Opens.toTopCat X).obj U)) n).mapIso
    (schemeModuleAbSheafRestrictIso U.ι M)
  let e₂ := (extFunctorObj (constantZ ((Opens.toTopCat X).obj U)) n).mapIso
    (schemeModuleAbSheafPushforwardRestrictIso e F)
  let e₃ := (homeomorphismCohomologyFunctorIso (Scheme.forgetToTop.mapIso e) n).app
    (schemeModuleAbSheaf N)
  let e₄ := (extFunctorObj (constantZ (Spec Γ(X, U))) n).mapIso
    (schemeModuleAbSheafIso ((Scheme.Modules.restrictFunctorComp e.hom U.ι).app M).symm)
  exact (e₁.symm ≪≫ e₂.symm ≪≫ e₃ ≪≫ e₄).addCommGroupIsoToAddEquiv

/-- A genuine quasi-coherent module on a noetherian affine scheme is acyclic
in positive degrees, through its canonical associated-module presentation. -/
theorem affineQuasicoherent_H_pos_subsingleton {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (H (schemeModuleAbSheaf M) (n + 1)) := by
  let e := (extFunctorObj (constantZ (Spec R)) (n + 1)).mapIso
    (schemeModuleAbSheafIso (affineQuasicoherentPresentationIso M))
  exact e.addCommGroupIsoToAddEquiv.subsingleton_congr.mp
    (affineTildeAb_H_pos_subsingleton (affineModuleCoefficients M) n)

/-- Positive cohomology of the actual restricted abelian sheaf vanishes
on every affine open of a locally noetherian scheme. -/
theorem affineOpen_H_pos_subsingleton [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Subsingleton (H (restrictToOpen (schemeModuleAbSheaf M) U) (n + 1)) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have := affineQuasicoherent_H_pos_subsingleton (M.restrict hU.fromSpec) n
  exact (affineChartCohomologyEquiv M U hU (n + 1)).injective.subsingleton

end SGA.SGA2.ExposeIII
