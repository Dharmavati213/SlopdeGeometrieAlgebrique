/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.YonedaExtColimitSequence
import SGA.SGA2.ExposeV.LocalDualityFiniteFree

/-!
# Yoneda exact sequences on original local cohomology

The original ideal-power colimit comparison transports the Yoneda boundary
to actual local-cohomology objects, preserving every original stage map.
This supplies exact sequences for proving V.2.1 without assuming equality
with the independently constructed Hom-complex connecting maps.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable (J : Ideal R) (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ)

/-- The Yoneda boundary on the actual local-cohomology objects. -/
def localCohomologyYonedaBoundary :
    (_root_.localCohomology J i).obj S.X₃ ⟶
      (_root_.localCohomology J (i + 1)).obj S.X₁ :=
  (idealPowerExtIsoLocalCohomology J i).inv.app S.X₃ ≫
    extColimitYonedaBoundary
      (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram J)) S hS i ≫
        (idealPowerExtIsoLocalCohomology J (i + 1)).hom.app S.X₁

/-- The new boundary is induced by the transported Yoneda boundary at
each original quotient Ext stage. -/
@[reassoc (attr := simp)]
theorem localCohomologyYonedaBoundary_stage (k : ℕ) :
    localCohomologyPowerStageι J S.X₃ i k ≫ localCohomologyYonedaBoundary J S hS i =
      moduleExtYonedaCovariantBoundary (ModuleCat.of R (R ⧸ J ^ k)) S hS i ≫
        localCohomologyPowerStageι J S.X₁ (i + 1) k := by
  simp only [localCohomologyPowerStageι, localCohomologyYonedaBoundary,
    idealPowerExtIsoLocalCohomology, colimitIsoFlipCompColim,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    Iso.symm_hom, Iso.symm_inv,
    colimitObjIsoColimitCompEvaluation_ι_app_hom_assoc,
    extColimitYonedaBoundary, colimit.ι_map_assoc,
    extColimitYonedaBoundaryDiagram]
  exact congrArg (fun f =>
    moduleExtYonedaCovariantBoundary (ModuleCat.of R (R ⧸ J ^ k)) S hS i ≫ f)
    (colimitObjIsoColimitCompEvaluation_ι_inv
      (localCohomology.diagram (localCohomology.idealPowersDiagram J) (i + 1))
      (op (op k)) S.X₁)

@[reassoc (attr := simp)]
theorem localCohomologyYonedaBoundary_comp :
    localCohomologyYonedaBoundary J S hS i ≫
      (_root_.localCohomology J (i + 1)).map S.f = 0 := by
  simp only [localCohomologyYonedaBoundary, Category.assoc,
    ← (idealPowerExtIsoLocalCohomology J (i + 1)).hom.naturality,
    extColimitYonedaBoundary_comp_assoc, zero_comp, comp_zero]

@[reassoc (attr := simp)]
theorem comp_localCohomologyYonedaBoundary :
    (_root_.localCohomology J i).map S.g ≫ localCohomologyYonedaBoundary J S hS i = 0 := by
  rw [localCohomologyYonedaBoundary, ← Category.assoc,
    (idealPowerExtIsoLocalCohomology J i).inv.naturality,
    Category.assoc, comp_extColimitYonedaBoundary_assoc, zero_comp, comp_zero]

/-- Exactness after the boundary on the actual local-cohomology values. -/
theorem localCohomologyYoneda_exact₁ :
    (ShortComplex.mk _ _ (localCohomologyYonedaBoundary_comp J S hS i)).Exact := by
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk ((idealPowerExtIsoLocalCohomology J i).app S.X₃)
      ((idealPowerExtIsoLocalCohomology J (i + 1)).app S.X₁)
      ((idealPowerExtIsoLocalCohomology J (i + 1)).app S.X₂) ?_ ?_)
    (extColimitYoneda_exact₁ _ S hS i)
  · simp [localCohomologyYonedaBoundary]
  · exact ((idealPowerExtIsoLocalCohomology J (i + 1)).hom.naturality S.f).symm

/-- Exactness before the boundary on the actual local-cohomology values. -/
theorem localCohomologyYoneda_exact₃ :
    (ShortComplex.mk _ _ (comp_localCohomologyYonedaBoundary J S hS i)).Exact := by
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk ((idealPowerExtIsoLocalCohomology J i).app S.X₂)
      ((idealPowerExtIsoLocalCohomology J i).app S.X₃)
      ((idealPowerExtIsoLocalCohomology J (i + 1)).app S.X₁) ?_ ?_)
    (extColimitYoneda_exact₃ _ S hS i)
  · exact ((idealPowerExtIsoLocalCohomology J i).hom.naturality S.g).symm
  · simp [localCohomologyYonedaBoundary]

/-- If the preceding free coefficient value vanishes, the boundary is
monic. This is the left edge used by descending local duality. -/
theorem localCohomologyYonedaBoundary_mono
    (hz : IsZero ((_root_.localCohomology J i).obj S.X₂)) :
    Mono (localCohomologyYonedaBoundary J S hS i) :=
  (localCohomologyYoneda_exact₃ J S hS i).mono_g (hz.eq_zero_of_src _)

end SGA.SGA2.ExposeV
