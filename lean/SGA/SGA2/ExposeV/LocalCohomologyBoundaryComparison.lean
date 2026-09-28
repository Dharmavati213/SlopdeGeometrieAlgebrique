/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.ModuleExtCoefficientBoundaryComparison
import SGA.SGA2.ExposeV.LocalCohomologyYonedaSequence
import SGA.SGA2.ExposeII.LocalCohomologyReindexing

/-! # The signed boundary comparison on original local-cohomology objects -/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The existing Yoneda and Hom boundaries agree up to their proved sign
as morphisms of the original Ext diagrams, in every degree. -/
theorem extColimitYonedaBoundaryDiagram_eq_signed
    (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (n : ℕ) :
    extColimitYonedaBoundaryDiagram Q S hS n =
      (n + 1 : ℤ).negOnePow • extCoefficientδDiagram Q S hS n := by
  apply NatTrans.ext
  funext j
  exact moduleExtYonedaCovariantBoundary_eq_signed_extCoefficientδ (Q.obj j.unop) S hS n

/-- The same signed equality holds for the unchanged filtered Ext colimits. -/
theorem extColimitYonedaBoundary_eq_signed_extColimitδ
    (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (n : ℕ) :
    extColimitYonedaBoundary Q S hS n = (n + 1 : ℤ).negOnePow • extColimitδ Q S hS n := by
  rw [extColimitYonedaBoundary, extColimitYonedaBoundaryDiagram_eq_signed]
  change colim.map (((n + 1 : ℤ).negOnePow : ℤ) • extCoefficientδDiagram Q S hS n) = _
  exact colim.map_zsmul

/-- On the original ideal-power local-cohomology objects, in every degree,
the Yoneda boundary is exactly the signed original coefficient boundary. -/
theorem localCohomologyYonedaBoundary_eq_signed_localCohomologyδ
    (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (n : ℕ) :
    localCohomologyYonedaBoundary I S hS n =
      (n + 1 : ℤ).negOnePow • localCohomologyδ I S hS n := by
  apply colimit_obj_ext (H := localCohomology.diagram (localCohomology.idealPowersDiagram I) n)
  intro j
  change localCohomologyPowerStageι I S.X₃ n j.unop.unop ≫
    localCohomologyYonedaBoundary I S hS n = _
  rw [localCohomologyYonedaBoundary_stage,
    moduleExtYonedaCovariantBoundary_eq_signed_extCoefficientδ]
  change (((n + 1 : ℤ).negOnePow : ℤ) • _) ≫ _ = _ ≫
    (((n + 1 : ℤ).negOnePow : ℤ) • idealExtColimitδ _ S hS n)
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, ι_idealExtColimitδ]
  rfl

end SGA.SGA2.ExposeV
