/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ModulesHomPresentation
import SGA.Foundations.Analytic.CoherentRestrict
import SGA.Foundations.QuasiCoherent.Local
import Mathlib.Topology.Sheaves.Module

/-!
# Finite presentations after restriction to open subspaces

The module category on the site over an open set agrees with the module category on
the corresponding open locally ringed subspace (`restrictOpenFunctor`, in
`SGA.Foundations.Analytic.CoherentRestrict`). Local finite presentations therefore
become global finite presentations after restriction (`exists_finitePresentation_restrictOpen`).

Adopted from the unmerged branch `codex/foundations-missing-inputs` (commit `c65c9a0`, second half
of `ModuleHomRestriction.lean`; the first half is an-coh's `CoherentRestrict.lean`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}}

/-- A finite presentation of `M` over the open `U` (on the site `Over U`, `M.over U`) gives a
finite presentation of the restriction of `M` to the open subspace `U`. -/
def presentationRestrictOpen (U : Opens X) {M : X.Modules} (P : (M.over U).Presentation) :
    ((restrictOpenFunctor U).obj M).Presentation :=
  P.mapOfAdjunction (U.sheafOfModulesEquivOver X.ringCatSheaf).toAdjunction
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm

instance isFinite_presentationRestrictOpen (U : Opens X) {M : X.Modules}
    (P : (M.over U).Presentation) [P.IsFinite] : (presentationRestrictOpen U P).IsFinite :=
  inferInstanceAs (P.mapOfAdjunction (U.sheafOfModulesEquivOver X.ringCatSheaf).toAdjunction
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm).IsFinite

/-- A locally finitely presented module sheaf has a finite global presentation on an
open subspace around each point. -/
theorem exists_finitePresentation_restrictOpen (M : X.Modules) [M.IsFinitePresentation] (x : X) :
    ∃ (U : Opens X), x ∈ U ∧ ∃ P : ((restrictOpenFunctor U).obj M).Presentation, P.IsFinite := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have hcov := (Opens.coversTop_iff _ _).mp q.coversTop
  obtain ⟨i, hxi⟩ := TopologicalSpace.IsOpenCover.exists_mem hcov x
  exact ⟨q.X i, hxi, presentationRestrictOpen (q.X i) (q.presentation i), inferInstance⟩

end AlgebraicGeometry.LocallyRingedSpace.Modules
