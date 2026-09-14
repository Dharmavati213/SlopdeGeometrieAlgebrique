/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.LocalCohomologyYonedaSequence
import SGA.SGA2.ExposeV.LocalDualityTargetYonedaSequence

/-!
# The canonical local-duality map commutes with Yoneda boundaries

The equality is proved at every original quotient-Ext stage using Yoneda
associativity, then descended through the actual local-cohomology colimit.
It concerns the unchanged canonical map, not a comparison chosen by an
abstract extension theorem.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The actual canonical map intertwines the two proved Yoneda sequences. -/
@[reassoc]
theorem localDualityMap_yoneda_connecting (J : Ideal R) (P : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (i j n : ℕ) (hleft : (i + 1) + j = n) (hright : i + (j + 1) = n) :
    localCohomologyYonedaBoundary J S hS i ≫
        localDualityMap J S.X₁ P (i + 1) j n hleft =
      localDualityMap J S.X₃ P i (j + 1) n hright ≫
        localDualityTargetYonedaBoundary J P S hS j n := by
  apply colimit_obj_ext (H := localCohomology.diagram (localCohomology.idealPowersDiagram J) i)
  intro k
  change localCohomologyPowerStageι J S.X₃ i k.unop.unop ≫ _ =
    localCohomologyPowerStageι J S.X₃ i k.unop.unop ≫ _
  rw [localCohomologyYonedaBoundary_stage_assoc, localDualityMap_stage,
    localDualityMap_stage_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact congrArg (localCohomologyPowerStageι J P n k.unop.unop)
    (moduleExtPairing_yoneda_connecting (ModuleCat.of R (R ⧸ J ^ k.unop.unop)) P
      S hS i j n hleft hright x y)

end SGA.SGA2.ExposeV
