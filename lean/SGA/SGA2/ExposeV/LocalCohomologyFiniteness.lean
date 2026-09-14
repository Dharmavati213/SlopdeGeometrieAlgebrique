/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.LocalCohomologyDualCompletion
import SGA.SGA2.ExposeIV.MatlisArtinianModules
import SGA.SGA2.ExposeIV.CompleteModuleScalarChange

/-!
# Finiteness consequences of regular local duality

Every local-cohomology module of a finite module over a regular local ring
is genuinely Artinian, without completeness of the base. It has finite
actual socle and finite-length power annihilators. Over a complete regular
local ring, its actual dual is finite in every degree, by V, formula (22), and upper
vanishing. Without completeness, the original completed dual is finite over
the actual completed ring. The general-local finite-generation assertion is
proved separately in `LocalRingFiniteness`; the dual-dimension bound remains open.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable (n : ℕ) (hdim : ringKrullDim R = n)
variable (M : ModuleCat.{u} R) [Module.Finite R M]

include n hdim

/-- All actual local-cohomology values of a finite module are Artinian
over a regular local base, even when that base is not complete. -/
theorem regularLocal_localCohomology_isArtinian (i : ℕ) :
    IsArtinian R ((_root_.localCohomology (maximalIdeal R) i).obj M) := by
  by_cases hi : i ≤ n
  · have := (regularLocal_localCohomology_dualizing n hdim).finiteSource_dual_isArtinian
      (moduleExtValue M (ModuleCat.of R R) (n - i))
    exact isArtinian_of_linearEquiv
      (regularLocal_localCohomologyHomIso n hdim i (n - i) (by omega) M).symm.toLinearEquiv
  · have := ModuleCat.subsingleton_of_isZero
      (regularLocal_localCohomology_isZero_of_gt n hdim M i (by omega))
    infer_instance

/-- The actual local-cohomology socle is finite, using the literal
annihilator comparison under canonical local duality. -/
theorem regularLocal_localCohomology_socle_finite (i : ℕ) :
    Module.Finite R (localSocle (R := R)
      ((_root_.localCohomology (maximalIdeal R) i).obj M)) := by
  by_cases hi : i ≤ n
  · have hD := regularLocal_localCohomology_dualizing n hdim
    have := (hD.finiteSource_dual_locallyArtinian_finiteSocle
      (moduleExtValue M (ModuleCat.of R R) (n - i))).2
    exact Module.Finite.equiv (localSocleLinearEquiv
      (regularLocal_localCohomologyHomIso n hdim i (n - i) (by omega) M).toLinearEquiv).symm
  · have := ModuleCat.subsingleton_of_isZero
      (regularLocal_localCohomology_isZero_of_gt n hdim M i (by omega))
    infer_instance

/-- The actual local-cohomology object lies in the original Matlis category. -/
theorem regularLocal_localCohomology_matlisArtinian (i : ℕ) :
    matlisArtinianModuleProperty R ((_root_.localCohomology (maximalIdeal R) i).obj M) := by
  have := regularLocal_localCohomology_isArtinian n hdim M i
  exact ⟨fun N _ => inferInstance, regularLocal_localCohomology_socle_finite n hdim M i⟩

/-- Every original maximal-ideal-power annihilator has actual finite length. -/
theorem regularLocal_localCohomology_annihilator_isFiniteLength (i k : ℕ) :
    IsFiniteLength R (Submodule.torsionBySet R
      ((_root_.localCohomology (maximalIdeal R) i).obj M)
      ((maximalIdeal R ^ k : Ideal R) : Set R)) :=
  (show MatlisArtinianModuleCat R from
    ⟨_, regularLocal_localCohomology_matlisArtinian n hdim M i⟩).annihilator_isFiniteLength k

/-- For any original supported dualizing coefficient, the dual of local
cohomology satisfies the literal complete-category conditions. -/
theorem regularLocal_localCohomology_dual_completeProperty_of_dualizing
    (D : ModuleCat.{u} R) (hD : SupportedDualizingModule D) (i : ℕ) :
    matlisCompleteModuleProperty R
      ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) i).obj M))) :=
  matlisArtinianHom_completeProperty D hD
    ⟨_, regularLocal_localCohomology_matlisArtinian n hdim M i⟩

/-- The actual dual has the original completeness and finite-length
power-quotient properties, even over a noncomplete base. -/
theorem regularLocal_localCohomology_dual_completeProperty (i : ℕ) :
    matlisCompleteModuleProperty R
      ((moduleHomDual ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R))).obj
        (op ((_root_.localCohomology (maximalIdeal R) i).obj M))) :=
  regularLocal_localCohomology_dual_completeProperty_of_dualizing n hdim M _
    (regularLocal_localCohomology_dualizing n hdim) i

/-- **V.3.1(ii), finite-generation part over every regular local base.**
The original completed dual is finite over the actual completed ring;
the coefficient can be any original supported dualizing module. -/
theorem regularLocal_completedLocalCohomologyDual_finite_of_dualizing
    (D : ModuleCat.{u} R) (hD : SupportedDualizingModule D) (i : ℕ) :
    Module.Finite (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R)
        ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) i).obj M)))) :=
  matlisComplete_completion_finite _
    (regularLocal_localCohomology_dual_completeProperty_of_dualizing n hdim M D hD i)

/-- Actual completed-dual finiteness with top local cohomology as coefficient,
without assuming the original regular local ring complete. -/
theorem regularLocal_completedLocalCohomologyDual_finite (i : ℕ) :
    Module.Finite (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R)
        ((moduleHomDual
          ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R))).obj
            (op ((_root_.localCohomology (maximalIdeal R) i).obj M)))) :=
  regularLocal_completedLocalCohomologyDual_finite_of_dualizing n hdim M _
    (regularLocal_localCohomology_dualizing n hdim) i

/-- The finite-generation part over a complete regular base holds for
any original supported dualizing coefficient, not only top local cohomology. -/
theorem regularLocal_localCohomology_dual_finite_of_dualizing
    [IsAdicComplete (maximalIdeal R) R]
    (D : ModuleCat.{u} R) (hD : SupportedDualizingModule D) (i : ℕ) :
    Module.Finite R
      ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) i).obj M))) := by
  have := regularLocal_localCohomology_socle_finite n hdim M i
  exact hD.supported_finiteSocle_dual_finite
    _ (show MatlisArtinianModuleCat R from
      ⟨_, regularLocal_localCohomology_matlisArtinian n hdim M i⟩).supported

/-- **V.3.1(ii), finite-generation part over a complete regular base.**
The dual is finite in every degree; no dimension bound is asserted here. -/
theorem regularLocal_localCohomology_dual_finite [IsAdicComplete (maximalIdeal R) R]
    (i : ℕ) :
    Module.Finite R
      ((moduleHomDual ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R))).obj
        (op ((_root_.localCohomology (maximalIdeal R) i).obj M))) :=
  regularLocal_localCohomology_dual_finite_of_dualizing n hdim M _
    (regularLocal_localCohomology_dualizing n hdim) i

end SGA.SGA2.ExposeV
