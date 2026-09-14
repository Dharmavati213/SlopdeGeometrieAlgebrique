/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.LocalCohomologyArtinian
import SGA.SGA2.ExposeIV.CompleteModuleScalarChange

/-!
# V.3.1(ii): finite generation over every noetherian local base

Genuine Artinianity places original local cohomology in the literal Matlis
category. For any supported dualizing coefficient its actual Hom dual is
complete with finite-length power quotients, and its original completion is
finite over the actual completed ring. The base need not be regular or
complete. The bound on the dimension of that finite dual remains separate.
-/

noncomputable section
universe u
open CategoryTheory Opposite IsLocalRing
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (M : ModuleCat.{u} R) [Module.Finite R M]

/-- The unchanged local-cohomology object belongs to the original Matlis
category over every noetherian local ring. -/
theorem localRing_localCohomology_matlisArtinian (i : ℕ) :
    matlisArtinianModuleProperty R ((_root_.localCohomology (maximalIdeal R) i).obj M) := by
  have := localRing_localCohomology_isArtinian M i
  exact matlisArtinianModuleProperty_of_isArtinian _

/-- The actual maximal-ideal socle of local cohomology is finite. -/
theorem localRing_localCohomology_socle_finite (i : ℕ) :
    Module.Finite R (localSocle (R := R)
      ((_root_.localCohomology (maximalIdeal R) i).obj M)) :=
  (localRing_localCohomology_matlisArtinian M i).2

/-- Original local cohomology has actual support at the closed point. -/
theorem localRing_localCohomology_supported (i : ℕ) :
    supportedModuleProperty (maximalIdeal R)
      ((_root_.localCohomology (maximalIdeal R) i).obj M) :=
  (show MatlisArtinianModuleCat R from
    ⟨_, localRing_localCohomology_matlisArtinian M i⟩).supported

/-- Every actual maximal-ideal-power annihilator in local cohomology has
finite length, without a regularity or completeness assumption. -/
theorem localRing_localCohomology_annihilator_isFiniteLength (i k : ℕ) :
    IsFiniteLength R (Submodule.torsionBySet R
      ((_root_.localCohomology (maximalIdeal R) i).obj M)
      ((maximalIdeal R ^ k : Ideal R) : Set R)) :=
  (show MatlisArtinianModuleCat R from
    ⟨_, localRing_localCohomology_matlisArtinian M i⟩).annihilator_isFiniteLength k

/-- For any actual supported dualizing coefficient, the original dual of
local cohomology satisfies the literal complete-category conditions. -/
theorem localRing_localCohomology_dual_completeProperty
    (D : ModuleCat.{u} R) (hD : SupportedDualizingModule D) (i : ℕ) :
    matlisCompleteModuleProperty R
      ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) i).obj M))) :=
  matlisArtinianHom_completeProperty D hD
    ⟨_, localRing_localCohomology_matlisArtinian M i⟩

/-- **V.3.1(ii), finite-generation assertion.** The original completed
dual of local cohomology is finite over the actual completed ring, for
every noetherian local base and any supported dualizing coefficient.
This does not assert the separate dimension bound. -/
theorem localRing_completedLocalCohomologyDual_finite
    (D : ModuleCat.{u} R) (hD : SupportedDualizingModule D) (i : ℕ) :
    Module.Finite (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R)
        ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) i).obj M)))) :=
  matlisComplete_completion_finite _ (localRing_localCohomology_dual_completeProperty M D hD i)

/-- Over a complete noetherian local base the original dual itself is
finite, without regularity of the ring. -/
theorem localRing_localCohomology_dual_finite [IsAdicComplete (maximalIdeal R) R]
    (D : ModuleCat.{u} R) (hD : SupportedDualizingModule D) (i : ℕ) :
    Module.Finite R
      ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) i).obj M))) := by
  have := localRing_localCohomology_socle_finite M i
  exact hD.supported_finiteSocle_dual_finite _ (localRing_localCohomology_supported M i)

end SGA.SGA2.ExposeV
