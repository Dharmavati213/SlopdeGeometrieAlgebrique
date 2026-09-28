/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.LocalCohomologyDualCompletion
import SGA.SGA2.ExposeV.LocalRingFiniteness

/-!
# Finiteness consequences of regular local duality

These regular-local specializations use the general Artinianity and finiteness
results in `LocalRingFiniteness`. Top local cohomology supplies the canonical
dualizing coefficient; no completeness assumption is needed for Artinianity
or finiteness of the completed dual. The dimension bound is proved in
`CompletedDualDimension`. Dimension arguments are retained for compatibility
with the regular-local API.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Local cohomology of a finite module is Artinian. -/
theorem regularLocal_localCohomology_isArtinian
    (n : ℕ) (_hdim : ringKrullDim R = n) (M : ModuleCat.{u} R) [Module.Finite R M]
    (i : ℕ) :
    IsArtinian R ((_root_.localCohomology (maximalIdeal R) i).obj M) :=
  localRing_localCohomology_isArtinian M i

/-- The maximal-ideal socle of local cohomology is finite. -/
theorem regularLocal_localCohomology_socle_finite
    (n : ℕ) (_hdim : ringKrullDim R = n) (M : ModuleCat.{u} R) [Module.Finite R M]
    (i : ℕ) :
    Module.Finite R (localSocle (R := R)
      ((_root_.localCohomology (maximalIdeal R) i).obj M)) :=
  localRing_localCohomology_socle_finite M i

/-- Local cohomology belongs to the Artinian Matlis category. -/
theorem regularLocal_localCohomology_matlisArtinian
    (n : ℕ) (_hdim : ringKrullDim R = n) (M : ModuleCat.{u} R) [Module.Finite R M]
    (i : ℕ) :
    matlisArtinianModuleProperty R ((_root_.localCohomology (maximalIdeal R) i).obj M) :=
  localRing_localCohomology_matlisArtinian M i

/-- Every maximal-ideal-power annihilator has finite length. -/
theorem regularLocal_localCohomology_annihilator_isFiniteLength
    (n : ℕ) (_hdim : ringKrullDim R = n) (M : ModuleCat.{u} R) [Module.Finite R M]
    (i k : ℕ) :
    IsFiniteLength R (Submodule.torsionBySet R
      ((_root_.localCohomology (maximalIdeal R) i).obj M)
      ((maximalIdeal R ^ k : Ideal R) : Set R)) :=
  localRing_localCohomology_annihilator_isFiniteLength M i k

/-- The dual of local cohomology belongs to the complete Matlis category. -/
theorem regularLocal_localCohomology_dual_completeProperty_of_dualizing
    (n : ℕ) (_hdim : ringKrullDim R = n) (M : ModuleCat.{u} R) [Module.Finite R M]
    (D : ModuleCat.{u} R) (hD : SupportedDualizingModule D) (i : ℕ) :
    matlisCompleteModuleProperty R
      ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) i).obj M))) :=
  localRing_localCohomology_dual_completeProperty M D hD i

/-- The canonical dual is complete and has finite-length power quotients. -/
theorem regularLocal_localCohomology_dual_completeProperty
    (n : ℕ) (hdim : ringKrullDim R = n) (M : ModuleCat.{u} R) [Module.Finite R M]
    (i : ℕ) :
    matlisCompleteModuleProperty R
      ((moduleHomDual ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R))).obj
        (op ((_root_.localCohomology (maximalIdeal R) i).obj M))) :=
  regularLocal_localCohomology_dual_completeProperty_of_dualizing n hdim M _
    (regularLocal_localCohomology_dualizing n hdim) i

/-- **V.3.1(ii):** the completed dual is finite over the completed ring. -/
theorem regularLocal_completedLocalCohomologyDual_finite_of_dualizing
    (n : ℕ) (_hdim : ringKrullDim R = n) (M : ModuleCat.{u} R) [Module.Finite R M]
    (D : ModuleCat.{u} R) (hD : SupportedDualizingModule D) (i : ℕ) :
    Module.Finite (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R)
        ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) i).obj M)))) :=
  localRing_completedLocalCohomologyDual_finite M D hD i

/-- The completed canonical dual is finite over the completed ring. -/
theorem regularLocal_completedLocalCohomologyDual_finite
    (n : ℕ) (hdim : ringKrullDim R = n) (M : ModuleCat.{u} R) [Module.Finite R M]
    (i : ℕ) :
    Module.Finite (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R)
        ((moduleHomDual
          ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R))).obj
            (op ((_root_.localCohomology (maximalIdeal R) i).obj M)))) :=
  regularLocal_completedLocalCohomologyDual_finite_of_dualizing n hdim M _
    (regularLocal_localCohomology_dualizing n hdim) i

/-- Over a complete base, the dual itself is finite. -/
theorem regularLocal_localCohomology_dual_finite_of_dualizing
    (n : ℕ) (_hdim : ringKrullDim R = n) (M : ModuleCat.{u} R) [Module.Finite R M]
    [IsAdicComplete (maximalIdeal R) R]
    (D : ModuleCat.{u} R) (hD : SupportedDualizingModule D) (i : ℕ) :
    Module.Finite R
      ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) i).obj M))) :=
  localRing_localCohomology_dual_finite M D hD i

/-- **V.3.1(ii):** over a complete base, the canonical dual is finite. -/
theorem regularLocal_localCohomology_dual_finite
    (n : ℕ) (hdim : ringKrullDim R = n) (M : ModuleCat.{u} R) [Module.Finite R M]
    [IsAdicComplete (maximalIdeal R) R]
    (i : ℕ) :
    Module.Finite R
      ((moduleHomDual ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R))).obj
        (op ((_root_.localCohomology (maximalIdeal R) i).obj M))) :=
  regularLocal_localCohomology_dual_finite_of_dualizing n hdim M _
    (regularLocal_localCohomology_dualizing n hdim) i

end SGA.SGA2.ExposeV
