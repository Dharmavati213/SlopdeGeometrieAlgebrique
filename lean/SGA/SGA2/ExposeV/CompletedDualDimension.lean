/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.LocalCohomologyDualDimension
import SGA.SGA2.ExposeIV.CompletionExactness

/-!
# V.3.1(ii): dimension of the original completed dual

No completeness of the base ring is assumed. The dual local-cohomology
modules themselves are complete, so their original exact sequence remains
exact under actual completion. The completed-ring dimension inequality then
allows induction on cohomological degree, with the original coefficient
torsion quotient and regular-element sequence.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The original degree-zero Hom dual is supported at the closed point,
even when the base ring is not complete. -/
theorem localRing_localCohomologyZero_dual_supported
    (M D : ModuleCat.{u} R) [Module.Finite R M] (hD : SupportedDualizingModule D) :
    supportedModuleProperty (maximalIdeal R)
      ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) 0).obj M))) := by
  let T := ModuleCat.of R (powerTorsion (maximalIdeal R) M)
  have hs : supportedModuleProperty (maximalIdeal R) T :=
    support_powerTorsion_subset_zeroLocus _ M
  have : Module.Finite R ((moduleHomDual D).obj (op T)) := hD.2.1 T inferInstance hs
  let e := (moduleHomDual D).mapIso (localCohomologyZeroIsoPowerTorsion (maximalIdeal R) M).op
  exact (Module.support_subset_of_surjective e.hom.hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)).trans
      ((moduleHomDual_support_subset D T).trans hs)

/-- The original completed degree-zero dual has dimension at most zero. -/
theorem localRing_completedLocalCohomologyZeroDual_supportDim_le
    (M D : ModuleCat.{u} R) [Module.Finite R M] (hD : SupportedDualizingModule D) :
    Module.supportDim (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R)
        ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) 0).obj M)))) ≤ 0 := by
  have := (localRing_localCohomology_dual_completeProperty M D hD 0).2
  let C := ModuleCat.of (AdicCompletion (maximalIdeal R) R)
    (AdicCompletion (maximalIdeal R)
      ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) 0).obj M))))
  apply supportDim_le_zero_of_supported_maximalIdeal C
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact completion_supported_of_complete _ (IsNoetherian.noetherian _) _
    (localRing_localCohomologyZero_dual_supported M D hD)

/-- The actual completed regular-element sequence bounds the principal
quotient of the completed higher dual by the completed lower dual. -/
theorem localRing_completedLocalCohomologyDual_quotSMulTop_supportDim_le
    (M D : ModuleCat.{u} R) [Module.Finite R M] (hD : SupportedDualizingModule D)
    (x : R) (hx : IsSMulRegular M x) (i : ℕ) :
    Module.supportDim (AdicCompletion (maximalIdeal R) R)
      (QuotSMulTop (algebraMap R (AdicCompletion (maximalIdeal R) R) x)
        (AdicCompletion (maximalIdeal R)
          ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) (i + 1)).obj M))))) ≤
      Module.supportDim (AdicCompletion (maximalIdeal R) R)
        (AdicCompletion (maximalIdeal R) ((moduleHomDual D).obj
          (op ((_root_.localCohomology (maximalIdeal R) i).obj
            (ModuleCat.of R (QuotSMulTop x M)))))) := by
  have : Injective D := ((supportedDualizingModule_iff_injective_essential_residue D).mp hD).1
  let S := localCohomologyDualScalarSequence (maximalIdeal R) M D x hx i
  have : IsAdicComplete (maximalIdeal R) S.X₁ :=
    (localRing_localCohomology_dual_completeProperty M D hD (i + 1)).2
  have : IsAdicComplete (maximalIdeal R) S.X₂ :=
    (localRing_localCohomology_dual_completeProperty M D hD (i + 1)).2
  have : IsAdicComplete (maximalIdeal R) S.X₃ :=
    (localRing_localCohomology_dual_completeProperty
      (ModuleCat.of R (QuotSMulTop x M)) D hD i).2
  let C := completionShortComplex (maximalIdeal R) S
  have he : C.Exact := completionShortComplex_exact_of_complete _ S
    (localCohomologyDualScalarSequence_exact _ M D x hx i)
  have hf : C.f = algebraMap R (AdicCompletion (maximalIdeal R) R) x • 𝟙 C.X₂ := by
    change ModuleCat.ofHom (AdicCompletion.map (maximalIdeal R) S.f.hom) = _
    have hfS : S.f = x • 𝟙 S.X₂ := localCohomologyDualScalarSequence_f _ M D x hx i
    rw [hfS]
    exact completion_map_smul_id _ S.X₂ x
  have hw := C.zero
  rw [hf] at hw
  apply supportDim_quotSMulTop_le_of_exact C.X₂ C.X₃ _ C.g hw
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range
    (algebraMap R (AdicCompletion (maximalIdeal R) R) x • 𝟙 C.X₂).hom = LinearMap.ker C.g.hom
  rw [← hf]
  exact he.moduleCat_range_eq_ker

/-- **V.3.1(ii), dimension assertion.** The original completed dual of
degree-`i` local cohomology has dimension at most `i` over the actual
completed ring, for every noetherian local base. -/
theorem localRing_completedLocalCohomologyDual_supportDim_le
    (M D : ModuleCat.{u} R) [Module.Finite R M] (hD : SupportedDualizingModule D) (i : ℕ) :
    Module.supportDim (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R)
        ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) i).obj M)))) ≤ i := by
  induction i generalizing M with
  | zero => exact localRing_completedLocalCohomologyZeroDual_supportDim_le M D hD
  | succ i ih =>
    let Q := ModuleCat.of R (M ⧸ powerTorsion (maximalIdeal R) M)
    have := localCohomology_powerTorsion_mkQ_isIso (maximalIdeal R) M (i + 1) (by omega)
    let e := asIso ((_root_.localCohomology (maximalIdeal R) (i + 1)).map
      (ModuleCat.ofHom (powerTorsion (maximalIdeal R) M).mkQ))
    rw [← Module.supportDim_eq_of_equiv (AdicCompletion.congr (maximalIdeal R)
      ((moduleHomDual D).mapIso e.op).toLinearEquiv)]
    obtain ⟨x, hxm, hx⟩ := exists_regular_on_powerTorsion_quotient M
    let A := AdicCompletion (maximalIdeal R) R
    let N := AdicCompletion (maximalIdeal R) ((moduleHomDual D).obj
      (op ((_root_.localCohomology (maximalIdeal R) (i + 1)).obj Q)))
    have : Module.Finite A N := localRing_completedLocalCohomologyDual_finite Q D hD (i + 1)
    have hxa : algebraMap R A x ∈ maximalIdeal A := by
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem _ hxm
    calc
      Module.supportDim A N ≤ Module.supportDim A (QuotSMulTop (algebraMap R A x) N) + 1 :=
        Module.supportDim_le_supportDim_quotSMulTop_succ hxa
      _ ≤ Module.supportDim A (AdicCompletion (maximalIdeal R) ((moduleHomDual D).obj
          (op ((_root_.localCohomology (maximalIdeal R) i).obj
            (ModuleCat.of R (QuotSMulTop x Q)))))) + 1 :=
        _root_.add_le_add (localRing_completedLocalCohomologyDual_quotSMulTop_supportDim_le
          Q D hD x hx i) le_rfl
      _ ≤ (i : WithBot ℕ∞) + 1 := _root_.add_le_add
        (ih (ModuleCat.of R (QuotSMulTop x Q))) le_rfl
      _ = (i + 1 : ℕ) := by simp

end SGA.SGA2.ExposeV
