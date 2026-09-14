/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.CompletionRegularElements
import SGA.SGA2.ExposeV.CompletedDualRegularSequence
import SGA.SGA2.ExposeV.LocalCohomologyZeroNonvanishing
import SGA.SGA2.ExposeV.ModuleDimensionVanishing

/-!
# V.3.1(iii): top nonvanishing over every noetherian local base

Choose actual original-ring parameters by avoiding the contractions of
the associated primes of the preceding completed dual's torsion quotient.
The genuine completed dual sequence and upper vanishing give the exact
dimension of the completed top dual. This forces the unchanged original
top local-cohomology module to be nonzero, without completeness of the base.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The actual completed degree-zero dual of a zero-dimensional finite
coefficient module has dimension exactly zero. -/
theorem localRing_completedLocalCohomologyZeroDual_supportDim_eq_zero
    (M D : ModuleCat.{u} R) [Module.Finite R M] (hD : SupportedDualizingModule D)
    (hdim : Module.supportDim R M = 0) :
    Module.supportDim (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R)
        ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) 0).obj M)))) = 0 := by
  let N := (moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) 0).obj M))
  have hdN : Module.supportDim R N = 0 :=
    localRing_localCohomologyZero_dual_supportDim_eq_zero M D hD hdim
  have : Nontrivial N := (Module.supportDim_ne_bot_iff_nontrivial R N).mp (by simp [hdN])
  have : IsAdicComplete (maximalIdeal R) N :=
    (localRing_localCohomology_dual_completeProperty M D hD 0).2
  have : Nontrivial (AdicCompletion (maximalIdeal R) N) :=
    (AdicCompletion.of_bijective (maximalIdeal R) N).1.nontrivial
  have : Nonempty (Module.support (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R) N)) := Module.nonempty_support_of_nontrivial.to_subtype
  exact le_antisymm (localRing_completedLocalCohomologyZeroDual_supportDim_le M D hD)
    Order.krullDim_nonneg

/-- The original completed top local-cohomology dual has exactly the
actual coefficient support dimension over every noetherian local base. -/
theorem localRing_completedTopLocalCohomologyDual_supportDim_eq
    (n : ℕ) (M D : ModuleCat.{u} R) [Module.Finite R M]
    (hD : SupportedDualizingModule D) (hdim : Module.supportDim R M = n) :
    Module.supportDim (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R) ((moduleHomDual D).obj
        (op ((_root_.localCohomology (maximalIdeal R) n).obj M)))) = n := by
  have : Injective D := ((supportedDualizingModule_iff_injective_essential_residue D).mp hD).1
  induction n generalizing M with
  | zero => exact localRing_completedLocalCohomologyZeroDual_supportDim_eq_zero M D hD hdim
  | succ n ih =>
    let Q := ModuleCat.of R (M ⧸ powerTorsion (maximalIdeal R) M)
    have hdQ : Module.supportDim R Q = n + 1 :=
      (supportDim_powerTorsion_quotient_eq M (by rw [hdim]; positivity)).trans hdim
    have := localCohomology_powerTorsion_mkQ_isIso (maximalIdeal R) M (n + 1) (by omega)
    let e := asIso ((_root_.localCohomology (maximalIdeal R) (n + 1)).map
      (ModuleCat.ofHom (powerTorsion (maximalIdeal R) M).mkQ))
    rw [← Module.supportDim_eq_of_equiv (AdicCompletion.congr (maximalIdeal R)
      ((moduleHomDual D).mapIso e.op).toLinearEquiv)]
    let A := AdicCompletion (maximalIdeal R) R
    let L := ModuleCat.of A (AdicCompletion (maximalIdeal R)
      ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) n).obj Q))))
    have : Module.Finite A L := localRing_completedLocalCohomologyDual_finite Q D hD n
    obtain ⟨x, hxm, hxQ, hxL⟩ := exists_regular_coefficient_and_completion_torsion_quotient
      Q (idealRegular_powerTorsion_quotient (maximalIdeal R) M) L
    let a := algebraMap R A x
    have ha : a ∈ maximalIdeal A := by
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem _ hxm
    let P := ModuleCat.of R (QuotSMulTop x Q)
    have hdP : Module.supportDim R P = n := by
      apply ENat.WithBot.add_one_cancel.mp
      exact (Module.supportDim_quotSMulTop_succ_eq_supportDim hxQ hxm).trans hdQ
    let N₀ := (moduleHomDual D).obj
      (op ((_root_.localCohomology (maximalIdeal R) (n + 1)).obj Q))
    have : IsAdicComplete (maximalIdeal R) N₀ :=
      (localRing_localCohomology_dual_completeProperty Q D hD (n + 1)).2
    let N := ModuleCat.of A (AdicCompletion (maximalIdeal R) N₀)
    have : Module.Finite A N := localRing_completedLocalCohomologyDual_finite Q D hD (n + 1)
    let B₀ := (moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) n).obj P))
    let B := ModuleCat.of A (AdicCompletion (maximalIdeal R) B₀)
    have hdB : Module.supportDim A B = n := ih P hdP
    have hxN : IsSMulRegular N a := completion_isSMulRegular_of_complete (maximalIdeal R) N₀ x
      (localCohomology_dual_regular_of_quotient_vanishing (maximalIdeal R) Q D x hxQ (n + 1)
        (localRing_localCohomology_isZero_of_gt_moduleDim P n hdP (n + 1) (by omega)))
    have hlower : (n : WithBot ℕ∞) ≤ Module.supportDim A (QuotSMulTop a N) := by
      cases n with
      | zero =>
        have hz := localCohomologyZero_powerTorsion_quotient_isZero (maximalIdeal R) M
        let δ := localCohomologyYonedaBoundary (maximalIdeal R) (Q.smulShortComplex x)
          hxQ.smulShortComplex_shortExact 0
        have : Mono δ := localCohomologyYonedaBoundary_mono _ _ _ _ hz
        have : Epi ((moduleHomDual D).map δ.op) := inferInstance
        let f : N₀ ⟶ B₀ := (moduleHomDual D).map δ.op
        have hf : Function.Surjective f.hom :=
          (ModuleCat.epi_iff_surjective ((moduleHomDual D).map δ.op)).mp inferInstance
        let g : N ⟶ B := ModuleCat.ofHom (AdicCompletion.map (maximalIdeal R) f.hom)
        have hg : Function.Surjective g.hom := AdicCompletion.map_surjective (maximalIdeal R) hf
        have : Nontrivial B := (Module.supportDim_ne_bot_iff_nontrivial A B).mp (by simp [hdB])
        have : Nontrivial N := hg.nontrivial
        have : Nontrivial (QuotSMulTop a N) := nontrivial_quotSMulTop_of_mem_maximalIdeal N ha
        have : Nonempty (Module.support A (QuotSMulTop a N)) :=
          Module.nonempty_support_of_nontrivial.to_subtype
        exact Order.krullDim_nonneg
      | succ k =>
        rw [← hdB]
        exact localRing_completedDual_quotient_supportDim_le_quotSMulTop Q D hD x hxQ (k + 1)
          (support_ker_smul_subset_of_quotient_regular (maximalIdeal A) L a hxL)
          (by rw [hdB]; positivity)
    apply le_antisymm (localRing_completedLocalCohomologyDual_supportDim_le Q D hD (n + 1))
    calc
      ((n + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) + 1 := by simp
      _ ≤ Module.supportDim A (QuotSMulTop a N) + 1 := _root_.add_le_add hlower le_rfl
      _ = Module.supportDim A N := Module.supportDim_quotSMulTop_succ_eq_supportDim hxN ha

/-- **V.3.1(iii), top nonvanishing.** The unchanged local cohomology in
the actual dimension of a nonzero finite module is nonzero over every
noetherian local ring, without completeness or regularity of the base. -/
theorem localRing_topLocalCohomology_nontrivial
    (n : ℕ) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hdim : Module.supportDim R M = n) :
    Nontrivial ((_root_.localCohomology (maximalIdeal R) n).obj M) := by
  obtain ⟨D, hD⟩ := exists_supportedDualizingModule (R := R)
  have hd := localRing_completedTopLocalCohomologyDual_supportDim_eq n M D hD hdim
  let N := (moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) n).obj M))
  have : IsAdicComplete (maximalIdeal R) N :=
    (localRing_localCohomology_dual_completeProperty M D hD n).2
  by_contra! hz
  have := hz
  have hz' := ModuleCat.isZero_of_subsingleton
    ((_root_.localCohomology (maximalIdeal R) n).obj M)
  have : Subsingleton N := ⟨fun f g => hz'.eq_of_src f g⟩
  have : Subsingleton (AdicCompletion (maximalIdeal R) N) :=
    (AdicCompletion.of_bijective (maximalIdeal R) N).2.subsingleton
  rw [Module.supportDim_eq_bot_of_subsingleton] at hd
  exact (WithBot.bot_ne_coe : (⊥ : WithBot ℕ∞) ≠ (n : ℕ∞)) hd

end SGA.SGA2.ExposeV
