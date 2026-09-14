/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.LocalCohomologyDualRegularSequence
import SGA.SGA2.ExposeV.LocalCohomologyZeroNonvanishing
import SGA.SGA2.ExposeV.ModuleDimensionVanishing

/-!
# V.3.1(iii): the top dual's dimension over a complete local ring

Induction on the actual coefficient support dimension uses a simultaneous
regular element on the coefficient torsion quotient and the preceding
dual's torsion quotient. The original dual regular-element sequence confines
its error to the closed point. Upper vanishing makes the chosen element
regular on the top dual, giving the exact dimension equality.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable [IsAdicComplete (maximalIdeal R) R]

/-- **V.3.1(iii), top-dual dimension.** Over a complete noetherian local
ring, the original top local-cohomology dual has exactly the actual
support dimension of the nonzero finite coefficient module. -/
theorem completeLocal_topLocalCohomology_dual_supportDim_eq
    (n : ℕ) (M D : ModuleCat.{u} R) [Module.Finite R M]
    (hD : SupportedDualizingModule D) (hdim : Module.supportDim R M = n) :
    Module.supportDim R ((moduleHomDual D).obj
      (op ((_root_.localCohomology (maximalIdeal R) n).obj M))) = n := by
  have : Injective D := ((supportedDualizingModule_iff_injective_essential_residue D).mp hD).1
  induction n generalizing M with
  | zero => exact localRing_localCohomologyZero_dual_supportDim_eq_zero M D hD hdim
  | succ n ih =>
    let Q := ModuleCat.of R (M ⧸ powerTorsion (maximalIdeal R) M)
    have hdQ : Module.supportDim R Q = n + 1 :=
      (supportDim_powerTorsion_quotient_eq M (by rw [hdim]; positivity)).trans hdim
    have := localCohomology_powerTorsion_mkQ_isIso (maximalIdeal R) M (n + 1) (by omega)
    let e := asIso ((_root_.localCohomology (maximalIdeal R) (n + 1)).map
      (ModuleCat.ofHom (powerTorsion (maximalIdeal R) M).mkQ))
    rw [← Module.supportDim_eq_of_equiv ((moduleHomDual D).mapIso e.op).toLinearEquiv]
    let L := (moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) n).obj Q))
    have : Module.Finite R L := localRing_localCohomology_dual_finite Q D hD n
    obtain ⟨x, hxm, hxQ, hxL⟩ := exists_simultaneous_regular_of_idealRegular (maximalIdeal R)
      Q (ModuleCat.of R (L ⧸ powerTorsion (maximalIdeal R) L))
      (idealRegular_powerTorsion_quotient (maximalIdeal R) M)
      (idealRegular_powerTorsion_quotient (maximalIdeal R) L)
    let P := ModuleCat.of R (QuotSMulTop x Q)
    have hdP : Module.supportDim R P = n := by
      apply ENat.WithBot.add_one_cancel.mp
      exact (Module.supportDim_quotSMulTop_succ_eq_supportDim hxQ hxm).trans hdQ
    let N := (moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) (n + 1)).obj Q))
    have : Module.Finite R N := localRing_localCohomology_dual_finite Q D hD (n + 1)
    let B := (moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) n).obj P))
    have hdB : Module.supportDim R B = n := ih P hdP
    have hxN : IsSMulRegular N x := localCohomology_dual_regular_of_quotient_vanishing
      (maximalIdeal R) Q D x hxQ (n + 1)
      (localRing_localCohomology_isZero_of_gt_moduleDim P n hdP (n + 1) (by omega))
    have hlower : (n : WithBot ℕ∞) ≤ Module.supportDim R (QuotSMulTop x N) := by
      cases n with
      | zero =>
        have hz := localCohomologyZero_powerTorsion_quotient_isZero (maximalIdeal R) M
        let δ := localCohomologyYonedaBoundary (maximalIdeal R) (Q.smulShortComplex x)
          hxQ.smulShortComplex_shortExact 0
        have : Mono δ := localCohomologyYonedaBoundary_mono _ _ _ _ hz
        have : Epi ((moduleHomDual D).map δ.op) := inferInstance
        have : Nontrivial B := (Module.supportDim_ne_bot_iff_nontrivial R B).mp (by simp [hdB])
        let f : N ⟶ B := (moduleHomDual D).map δ.op
        have hsurj : Function.Surjective f.hom :=
          (ModuleCat.epi_iff_surjective ((moduleHomDual D).map δ.op)).mp inferInstance
        have : Nontrivial N := hsurj.nontrivial
        have : Nontrivial (QuotSMulTop x N) := nontrivial_quotSMulTop_of_mem_maximalIdeal N hxm
        have : Nonempty (Module.support R (QuotSMulTop x N)) :=
          Module.nonempty_support_of_nontrivial.to_subtype
        exact Order.krullDim_nonneg
      | succ k =>
        rw [← hdB]
        exact localCohomology_dual_quotient_supportDim_le_quotSMulTop (maximalIdeal R)
          Q D x hxQ (k + 1)
          (support_ker_smul_subset_of_quotient_regular (maximalIdeal R) L x hxL)
          (by rw [hdB]; positivity)
    apply le_antisymm (completeLocal_localCohomology_dual_supportDim_le Q D hD (n + 1))
    calc
      ((n + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) + 1 := by simp
      _ ≤ Module.supportDim R (QuotSMulTop x N) + 1 := _root_.add_le_add hlower le_rfl
      _ = Module.supportDim R N := Module.supportDim_quotSMulTop_succ_eq_supportDim hxN hxm

/-- **V.3.1(iii), complete-base nonvanishing.** The original local
cohomology in the actual dimension of a nonzero finite module is nonzero. -/
theorem completeLocal_topLocalCohomology_nontrivial
    (n : ℕ) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hdim : Module.supportDim R M = n) :
    Nontrivial ((_root_.localCohomology (maximalIdeal R) n).obj M) := by
  obtain ⟨D, hD⟩ := exists_supportedDualizingModule (R := R)
  have hd := completeLocal_topLocalCohomology_dual_supportDim_eq n M D hD hdim
  by_contra! hz
  have := hz
  have hz' := ModuleCat.isZero_of_subsingleton
    ((_root_.localCohomology (maximalIdeal R) n).obj M)
  have : Subsingleton ((moduleHomDual D).obj
      (op ((_root_.localCohomology (maximalIdeal R) n).obj M))) :=
    ⟨fun f g => hz'.eq_of_src f g⟩
  rw [Module.supportDim_eq_bot_of_subsingleton] at hd
  exact (WithBot.bot_ne_coe : (⊥ : WithBot ℕ∞) ≠ (n : ℕ∞)) hd

end SGA.SGA2.ExposeV
