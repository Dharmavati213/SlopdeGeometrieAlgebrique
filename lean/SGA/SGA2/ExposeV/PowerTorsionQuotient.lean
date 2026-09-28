/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.InjectiveTorsion
import SGA.SGA2.ExposeIII.AssociatedPrimes

/-!
# Removing actual ideal-power torsion from a finite module

The quotient by the original power-torsion submodule has no remaining
power torsion. Uniform annihilation of the finite torsion submodule proves
the assertion. At the maximal ideal, the actual quotient consequently
admits a regular element in that ideal.
-/

noncomputable section
universe u
open CategoryTheory IsLocalRing
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A finite module's original power-torsion submodule is uniformly
annihilated by some ideal power. -/
theorem powerTorsion_exists_pow_annihilator (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ k : ℕ, I ^ k ≤ Module.annihilator R (powerTorsion I M) := by
  obtain ⟨k, hk⟩ := exists_le_torsionBySet_pow_of_fg I (powerTorsion I M)
    (IsNoetherian.noetherian _) le_rfl
  refine ⟨k, fun r hr => Module.mem_annihilator.mpr (fun x => ?_)⟩
  apply Subtype.ext
  exact ((Submodule.mem_torsionBySet_iff _ _).mp (hk x.property)) ⟨r, hr⟩

/-- The actual quotient by ideal-power torsion has no ideal-power torsion. -/
theorem powerTorsion_quotient_eq_bot (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    powerTorsion I (M ⧸ powerTorsion I M) = ⊥ := by
  obtain ⟨k, hk⟩ := powerTorsion_exists_pow_annihilator I M
  apply bot_unique
  intro x hx
  obtain ⟨y, rfl⟩ := (powerTorsion I M).mkQ_surjective x
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨n, hn⟩ := (mem_powerTorsion_iff I _ _).mp hx
  apply (mem_powerTorsion_iff I M y).mpr
  refine ⟨k + n, fun a ha => ?_⟩
  rw [pow_add, ← Ideal.smul_eq_mul] at ha
  refine Submodule.smul_induction_on ha ?_ ?_
  · intro r hr s hs
    have hsy : s • y ∈ powerTorsion I M := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change (powerTorsion I M).mkQ (s • y) = 0
      simpa only [map_smul] using hn s hs
    exact (mul_smul r s y).trans
      (congrArg Subtype.val (Module.mem_annihilator.mp (hk hr) ⟨s • y, hsy⟩))
  · intro a b ha hb
    simp only [add_smul, ha, hb, add_zero]

/-- The original torsion quotient has no nonzero element killed by the
whole ideal. -/
theorem idealRegular_powerTorsion_quotient (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IdealRegular (M ⧸ powerTorsion I M) I := by
  intro x hx
  have hmem : x ∈ powerTorsion I (M ⧸ powerTorsion I M) :=
    (mem_powerTorsion_iff I _ x).mpr ⟨1, by simpa only [pow_one] using hx⟩
  simpa only [powerTorsion_quotient_eq_bot, Submodule.mem_bot] using hmem

/-- An actual regular element exists on the finite maximal-ideal torsion
quotient, without regularity of the original local ring. -/
theorem exists_regular_on_powerTorsion_quotient [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ x ∈ maximalIdeal R, IsSMulRegular (M ⧸ powerTorsion (maximalIdeal R) M) x :=
  (idealRegular_iff_exists_regular _ _).mp
    (idealRegular_powerTorsion_quotient (maximalIdeal R) M)

end SGA.SGA2.ExposeV
