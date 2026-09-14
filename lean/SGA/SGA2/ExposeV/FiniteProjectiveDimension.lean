/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.RegularLocalExtVanishing
import SGA.SGA2.ExposeV.ClosedPointSupportDimension
import Mathlib.RingTheory.Regular.ProjectiveDimension

/-!
# Finite-module projective dimension over a regular local ring

A uniform bound for finite-length modules bounds all finite modules over a
noetherian local ring. Induction on the actual support dimension removes
closed-point torsion, then quotients by a genuine regular element. Applying
the proved residue-field and finite-length bound gives the Krull-dimension
bound over an actual regular local ring, without assuming global dimension.
This supplies a homological input for regularity of prime localizations.
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

section Local

variable [IsNoetherianRing R] [IsLocalRing R]

/-- A finite-length projective-dimension bound extends to every finite
module of a specified support dimension. The support dimension is only the
induction parameter, not an additional constraint on the bound. -/
theorem finite_hasProjectiveDimensionLE_of_supportDim
    (n : ℕ)
    (hfiniteLength : ∀ N : ModuleCat.{u} R, IsFiniteLength R N →
      HasProjectiveDimensionLE N n)
    (d : ℕ) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hdim : Module.supportDim R M = d) : HasProjectiveDimensionLE M n := by
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  induction d generalizing M with
  | zero =>
    exact hfiniteLength M (isFiniteLength_of_finite_of_support (maximalIdeal R) M
      (support_of_supportDim_eq_zero R M (by simpa using hdim)).le)
  | succ d ih =>
    let T := ModuleCat.of R (powerTorsion (maximalIdeal R) M)
    let Q := ModuleCat.of R (M ⧸ powerTorsion (maximalIdeal R) M)
    have hT : HasProjectiveDimensionLE T n :=
      hfiniteLength T (isFiniteLength_of_finite_of_support (maximalIdeal R) T
        (support_powerTorsion_subset_zeroLocus (maximalIdeal R) M))
    have hdQ : Module.supportDim R Q = d + 1 :=
      (supportDim_powerTorsion_quotient_eq M (by rw [hdim]; positivity)).trans hdim
    obtain ⟨x, hxm, hxQ⟩ := exists_regular_on_powerTorsion_quotient M
    let P := ModuleCat.of R (QuotSMulTop x Q)
    have hdP : Module.supportDim R P = d := by
      apply ENat.WithBot.add_one_cancel.mp
      exact (Module.supportDim_quotSMulTop_succ_eq_supportDim hxQ hxm).trans hdQ
    have hP := ih P hdP
    have hQ : HasProjectiveDimensionLE Q n := by
      apply (projectiveDimension_le_iff Q n).mp
      have heq := ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular Q x hxQ hxm
      have hle := (projectiveDimension_le_iff P n).mpr hP
      rw [show P = ModuleCat.of R (QuotSMulTop x Q) from rfl, heq] at hle
      exact le_trans (by exact le_add_of_nonneg_right (by norm_num)) hle
    exact (powerTorsionShortComplex_shortExact (maximalIdeal R) M).hasProjectiveDimensionLT_X₂
      (n + 1) hT hQ

/-- Over a noetherian local ring, a uniform finite-length bound is already
a uniform bound for every finite module, including the zero module. -/
theorem finite_hasProjectiveDimensionLE_of_finiteLength
    (n : ℕ)
    (hfiniteLength : ∀ N : ModuleCat.{u} R, IsFiniteLength R N →
      HasProjectiveDimensionLE N n)
    (M : ModuleCat.{u} R) [Module.Finite R M] : HasProjectiveDimensionLE M n := by
  by_cases hM : Subsingleton M
  · have := hM
    have := (ModuleCat.isZero_of_subsingleton M).hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge M 0 (n + 1) (Nat.zero_le _)
  · have : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    have hb := Module.supportDim_ne_bot_of_nontrivial R M
    obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hb
    have hdt : d ≠ ⊤ := by
      intro ht
      have hbound := Module.supportDim_le_ringKrullDim R M
      rw [← hd, ht, ringKrullDim, Order.krullDim_eq_length_of_finiteDimensionalOrder] at hbound
      exact (not_le_of_gt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))) hbound
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hdt
    exact finite_hasProjectiveDimensionLE_of_supportDim n hfiniteLength k M
      (hd.symm.trans (congrArg WithBot.some hk.symm))

/-- The residue field alone detects a uniform projective-dimension bound
on every finite module over a noetherian local ring. -/
theorem finite_hasProjectiveDimensionLE_of_residueField (n : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n]
    (M : ModuleCat.{u} R) [Module.Finite R M] : HasProjectiveDimensionLE M n :=
  finite_hasProjectiveDimensionLE_of_finiteLength n
    (local_finiteLength_hasProjectiveDimensionLE_of_residueField n) M

end Local

section Regular

variable [IsRegularLocalRing R]

/-- Every actual finite module over a regular local ring has projective
dimension at most the ring's actual Krull dimension. -/
theorem regularLocal_finite_hasProjectiveDimensionLE (n : ℕ)
    (hdim : ringKrullDim R = n) (M : ModuleCat.{u} R) [Module.Finite R M] :
    HasProjectiveDimensionLE M n :=
  finite_hasProjectiveDimensionLE_of_finiteLength n
    (regularLocal_finiteLength_hasProjectiveDimensionLE n hdim) M

/-- The same bound as an inequality of the original extended dimensions. -/
theorem regularLocal_finite_projectiveDimension_le (n : ℕ)
    (hdim : ringKrullDim R = n) (M : ModuleCat.{u} R) [Module.Finite R M] :
    projectiveDimension M ≤ n :=
  (projectiveDimension_le_iff M n).mpr (regularLocal_finite_hasProjectiveDimensionLE n hdim M)

/-- All original Ext groups above the ring dimension vanish, with finite
first argument and completely arbitrary second argument. -/
theorem regularLocal_ext_subsingleton_of_finite_of_gt (n : ℕ)
    (hdim : ringKrullDim R = n) (M N : ModuleCat.{u} R) [Module.Finite R M]
    (i : ℕ) (hi : n < i) : Subsingleton (Abelian.Ext M N i) := by
  have := regularLocal_finite_hasProjectiveDimensionLE n hdim M
  exact HasProjectiveDimensionLT.subsingleton M (n + 1) i hi N

end Regular

end SGA.SGA2.ExposeV
