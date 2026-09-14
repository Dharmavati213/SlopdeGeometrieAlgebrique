/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVII.DepthCodimension
import SGA.SGA2.ExposeVII.VanishingCriteria
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Ideal.Height

/-!
# SGA 2, VII.1.4: Cohen–Macaulay modules and codimension

Local Cohen–Macaulay: depth equals support dimension. Under that equality the
vanishing criteria of VII.1.2 become support-dimension / codimension bounds.
-/

noncomputable section

universe u

open CategoryTheory
open SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeVII

variable {R : Type u} [CommRing R]

/-- Local Cohen–Macaulay condition: depth equals support dimension as
`WithBot ℕ∞`. -/
def IsCohenMacaulayAtMaximalIdeal [IsLocalRing R] (M : ModuleCat.{u} R) : Prop :=
  (depth (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) = Module.supportDim R M

noncomputable def supportCodim (J : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] : WithBot ℕ∞ :=
  Order.krullDim
    (Module.support R M ∩ PrimeSpectrum.zeroLocus (J : Set R) : Set _)

variable [IsNoetherianRing R]

theorem VII_1_4_depth_iff_dim_bound (J : Ideal R) (M : ModuleCat.{u} R)
    (d : ℕ∞) (h : depth J M = d) (n : ℕ) :
    (n : ℕ∞) ≤ depth J M ↔ (n : ℕ∞) ≤ d :=
  depth_ge_iff_of_eq_dim J M d h n

theorem VII_1_4_local_CM_depth_iff_supportDim [IsLocalRing R]
    (M : ModuleCat.{u} R) (hCM : IsCohenMacaulayAtMaximalIdeal M) (n : ℕ) :
    ((n : ℕ∞) : WithBot ℕ∞) ≤ depth (IsLocalRing.maximalIdeal R) M ↔
      (n : WithBot ℕ∞) ≤ Module.supportDim R M := by
  rw [← hCM]
  simp

theorem VII_1_4_local_CM_vanishing_iff_supportDim [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hCM : IsCohenMacaulayAtMaximalIdeal M) (n : ℕ) :
    LocalCohomologyVanishesBelow (IsLocalRing.maximalIdeal R) M n ↔
      (n : WithBot ℕ∞) ≤ Module.supportDim R M := by
  rw [VII_1_2_i_iff_depth]
  constructor
  · intro h
    exact (VII_1_4_local_CM_depth_iff_supportDim M hCM n).mp (by exact_mod_cast h)
  · intro h
    exact_mod_cast (VII_1_4_local_CM_depth_iff_supportDim M hCM n).mpr h

theorem VII_1_4_subsingleton_depth_top (J : Ideal R) (M : ModuleCat.{u} R)
    [Subsingleton M] : depth J M = ⊤ :=
  depth_eq_top_of_subsingleton_coeff J M

theorem VII_1_4_depth_lt_top_iff_meets (J : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] :
    depth J M < ⊤ ↔
      (Module.support R M ∩ PrimeSpectrum.zeroLocus (J : Set R)).Nonempty :=
  depth_lt_top_iff_support_meets J M

end SGA.SGA2.ExposeVII
