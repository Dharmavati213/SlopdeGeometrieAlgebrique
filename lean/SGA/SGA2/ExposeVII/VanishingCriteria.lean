/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVII.HomVanishing
import SGA.SGA2.ExposeVII.SupportedExtHomComparison
import SGA.SGA2.ExposeIII.DepthLocalCohomology

/-!
# SGA 2, VII.1.2: equivalent vanishing criteria

Affine avatar of the four equivalent conditions of VII.1.2, identified with
`n ≤ depth J N` via the III.2 / III.3 comparisons.
-/

noncomputable section

universe u

open CategoryTheory Limits
open SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeVII

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- VII.1.2(i): vanishing of algebraic local cohomology below `n`. -/
def LocalCohomologyVanishesBelow (J : Ideal R) (N : ModuleCat.{u} R) (n : ℕ) : Prop :=
  ∀ i < n, IsZero ((_root_.localCohomology J i).obj N)

/-- VII.1.2(iii): Ext vanishing for every finite module supported in `V(J)`. -/
def ExtVanishesOnAllSupported (J : Ideal R) (N : ModuleCat.{u} R) (n : ℕ) : Prop :=
  ExtVanishesBelow J N n

/-- VII.1.2(ii): Ext vanishing for some finite module of full support `V(J)`. -/
def ExtVanishesOnSomeFullSupport (J : Ideal R) (N : ModuleCat.{u} R) (n : ℕ) : Prop :=
  ∃ M : ModuleCat.{u} R, Module.Finite R M ∧
    Module.support R M = PrimeSpectrum.zeroLocus J ∧
      ∀ i < n, Subsingleton (Abelian.Ext M N i)

variable (J : Ideal R) (N : ModuleCat.{u} R) [Module.Finite R N] (n : ℕ)

theorem VII_1_2_i_iff_depth :
    LocalCohomologyVanishesBelow J N n ↔ (n : ℕ∞) ≤ depth J N :=
  (le_depth_iff_localCohomology_vanishes J N n).symm

theorem VII_1_2_iii_iff_depth :
    ExtVanishesOnAllSupported J N n ↔ (n : ℕ∞) ≤ depth J N :=
  (le_depth_iff J N n).symm

theorem VII_1_2_ii_iff_depth :
    ExtVanishesOnSomeFullSupport J N n ↔ (n : ℕ∞) ≤ depth J N :=
  (le_depth_iff_exists_test_module J N n).symm

theorem VII_1_2_equivalent :
    LocalCohomologyVanishesBelow J N n ↔
      ExtVanishesOnSomeFullSupport J N n ∧
        ExtVanishesOnAllSupported J N n := by
  constructor
  · intro h
    have hd : (n : ℕ∞) ≤ depth J N := (VII_1_2_i_iff_depth J N n).mp h
    exact ⟨(VII_1_2_ii_iff_depth J N n).mpr hd, (VII_1_2_iii_iff_depth J N n).mpr hd⟩
  · rintro ⟨hii, _⟩
    exact (VII_1_2_i_iff_depth J N n).mpr ((VII_1_2_ii_iff_depth J N n).mp hii)

theorem VII_1_2_ii_implies_i_via_homVanishing
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hsupp : Module.support R M = PrimeSpectrum.zeroLocus J)
    (hExt : ∀ i < n, Subsingleton (Abelian.Ext M N i))
    (i : ℕ) (hi : i < n) :
    IsZero ((_root_.localCohomology J i).obj N) := by
  have hd : (n : ℕ∞) ≤ depth J N :=
    (le_depth_iff_ext_vanishes J M N hsupp n).mpr hExt
  exact isZero_localCohomology_of_lt_depth J N n hd i hi

/-- After VII.1.2(i), Ext vanishes on every finite supported module below `n`. -/
theorem VII_1_2_degree_n_hom_criterion
    (h : LocalCohomologyVanishesBelow J N n) :
    ExtVanishesOnSupported J N n := by
  intro M' i hi
  have hd := (VII_1_2_i_iff_depth J N n).mp h
  obtain ⟨k, hk⟩ := supportedFinite_exists_pow_annihilator J M'
  exact (le_depth_iff J N n).mp hd M'.obj.obj inferInstance ⟨k, hk⟩ i hi

end SGA.SGA2.ExposeVII
