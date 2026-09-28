/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.DepthLocalCohomology
import SGA.SGA2.ExposeIII.DepthLocalization
import SGA.SGA2.ExposeII.AffineCohomologyComparison

/-!
# Depth and actual supported cohomology on affine schemes

The algebraic depth criterion and the proved affine comparison give the
group-valued affine bridge for III.§3: depth bounds are exactly vanishing of
the actual supported sheaf cohomology of the associated sheaf. They can also
be tested by depths of localized modules or by Ext from a finite module with
the prescribed support.

This is not a sheaf-Ext comparison or a descent theorem for general schemes.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIII

variable {R : CommRingCat.{u}} [IsNoetherianRing R]

set_option backward.isDefEq.respectTransparency false

/-- The actual affine comparison identifies vanishing of algebraic local
cohomology and the original Ext-defined supported sheaf cohomology. -/
theorem subsingleton_localCohomology_iff_affine_H_Z
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    Subsingleton ((_root_.localCohomology I n).obj M) ↔
      Subsingleton (ExposeI.H_Z (affineSupportClosed I) (affineTildeAbSheaf M) n) :=
  (affineLocalCohomologyIso I M n).addCommGroupIsoToAddEquiv.subsingleton_congr

/-- **III.§3, affine depth criterion:** depth is bounded below by `n`
exactly when actual supported sheaf cohomology vanishes below `n`. -/
theorem le_depth_iff_affine_H_Z_vanishes (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔
      ∀ i < n, Subsingleton
        (ExposeI.H_Z (affineSupportClosed I) (affineTildeAbSheaf M) i) := by
  simp_rw [← subsingleton_localCohomology_iff_affine_H_Z]
  exact le_depth_iff_subsingleton_localCohomology I M n

/-- Depth is the first nonzero actual supported sheaf-cohomology degree,
including the case of infinite depth. -/
theorem depth_eq_iInf_affine_H_Z (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth I M = ⨅ (i : ℕ)
      (_ : ¬ Subsingleton (ExposeI.H_Z (affineSupportClosed I) (affineTildeAbSheaf M) i)),
        (i : ℕ∞) := by
  simp_rw [← subsingleton_localCohomology_iff_affine_H_Z,
    ← ModuleCat.isZero_iff_subsingleton]
  exact depth_eq_iInf_localCohomology I M

/-- **III.3.3, affine group-valued bridge:** supported cohomological vanishing
is equivalent to the depth bound on all localized modules along `V(I)`. -/
theorem affine_H_Z_vanishes_iff_localDepth (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (∀ i < n, Subsingleton
      (ExposeI.H_Z (affineSupportClosed I) (affineTildeAbSheaf M) i)) ↔
    ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      (n : ℕ∞) ≤ localDepth M p :=
  (le_depth_iff_affine_H_Z_vanishes I M n).symm.trans
    (le_depth_iff_forall_localDepth I M n)

/-- A finite module supported exactly on `V(I)` tests the vanishing of
actual affine supported sheaf cohomology. -/
theorem affine_H_Z_vanishes_iff_testModule_ext (I : Ideal R)
    (N M : ModuleCat.{u} R) [Module.Finite R N] [Module.Finite R M]
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) (n : ℕ) :
    (∀ i < n, Subsingleton
      (ExposeI.H_Z (affineSupportClosed I) (affineTildeAbSheaf M) i)) ↔
    ∀ i < n, Subsingleton (Abelian.Ext N M i) :=
  (le_depth_iff_affine_H_Z_vanishes I M n).symm.trans
    (le_depth_iff_ext_vanishes I N M hsupp n)

/-- The quotient `R/I` is a test module for the actual supported cohomology. -/
theorem affine_H_Z_vanishes_iff_quotient_ext (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (∀ i < n, Subsingleton
      (ExposeI.H_Z (affineSupportClosed I) (affineTildeAbSheaf M) i)) ↔
    ∀ i < n, Subsingleton (Abelian.Ext (ModuleCat.of R (R ⧸ I)) M i) :=
  affine_H_Z_vanishes_iff_testModule_ext I (ModuleCat.of R (R ⧸ I)) M
    (by simp [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]) n

end SGA.SGA2.ExposeIII
