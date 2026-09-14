/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Group.Units.Basic

/-!
# SGA 2, XI: units as the degree-zero Picard input

Exposé XI studies the Picard group via Lefschetz-type theorems. The
degree-zero comparison begins with the group of units of a ring.
-/

universe u

namespace SGA.SGA2.ExposeXI

variable {R : Type u} [CommRing R]

/-- Units form a commutative group (mathlib). -/
theorem units_comm : ∀ u v : Rˣ, u * v = v * u := mul_comm

/-- Invertible elements are nonzero in a nontrivial ring. -/
theorem units_ne_zero [Nontrivial R] (u : Rˣ) : (u : R) ≠ 0 :=
  Units.ne_zero u

/-- The unit group map induced by a ring homomorphism. -/
def mapUnits {S : Type u} [CommRing S] (f : R →+* S) : Rˣ →* Sˣ :=
  Units.map f

theorem mapUnits_apply {S : Type u} [CommRing S] (f : R →+* S) (u : Rˣ) :
    (mapUnits f u : S) = f u :=
  rfl

end SGA.SGA2.ExposeXI
