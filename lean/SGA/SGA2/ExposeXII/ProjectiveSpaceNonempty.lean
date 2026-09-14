/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# SGA 2, XII: polynomial ring inputs for projective schemes

Exposé XII applies Lefschetz theorems to projective algebraic schemes. The
affine cones are spectra of graded polynomial rings; we record basic facts
about polynomial rings used in that setup.
-/

universe u

namespace SGA.SGA2.ExposeXII

variable (R : Type u) [CommRing R]

/-- Polynomial rings over a nontrivial ring are nontrivial. -/
instance polynomial_nontrivial [Nontrivial R] : Nontrivial (Polynomial R) :=
  inferInstance

/-- The constant polynomial embedding is injective. -/
theorem C_injective : Function.Injective (Polynomial.C : R → Polynomial R) :=
  Polynomial.C_injective

/-- Degree of a nonzero constant equals zero. -/
theorem degree_C_ne_zero {a : R} (ha : a ≠ 0) :
    (Polynomial.C a).degree = 0 :=
  Polynomial.degree_C ha

end SGA.SGA2.ExposeXII
