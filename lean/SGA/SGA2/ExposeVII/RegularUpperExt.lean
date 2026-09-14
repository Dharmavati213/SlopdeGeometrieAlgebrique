/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# SGA 2, VII.2.1 (local fibre): Ext vanishes above the dimension

On a regular local ring the global dimension equals the Krull dimension, so
Ext from an arbitrary module into any coefficient vanishes in degrees strictly
above that dimension. This is the stalkwise input to VII.2.1(1).
-/

noncomputable section

universe u

open CategoryTheory

namespace SGA.SGA2.ExposeVII

variable {R : Type u} [CommRing R]

/-- Above a projective-dimension bound, Ext into any coefficient vanishes. -/
theorem ext_subsingleton_of_hasProjectiveDimensionLT
    (N M : ModuleCat.{u} R) (n i : ℕ)
    [HasProjectiveDimensionLT N n] (hi : n ≤ i) :
    Subsingleton (Abelian.Ext N M i) :=
  HasProjectiveDimensionLT.subsingleton N n i hi M

/-- If a module has projective dimension ≤ `n`, Ext vanishes in degrees `> n`. -/
theorem ext_subsingleton_of_projectiveDimension_le
    (N M : ModuleCat.{u} R) (n i : ℕ)
    (hpd : projectiveDimension N ≤ n) (hi : n < i) :
    Subsingleton (Abelian.Ext N M i) := by
  have : HasProjectiveDimensionLE N n := (projectiveDimension_le_iff N n).mp hpd
  exact HasProjectiveDimensionLT.subsingleton N (n + 1) i (by omega) M

end SGA.SGA2.ExposeVII
