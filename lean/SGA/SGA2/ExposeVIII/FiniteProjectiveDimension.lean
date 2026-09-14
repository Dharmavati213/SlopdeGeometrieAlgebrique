/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# SGA 2, VIII.1: finite projective dimension inputs

Exposé VIII's biduality spectral sequence is stated for modules of finite
projective dimension. We record the Ext-vanishing consequences of that
hypothesis used to set up VIII.1.2.
-/

noncomputable section

universe u

open CategoryTheory

namespace SGA.SGA2.ExposeVIII

variable {R : Type u} [CommRing R]

/-- Modules of projective dimension `< n` have vanishing Ext in degrees `≥ n`. -/
theorem ext_subsingleton_of_hasProjectiveDimensionLT
    (N M : ModuleCat.{u} R) (n i : ℕ)
    [HasProjectiveDimensionLT N n] (hi : n ≤ i) :
    Subsingleton (Abelian.Ext N M i) :=
  HasProjectiveDimensionLT.subsingleton N n i hi M

/-- If projective dimension is at most `n`, Ext vanishes in degrees strictly above `n`. -/
theorem ext_subsingleton_of_projectiveDimension_le
    (N M : ModuleCat.{u} R) (n i : ℕ)
    (hpd : projectiveDimension N ≤ n) (hi : n < i) :
    Subsingleton (Abelian.Ext N M i) := by
  have : HasProjectiveDimensionLE N n := (projectiveDimension_le_iff N n).mp hpd
  exact HasProjectiveDimensionLT.subsingleton N (n + 1) i (by omega) M

/-- Dual form used in VIII.1.2: Ext into the ring vanishes above the bound. -/
theorem ext_ring_subsingleton_of_hasProjectiveDimensionLT
    (N : ModuleCat.{u} R) (n i : ℕ)
    [HasProjectiveDimensionLT N n] (hi : n ≤ i) :
    Subsingleton (Abelian.Ext N (ModuleCat.of R R) i) :=
  ext_subsingleton_of_hasProjectiveDimensionLT N (ModuleCat.of R R) n i hi

end SGA.SGA2.ExposeVIII
