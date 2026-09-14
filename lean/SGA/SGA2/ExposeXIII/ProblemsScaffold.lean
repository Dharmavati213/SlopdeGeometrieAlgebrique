/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# SGA 2, XIII: problems and conjectures — dimension scaffolding

Exposé XIII collects open problems. We record the Krull-dimension comparison
for quotients by a surjective ring map, used throughout the conjectural
statements.
-/

universe u

namespace SGA.SGA2.ExposeXIII

variable {R : Type u} [CommRing R]

/-- Krull dimension is monotone for surjective ring maps. -/
theorem ringKrullDim_le_of_surjective {S : Type u} [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    ringKrullDim S ≤ ringKrullDim R :=
  _root_.ringKrullDim_le_of_surjective f hf

/-- The zero ring has Krull dimension `⊥`. -/
theorem ringKrullDim_eq_bot_of_subsingleton [Subsingleton R] :
    ringKrullDim R = ⊥ :=
  _root_.ringKrullDim_eq_bot_of_subsingleton

/-- Nontrivial rings have Krull dimension at least `0`. -/
theorem ringKrullDim_nonneg [Nontrivial R] : 0 ≤ ringKrullDim R :=
  ringKrullDim_nonneg_of_nontrivial

end SGA.SGA2.ExposeXIII
