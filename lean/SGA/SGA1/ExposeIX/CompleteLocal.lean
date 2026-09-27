/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.Algebra
import SGA.Foundations.HenselianFiniteEtale

/-!
# SGA 1, Exposé IX, 1.8: finite étale algebras over a complete local ring

IX.1.8: for a complete noetherian local ring `A` with residue field `k`, `B ↦ B ⊗_A k` is an
equivalence from finite étale `A`-algebras to finite étale `k`-algebras. A complete local ring is
henselian, and the equivalence holds over any henselian local ring
(`HenselianLocalRing.isEquivalence_baseChange_residueField`, Stacks 04GG); in particular the
noetherian hypothesis is not needed.
-/

universe u

open IsLocalRing

namespace SGA.SGA1.ExposeIX

/-- A local ring which is complete for its maximal ideal is henselian. -/
theorem henselianLocalRing_of_isAdicComplete (A : Type*) [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] : HenselianLocalRing A where
  is_henselian f hf a₀ h₁ h₂ := HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

/-- IX.1.8: for a complete local ring `A` with residue field `k`, `B ↦ B ⊗_A k` is an
equivalence between finite étale `A`-algebras and finite étale `k`-algebras (i.e. finite
products of finite separable extensions of `k`). SGA assumes `A` noetherian; this is not
needed. -/
theorem isEquivalence_baseChange_residueField_of_isAdicComplete (A : Type u) [CommRing A]
    [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] :
    (CommAlgCat.FiniteEtale.baseChange.{u, u} A (ResidueField A)).IsEquivalence :=
  have := henselianLocalRing_of_isAdicComplete A
  inferInstance

end SGA.SGA1.ExposeIX
