/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.IntegerCycleSequences

/-!
# Supported sections of acyclic bounded-below flasque complexes

Starting below the complex, exact cycle sequences show that every cycle sheaf
is flasque. Supported sections consequently preserve exactness in every degree.
The lower bound is explicit and arbitrary, so this applies to mapping cones.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex TopologicalSpace TopCat

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- A zero sheaf is flasque. -/
theorem isFlasque_of_isZero (F : Sheaf AddCommGrpCat.{u} X) (h : IsZero F) : IsFlasque F := by
  have : Injective F := h.injective
  exact isFlasque_of_injective F

/-- All cycles of a bounded-below acyclic complex of flasque sheaves are flasque. -/
theorem acyclicFlasqueComplex_cycles_isFlasque
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
    (hK : K.Acyclic) (d : ℤ) (hd : ∀ n < d, IsZero (K.X n))
    [∀ n, IsFlasque (K.X n)] (n : ℤ) : IsFlasque (K.cycles n) := by
  by_cases hn : d - 1 ≤ n
  · induction n, hn using Int.leInduction with
    | base =>
      exact isFlasque_of_isZero _ (cycles_isZero_of_term_isZero K (d - 1) (hd _ (by omega)))
    | succ n hn ih =>
      have : IsFlasque (integerCochainCyclesSequence K n).X₁ := ih
      have : IsFlasque (integerCochainCyclesSequence K n).X₂ := inferInstanceAs
        (IsFlasque (K.X n))
      exact Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (integerCochainCyclesSequence_shortExact K n (hK (n + 1)))
  · exact isFlasque_of_isZero _ (cycles_isZero_of_term_isZero K n (hd _ (by omega)))

/-- Actual supported sections take an acyclic bounded-below complex of flasque
sheaves to an acyclic complex of groups, on every open and for every closed support. -/
theorem gammaZSections_acyclic_of_boundedBelow_flasque
    (Z : Closeds X) (U : Opens X) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
    (hK : K.Acyclic) (d : ℤ) (hd : ∀ n < d, IsZero (K.X n))
    [∀ n, IsFlasque (K.X n)] :
    (((gammaZSectionsFunctor Z U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  suffices h : ∀ n : ℤ,
      (((gammaZSectionsFunctor Z U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt
        (n + 1) by
    intro n
    convert h (n - 1) using 1
    omega
  intro n
  have : IsFlasque (integerCochainCyclesSequence K n).X₁ :=
    acyclicFlasqueComplex_cycles_isFlasque K hK d hd n
  have hseq := gammaZSectionsFunctor_map_shortExact
    (integerCochainCyclesSequence_shortExact K n (hK _)) Z U
  have : Epi ((gammaZSectionsFunctor Z U).map (K.toCycles n (n + 1))) := hseq.epi_g
  exact map_integerCochain_exactAt_of_cycle_surjective (gammaZSectionsFunctor Z U) K n

end SGA.SGA2.ExposeI
