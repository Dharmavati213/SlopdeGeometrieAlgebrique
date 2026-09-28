/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.Noetherian.Basic

/-!
# SGA 2, Exposé II, Lemma 11: noetherian homology modules

Homology in degree `i` is a quotient of the cycles, which embed in the
degree-`i` term. Thus noetherianness of this one term suffices for
noetherianness of its homology. This supplies the coefficient hypothesis
for the principal-annihilator argument inside the induction in II.11.
-/

universe u v

open CategoryTheory

namespace SGA.SGA2.ExposeII

variable {R : Type u} [Ring R] {ι : Type v} {c : ComplexShape ι}

/-- Cycles in a noetherian term are noetherian. -/
theorem isNoetherian_cycles (K : HomologicalComplex (ModuleCat.{u} R) c) (i : ι)
    [IsNoetherian R (K.X i)] : IsNoetherian R (K.cycles i) :=
  isNoetherian_of_injective (K.iCycles i).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- II.11: homology of a noetherian term is noetherian. -/
theorem isNoetherian_homology (K : HomologicalComplex (ModuleCat.{u} R) c) (i : ι)
    [IsNoetherian R (K.X i)] : IsNoetherian R (K.homology i) := by
  have := isNoetherian_cycles K i
  exact isNoetherian_of_surjective (K.homologyπ i).hom
    (LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp inferInstance))

end SGA.SGA2.ExposeII
