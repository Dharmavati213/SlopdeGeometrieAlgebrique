/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Integer-indexed exact cohomological functors

The data of an exact delta functor consists of additive functors in every
integer degree and natural connecting maps giving long exact sequences.
No vanishing, left exactness, or representing object is included in the
data. Vanishing in one degree implies left exactness in the next degree.
-/

noncomputable section

universe u v u' v'

open CategoryTheory Limits

namespace SGA.SGA2.ExposeIV

variable (C : Type u) [Category.{v} C] [Abelian C]
  (D : Type u') [Category.{v'} D] [Abelian D]

/-- An integer-indexed exact delta functor. Contravariant delta functors
are obtained by using an opposite category as the source. -/
structure IntegerCohomologicalSequence where
  obj : ℤ → C ⥤ D
  additive (n : ℤ) : (obj n).Additive
  δ (S : ShortComplex C) (hS : S.ShortExact) (n : ℤ) :
    (obj n).obj S.X₃ ⟶ (obj (n + 1)).obj S.X₁
  map_δ (S : ShortComplex C) (hS : S.ShortExact) (n : ℤ) :
    (obj n).map S.g ≫ δ S hS n = 0
  δ_map (S : ShortComplex C) (hS : S.ShortExact) (n : ℤ) :
    δ S hS n ≫ (obj (n + 1)).map S.f = 0
  exact_left (S : ShortComplex C) (hS : S.ShortExact) (n : ℤ) :
    (ShortComplex.mk ((obj n).map S.g) (δ S hS n) (map_δ S hS n)).Exact
  exact_middle (S : ShortComplex C) (hS : S.ShortExact) (n : ℤ) :
    letI := additive n
    (S.map (obj n)).Exact
  exact_right (S : ShortComplex C) (hS : S.ShortExact) (n : ℤ) :
    (ShortComplex.mk (δ S hS n) ((obj (n + 1)).map S.f) (δ_map S hS n)).Exact
  naturality {S S' : ShortComplex C} (f : S ⟶ S')
    (hS : S.ShortExact) (hS' : S'.ShortExact) (n : ℤ) :
    δ S hS n ≫ (obj (n + 1)).map f.τ₁ = (obj n).map f.τ₃ ≫ δ S' hS' n

attribute [instance] IntegerCohomologicalSequence.additive

namespace IntegerCohomologicalSequence

variable {C D} (T : IntegerCohomologicalSequence C D)

/-- Vanishing of the preceding functor forces left exactness; it is
derived from the original connecting maps and exactness, not assumed. -/
theorem preservesFiniteLimits_succ_of_isZero (n : ℤ) (h : IsZero (T.obj n)) :
    PreservesFiniteLimits (T.obj (n + 1)) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr
  intro S hS
  refine ⟨T.exact_middle S hS (n + 1), ?_⟩
  exact (ShortComplex.exact_iff_mono _ ((h.obj S.X₃).eq_of_src _ _)).mp
    (T.exact_right S hS n)

/-- The predecessor-indexed form used in bounded-below induction. -/
theorem preservesFiniteLimits_of_isZero_pred (n : ℤ) (h : IsZero (T.obj (n - 1))) :
    PreservesFiniteLimits (T.obj n) := by
  simpa using T.preservesFiniteLimits_succ_of_isZero (n - 1) h

end IntegerCohomologicalSequence

end SGA.SGA2.ExposeIV
