/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.IntegerCohomologicalSequence
import SGA.SGA2.ExposeIV.SupportedFunctorVanishing
import Mathlib.Data.Int.Init

/-!
# SGA 2, IV.1.4: bounded-below supported delta-functor vanishing

For an actual integer-indexed exact delta functor on finite supported
modules, the three original lower-vanishing conditions are equivalent.
The proof derives left exactness at the first potentially nonzero degree
from the connecting sequence, then applies the canonical colimit
representation and the finite full-support Hom detection theorem.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (J : Ideal R)
variable (T : IntegerCohomologicalSequence (SupportedFGModuleCat J)ᵒᵖ AddCommGrpCat.{u})

/-- Integer induction propagates a degreewise vanishing detector from the
given lower bound. This logical lemma imposes no extra condition on the
cohomological functor in the final theorem. -/
private theorem vanishesBelow_of_step (P : ℤ → Prop)
    (hstep : ∀ i : ℤ, IsZero (T.obj (i - 1)) → P i → IsZero (T.obj i))
    (i₀ : ℤ) (h₀ : ∀ i : ℤ, i < i₀ → IsZero (T.obj i))
    (n : ℤ) (hP : ∀ i : ℤ, i < n → P i) :
    ∀ i : ℤ, i < n → IsZero (T.obj i) := by
  by_cases hn : n ≤ i₀
  · exact fun i hi ↦ h₀ i (lt_of_lt_of_le hi hn)
  have hbound : i₀ ≤ n := by omega
  suffices ∀ (k : ℤ), i₀ ≤ k →
      (∀ i : ℤ, i < k → P i) → ∀ i : ℤ, i < k → IsZero (T.obj i) from
    this n hbound hP
  intro k hk
  induction k, hk using Int.leInduction with
  | base => exact fun _ ↦ h₀
  | succ k hk ih =>
    intro hp i hi
    have hprev := ih (fun j hj ↦ hp j (by omega))
    by_cases hik : i < k
    · exact hprev i hik
    · have heq : i = k := by omega
      subst i
      exact hstep k (hprev (k - 1) (by omega)) (hp k (by omega))

/-- Lower vanishing of the actual colimit modules detects lower vanishing
of the original delta functor. -/
theorem supportedDelta_vanishes_of_colimit
    (hbounded : ∃ i₀ : ℤ, ∀ i : ℤ, i < i₀ → IsZero (T.obj i))
    (n : ℤ) (h : ∀ i : ℤ, i < n → IsZero (supportedFunctorColimit J (T.obj i))) :
    ∀ i : ℤ, i < n → IsZero (T.obj i) := by
  obtain ⟨i₀, h₀⟩ := hbounded
  apply vanishesBelow_of_step J T
    (fun i ↦ IsZero (supportedFunctorColimit J (T.obj i))) ?_ i₀ h₀ n h
  intro i hprev hi
  have := T.preservesFiniteLimits_of_isZero_pred i hprev
  exact supportedFunctor_isZero_of_colimit J (T.obj i) hi

/-- One actual finite module of full support detects lower vanishing of
the entire bounded-below delta functor. -/
theorem supportedDelta_vanishes_of_fullSupport
    (hbounded : ∃ i₀ : ℤ, ∀ i : ℤ, i < i₀ → IsZero (T.obj i))
    (M : SupportedFGModuleCat J)
    (hM : Module.support R M.obj = PrimeSpectrum.zeroLocus (J : Set R))
    (n : ℤ) (h : ∀ i : ℤ, i < n → IsZero ((T.obj i).obj (op M))) :
    ∀ i : ℤ, i < n → IsZero (T.obj i) := by
  obtain ⟨i₀, h₀⟩ := hbounded
  apply vanishesBelow_of_step J T (fun i ↦ IsZero ((T.obj i).obj (op M))) ?_ i₀ h₀ n h
  intro i hprev hi
  have := T.preservesFiniteLimits_of_isZero_pred i hprev
  exact (supportedFunctor_isZero_iff_at J (T.obj i) M hM).mpr hi

/-- **IV.1.4:** all three original conditions for an integer threshold and
an arbitrary bounded-below exact delta functor. The colimits and support
condition are the actual ones; no degreewise left exactness is assumed. -/
theorem supportedDeltaFunctor_vanishing_tfae
    (hbounded : ∃ i₀ : ℤ, ∀ i : ℤ, i < i₀ → IsZero (T.obj i)) (n : ℤ) :
    List.TFAE [
      ∀ i : ℤ, i < n → IsZero (T.obj i),
      ∀ i : ℤ, i < n → IsZero (supportedFunctorColimit J (T.obj i)),
      ∃ M : SupportedFGModuleCat J,
        Module.support R M.obj = PrimeSpectrum.zeroLocus (J : Set R) ∧
          ∀ i : ℤ, i < n → IsZero ((T.obj i).obj (op M))] := by
  tfae_have 1 → 2
  | h, i, hi => supportedFunctorColimit_isZero_of_isZero J (T.obj i) (h i hi)
  tfae_have 2 → 1 := supportedDelta_vanishes_of_colimit J T hbounded n
  tfae_have 1 → 3
  | h => ⟨supportedRingQuotient J 1, supportedRingQuotient_one_support J,
      fun i hi ↦ (h i hi).obj _⟩
  tfae_have 3 → 1
  | ⟨M, hM, h⟩ => supportedDelta_vanishes_of_fullSupport J T hbounded M hM n h
  tfae_finish

end SGA.SGA2.ExposeIV
