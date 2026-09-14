/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Ideal.Height
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.KrullDimension

/-!
# SGA 2, VII.2.2: the dimension set of a connected locus is an interval

Affine avatar of VII.2.2: on `Spec R`, `dim O_{X,p} = height(p)`. Height
intervals and unions of meeting order-connected sets remain order-connected.
-/

noncomputable section

universe u

open Set Order

namespace SGA.SGA2.ExposeVII

variable {R : Type u} [CommRing R]

/-- VII.2.2's dimension set: heights of primes in `P`. -/
def dimensionSet (P : Set (PrimeSpectrum R)) : Set ℕ∞ :=
  { h | ∃ p ∈ P, (p.asIdeal.height : ℕ∞) = h }

theorem mem_dimensionSet {P : Set (PrimeSpectrum R)} {h : ℕ∞} :
    h ∈ dimensionSet P ↔ ∃ p ∈ P, (p.asIdeal.height : ℕ∞) = h :=
  Iff.rfl

/-- Along a strict chain, height grows by at least one at each step. -/
theorem height_add_one_le_of_ltSeries_step (l : LTSeries (PrimeSpectrum R))
    (i : Fin l.length) :
    (l.toFun i.castSucc).asIdeal.height + 1 ≤
      (l.toFun i.succ).asIdeal.height := by
  have hlt : l.toFun i.castSucc < l.toFun i.succ :=
    l.strictMono i.castSucc_lt_succ
  exact Ideal.height_add_one_le_of_lt_of_isPrime hlt

theorem exists_ltSeries_of_height (p : Ideal R) [p.IsPrime] [p.FiniteHeight] :
    ∃ l : LTSeries (PrimeSpectrum R),
      l.last = ⟨p, ‹_›⟩ ∧ l.length = p.height := by
  obtain ⟨l, last, len⟩ := Ideal.exists_ltSeries_length_eq_height p
  exact ⟨l, last, by simpa using len⟩

theorem dimensionSet_below_prime_ordConnected (p : Ideal R)
    [p.IsPrime] [p.FiniteHeight] :
    OrdConnected (Set.Icc (0 : ℕ∞) p.height) :=
  inferInstance

theorem height_Icc_ordConnected (p q : PrimeSpectrum R)
    (_hpq : p ≤ q) [p.asIdeal.FiniteHeight] [q.asIdeal.FiniteHeight] :
    OrdConnected (Set.Icc (p.asIdeal.height : ℕ∞) q.asIdeal.height) :=
  inferInstance

theorem dim_eq_height (p : Ideal R) [p.IsPrime] :
    ringKrullDim (Localization.AtPrime p) = p.height :=
  IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)

/-- Union of two meeting order-connected sets is order-connected. -/
theorem dimensionSet_union_ordConnected
    {A B : Set ℕ∞} (hA : OrdConnected A) (hB : OrdConnected B)
    (hmeet : (A ∩ B).Nonempty) : OrdConnected (A ∪ B) := by
  rw [ordConnected_iff]
  intro x hx y hy _hxy z hz
  rcases hx with hxA | hxB
  · rcases hy with hyA | hyB
    · exact Or.inl (hA.out hxA hyA hz)
    · obtain ⟨w, hwA, hwB⟩ := hmeet
      cases le_total z w with
      | inl hzw => exact Or.inl (hA.out hxA hwA ⟨hz.1, hzw⟩)
      | inr hwz => exact Or.inr (hB.out hwB hyB ⟨hwz, hz.2⟩)
  · rcases hy with hyA | hyB
    · obtain ⟨w, hwA, hwB⟩ := hmeet
      cases le_total z w with
      | inl hzw => exact Or.inr (hB.out hxB hwB ⟨hz.1, hzw⟩)
      | inr hwz => exact Or.inl (hA.out hwA hyA ⟨hwz, hz.2⟩)
    · exact Or.inr (hB.out hxB hyB hz)

theorem dimensionSet_singleton (p : PrimeSpectrum R) :
    dimensionSet {p} = {(p.asIdeal.height : ℕ∞)} := by
  ext h
  simp [dimensionSet]

theorem not_mem_Icc {a b : ℕ∞} {n : ℕ∞} (_hab : a ≤ b) (hn : n ∉ Set.Icc a b) :
    n < a ∨ b < n := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hn
  exact hn

end SGA.SGA2.ExposeVII
