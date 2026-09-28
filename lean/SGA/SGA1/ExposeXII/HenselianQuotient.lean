/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Quotients of henselian local rings

A nontrivial quotient of a henselian local ring is henselian
(`SGA.SGA1.ExposeXII.henselianLocalRing_of_surjective`); used for the local rings of analytic
spaces, quotients of rings of convergent power series (XII.2.1).
-/

open Polynomial IsLocalRing

namespace SGA.SGA1.ExposeXII

variable {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
  (f : R →+* S) (hf : Function.Surjective f)
include hf

/-- For a surjective ring homomorphism `f` from a local ring to a nontrivial ring, `x` is a unit
as soon as `f x` is. -/
lemma isUnit_of_isUnit_map_of_surjective [IsLocalRing R] {x : R} (hx : IsUnit (f x)) :
    IsUnit x := by
  obtain ⟨y, hy⟩ := hf ↑(hx.unit⁻¹)
  have h1 : f (x * y) = 1 := by rw [map_mul, hy]; exact hx.mul_val_inv
  rcases isUnit_or_isUnit_one_sub_self (x * y) with h | h
  · exact isUnit_of_mul_isUnit_left h
  · have : f (1 - x * y) = 0 := by rw [map_sub, map_one, h1, sub_self]
    exact absurd (h.map f) (by rw [this]; exact not_isUnit_zero)

/-- A nontrivial quotient of a henselian local ring is henselian. -/
theorem henselianLocalRing_of_surjective [HenselianLocalRing R] : HenselianLocalRing S where
  toIsLocalRing := .of_surjective' f hf
  is_henselian g hg b₀ hb₀ hu := by
    have : IsLocalRing S := .of_surjective' f hf
    have hmem (x : R) : f x ∈ maximalIdeal S ↔ x ∈ maximalIdeal R := by
      simp only [mem_maximalIdeal, mem_nonunits_iff]
      exact ⟨fun h h' ↦ h (h'.map f), fun h h' ↦ h (isUnit_of_isUnit_map_of_surjective f hf h')⟩
    obtain ⟨G, hG, -, hGm⟩ := lifts_and_natDegree_eq_and_monic
      ((lifts_iff_set_range g).mpr (map_surjective f hf g)) hg
    obtain ⟨a₀, rfl⟩ := hf b₀
    have heval (x : R) : g.eval (f x) = f (G.eval x) := by
      rw [← hG, eval_map, eval₂_hom]
    have hderiv (x : R) : g.derivative.eval (f x) = f (G.derivative.eval x) := by
      rw [← hG, derivative_map, eval_map, eval₂_hom]
    obtain ⟨a, ha, haa₀⟩ := HenselianLocalRing.is_henselian G hGm a₀
      ((hmem _).mp (heval a₀ ▸ hb₀))
      (isUnit_of_isUnit_map_of_surjective f hf (hderiv a₀ ▸ hu))
    refine ⟨f a, ?_, ?_⟩
    · rw [IsRoot, heval, ha.eq_zero, map_zero]
    · rw [← map_sub]
      exact (hmem _).mpr haa₀

end SGA.SGA1.ExposeXII
