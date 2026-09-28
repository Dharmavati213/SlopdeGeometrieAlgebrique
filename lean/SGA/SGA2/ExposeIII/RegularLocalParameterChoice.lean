/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.RegularLocalParameters
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Choosing an actual first parameter

Finite prime avoidance supplies an element of the maximal ideal outside its
square and all minimal primes in positive dimension. Extending its nonzero
cotangent class to a basis and lifting that basis gives an actual minimal
generating set containing the specified original element.
-/

noncomputable section
universe u
open IsLocalRing Module

namespace SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- In positive dimension, finite prime avoidance produces an element
outside both the square of the maximal ideal and every minimal prime. -/
theorem local_exists_parameter_avoiding_minimalPrimes (hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧
      ∀ p ∈ minimalPrimes R, x ∉ p := by
  have hmnot : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2 := by
    intro h
    have hm0 : maximalIdeal R = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
        (maximalIdeal R).fg_of_isNoetherianRing
        (by simpa only [Ideal.smul_eq_mul, ← pow_two] using h)
        (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
    exact (ne_of_gt hdim) (ringKrullDim_eq_zero_of_isField
      (isField_iff_maximalIdeal_eq.mpr hm0))
  have hpnot : ∀ p ∈ minimalPrimes R, ¬ maximalIdeal R ≤ p := by
    intro p hp hle
    have heq : p = maximalIdeal R := (le_maximalIdeal hp.isPrime.ne_top).antisymm hle
    subst p
    have hzero := Ideal.height_eq_zero_iff.mpr hp
    have hd0 : ringKrullDim R = 0 := by
      rw [← maximalIdeal_height_eq_ringKrullDim, hzero]
      rfl
    exact (ne_of_gt hdim) hd0
  let S : Set (Ideal R) := insert (maximalIdeal R ^ 2) (minimalPrimes R)
  have hS : S.Finite := (minimalPrimes.finite_of_isNoetherianRing R).insert _
  have hnsub : ¬ (maximalIdeal R : Set R) ⊆ ⋃ p ∈ S, (p : Set R) := by
    intro hsub
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime_finite hS
      (f := id) (maximalIdeal R ^ 2) (maximalIdeal R ^ 2)
      (fun p hp hne _ ↦ ((Set.mem_insert_iff.mp hp).resolve_left hne).isPrime)).mp hsub
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact hmnot hmp
    · exact hpnot p hp hmp
  obtain ⟨x, hx, havoid⟩ := Set.not_subset.mp hnsub
  refine ⟨x, hx, ?_, ?_⟩
  · intro hx2
    exact havoid (Set.mem_iUnion₂_of_mem (Set.mem_insert _ _) hx2)
  · intro p hp hxp
    exact havoid (Set.mem_iUnion₂_of_mem (Set.mem_insert_of_mem _ hp) hxp)

/-- Extend the specified nonzero cotangent class to a basis and lift it,
keeping the original element as one of the actual minimal generators. -/
theorem local_exists_minimal_generators_containing (x : R)
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ s : Finset R, x ∈ s ∧ Ideal.span (s : Set R) = maximalIdeal R ∧
      s.card = (maximalIdeal R).spanFinrank := by
  classical
  let v : CotangentSpace R := (maximalIdeal R).toCotangent ⟨x, hx⟩
  have hv : v ≠ 0 := fun h ↦ hx2 ((Ideal.toCotangent_eq_zero _ _).mp h)
  have hlin : LinearIndepOn (ResidueField R) id ({v} : Set (CotangentSpace R)) :=
    (linearIndepOn_singleton_iff (ResidueField R)).mpr hv
  let B : Set (CotangentSpace R) := hlin.extend (Set.subset_univ {v})
  let b : Basis B (ResidueField R) (CotangentSpace R) := Basis.extend hlin
  let : Finite B := b.linearIndependent.finite
  let : Fintype B := Fintype.ofFinite B
  let g : B → maximalIdeal R := fun i ↦
    if hi : i.val = v then ⟨x, hx⟩ else
      ((maximalIdeal R).toCotangent_surjective i.val).choose
  have hg (i : B) : (maximalIdeal R).toCotangent (g i) = i.val := by
    dsimp only [g]
    split_ifs with hi
    · exact hi.symm
    · exact ((maximalIdeal R).toCotangent_surjective i.val).choose_spec
  let gR : B → R := fun i ↦ (g i).val
  have hginj : Function.Injective gR := by
    intro i j hij
    apply Subtype.ext
    rw [← hg i, ← hg j]
    congr 1
    exact Subtype.ext hij
  let s : Finset R := Finset.univ.image gR
  have hs_set : (s : Set R) = Set.range gR := by
    ext y
    simp [s]
  have hspan_g : Submodule.span R (Set.range g) = ⊤ := by
    apply CotangentSpace.span_image_eq_top_iff.mp
    rw [← Set.range_comp]
    have heq : (maximalIdeal R).toCotangent ∘ g = b := by
      funext i
      exact (hg i).trans (Basis.extend_apply_self hlin i).symm
    rw [heq]
    exact b.span_eq
  have hs_span : Ideal.span (s : Set R) = maximalIdeal R := by
    rw [hs_set]
    change Submodule.span R (Set.range gR) = maximalIdeal R
    have hh := congrArg (Submodule.map (maximalIdeal R).subtype) hspan_g
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hh
    rw [← Set.range_comp] at hh
    have heq : ((maximalIdeal R).subtype : maximalIdeal R → R) ∘ g = gR := by
      funext i
      rfl
    rw [heq] at hh
    exact hh
  have hvB : v ∈ B := hlin.subset_extend _ (Set.mem_singleton v)
  let i₀ : B := ⟨v, hvB⟩
  have hg₀ : gR i₀ = x := by simp [gR, g, i₀]
  refine ⟨s, ?_, hs_span, ?_⟩
  · change x ∈ (s : Set R)
    rw [hs_set]
    exact ⟨i₀, hg₀⟩
  · calc
      s.card = Fintype.card B := by
        rw [Finset.card_image_of_injective _ hginj, Finset.card_univ]
      _ = Module.finrank (ResidueField R) (CotangentSpace R) :=
        (Module.finrank_eq_card_basis b).symm
      _ = (maximalIdeal R).spanFinrank :=
        (spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)).symm

end SGA.SGA2.ExposeIII
