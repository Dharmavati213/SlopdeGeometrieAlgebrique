/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import SGA.Foundations.Semistable.LinearAlgebra

/-!
# `ℓ`-torsion in the cokernel of an intersection matrix

Let `A` be a symmetric integer matrix with `A m = 0` for an integer vector `m` (e.g. the
intersection matrix of the components of a fibre of a regular arithmetic surface and the vector of
multiplicities). This file bounds the `ℓ`-torsion of `Coker(A) = ℤⁿ / A ℤⁿ`:

* `Matrix.card_torsionBy_cokernel_mul_le`: if `m mod ℓ ≠ 0`, then
  `|Coker(A)[ℓ]| · ℓ ≤ ℓ^{dim_{𝔽_ℓ} ker (A mod ℓ)}`. The proof is a direct injection of
  `Coker(A)[ℓ]` into `ker (A mod ℓ) / 𝔽_ℓ m̄`: a class `x` with `ℓ x = A y` goes to `ȳ`;
* `Matrix.card_torsionBy_cokernel_mul_pow_le` (Stacks, Tag 0C6X): if moreover the graph of `A`
  is connected and the prime `ℓ` divides none of the `mᵢ` and none of the nonzero `aᵢⱼ`, then
  `|Coker(A)[ℓ]| · ℓⁿ ≤ ℓ^{1 + e}`, i.e. `dim_{𝔽_ℓ} Coker(A)[ℓ] ≤ 1 - n + e`, with `e` the number of
  edges (pairs `i < j` with `aᵢⱼ ≠ 0`). The hypothesis `aᵢⱼ ≥ 0` for `i ≠ j` of Stacks is not
  needed.

The proof of 0C6X here is not the Stacks one (orthogonal complements of lattices, Tags 0C6V and
0C6W). It combines the injection above with the field-level bound
`Matrix.finrank_ker_mulVecLin_add_card_le` (`dim ker Ā ≤ 2 - n + e`), proved via the incidence
matrix of the graph.

## References

* [Stacks Project, Tag 0C6X](https://stacks.math.columbia.edu/tag/0C6X)
-/

namespace Matrix

open Module

variable {n : Type*} [Fintype n]

private lemma map_intCast_mulVec {ℓ : ℕ} (A : Matrix n n ℤ) (v : n → ℤ) :
    A.map (Int.castRingHom (ZMod ℓ)) *ᵥ (fun i ↦ (v i : ZMod ℓ)) =
      fun i ↦ ((A *ᵥ v) i : ZMod ℓ) := by
  ext i
  simp [mulVec, dotProduct]

/-- The `ℓ`-torsion of the cokernel of an integer matrix `A` with `A m = 0`, `m mod ℓ ≠ 0`, injects
into `ker (A mod ℓ) / 𝔽_ℓ m̄`; hence `|Coker(A)[ℓ]| · ℓ ≤ ℓ^{dim_{𝔽_ℓ} ker (A mod ℓ)}`. -/
theorem card_torsionBy_cokernel_mul_le (A : Matrix n n ℤ) (m : n → ℤ) (hAm : A *ᵥ m = 0)
    (ℓ : ℕ) [Fact ℓ.Prime] (hm : ∃ i, (m i : ZMod ℓ) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ ((n → ℤ) ⧸ LinearMap.range A.mulVecLin) (ℓ : ℤ)) * ℓ ≤
      ℓ ^ finrank (ZMod ℓ) (LinearMap.ker (A.map (Int.castRingHom (ZMod ℓ))).mulVecLin) := by
  classical
  set K := LinearMap.ker (A.map (Int.castRingHom (ZMod ℓ))).mulVecLin
  let red : (n → ℤ) → (n → ZMod ℓ) := fun v i ↦ (v i : ZMod ℓ)
  have hredK : ∀ v, A *ᵥ v = 0 → red v ∈ K := fun v hv ↦ by
    rw [LinearMap.mem_ker, mulVecLin_apply, map_intCast_mulVec, hv]
    ext
    simp
  have hmK : red m ∈ K := hredK m hAm
  have hm0 : (⟨red m, hmK⟩ : K) ≠ 0 := by
    obtain ⟨i, hi⟩ := hm
    intro h
    exact hi (congrFun (congrArg Subtype.val h) i)
  let W : Submodule (ZMod ℓ) K := Submodule.span (ZMod ℓ) {⟨red m, hmK⟩}
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  -- representatives `x` of the torsion classes and `y` with `A y = ℓ x`
  have hrep : ∀ c : Submodule.torsionBy ℤ ((n → ℤ) ⧸ LinearMap.range A.mulVecLin) (ℓ : ℤ),
      ∃ x y : n → ℤ, Submodule.Quotient.mk x = (c : (n → ℤ) ⧸ LinearMap.range A.mulVecLin) ∧
        A *ᵥ y = (ℓ : ℤ) • x := by
    intro c
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ c.1
    have hc := (Submodule.mem_torsionBy_iff _ _).mp c.2
    rw [← hx, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hc
    obtain ⟨y, hy⟩ := hc
    exact ⟨x, y, hx, hy⟩
  choose x y hxc hy using hrep
  have hyK : ∀ c, red (y c) ∈ K := fun c ↦ by
    rw [LinearMap.mem_ker, mulVecLin_apply, map_intCast_mulVec, hy c]
    ext i
    simp
  let Φ : Submodule.torsionBy ℤ ((n → ℤ) ⧸ LinearMap.range A.mulVecLin) (ℓ : ℤ) → K ⧸ W :=
    fun c ↦ W.mkQ ⟨red (y c), hyK c⟩
  have hΦ : Function.Injective Φ := by
    intro c c' h
    change W.mkQ _ = W.mkQ _ at h
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
      Submodule.mem_span_singleton] at h
    obtain ⟨t, ht⟩ := h
    obtain ⟨τ, rfl⟩ := ZMod.intCast_surjective t
    have hdiv : ∀ i, (ℓ : ℤ) ∣ y c i - y c' i - τ * m i := fun i ↦ by
      have := congrFun (congrArg Subtype.val ht) i
      simp only [Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, red] at this
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [this]
      ring
    choose w hw using hdiv
    have hyw : y c - y c' = (ℓ : ℤ) • w + τ • m := by
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination hw i
    have hxw : x c - x c' = A *ᵥ w := by
      apply smul_right_injective (n → ℤ) hℓ0
      simp only
      rw [smul_sub, ← hy, ← hy, ← mulVec_sub, hyw, mulVec_add, mulVec_smul, mulVec_smul, hAm,
        smul_zero, add_zero]
    apply Subtype.ext
    rw [← hxc, ← hxc, Submodule.Quotient.eq, hxw]
    exact ⟨w, rfl⟩
  have h1 := Nat.card_le_card_of_injective Φ hΦ
  have hK := (Submodule.card_eq_card_quotient_mul_card W)
  have hWcard : Nat.card W = ℓ := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod ℓ), finrank_span_singleton hm0, pow_one,
      Nat.card_zmod]
  have hKcard : Nat.card K = ℓ ^ finrank (ZMod ℓ) K := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod ℓ), Nat.card_zmod]
  rw [hWcard, hKcard] at hK
  calc _ ≤ Nat.card (K ⧸ W) * ℓ := Nat.mul_le_mul_right ℓ h1
    _ = _ := by rw [hK, mul_comm]

/-- Stacks, Tag 0C6X: let `A` be a symmetric integer matrix whose graph (an edge `{i, j}` for
`aᵢⱼ ≠ 0`, `i ≠ j`) is connected, and `m` an integer vector with `A m = 0`. If the prime `ℓ`
divides none of the `mᵢ` and none of the nonzero entries `aᵢⱼ`, then
`|Coker(A)[ℓ]| · ℓⁿ ≤ ℓ^{1 + e}`, i.e. `dim_{𝔽_ℓ} Coker(A)[ℓ] ≤ 1 - n + e`, where `n ≥ 1` is the
size of `A` and `e` the number of edges. (Stacks also assumes `aᵢⱼ ≥ 0` for `i ≠ j` and `mᵢ > 0`;
these are not needed.) -/
theorem card_torsionBy_cokernel_mul_pow_le [LinearOrder n] [Nonempty n] (A : Matrix n n ℤ)
    (hA : A.IsSymm) (m : n → ℤ) (hAm : A *ᵥ m = 0)
    (hconn : ∀ I : Set n, I.Nonempty → I ≠ Set.univ → ∃ i ∈ I, ∃ j ∉ I, A i j ≠ 0)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓm : ∀ i, ¬ (ℓ : ℤ) ∣ m i)
    (hℓA : ∀ i j, A i j ≠ 0 → ¬ (ℓ : ℤ) ∣ A i j) :
    Nat.card (Submodule.torsionBy ℤ ((n → ℤ) ⧸ LinearMap.range A.mulVecLin) (ℓ : ℤ)) *
      ℓ ^ Fintype.card n ≤ ℓ ^ (1 + A.edgeFinset.card) := by
  classical
  set Ā := A.map (Int.castRingHom (ZMod ℓ))
  have hne : ∀ i j, Ā i j ≠ 0 ↔ A i j ≠ 0 := fun i j ↦ by
    simp only [Ā, map_apply, eq_intCast, ne_eq]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨fun h h0 ↦ h (h0 ▸ dvd_zero _), fun h ↦ hℓA i j h⟩
  have hm : ∀ i, (m i : ZMod ℓ) ≠ 0 := fun i ↦ by
    rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hℓm i
  have hĀ : Ā.IsSymm := hA.map _
  have hĀm : Ā *ᵥ (fun i ↦ (m i : ZMod ℓ)) = 0 := by
    rw [map_intCast_mulVec, hAm]
    ext
    simp
  have hĀconn : ∀ I : Set n, I.Nonempty → I ≠ Set.univ → ∃ i ∈ I, ∃ j ∉ I, Ā i j ≠ 0 :=
    fun I hI hI' ↦ by
      obtain ⟨i, hi, j, hj, hij⟩ := hconn I hI hI'
      exact ⟨i, hi, j, hj, (hne i j).mpr hij⟩
  have hedge : Ā.edgeFinset = A.edgeFinset := by
    ext p
    simp only [edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and, hne]
  have hker := finrank_ker_mulVecLin_add_card_le Ā hĀ _ hm hĀm hĀconn
  rw [hedge] at hker
  obtain ⟨i₀⟩ := (inferInstance : Nonempty n)
  have htors := card_torsionBy_cokernel_mul_le A m hAm ℓ ⟨i₀, hm i₀⟩
  have hℓ1 : 1 ≤ ℓ := (Fact.out : ℓ.Prime).one_lt.le
  have hpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have key : Nat.card (Submodule.torsionBy ℤ ((n → ℤ) ⧸ LinearMap.range A.mulVecLin) (ℓ : ℤ)) *
      ℓ ^ Fintype.card n * ℓ ≤ ℓ ^ (1 + A.edgeFinset.card) * ℓ := by
    calc _ = Nat.card (Submodule.torsionBy ℤ ((n → ℤ) ⧸ LinearMap.range A.mulVecLin) (ℓ : ℤ)) *
          ℓ * ℓ ^ Fintype.card n := by ring
      _ ≤ ℓ ^ finrank (ZMod ℓ) (LinearMap.ker Ā.mulVecLin) * ℓ ^ Fintype.card n :=
          Nat.mul_le_mul_right _ htors
      _ = ℓ ^ (finrank (ZMod ℓ) (LinearMap.ker Ā.mulVecLin) + Fintype.card n) := by
          rw [pow_add]
      _ ≤ ℓ ^ (2 + A.edgeFinset.card) := Nat.pow_le_pow_right hpos hker
      _ = ℓ ^ (1 + A.edgeFinset.card) * ℓ := by rw [← pow_succ]; ring_nf
  exact Nat.le_of_mul_le_mul_right key hpos

end Matrix
