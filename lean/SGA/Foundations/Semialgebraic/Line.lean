/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Semialgebraic.TarskiSeidenberg

/-!
# Semialgebraic sets meet lines in finitely many points and intervals

A semialgebraic set `S ⊆ ℝ^ι` meets every affine line `t ↦ x + t • v` in a finite union of points
and open intervals: there is a finite set `Z ⊆ ℝ` such that membership of `x + t • v` in `S` is
constant on every interval `[t, t']` avoiding `Z` (`IsSemialgebraic.exists_finset_mem_iff_line`).
Indeed `S` is a union of sign classes of finitely many polynomials, whose restrictions to the line
are polynomials in `t`; take for `Z` their roots. In particular, just to the right of any point
`a`, the line is either inside or outside `S` (`IsSemialgebraic.exists_pos_line`). For `ι` a
singleton this is the structure of semialgebraic subsets of `ℝ`.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Proposition 2.1.7][BCR]
-/

open Set MvPolynomial

variable {ι : Type*}

namespace MvPolynomial

/-- The restriction of `p` to the affine line `t ↦ x + t • v`, a polynomial in `t`. -/
noncomputable def restrictLine (x v : ι → ℝ) (p : MvPolynomial ι ℝ) : Polynomial ℝ :=
  aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) p

@[simp]
lemma eval_restrictLine (x v : ι → ℝ) (p : MvPolynomial ι ℝ) (t : ℝ) :
    (restrictLine x v p).eval t = eval (x + t • v) p := by
  have key : (Polynomial.evalRingHom t).comp
      (aeval fun i ↦ Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X :
        MvPolynomial ι ℝ →ₐ[ℝ] Polynomial ℝ).toRingHom = eval (x + t • v) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) fun i ↦ ?_
    · simp
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X, eval_X]
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  exact congrArg (fun f : MvPolynomial ι ℝ →+* ℝ ↦ f p) key

end MvPolynomial

namespace IsSemialgebraic

/-- A semialgebraic set meets an affine line in a finite union of points and intervals: membership
of `x + t • v` in `S` is constant on the intervals `[t, t']` avoiding a finite set `Z`. -/
theorem exists_finset_mem_iff_line {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) (x v : ι → ℝ) :
    ∃ Z : Finset ℝ, ∀ t t', t ≤ t' → (∀ z ∈ Z, z ∉ Icc t t') →
      (x + t • v ∈ S ↔ x + t' • v ∈ S) := by
  classical
  obtain ⟨T, hT⟩ := hS.exists_finset_mem_iff_of_sign_eq
  refine ⟨T.biUnion fun p ↦ (restrictLine x v p).roots.toFinset, fun t t' htt' hZ ↦
    hT _ _ fun p hp ↦ ?_⟩
  rw [← eval_restrictLine, ← eval_restrictLine]
  by_cases h0 : restrictLine x v p = 0
  · simp [h0]
  refine isPreconnected_Icc.sign_eq (restrictLine x v p).continuous.continuousOn
    (fun s hs hs0 ↦ hZ s ?_ hs) ⟨le_rfl, htt'⟩ ⟨htt', le_rfl⟩
  exact Finset.mem_biUnion.mpr ⟨p, hp, Multiset.mem_toFinset.mpr
    ((Polynomial.mem_roots h0).mpr hs0)⟩

/-- Just to the right of any point `a`, an affine line is either inside or outside a semialgebraic
set. -/
theorem exists_pos_line {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) (x v : ι → ℝ) (a : ℝ) :
    ∃ δ > 0, (∀ t ∈ Ioo a (a + δ), x + t • v ∈ S) ∨ ∀ t ∈ Ioo a (a + δ), x + t • v ∉ S := by
  obtain ⟨Z, hZ⟩ := hS.exists_finset_mem_iff_line x v
  obtain ⟨δ, hδ, hδZ⟩ := Metric.isOpen_iff.mp
    ((Z.finite_toSet.sdiff (t := {a})).isClosed.isOpen_compl) a fun h ↦ h.2 rfl
  have hI (t : ℝ) (ht : t ∈ Ioo a (a + δ)) : t ∈ Metric.ball a δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hiff (t t' : ℝ) (ht : t ∈ Ioo a (a + δ)) (ht' : t' ∈ Ioo a (a + δ)) (htt' : t ≤ t') :
      x + t • v ∈ S ↔ x + t' • v ∈ S :=
    hZ t t' htt' fun z hz hzI ↦ hδZ (hI z ⟨ht.1.trans_le hzI.1, hzI.2.trans_lt ht'.2⟩)
      ⟨hz, fun h ↦ (lt_irrefl a) (h ▸ ht.1.trans_le hzI.1)⟩
  have hmid : a + δ / 2 ∈ Ioo a (a + δ) := ⟨by linarith, by linarith⟩
  have hall (t : ℝ) (ht : t ∈ Ioo a (a + δ)) : x + t • v ∈ S ↔ x + (a + δ / 2) • v ∈ S := by
    rcases le_total t (a + δ / 2) with h | h
    · exact hiff _ _ ht hmid h
    · exact (hiff _ _ hmid ht h).symm
  by_cases hS' : x + (a + δ / 2) • v ∈ S
  · exact ⟨δ, hδ, Or.inl fun t ht ↦ (hall t ht).mpr hS'⟩
  · exact ⟨δ, hδ, Or.inr fun t ht h ↦ hS' ((hall t ht).mp h)⟩

end IsSemialgebraic
