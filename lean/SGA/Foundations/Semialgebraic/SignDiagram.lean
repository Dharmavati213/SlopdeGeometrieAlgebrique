/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Algebra.Polynomial
import SGA.Foundations.Semialgebraic.OrderIso

/-!
# Sign diagrams of families of real polynomials

Two families `f g : α → ℝ[X]` of real polynomials have the same *sign diagram*
(`Polynomial.SignEquiv f g`) if an order automorphism `h` of `ℝ` matches their signs:
`sign (g i (h x)) = sign (f i x)` for all `i` and `x`. Equivalently, the sequences of sign vectors
of the family along the real line (at the roots and on the intervals in between) agree. In
particular the families realize the same sign conditions (`Polynomial.SignEquiv.exists_iff`).

Hörmander's proof of the Tarski–Seidenberg theorem shows that the sign diagram of a family depends
only on the sign diagram of a family of smaller degrees (derivatives and remainders); this file
provides the definition and the elementary facts on signs of real polynomials it uses:

* `IsPreconnected.sign_eq`: a continuous function without zeros on a preconnected set has
  constant sign there;
* `Polynomial.sign_eval_eq_of_forall_ge`, `Polynomial.sign_eval_eq_of_forall_le`: from its last
  root on, a polynomial has the sign of its leading coefficient (times `(-1)ⁿ` towards `-∞`);
* `Polynomial.exists_isRoot_derivative_between`: Rolle's theorem for polynomials.

## References

* [L. Hörmander, *The analysis of linear partial differential operators II*, Appendix A.2]
* [J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, §1.4]
-/

open Set Filter Topology

/-- A continuous real function without zeros on a preconnected set has constant sign there. -/
theorem IsPreconnected.sign_eq {s : Set ℝ} (hs : IsPreconnected s) {f : ℝ → ℝ}
    (hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    SignType.sign (f a) = SignType.sign (f b) := by
  have key : ∀ a ∈ s, ∀ b ∈ s, f a < 0 → ¬ 0 < f b := by
    intro a ha b hb hfa hfb
    obtain ⟨c, hc, hc0⟩ := hs.intermediate_value ha hb hf ⟨hfa.le, hfb.le⟩
    exact h0 c hc hc0
  rcases lt_trichotomy (f a) 0 with h | h | h
  · have hb' : f b < 0 := lt_of_le_of_ne (not_lt.mp (key a ha b hb h)) (h0 b hb)
    rw [sign_neg h, sign_neg hb']
  · exact absurd h (h0 a ha)
  · have hb' : 0 < f b := lt_of_le_of_ne (not_lt.mp fun h' ↦ key b hb a ha h' h) (h0 b hb).symm
    rw [sign_pos h, sign_pos hb']

namespace Polynomial

/-! ### Signs of real polynomials -/

/-- Rolle's theorem for real polynomials: between two roots of `p` lies a root of `p'`. -/
theorem exists_isRoot_derivative_between {p : ℝ[X]} {a b : ℝ} (hab : a < b) (ha : p.eval a = 0)
    (hb : p.eval b = 0) : ∃ c ∈ Ioo a b, p.derivative.eval c = 0 := by
  obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hab p.continuous.continuousOn (ha.trans hb.symm)
  exact ⟨c, hc, by rwa [Polynomial.deriv] at hc0⟩

/-- A nonzero real polynomial eventually has the sign of its leading coefficient at `+∞`. -/
theorem eventually_sign_eval_atTop {p : ℝ[X]} (hp : p ≠ 0) :
    ∀ᶠ x in atTop, SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  rcases p.natDegree.eq_zero_or_pos with h | h
  · rw [eq_C_of_natDegree_eq_zero h]
    exact Eventually.of_forall fun x ↦ by simp
  have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp h
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp) with hlc | hlc
  · have := tendsto_atBot_of_leadingCoeff_nonpos (P := p) hdeg hlc.le
    filter_upwards [this.eventually_lt_atBot 0] with x hx
    rw [sign_neg hx, sign_neg hlc]
  · have := tendsto_atTop_of_leadingCoeff_nonneg (P := p) hdeg hlc.le
    filter_upwards [this.eventually_gt_atTop 0] with x hx
    rw [sign_pos hx, sign_pos hlc]

/-- A real polynomial without zeros on `[a, ∞)` has the sign of its leading coefficient at `a`
(hence on `[a, ∞)`). -/
theorem sign_eval_eq_of_forall_ge {p : ℝ[X]} (hp : p ≠ 0) {a : ℝ}
    (ha : ∀ x, a ≤ x → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = SignType.sign p.leadingCoeff := by
  obtain ⟨y, hy, hya⟩ := ((eventually_sign_eval_atTop hp).and (eventually_ge_atTop a)).exists
  rw [← hy]
  exact isPreconnected_Ici.sign_eq p.continuous.continuousOn (fun z hz ↦ ha z hz)
    (Set.mem_Ici.mpr le_rfl) hya

/-- A nonzero real polynomial eventually has the sign of `(-1)ⁿ` times its leading coefficient at
`-∞`, `n` its degree. -/
theorem eventually_sign_eval_atBot {p : ℝ[X]} (hp : p ≠ 0) :
    ∀ᶠ x in atBot, SignType.sign (p.eval x) =
      SignType.sign ((-1) ^ p.natDegree * p.leadingCoeff) := by
  have hq : p.comp (-X) ≠ 0 := fun h ↦ hp (by
    simpa [comp_neg_X_comp_neg_X] using congrArg (fun q ↦ q.comp (-X)) h)
  have hlc : (p.comp (-X)).leadingCoeff = (-1) ^ p.natDegree * p.leadingCoeff := by
    rw [leadingCoeff_comp (by simp), mul_comm]
    simp
  filter_upwards [tendsto_neg_atBot_atTop.eventually (eventually_sign_eval_atTop hq)] with x hx
  simpa [hlc] using hx

/-- A real polynomial without zeros on `(-∞, a]` has the sign of `(-1)ⁿ` times its leading
coefficient at `a`, `n` its degree. -/
theorem sign_eval_eq_of_forall_le {p : ℝ[X]} (hp : p ≠ 0) {a : ℝ}
    (ha : ∀ x, x ≤ a → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = SignType.sign ((-1) ^ p.natDegree * p.leadingCoeff) := by
  obtain ⟨y, hy, hya⟩ := ((eventually_sign_eval_atBot hp).and (eventually_le_atBot a)).exists
  rw [← hy]
  exact isPreconnected_Iic.sign_eq p.continuous.continuousOn (fun z hz ↦ ha z hz)
    (Set.mem_Iic.mpr le_rfl) hya

/-! ### Sign diagrams -/

variable {α β : Type*}

/-- Two families of real polynomials have the same *sign diagram* if an order automorphism `h`
of `ℝ` matches their signs: `sign (g i (h x)) = sign (f i x)` for all `i` and `x`. -/
def SignEquiv (f g : α → ℝ[X]) : Prop :=
  ∃ h : ℝ ≃o ℝ, ∀ i x, SignType.sign ((g i).eval (h x)) = SignType.sign ((f i).eval x)

namespace SignEquiv

variable {f g k : α → ℝ[X]}

@[refl] protected lemma refl (f : α → ℝ[X]) : SignEquiv f f :=
  ⟨OrderIso.refl ℝ, fun _ _ ↦ rfl⟩

@[symm] protected lemma symm (h : SignEquiv f g) : SignEquiv g f := by
  obtain ⟨h, hh⟩ := h
  exact ⟨h.symm, fun i x ↦ by rw [← hh i, OrderIso.apply_symm_apply]⟩

@[trans] protected lemma trans (h₁ : SignEquiv f g) (h₂ : SignEquiv g k) : SignEquiv f k := by
  obtain ⟨h₁, hh₁⟩ := h₁
  obtain ⟨h₂, hh₂⟩ := h₂
  exact ⟨h₁.trans h₂, fun i x ↦ (hh₂ i (h₁ x)).trans (hh₁ i x)⟩

/-- Restricting families with the same sign diagram along a map of index types. -/
lemma comp (h : SignEquiv f g) (e : β → α) : SignEquiv (f ∘ e) (g ∘ e) := by
  obtain ⟨h, hh⟩ := h
  exact ⟨h, fun i x ↦ hh (e i) x⟩

/-- Families with the same sign diagram realize the same sign conditions. -/
lemma exists_iff (h : SignEquiv f g) (ε : α → SignType) :
    (∃ x, ∀ i, SignType.sign ((f i).eval x) = ε i) ↔
      ∃ x, ∀ i, SignType.sign ((g i).eval x) = ε i := by
  obtain ⟨h, hh⟩ := h
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨h x, fun i ↦ (hh i x).trans (hx i)⟩
  · rintro ⟨y, hy⟩
    exact ⟨h.symm y, fun i ↦ by rw [← hh i, OrderIso.apply_symm_apply, hy i]⟩

/-- Families with the same sign diagram have the same zero polynomials. -/
lemma eq_zero_iff (h : SignEquiv f g) (i : α) : f i = 0 ↔ g i = 0 := by
  obtain ⟨h, hh⟩ := h
  have key (p q : ℝ[X]) (φ : ℝ → ℝ) (hφ : Function.Surjective φ)
      (hpq : ∀ x, SignType.sign (q.eval (φ x)) = SignType.sign (p.eval x)) (hp : p = 0) :
      q = 0 := by
    refine Polynomial.funext fun y ↦ ?_
    obtain ⟨x, rfl⟩ := hφ y
    simpa [hp] using hpq x
  exact ⟨key _ _ h h.surjective (hh i), key _ _ h.symm h.symm.surjective
    (fun y ↦ by rw [← hh i, OrderIso.apply_symm_apply])⟩

end SignEquiv

end Polynomial
