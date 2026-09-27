/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.Basic

/-!
# Functions which are polynomial on lines

For `h ≠ 0` a polynomial on `ℂⁿ`, a function on `{h ≠ 0}` whose restrictions to all complex lines
through points of `{h ≠ 0}` agree (off `h = 0`) with polynomials of bounded degree is the
restriction of a polynomial (`exists_mvPolynomial_eq_of_forall_line`), by Lagrange interpolation
and induction on `n`. Also: restriction of polynomials to lines (`lineRestrict`) and their growth
along lines (`exists_norm_eval_line_le`). Used in the proof of XII.2.4 (`RootLocus.lean`).
-/

open Polynomial Set

namespace SGA.SGA1.ExposeXII

variable {σ : Type*}

/-- The restriction of a polynomial `p` on `ℂ^σ` to the complex line `s ↦ a + s • v`. -/
noncomputable def lineRestrict (p : MvPolynomial σ ℂ) (a v : σ → ℂ) : ℂ[X] :=
  MvPolynomial.aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * X) p

@[simp] lemma eval_lineRestrict (p : MvPolynomial σ ℂ) (a v : σ → ℂ) (s : ℂ) :
    (lineRestrict p a v).eval s = MvPolynomial.eval (a + s • v) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [lineRestrict]
  | add p q hp hq => simp only [lineRestrict, map_add, eval_add] at hp hq ⊢; rw [hp, hq]
  | mul_X p i hp =>
    simp only [lineRestrict, map_mul, eval_mul] at hp ⊢
    rw [hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]
    simp only [eval_add, eval_C, eval_mul, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- A nonzero polynomial vanishes at only finitely many points of a line through a point where it
does not vanish. -/
lemma finite_setOf_eval_line_eq_zero {p : MvPolynomial σ ℂ} {a : σ → ℂ}
    (ha : MvPolynomial.eval a p ≠ 0) (v : σ → ℂ) :
    {s : ℂ | MvPolynomial.eval (a + s • v) p = 0}.Finite := by
  have hne : lineRestrict p a v ≠ 0 := fun h ↦ ha (by simpa using congrArg (eval 0) h)
  refine (Polynomial.finite_setOfPred_isRoot hne).subset fun s hs ↦ ?_
  simpa [IsRoot] using hs

/-- Polynomial growth of a polynomial along a complex line. -/
lemma exists_norm_eval_line_le (p : MvPolynomial σ ℂ) (a v : σ → ℂ) : ∃ C : ℝ, ∀ s : ℂ,
    ‖MvPolynomial.eval (a + s • v) p‖ ≤ C * (1 + ‖s‖) ^ p.totalDegree := by
  refine ⟨∑ d ∈ p.support, ‖p.coeff d‖ * ∏ i ∈ d.support, (‖a i‖ + ‖v i‖) ^ d i, fun s ↦ ?_⟩
  rw [MvPolynomial.eval_eq, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd ↦ ?_)
  rw [norm_mul, mul_assoc]
  gcongr
  rw [norm_prod]
  have hdeg : (d.sum fun _ e ↦ e) ≤ p.totalDegree := MvPolynomial.le_totalDegree hd
  have h1 : (1 : ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  calc ∏ i ∈ d.support, ‖(a + s • v) i ^ d i‖
      ≤ ∏ i ∈ d.support, ((‖a i‖ + ‖v i‖) * (1 + ‖s‖)) ^ d i := by
        gcongr with i hi
        rw [norm_pow]
        gcongr
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
        nlinarith [norm_nonneg (a i), norm_nonneg (v i), norm_nonneg s]
    _ = (∏ i ∈ d.support, (‖a i‖ + ‖v i‖) ^ d i) * (1 + ‖s‖) ^ (d.sum fun _ e ↦ e) := by
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        rfl
    _ ≤ _ := by
        gcongr

lemma fin_cons_add_smul {n : ℕ} (y : ℂ) (a v : Fin n → ℂ) (s : ℂ) :
    (Fin.cons y a : Fin (n + 1) → ℂ) + s • Fin.cons 0 v = Fin.cons y (a + s • v) := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

lemma fin_cons_add_smul_single {n : ℕ} (y : ℂ) (a : Fin n → ℂ) (s : ℂ) :
    (Fin.cons y a : Fin (n + 1) → ℂ) + s • Fin.cons 1 0 = Fin.cons (y + s) a := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

lemma exists_eval_ne_zero {n : ℕ} {p : MvPolynomial (Fin n) ℂ} (hp : p ≠ 0) :
    ∃ b, MvPolynomial.eval b p ≠ 0 := by
  by_contra! H
  exact hp (MvPolynomial.funext fun b ↦ by simp [H b])

lemma eval_aeval_X_zero {n : ℕ} (x : Fin (n + 1) → ℂ) (L : ℂ[X]) :
    MvPolynomial.eval x (Polynomial.aeval (MvPolynomial.X 0) L) = L.eval (x 0) := by
  induction L using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k c => simp

/-- A function on the complement `{h ≠ 0}` of a hypersurface in `ℂⁿ` whose restrictions to the
complex lines (through points of `{h ≠ 0}`) agree with polynomials of degree at most `N` is the
restriction of a polynomial. -/
theorem exists_mvPolynomial_eq_of_forall_line (N : ℕ) : ∀ {n : ℕ} (h : MvPolynomial (Fin n) ℂ),
    h ≠ 0 → ∀ (F : (Fin n → ℂ) → ℂ), (∀ a v : Fin n → ℂ, MvPolynomial.eval a h ≠ 0 →
      ∃ q : ℂ[X], q.natDegree ≤ N ∧ ∀ s : ℂ, MvPolynomial.eval (a + s • v) h ≠ 0 →
        F (a + s • v) = q.eval s) →
    ∃ G : MvPolynomial (Fin n) ℂ, ∀ z, MvPolynomial.eval z h ≠ 0 → F z = MvPolynomial.eval z G := by
  intro n
  induction n with
  | zero =>
    intro h hh F hF
    exact ⟨MvPolynomial.C (F default), fun z _ ↦ by
      rw [MvPolynomial.eval_C, Subsingleton.elim z default]⟩
  | succ n ih =>
    intro h hh F hF
    classical
    set H := MvPolynomial.finSuccEquiv ℂ n h with hH
    have hH0 : H ≠ 0 := by
      intro h0
      apply hh
      have := congrArg (MvPolynomial.finSuccEquiv ℂ n).symm h0
      simpa [hH] using this
    have heval (y : ℂ) (z' : Fin n → ℂ) :
        MvPolynomial.eval (Fin.cons y z') h = (H.map (MvPolynomial.eval z')).eval y :=
      MvPolynomial.eval_eq_eval_mv_eval' z' y h
    let hw : ℂ → MvPolynomial (Fin n) ℂ := fun w ↦ H.eval (MvPolynomial.C w)
    have hw_eval (w : ℂ) (z' : Fin n → ℂ) :
        MvPolynomial.eval z' (hw w) = MvPolynomial.eval (Fin.cons w z') h := by
      rw [heval, Polynomial.eval_map, ← MvPolynomial.eval_C (f := z') w, Polynomial.eval₂_hom,
        MvPolynomial.eval_C]
    -- the inductive hypothesis on the horizontal hyperplanes `{w} × ℂⁿ`
    have hG (w : ℂ) (hw0 : hw w ≠ 0) : ∃ G : MvPolynomial (Fin n) ℂ, ∀ z',
        MvPolynomial.eval z' (hw w) ≠ 0 → F (Fin.cons w z') = MvPolynomial.eval z' G := by
      refine ih (hw w) hw0 (fun z' ↦ F (Fin.cons w z')) fun a' v' ha' ↦ ?_
      rw [hw_eval] at ha'
      obtain ⟨q, hq, hFq⟩ := hF (Fin.cons w a') (Fin.cons 0 v') ha'
      refine ⟨q, hq, fun s hs ↦ ?_⟩
      rw [hw_eval, ← fin_cons_add_smul] at hs
      rw [← fin_cons_add_smul]
      exact hFq s hs
    choose! Gw hGw using hG
    -- the nodes of the interpolation
    have hbad : {w : ℂ | hw w = 0}.Finite :=
      ((Polynomial.finite_setOfPred_isRoot hH0).preimage
        (MvPolynomial.C_injective (Fin n) ℂ).injOn).subset fun w hw0 ↦ hw0
    obtain ⟨nodes, hnodes, hcard⟩ := hbad.infinite_compl.exists_subset_card_eq (N + 1)
    have hgood (w : ℂ) (hw' : w ∈ nodes) : hw w ≠ 0 := hnodes hw'
    let G : MvPolynomial (Fin (n + 1)) ℂ := ∑ w ∈ nodes,
      MvPolynomial.rename Fin.succ (Gw w) *
        Polynomial.aeval (MvPolynomial.X 0) (Lagrange.basis nodes id w)
    have hGeval (s : ℂ) (z' : Fin n → ℂ) : MvPolynomial.eval (Fin.cons s z') G =
        ∑ w ∈ nodes, MvPolynomial.eval z' (Gw w) * (Lagrange.basis nodes id w).eval s := by
      simp only [G, map_sum, map_mul, MvPolynomial.eval_rename]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      rw [eval_aeval_X_zero, Fin.cons_zero]
      congr 2
    let lead := H.leadingCoeff
    have hlead : lead ≠ 0 := leadingCoeff_ne_zero.mpr hH0
    -- (i) on the good points
    have hi (s : ℂ) (z' : Fin n → ℂ) (hs : MvPolynomial.eval (Fin.cons s z') h ≠ 0)
        (hl : MvPolynomial.eval z' lead ≠ 0) (hn : ∀ w ∈ nodes, MvPolynomial.eval z' (hw w) ≠ 0) :
        F (Fin.cons s z') = MvPolynomial.eval (Fin.cons s z') G := by
      have hmap : H.map (MvPolynomial.eval z') ≠ 0 := by
        intro h0
        apply hl
        have := congrArg (fun p ↦ p.coeff H.natDegree) h0
        simpa [Polynomial.coeff_map, lead] using this
      obtain ⟨y₀, hy₀⟩ : ∃ y₀, (H.map (MvPolynomial.eval z')).eval y₀ ≠ 0 := by
        by_contra! H'
        exact hmap (Polynomial.funext fun y ↦ by simp [H' y])
      rw [← heval] at hy₀
      obtain ⟨q, hq, hFq⟩ := hF (Fin.cons y₀ z') (Fin.cons 1 0) hy₀
      let q' := q.comp (X - Polynomial.C y₀)
      have hq' : q'.natDegree ≤ N := by
        refine (natDegree_comp_le).trans ?_
        have : (X - Polynomial.C y₀).natDegree ≤ 1 := by
          rw [natDegree_X_sub_C]
        nlinarith
      have hFq' (y : ℂ) (hy : MvPolynomial.eval (Fin.cons y z') h ≠ 0) :
          F (Fin.cons y z') = q'.eval y := by
        have := hFq (y - y₀) (by rwa [fin_cons_add_smul_single, add_sub_cancel])
        rw [fin_cons_add_smul_single, add_sub_cancel] at this
        rw [this]
        simp [q']
      have hinterp : q' = Lagrange.interpolate nodes id (fun w ↦ MvPolynomial.eval z' (Gw w)) := by
        refine Lagrange.eq_interpolate_of_eval_eq _ (Set.injOn_id _) ?_ fun w hw' ↦ ?_
        · rw [hcard]
          exact (degree_le_of_natDegree_le hq').trans_lt (by exact_mod_cast Nat.lt_succ_self N)
        · have h1 : MvPolynomial.eval (Fin.cons w z') h ≠ 0 := by
            rw [← hw_eval]
            exact hn w hw'
          rw [id, ← hFq' w h1]
          exact hGw w (hgood w hw') z' (hn w hw')
      rw [hFq' s hs, hinterp, Lagrange.interpolate_apply, hGeval, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C]
    -- the exceptional hypersurface
    let hstar : MvPolynomial (Fin (n + 1)) ℂ :=
      MvPolynomial.rename Fin.succ (lead * ∏ w ∈ nodes, hw w)
    have hstar0 : hstar ≠ 0 := by
      intro h0
      have h1 : lead * ∏ w ∈ nodes, hw w = 0 :=
        MvPolynomial.rename_injective _ (Fin.succ_injective n) (by simpa [hstar] using h0)
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hlead h2
      · obtain ⟨w, hw', hw0⟩ := Finset.prod_eq_zero_iff.mp h2
        exact hgood w hw' hw0
    have hgoodz (z : Fin (n + 1) → ℂ) (hz : MvPolynomial.eval z h ≠ 0)
        (hz' : MvPolynomial.eval z hstar ≠ 0) : F z = MvPolynomial.eval z G := by
      rw [← Fin.cons_self_tail z] at hz ⊢
      have htail : MvPolynomial.eval (Fin.tail z) (lead * ∏ w ∈ nodes, hw w) ≠ 0 := by
        have : Fin.tail z = z ∘ Fin.succ := rfl
        rw [this]
        simpa [hstar, MvPolynomial.eval_rename] using hz'
      rw [map_mul, mul_ne_zero_iff, map_prod, Finset.prod_ne_zero_iff] at htail
      exact hi _ _ hz htail.1 htail.2
    refine ⟨G, fun z hz ↦ ?_⟩
    obtain ⟨b, hb⟩ := exists_eval_ne_zero (mul_ne_zero hh hstar0)
    have hbh : MvPolynomial.eval b h ≠ 0 := fun h0 ↦ hb (by rw [map_mul, h0, zero_mul])
    obtain ⟨q, -, hFq⟩ := hF b (z - b) hbh
    have hfin := finite_setOf_eval_line_eq_zero hb (z - b)
    have hqr : q = lineRestrict G b (z - b) := by
      refine Polynomial.eq_of_infinite_eval_eq _ _ (hfin.infinite_compl.mono fun t ht ↦ ?_)
      simp only [mem_compl_iff, mem_ofPred_eq, map_mul, mul_eq_zero, not_or] at ht
      simp only [mem_ofPred_eq, eval_lineRestrict]
      rw [← hFq t ht.1]
      exact hgoodz _ ht.1 ht.2
    have h1 : b + (1 : ℂ) • (z - b) = z := by simp
    have := hFq 1 (by rwa [h1])
    rw [h1] at this
    rw [this, hqr, eval_lineRestrict, h1]

end SGA.SGA1.ExposeXII
