/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Data.Multiset.DershowitzManna
import SGA.Foundations.Semialgebraic.Hormander
import SGA.Foundations.Semialgebraic.PseudoDivision

/-!
# Hörmander's theorem with parameters

Let `R` be a commutative ring and `M` a finite family of polynomials in `R[X]` (the coefficients
are functions of parameters, e.g. `R = ℝ[y₁, …, yₙ]`). A ring homomorphism `φ : R →+* ℝ` (a value of
the parameters) specializes `M` to a family of real polynomials `P ↦ P.map φ`. The sign diagram of
the specialized family depends only on the signs of `φ` on a finite set `T ⊆ R`
(`Polynomial.exists_finset_signEquiv_map`): if `φ` and `ψ` have the same signs on `T`, the
specializations along `φ` and `ψ` have the same sign diagram (`Polynomial.SignEquiv`).

This is Hörmander's proof of the Tarski–Seidenberg theorem. By strong induction on the multiset
of degrees of the members (Dershowitz–Manna order):
* if a member `Q` of positive degree has `φ(lc Q) = 0`, replace it by `Q.eraseLead`, which has the
  same specialization;
* otherwise let `p` be a member of maximal degree; the family of the other members, `p'`, and the
  pseudo-remainders of `p` by the other members of positive degree and by `p'` has smaller
  degrees, and determines the sign diagram of the original family by Hörmander's lemma
  `Polynomial.exists_orderIso_signs_of_hormander` (the sign of `p` at a root of `Q` is that of
  `prem p Q` up to the sign of a power of `lc Q`, `Polynomial.sign_eval_map_eq_of_prem`).

`T` consists of the coefficients of all the polynomials met in this recursion.

## References

* [L. Hörmander, *The analysis of linear partial differential operators II*, Appendix A.2]
* [J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, §1.4]
-/

open Set

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- If `f` kills the leading coefficient of `Q`, then `Q` and `Q.eraseLead` have the same image
under `f`. -/
lemma map_eraseLead_of_map_leadingCoeff_eq_zero {S : Type*} [Semiring S] {f : R →+* S}
    {Q : R[X]} (h : f Q.leadingCoeff = 0) : Q.eraseLead.map f = Q.map f := by
  conv_rhs => rw [← eraseLead_add_C_mul_X_pow Q]
  rw [Polynomial.map_add, Polynomial.map_mul, map_C, h, C_0, zero_mul, add_zero]

lemma natDegree_eraseLead_lt_of_pos {Q : R[X]} (hQ : 0 < Q.natDegree) :
    Q.eraseLead.natDegree < Q.natDegree := by
  rcases eraseLead_natDegree_lt_or_eraseLead_eq_zero Q with h | h
  · exact h
  · rw [h, natDegree_zero]
    exact hQ

/-- If `f` does not kill the leading coefficient after specialization keeps the degree, `f`
does not kill the leading coefficient. -/
lemma map_leadingCoeff_ne_zero_of_natDegree_le {S : Type*} [Semiring S] {f : R →+* S} {Q : R[X]}
    (h : Q.natDegree ≤ (Q.map f).natDegree) (hQ : Q.map f ≠ 0) : f Q.leadingCoeff ≠ 0 := by
  have he : (Q.map f).natDegree = Q.natDegree := le_antisymm natDegree_map_le h
  rw [leadingCoeff, ← coeff_map, ← he]
  exact leadingCoeff_ne_zero.mpr hQ

/-- The sign of a specialization of `P` at a root of the specialization of `Q` is read off from
the pseudo-remainder `prem P Q`: `lc(Q)ᵐ P = q Q + prem P Q`. -/
lemma sign_eval_map_eq_of_prem {P Q : R[X]} {φ ψ : R →+* ℝ} (hφ : φ Q.leadingCoeff ≠ 0)
    (hs : SignType.sign (ψ Q.leadingCoeff) = SignType.sign (φ Q.leadingCoeff)) {x y : ℝ}
    (hx : (Q.map φ).eval x = 0) (hy : (Q.map ψ).eval y = 0)
    (hr : SignType.sign (((prem P Q).map ψ).eval y) = SignType.sign (((prem P Q).map φ).eval x)) :
    SignType.sign ((P.map ψ).eval y) = SignType.sign ((P.map φ).eval x) := by
  obtain ⟨m, q, e⟩ := exists_prem_eq P Q
  have key (χ : R →+* ℝ) (z : ℝ) (hz : (Q.map χ).eval z = 0) :
      χ Q.leadingCoeff ^ m * (P.map χ).eval z = ((prem P Q).map χ).eval z := by
    have := congrArg (fun F ↦ (F.map χ).eval z) e
    simpa [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, hz] using this
  rw [← key φ x hx, ← key ψ y hy, sign_mul, sign_mul, sign_pow, sign_pow, hs] at hr
  exact mul_left_cancel₀ (pow_ne_zero _ (sign_ne_zero.mpr hφ)) hr

/-- A Dershowitz–Manna descent: replacing an element `a` by smaller elements. -/
private lemma isDershowitzMannaLT_add_of_lt {X Y : Multiset ℕ} {a : ℕ} (h : ∀ y ∈ Y, y < a) :
    Multiset.IsDershowitzMannaLT (X + Y) (a ::ₘ X) :=
  ⟨X, Y, {a}, by simp, rfl, by rw [← Multiset.singleton_add, add_comm],
    fun y hy ↦ ⟨a, Multiset.mem_singleton_self a, h y hy⟩⟩

private lemma finite_subtype_mem (M : Multiset R[X]) : Finite {P // P ∈ M} := by
  classical
  exact Finite.of_injective (fun P : {P // P ∈ M} ↦ (⟨P.1, Multiset.mem_toFinset.mpr P.2⟩ :
    M.toFinset)) fun a b h ↦ Subtype.ext (congrArg (fun z : M.toFinset ↦ (z : R[X])) h)

/-- **Hörmander's theorem with parameters.** For a finite family `M` of polynomials over a
commutative ring `R`, there is a finite set `T ⊆ R` such that the specializations of `M` along
two ring homomorphisms `φ, ψ : R →+* ℝ` with the same signs on `T` have the same sign
diagram. -/
theorem exists_finset_signEquiv_map (M : Multiset R[X]) :
    ∃ T : Finset R, ∀ φ ψ : R →+* ℝ,
      (∀ c ∈ T, SignType.sign (φ c) = SignType.sign (ψ c)) →
        SignEquiv (fun P : {P // P ∈ M} ↦ P.1.map φ) (fun P ↦ P.1.map ψ) := by
  classical
  have hwf := InvImage.wf (fun M : Multiset R[X] ↦ M.map natDegree)
    Multiset.wellFounded_isDershowitzMannaLT
  induction M using hwf.induction with
  | _ M IH =>
    -- the coefficients of the members of a family
    let Co : Multiset R[X] → Finset R := fun M ↦
      M.toFinset.biUnion fun P ↦ (Finset.range (P.natDegree + 1)).image P.coeff
    have hCo {M : Multiset R[X]} {P : R[X]} (hP : P ∈ M) {n : ℕ} (hn : n ≤ P.natDegree) :
        P.coeff n ∈ Co M :=
      Finset.mem_biUnion.mpr ⟨P, Multiset.mem_toFinset.mpr hP,
        Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hn), rfl⟩⟩
    have hlc {M : Multiset R[X]} {P : R[X]} (hP : P ∈ M) : P.leadingCoeff ∈ Co M := hCo hP le_rfl
    -- Case A: all members are constant
    by_cases hconst : ∀ Q ∈ M, Q.natDegree = 0
    · refine ⟨Co M, fun φ ψ hT ↦ ⟨OrderIso.refl ℝ, fun P x ↦ ?_⟩⟩
      have hP := hconst _ P.2
      have e (χ : R →+* ℝ) (z : ℝ) : (P.1.map χ).eval z = χ (P.1.coeff 0) := by
        conv_lhs => rw [eq_C_of_natDegree_eq_zero hP]
        simp
      rw [e, e]
      exact (hT _ (hCo P.2 (Nat.zero_le _))).symm
    push Not at hconst
    obtain ⟨Q₀, hQ₀M, hQ₀⟩ := hconst
    -- `p`, a member of maximal degree `d > 0`
    obtain ⟨p, hpM', hpmax⟩ := M.toFinset.exists_max_image natDegree
      ⟨Q₀, Multiset.mem_toFinset.mpr hQ₀M⟩
    have hpM : p ∈ M := Multiset.mem_toFinset.mp hpM'
    have hpmax' (Q : R[X]) (hQ : Q ∈ M) : Q.natDegree ≤ p.natDegree :=
      hpmax Q (Multiset.mem_toFinset.mpr hQ)
    have hd : 0 < p.natDegree := (Nat.pos_of_ne_zero hQ₀).trans_le (hpmax' Q₀ hQ₀M)
    have hMdeg : M.map natDegree = p.natDegree ::ₘ (M.erase p).map natDegree := by
      conv_lhs => rw [← Multiset.cons_erase hpM]
      rw [Multiset.map_cons]
    -- the derived family
    set p' := derivative p
    have hp'd : p'.natDegree < p.natDegree := natDegree_derivative_lt hd.ne'
    set M' := M.erase p +
      (p' ::ₘ ((p' ::ₘ M.erase p).filter (fun Q ↦ 0 < Q.natDegree)).map (prem p))
    have hM' : Multiset.IsDershowitzMannaLT (M'.map natDegree) (M.map natDegree) := by
      rw [hMdeg, Multiset.map_add]
      refine isDershowitzMannaLT_add_of_lt fun y hy ↦ ?_
      rw [Multiset.map_cons, Multiset.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hp'd
      obtain ⟨_, hr, rfl⟩ := Multiset.mem_map.mp hy
      obtain ⟨r, hrQ, rfl⟩ := Multiset.mem_map.mp hr
      obtain ⟨hrM, hr0⟩ := Multiset.mem_filter.mp hrQ
      refine (natDegree_prem_lt p hr0).trans_le ?_
      rcases Multiset.mem_cons.mp hrM with rfl | hrM
      · exact hp'd.le
      · exact hpmax' r (Multiset.mem_of_mem_erase hrM)
    obtain ⟨T₂, hT₂⟩ := IH M' hM'
    have hmemM' {Q : R[X]} (hQ : Q ∈ M.erase p) : Q ∈ M' := Multiset.mem_add.mpr (Or.inl hQ)
    have hp'M' : p' ∈ M' := Multiset.mem_add.mpr (Or.inr (Multiset.mem_cons_self _ _))
    have hpremM' {Q : R[X]} (hQ : Q ∈ p' ::ₘ M.erase p) (hQ0 : 0 < Q.natDegree) : prem p Q ∈ M' :=
      Multiset.mem_add.mpr (Or.inr (Multiset.mem_cons_of_mem
        (Multiset.mem_map_of_mem _ (Multiset.mem_filter.mpr ⟨hQ, hQ0⟩))))
    -- the truncated families
    have IH₁ (Q : R[X]) (hQ : Q ∈ M) (hQ0 : 0 < Q.natDegree) :
        ∃ T : Finset R, ∀ φ ψ : R →+* ℝ,
          (∀ c ∈ T, SignType.sign (φ c) = SignType.sign (ψ c)) →
            SignEquiv (fun P : {P // P ∈ Q.eraseLead ::ₘ M.erase Q} ↦ P.1.map φ)
              (fun P ↦ P.1.map ψ) := by
      refine IH _ ?_
      change Multiset.IsDershowitzMannaLT ((Q.eraseLead ::ₘ M.erase Q).map natDegree)
        (M.map natDegree)
      conv_rhs => rw [← Multiset.cons_erase hQ]
      rw [Multiset.map_cons, Multiset.map_cons, ← Multiset.singleton_add, add_comm]
      exact isDershowitzMannaLT_add_of_lt fun y hy ↦ by
        rw [Multiset.mem_singleton] at hy
        exact hy ▸ natDegree_eraseLead_lt_of_pos hQ0
    choose! T₁ hT₁ using IH₁
    refine ⟨Co M ∪ Co M' ∪ T₂ ∪ M.toFinset.biUnion T₁, fun φ ψ hT ↦ ?_⟩
    have hTM (c : R) (hc : c ∈ Co M) : SignType.sign (φ c) = SignType.sign (ψ c) :=
      hT c (by simp [hc])
    have hTM' (c : R) (hc : c ∈ Co M') : SignType.sign (φ c) = SignType.sign (ψ c) :=
      hT c (by simp [hc])
    have hzero {c : R} (hc : c ∈ Co M) : φ c = 0 ↔ ψ c = 0 := by
      rw [← sign_eq_zero_iff, hTM c hc, sign_eq_zero_iff]
    by_cases hB : ∃ Q ∈ M, 0 < Q.natDegree ∧ φ Q.leadingCoeff = 0
    · -- Case B: truncate a member whose leading coefficient vanishes
      obtain ⟨Q, hQM, hQ0, hφQ⟩ := hB
      have hψQ : ψ Q.leadingCoeff = 0 := (hzero (hlc hQM)).mp hφQ
      obtain ⟨h, hh⟩ := hT₁ Q hQM hQ0 φ ψ fun c hc ↦ hT c (by
        simp only [Finset.mem_union, Finset.mem_biUnion, Multiset.mem_toFinset]
        exact Or.inr ⟨Q, hQM, hc⟩)
      let e : {P // P ∈ M} → {P // P ∈ Q.eraseLead ::ₘ M.erase Q} := fun P ↦
        if hPQ : P.1 = Q then ⟨Q.eraseLead, Multiset.mem_cons_self _ _⟩
        else ⟨P.1, Multiset.mem_cons_of_mem ((Multiset.mem_erase_of_ne hPQ).mpr P.2)⟩
      have he (χ : R →+* ℝ) (hχ : χ Q.leadingCoeff = 0) (P : {P // P ∈ M}) :
          (e P).1.map χ = P.1.map χ := by
        by_cases hPQ : P.1 = Q
        · simp [e, hPQ, map_eraseLead_of_map_leadingCoeff_eq_zero hχ]
        · simp [e, hPQ]
      refine ⟨h, fun P x ↦ ?_⟩
      change SignType.sign ((P.1.map ψ).eval (h x)) = SignType.sign ((P.1.map φ).eval x)
      rw [← he φ hφQ, ← he ψ hψQ]
      exact hh (e P) x
    -- Case C: all leading coefficients survive; Hörmander's lemma
    push Not at hB
    have hlcM {Q : R[X]} (hQ : Q ∈ M) (hQ0 : 0 < Q.natDegree) :
        φ Q.leadingCoeff ≠ 0 ∧ ψ Q.leadingCoeff ≠ 0 :=
      ⟨hB Q hQ hQ0, fun h ↦ hB Q hQ hQ0 ((hzero (hlc hQ)).mpr h)⟩
    obtain ⟨h, hh⟩ := hT₂ φ ψ fun c hc ↦ hT c (by simp [hc])
    have hhM' {Q : R[X]} (hQ : Q ∈ M') (x : ℝ) :
        SignType.sign ((Q.map ψ).eval (h x)) = SignType.sign ((Q.map φ).eval x) :=
      hh ⟨Q, hQ⟩ x
    have hpφ := (hlcM hpM hd).1
    have hpψ := (hlcM hpM hd).2
    have hdegφ : (p.map φ).natDegree = p.natDegree := natDegree_map_of_leadingCoeff_ne_zero φ hpφ
    have hdegψ : (p.map ψ).natDegree = p.natDegree := natDegree_map_of_leadingCoeff_ne_zero ψ hpψ
    -- the derivative of the specialization of `p`
    have hp'φ : p'.map φ ≠ 0 := by
      rw [← derivative_map, Ne, derivative_eq_zero, hdegφ]
      exact hd.ne'
    have hp'deg : p'.natDegree ≤ (p'.map φ).natDegree := by
      rw [← derivative_map, natDegree_derivative (p.map φ), hdegφ]
      exact natDegree_derivative_le p
    have : Finite {P // P ∈ M.erase p} := finite_subtype_mem _
    -- the signs of `p` on the Hörmander set
    have hA : ∀ x ∈ hormanderSet (fun Q : {P // P ∈ M.erase p} ↦ Q.1.map φ) (p.map φ),
        SignType.sign ((p.map ψ).eval (h x)) = SignType.sign ((p.map φ).eval x) := by
      intro x hx
      rcases hx with ⟨Q, hQ0, hQx⟩ | hx
      · change Q.1.map φ ≠ 0 at hQ0
        change (Q.1.map φ).eval x = 0 at hQx
        have hQM : Q.1 ∈ M := Multiset.mem_of_mem_erase Q.2
        have hQd : 0 < Q.1.natDegree := by
          refine Nat.pos_of_ne_zero fun hQd ↦ hQ0 ?_
          have hc : Q.1.map φ = C (φ (Q.1.coeff 0)) := by
            conv_lhs => rw [eq_C_of_natDegree_eq_zero hQd]
            simp
          rw [hc, eval_C] at hQx
          rw [hc, hQx, C_0]
        have hy : (Q.1.map ψ).eval (h x) = 0 := by
          rw [← sign_eq_zero_iff, hhM' (hmemM' Q.2) x, hQx, sign_zero]
        exact sign_eval_map_eq_of_prem (hlcM hQM hQd).1 (hTM _ (hlc hQM)).symm hQx hy
          (hhM' (hpremM' (Multiset.mem_cons_of_mem Q.2) hQd) x)
      · rw [derivative_map] at hx
        have hp'd0 : 0 < p'.natDegree := by
          refine Nat.pos_of_ne_zero fun h0 ↦ ?_
          have hc : p'.map φ = C (φ (p'.coeff 0)) := by
            conv_lhs => rw [eq_C_of_natDegree_eq_zero h0]
            simp
          rw [hc, eval_C] at hx
          exact hp'φ (by rw [hc, hx, C_0])
        have hy : (p'.map ψ).eval (h x) = 0 := by
          rw [← sign_eq_zero_iff, hhM' hp'M' x, hx, sign_zero]
        have hlc' : φ p'.leadingCoeff ≠ 0 := map_leadingCoeff_ne_zero_of_natDegree_le hp'deg hp'φ
        have hp'Co : p'.leadingCoeff ∈ Co M' := hlc hp'M'
        exact sign_eval_map_eq_of_prem hlc' (hTM' _ hp'Co).symm hx hy
          (hhM' (hpremM' (Multiset.mem_cons_self _ _) hp'd0) x)
    obtain ⟨H, hHf, hHp⟩ := exists_orderIso_signs_of_hormander (f := fun Q : {P // P ∈ M.erase p} ↦
      Q.1.map φ) (g := fun Q ↦ Q.1.map ψ) (p := p.map φ) (q := p.map ψ) h
      (fun Q x ↦ hhM' (hmemM' Q.2) x)
      (fun x ↦ by rw [derivative_map, derivative_map]; exact hhM' hp'M' x)
      hA
      (by rw [leadingCoeff_map_of_leadingCoeff_ne_zero ψ hpψ,
        leadingCoeff_map_of_leadingCoeff_ne_zero φ hpφ]; exact (hTM _ (hlc hpM)).symm)
      (by rw [leadingCoeff_map_of_leadingCoeff_ne_zero ψ hpψ,
        leadingCoeff_map_of_leadingCoeff_ne_zero φ hpφ, hdegφ, hdegψ, sign_mul, sign_mul,
        hTM _ (hlc hpM)])
    refine ⟨H, fun P x ↦ ?_⟩
    by_cases hPp : P.1 = p
    · simpa only [hPp] using hHp x
    · exact hHf ⟨P.1, (Multiset.mem_erase_of_ne hPp).mpr P.2⟩ x

end Polynomial
