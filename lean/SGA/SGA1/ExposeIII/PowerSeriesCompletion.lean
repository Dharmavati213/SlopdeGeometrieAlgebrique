/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.FormallySmooth

/-!
# The maximal-adic topology of a power series ring

For a local ring `A` and a finite set of variables `σ`, the `m`-th power of the maximal ideal
`𝔫` of `A⟦σ⟧` consists of the power series whose coefficient in multidegree `e` lies in
`𝔪 ^ (m - |e|)` (`pow_maximalIdeal_eq_powFiltration`). Consequently `A⟦σ⟧` is `𝔫`-adically
complete when `A` is `𝔪`-adically complete (`isAdicComplete_maximalIdeal`). SGA uses this in
III.2.2, (iv ter) ⇒ (v), and in the proof of III.1.5 ("`B₁` and `B` are the projective limits of
the corresponding rings reduced modulo `𝔪^q`").
-/

universe u

namespace SGA.SGA1.ExposeIII

open MvPowerSeries IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] {σ : Type*}

variable (σ A) in
/-- The ideal of power series whose coefficient in each multidegree `e` lies in
`𝔪 ^ (m - |e|)`. It is the `m`-th power of the maximal ideal of `A⟦σ⟧`
(`pow_maximalIdeal_eq_powFiltration`). -/
def powFiltration (m : ℕ) : Ideal (MvPowerSeries σ A) where
  carrier := {F | ∀ e, coeff e F ∈ maximalIdeal A ^ (m - e.degree)}
  add_mem' hF hG e := by rw [map_add]; exact add_mem (hF e) (hG e)
  zero_mem' e := by rw [map_zero]; exact zero_mem _
  smul_mem' c F hF e := by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ fun p hp ↦ Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right ?_ (hF p.2))
    have : p.2.degree ≤ e.degree := by
      rw [Finset.mem_antidiagonal] at hp
      exact Finsupp.degree_mono (hp ▸ le_add_self)
    omega

lemma mem_powFiltration {m : ℕ} {F : MvPowerSeries σ A} :
    F ∈ powFiltration A σ m ↔ ∀ e, coeff e F ∈ maximalIdeal A ^ (m - e.degree) := Iff.rfl

lemma mul_mem_powFiltration {m k : ℕ} {F G : MvPowerSeries σ A} (hF : F ∈ powFiltration A σ m)
    (hG : G ∈ powFiltration A σ k) : F * G ∈ powFiltration A σ (m + k) := by
  classical
  intro e
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun p hp ↦ ?_
  have hmem := Ideal.mul_mem_mul (hF p.1) (hG p.2)
  rw [← pow_add] at hmem
  refine Ideal.pow_le_pow_right ?_ hmem
  have : p.1.degree + p.2.degree = e.degree := by
    rw [Finset.mem_antidiagonal] at hp
    rw [← map_add, hp]
  omega

lemma maximalIdeal_le_powFiltration_one :
    maximalIdeal (MvPowerSeries σ A) ≤ powFiltration A σ 1 := by
  intro F hF e
  by_cases he : e = 0
  · subst he
    rw [map_zero, Nat.sub_zero, pow_one, coeff_zero_eq_constantCoeff_apply]
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff] at hF
    exact hF
  · have : 1 - e.degree = 0 := by
      have : e.degree ≠ 0 := fun h ↦ he ((Finsupp.degree_eq_zero_iff e).1 h)
      omega
    rw [this, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

lemma pow_maximalIdeal_le_powFiltration (m : ℕ) :
    maximalIdeal (MvPowerSeries σ A) ^ m ≤ powFiltration A σ m := by
  induction m with
  | zero => intro F _ e; simp
  | succ m ih =>
    rw [pow_succ]
    exact Ideal.mul_le.2 fun F hF G hG ↦
      mul_mem_powFiltration (ih hF) (maximalIdeal_le_powFiltration_one hG)

section Finite

variable [Finite σ]

omit [IsLocalRing A] in
/-- A power series minus its truncation in total degree `< m` lies in `(X)ᵐ`. -/
lemma sub_truncTotal_mem_pow_span_X (m : ℕ) (F : MvPowerSeries σ A) :
    F - (truncTotal m F : MvPowerSeries σ A) ∈ Ideal.span (Set.range (X : σ → _)) ^ m := by
  rw [← ker_truncTotalAlgHom, RingHom.mem_ker, map_sub, sub_eq_zero]
  have := (truncTotalAlgHom σ A m).commutes (truncTotal m F)
  rw [MvPowerSeries.algebraMap_apply', Algebra.algebraMap_self, MvPowerSeries.map_id,
    RingHom.id_apply] at this
  rw [this, truncTotalAlgHom_apply]
  rfl

omit [IsLocalRing A] in
/-- The monomial `tᵉ` lies in `(X) ^ |e|`. -/
lemma monomial_one_mem_pow_span_X (e : σ →₀ ℕ) :
    monomial e (1 : A) ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ A)) ^ e.degree := by
  classical
  have := sub_truncTotal_mem_pow_span_X e.degree (monomial e (1 : A))
  have h0 : truncTotal e.degree (monomial e (1 : A)) = 0 := by
    ext d
    rw [coeff_truncTotal_eq_ite, MvPolynomial.coeff_zero, coeff_monomial]
    split_ifs with h₁ h₂ <;> first | rfl | (subst h₂; exact absurd h₁ (lt_irrefl _))
  rwa [h0, MvPolynomial.coe_zero, sub_zero] at this

omit [Finite σ] in
lemma span_X_le_maximalIdeal :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ A)) ≤ maximalIdeal (MvPowerSeries σ A) := by
  refine Ideal.span_le.2 (Set.range_subset_iff.2 fun i ↦ ?_)
  rw [SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff,
    constantCoeff_X]
  exact not_isUnit_zero

omit [Finite σ] in
lemma C_mem_pow_maximalIdeal {k : ℕ} {a : A} (ha : a ∈ maximalIdeal A ^ k) :
    C a ∈ maximalIdeal (MvPowerSeries σ A) ^ k := by
  have hle : (maximalIdeal A).map (C (σ := σ) (R := A)) ≤ maximalIdeal (MvPowerSeries σ A) := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff,
      constantCoeff_C]
    exact hb
  have := Ideal.mem_map_of_mem (C (σ := σ) (R := A)) ha
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono hle k this

lemma powFiltration_le_pow_maximalIdeal (m : ℕ) :
    powFiltration A σ m ≤ maximalIdeal (MvPowerSeries σ A) ^ m := by
  classical
  intro F hF
  have hsub := Ideal.pow_right_mono span_X_le_maximalIdeal m (sub_truncTotal_mem_pow_span_X m F)
  rw [show F = (F - (truncTotal m F : MvPowerSeries σ A)) + (truncTotal m F : MvPowerSeries σ A)
    by ring]
  refine add_mem hsub ?_
  rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, (truncTotal m F).as_sum, map_sum]
  refine Ideal.sum_mem _ fun e he ↦ ?_
  have hlt : e.degree < m := by
    by_contra h
    exact MvPolynomial.mem_support_iff.1 he (coeff_truncTotal_eq_zero _ (not_lt.1 h))
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial,
    coeff_truncTotal _ hlt, show monomial e (coeff e F) = C (coeff e F) * monomial e 1 by
      rw [← monomial_zero_eq_C_apply, monomial_mul_monomial, zero_add, mul_one]]
  have := Ideal.mul_mem_mul (C_mem_pow_maximalIdeal (σ := σ) (hF e))
    (Ideal.pow_right_mono span_X_le_maximalIdeal _ (monomial_one_mem_pow_span_X (A := A) e))
  rwa [← pow_add, Nat.sub_add_cancel hlt.le] at this

/-- The powers of the maximal ideal of `A⟦σ⟧`, `σ` finite, in terms of coefficients:
`F ∈ 𝔫ᵐ` if and only if the coefficient of `F` in multidegree `e` lies in `𝔪 ^ (m - |e|)`. -/
theorem pow_maximalIdeal_eq_powFiltration (m : ℕ) :
    maximalIdeal (MvPowerSeries σ A) ^ m = powFiltration A σ m :=
  le_antisymm (pow_maximalIdeal_le_powFiltration m) (powFiltration_le_pow_maximalIdeal m)

lemma coeff_mem_of_mem_pow_maximalIdeal {m : ℕ} {F : MvPowerSeries σ A}
    (hF : F ∈ maximalIdeal (MvPowerSeries σ A) ^ m) (e : σ →₀ ℕ) :
    coeff e F ∈ maximalIdeal A ^ (m - e.degree) := by
  rw [pow_maximalIdeal_eq_powFiltration] at hF
  exact hF e

/-- A power series ring `A⟦t₁, …, tₙ⟧` over a complete local ring `A` is complete for its maximal
ideal (used in III.2.2, (iv ter) ⇒ (v)). The limit of a Cauchy sequence is computed coefficientwise,
using `pow_maximalIdeal_eq_powFiltration`. -/
theorem isAdicComplete_maximalIdeal [IsAdicComplete (maximalIdeal A) A] :
    IsAdicComplete (maximalIdeal (MvPowerSeries σ A)) (MvPowerSeries σ A) := by
  have hpow (n : ℕ) : (maximalIdeal (MvPowerSeries σ A) ^ n • ⊤ :
      Submodule (MvPowerSeries σ A) (MvPowerSeries σ A)) = maximalIdeal _ ^ n := by
    rw [smul_eq_mul, Ideal.mul_top]
  have hpowA (n : ℕ) : (maximalIdeal A ^ n • ⊤ : Submodule A A) = maximalIdeal A ^ n := by
    rw [smul_eq_mul, Ideal.mul_top]
  refine { haus' := fun F hF ↦ ?_, prec' := fun f hf ↦ ?_ }
  · ext e
    rw [map_zero]
    refine IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal A) A) _ fun k ↦ ?_
    have := SModEq.zero.1 (hF (k + e.degree))
    rw [hpow] at this
    rw [SModEq.zero, hpowA]
    simpa using coeff_mem_of_mem_pow_maximalIdeal this e
  · -- coefficientwise limits
    have hcauchy (e : σ →₀ ℕ) {k k' : ℕ} (hkk' : k ≤ k') :
        coeff e (f (k + e.degree)) ≡ coeff e (f (k' + e.degree))
          [SMOD (maximalIdeal A ^ k • ⊤ : Submodule A A)] := by
      have := SModEq.sub_mem.1 (hf (Nat.add_le_add_right hkk' e.degree))
      rw [hpow] at this
      rw [SModEq.sub_mem, hpowA, ← map_sub]
      simpa using coeff_mem_of_mem_pow_maximalIdeal this e
    choose L hL using fun e ↦
      IsPrecomplete.prec (inferInstance : IsPrecomplete (maximalIdeal A) A) (hcauchy e)
    let L' : MvPowerSeries σ A := fun e ↦ L e
    refine ⟨L', fun n ↦ ?_⟩
    rw [SModEq.sub_mem, hpow, pow_maximalIdeal_eq_powFiltration]
    intro e
    rw [map_sub, show coeff e L' = L e from rfl]
    by_cases hn : n ≤ e.degree
    · rw [Nat.sub_eq_zero_of_le hn, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · have := SModEq.sub_mem.1 (hL e (n - e.degree))
      rw [hpowA, Nat.sub_add_cancel (not_le.1 hn).le] at this
      exact this

end Finite

end SGA.SGA1.ExposeIII
