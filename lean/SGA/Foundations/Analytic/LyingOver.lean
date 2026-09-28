/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.GermEval
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Lying over for Weierstrass polynomials

Let `𝕜` be an algebraically closed complete field, `P` an ideal of `𝕜{z, y}` containing a
Weierstrass polynomial `ω = y^b - ∑ aₖ(z) yᵏ` (`aₖ(0) = 0`), and `Q = P ∩ 𝕜{z}`. Then every
point `z` of the zero set of `Q` close to `0` lifts to a point `(z, t)` of the zero set of `P`
close to `0` (`lyingOver`): the zero set of `P` maps onto the zero set of `Q` near `0`.

The proof ([Gunning–Rossi, *Analytic functions of several complex variables*, III.B],
[de Jong–Pfister, *Local analytic geometry*, 3.4]) reduces the generators `sᵢ` of `P` modulo `ω`
to polynomials `rᵢ(z, y)` of degree `< b` in `y`, and uses the resultant
`Res_y(ω, ∑ᵢ λ^{jᵢ} rᵢ) ∈ 𝕜{z}[λ]`, whose coefficients lie in `Q`: at a point `z` of the zero
set of `Q`, for every `λ` the polynomials `ω(z, y)` and `∑ λ^{jᵢ} rᵢ(z, y)` have a common root,
hence (as `𝕜` is infinite) some root `t` of `ω(z, y)` is a common root of all the `rᵢ(z, y)`;
the roots of `ω(z, y)` are small when `z` is small.
-/

open scoped NNReal ENNReal Topology
open Filter Finset

noncomputable section

namespace MvPowerSeries

/-! ### Two elementary lemmas -/

section Elementary

variable {𝕜 : Type*} [NormedField 𝕜]

/-- The roots of `y^b - ∑ cₖ yᵏ` are small when the coefficients `cₖ` are small. -/
lemma norm_lt_of_pow_eq_sum {b : ℕ} (hb : 1 ≤ b) {c : Fin b → 𝕜} {δ ε : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hε : ε * b < δ ^ b) (hc : ∀ k, ‖c k‖ ≤ ε) {t : 𝕜}
    (ht : t ^ b = ∑ k : Fin b, c k * t ^ (k : ℕ)) : ‖t‖ < δ := by
  have hsum : ‖t‖ ^ b ≤ ∑ k : Fin b, ε * ‖t‖ ^ (k : ℕ) := by
    rw [← norm_pow, ht]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    rw [norm_mul, norm_pow]
    gcongr
    exact hc k
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hc ⟨0, hb⟩)
  by_contra hge
  replace hge := not_lt.mp hge
  have hδb : δ ^ b ≤ 1 := pow_le_one₀ hδ.le hδ1
  rcases le_or_gt 1 ‖t‖ with h1 | h1
  · have h₂ : ∑ k : Fin b, ε * ‖t‖ ^ (k : ℕ) ≤ ∑ _k : Fin b, ε * ‖t‖ ^ (b - 1) :=
      Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ h1 (by have := k.2; omega)) hε0
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h₂
    have h₃ : ‖t‖ ^ b = ‖t‖ * ‖t‖ ^ (b - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hpos : 0 < ‖t‖ ^ (b - 1) := pow_pos (by linarith) _
    have h₄ : ‖t‖ * ‖t‖ ^ (b - 1) ≤ (b * ε) * ‖t‖ ^ (b - 1) := by
      rw [← h₃, mul_assoc]
      exact hsum.trans h₂
    have h₅ : ‖t‖ ≤ b * ε := le_of_mul_le_mul_right h₄ hpos
    linarith
  · have h₂ : ∑ k : Fin b, ε * ‖t‖ ^ (k : ℕ) ≤ ∑ _k : Fin b, ε :=
      Finset.sum_le_sum fun k _ ↦ by
        have : ‖t‖ ^ (k : ℕ) ≤ 1 := pow_le_one₀ (norm_nonneg _) h1.le
        nlinarith
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h₂
    have h₃ : δ ^ b ≤ ‖t‖ ^ b := pow_le_pow_left₀ hδ.le hge b
    linarith

/-- If for every `c` in an infinite field one of finitely many vectors `v t` satisfies
`∑ᵢ c^{jᵢ} v t i = 0` (with `j` injective), then one of the vectors vanishes. -/
lemma exists_forall_eq_zero_of_forall_exists [Infinite 𝕜] {ι : Type*} [Fintype ι] {j : ι → ℕ}
    (hj : Function.Injective j) (T : Finset 𝕜) (v : 𝕜 → ι → 𝕜)
    (h : ∀ c : 𝕜, ∃ t ∈ T, ∑ i, c ^ j i * v t i = 0) : ∃ t ∈ T, ∀ i, v t i = 0 := by
  classical
  by_contra! H
  let P : 𝕜 → Polynomial 𝕜 := fun t ↦ ∑ i, Polynomial.C (v t i) * Polynomial.X ^ j i
  have hP : ∀ t ∈ T, P t ≠ 0 := by
    intro t ht hPt
    obtain ⟨i, hi⟩ := H t ht
    apply hi
    have := congrArg (Polynomial.coeff · (j i)) hPt
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rwa [Finset.sum_eq_single i (fun i' _ hi' ↦ ite_eq_right fun h ↦ hi' (hj h.symm)) (by simp),
      ite_eq_left rfl] at this
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (T.biUnion fun t ↦ (P t).roots.toFinset)
  obtain ⟨t, ht, hct⟩ := h c
  apply hc
  rw [Finset.mem_biUnion]
  refine ⟨t, ht, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hP t ht), Polynomial.IsRoot.def]
  rw [Polynomial.eval_finsetSum, ← hct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]

end Elementary

/-! ### Weierstrass polynomials -/

section Weierstrass

variable {τ : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜]

omit [NontriviallyNormedField 𝕜] in
/-- The point `(z, t)` of `𝕜^{Option τ}`. -/
def optionPoint (z : τ → 𝕜) (t : 𝕜) : Option τ → 𝕜 := fun o ↦ o.elim t z

omit [NontriviallyNormedField 𝕜] in
@[simp] lemma optionPoint_none (z : τ → 𝕜) (t : 𝕜) : optionPoint z t none = t := rfl

omit [NontriviallyNormedField 𝕜] in
@[simp] lemma optionPoint_some (z : τ → 𝕜) (t : 𝕜) (i : τ) : optionPoint z t (some i) = z i :=
  rfl

variable (τ 𝕜) in
/-- The variable `y` of `𝕜{z, y}`. -/
abbrev yVar : convergent (Option τ) 𝕜 := ⟨X none, X_mem_convergent none⟩

/-- The polynomial `y^b - ∑_{k < b} aₖ(z) yᵏ` in `y` over `𝕜{z}`. -/
def weierstrassPoly {b : ℕ} (a : Fin b → convergent τ 𝕜) : convergent (Option τ) 𝕜 :=
  yVar τ 𝕜 ^ b - ∑ k : Fin b, algebraMap (convergent τ 𝕜) _ (a k) * yVar τ 𝕜 ^ (k : ℕ)

lemma coe_weierstrassPoly {b : ℕ} (a : Fin b → convergent τ 𝕜) :
    (weierstrassPoly a : MvPowerSeries (Option τ) 𝕜) =
      X none ^ b - ∑ k : Fin b, rename someEmb (a k).1 * X none ^ (k : ℕ) := by
  simp [weierstrassPoly, algebraMap_convergent_option]

lemma coeff_single_none_weierstrassPoly {b : ℕ} (a : Fin b → convergent τ 𝕜)
    (ha : ∀ k, constantCoeff (a k).1 = 0) (j : ℕ) :
    coeff (Finsupp.single none j) (weierstrassPoly a : MvPowerSeries (Option τ) 𝕜) =
      if j = b then 1 else 0 := by
  classical
  rw [coe_weierstrassPoly, map_sub, map_sum]
  have h₁ : ∀ k : Fin b, coeff (Finsupp.single none j)
      (rename someEmb (a k).1 * X none ^ (k : ℕ)) = 0 := fun k ↦ by
    rw [mul_comm, coeff_X_none_pow_mul_rename_some]
    split_ifs
    · rw [Finsupp.some_single_none, coeff_zero_eq_constantCoeff_apply, ha k]
    · rfl
  rw [Finset.sum_eq_zero fun k _ ↦ h₁ k, sub_zero, X_pow_eq, coeff_monomial]
  by_cases hj : j = b
  · simp [hj]
  · rw [ite_eq_right, ite_eq_right hj]
    intro h
    exact hj (by simpa using congrArg (fun α ↦ α none) h)

lemma isRegularOfOrder_weierstrassPoly {b : ℕ} (a : Fin b → convergent τ 𝕜)
    (ha : ∀ k, constantCoeff (a k).1 = 0) :
    IsRegularOfOrder b (weierstrassPoly a : MvPowerSeries (Option τ) 𝕜) := by
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [coeff_single_none_weierstrassPoly a ha, ite_eq_right hj.ne]
  · rw [coeff_single_none_weierstrassPoly a ha, ite_eq_left rfl]
    exact one_ne_zero

variable [Finite τ] [CompleteSpace 𝕜]

lemma germEval_algebraMap (c : convergent τ 𝕜) :
    germEval (Option τ) 𝕜 (algebraMap (convergent τ 𝕜) _ c) =
      Germ.coeRingHom _ (fun z ↦ tsumEval c.1 fun i ↦ z (some i)) := by
  rw [germEval_apply]
  congr 1
  funext z
  exact tsumEval_rename_some c.1 z

lemma germEval_yVar :
    germEval (Option τ) 𝕜 (yVar τ 𝕜) = Germ.coeRingHom _ (fun z ↦ z none) :=
  germEval_X none

/-- Near `0`, the value of a polynomial in `y` over `𝕜{z}`. -/
lemma eventually_tsumEval_poly {b : ℕ} (a : Fin b → convergent τ 𝕜) :
    ∀ᶠ z in 𝓝 (0 : Option τ → 𝕜), tsumEval (∑ k : Fin b,
      algebraMap (convergent τ 𝕜) (convergent (Option τ) 𝕜) (a k) * yVar τ 𝕜 ^ (k : ℕ)).1 z =
        ∑ k : Fin b, tsumEval (a k).1 (fun i ↦ z (some i)) * z none ^ (k : ℕ) := by
  have h : germEval (Option τ) 𝕜 (∑ k : Fin b,
      algebraMap (convergent τ 𝕜) (convergent (Option τ) 𝕜) (a k) * yVar τ 𝕜 ^ (k : ℕ)) =
      Germ.coeRingHom _ (∑ k : Fin b, (fun z : Option τ → 𝕜 ↦ tsumEval (a k).1
        fun i ↦ z (some i)) * (fun z : Option τ → 𝕜 ↦ z none) ^ (k : ℕ)) := by
    simp only [map_sum, map_mul, map_pow, germEval_algebraMap, germEval_yVar]
  filter_upwards [eventually_of_germEval_eq h] with z hz
  rw [hz]
  simp [Finset.sum_apply]

lemma eventually_tsumEval_weierstrassPoly {b : ℕ} (a : Fin b → convergent τ 𝕜) :
    ∀ᶠ z in 𝓝 (0 : Option τ → 𝕜), tsumEval (weierstrassPoly a).1 z =
      z none ^ b - ∑ k : Fin b, tsumEval (a k).1 (fun i ↦ z (some i)) * z none ^ (k : ℕ) := by
  have h : germEval (Option τ) 𝕜 (weierstrassPoly a) =
      Germ.coeRingHom _ ((fun z : Option τ → 𝕜 ↦ z none) ^ b - ∑ k : Fin b,
        (fun z : Option τ → 𝕜 ↦ tsumEval (a k).1 fun i ↦ z (some i)) *
          (fun z : Option τ → 𝕜 ↦ z none) ^ (k : ℕ)) := by
    simp only [weierstrassPoly, map_sub, map_sum, map_mul, map_pow, germEval_algebraMap,
      germEval_yVar]
  filter_upwards [eventually_of_germEval_eq h] with z hz
  rw [hz]
  simp [Finset.sum_apply]

end Weierstrass

/-! ### Lying over -/

section LyingOver

variable {τ : Type*} [Finite τ] {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- **Lying over for Weierstrass polynomials**: let `P ⊆ 𝕜{z, y}` be an ideal containing a
Weierstrass polynomial `ω = y^b - ∑ aₖ(z) yᵏ` (`aₖ(0) = 0`, `b ≥ 1`), `s` a finite family in `P`
and `sQ` a finite family generating an ideal containing `Q = P ∩ 𝕜{z}`. For every neighbourhood
`W` of `0`, every point `z` close to `0` of the zero set of `sQ` lifts to a point `(z, t) ∈ W` of
the zero set of `s`. -/
theorem lyingOver [IsAlgClosed 𝕜] {b : ℕ} (hb : 1 ≤ b) (a : Fin b → convergent τ 𝕜)
    (ha : ∀ k, constantCoeff (a k).1 = 0) {P : Ideal (convergent (Option τ) 𝕜)}
    (hω : weierstrassPoly a ∈ P) {ι : Type*} [Finite ι] (s : ι → convergent (Option τ) 𝕜)
    (hs : ∀ i, s i ∈ P) {κ : Type*} (sQ : κ → convergent τ 𝕜)
    (hsQ : P.comap (algebraMap (convergent τ 𝕜) (convergent (Option τ) 𝕜)) ≤
      Ideal.span (Set.range sQ))
    {W : Set (Option τ → 𝕜)} (hW : W ∈ 𝓝 (0 : Option τ → 𝕜)) :
    ∀ᶠ z in 𝓝 (0 : τ → 𝕜), ZeroLocus sQ z →
      ∃ t : 𝕜, optionPoint z t ∈ W ∧ ZeroLocus s (optionPoint z t) := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite τ
  set ω := weierstrassPoly a with hω_def
  have hreg := isRegularOfOrder_weierstrassPoly a ha
  /- Division of the generators by `ω`. -/
  choose q hq r hr hlow heq using fun i ↦ exists_weierstrassDiv ω.2 hreg (s i).2
  let qc : ι → convergent (Option τ) 𝕜 := fun i ↦ ⟨q i, hq i⟩
  let rc : ι → convergent (Option τ) 𝕜 := fun i ↦ ⟨r i, hr i⟩
  have hsqr : ∀ i, s i = ω * qc i + rc i := fun i ↦ Subtype.ext (heq i)
  have hrP : ∀ i, rc i ∈ P := fun i ↦ by
    have : rc i = s i - ω * qc i := by rw [hsqr i]; ring
    rw [this]
    exact P.sub_mem (hs i) (P.mul_mem_right _ hω)
  let y : ι → Fin b → convergent τ 𝕜 := fun i k ↦
    ⟨yCoeff k (r i), yCoeff_mem_convergent k (hr i)⟩
  have hry : ∀ i, rc i = ∑ k : Fin b,
      algebraMap (convergent τ 𝕜) (convergent (Option τ) 𝕜) (y i k) * yVar τ 𝕜 ^ (k : ℕ) :=
    fun i ↦ by
      apply Subtype.ext
      change r i = _
      rw [(hlow i).eq_sum, Finset.sum_range]
      simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
        algebraMap_convergent_option, coe_renameSomeHom]
      exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  /- A polydisc on which the coefficients converge. -/
  obtain ⟨ρ, hρ, hρF⟩ := exists_const_radius (σ := τ) (κ := Fin b ⊕ (ι × Fin b))
    (Sum.elim (fun k ↦ (a k).1) (fun p ↦ (y p.1 p.2).1)) (by
      rintro (k | p)
      · exact (a k).2
      · exact (y p.1 p.2).2)
  let R := polydisc τ 𝕜 (fun _ ↦ ρ)
  let aR : Fin b → R := fun k ↦ ⟨(a k).1, hρF (Sum.inl k)⟩
  let yR : ι → Fin b → R := fun i k ↦ ⟨(y i k).1, hρF (Sum.inr (i, k))⟩
  let incl : R →+* convergent τ 𝕜 :=
    { toFun f := ⟨f.1, fun _ ↦ ρ, fun _ ↦ hρ, f.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  /- The resultant. -/
  let j : ι → ℕ := fun i ↦ (Fintype.equivFin ι i : ℕ)
  have hj : Function.Injective j := fun i i' h ↦ (Fintype.equivFin ι).injective (Fin.ext h)
  let ωR : Polynomial R :=
    Polynomial.X ^ b - ∑ k : Fin b, Polynomial.C (aR k) * Polynomial.X ^ (k : ℕ)
  let ωΛ : Polynomial (Polynomial R) := ωR.map Polynomial.C
  let eΛ : Polynomial (Polynomial R) := ∑ i, ∑ k : Fin b,
    Polynomial.C (Polynomial.C (yR i k) * Polynomial.X ^ j i) * Polynomial.X ^ (k : ℕ)
  have hωdeg : ωΛ.natDegree ≤ b := by
    refine Polynomial.natDegree_map_le.trans ?_
    have h₁ : (∑ k : Fin b, Polynomial.C (aR k) * Polynomial.X ^ (k : ℕ)).natDegree ≤ b :=
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ ↦
        (Polynomial.natDegree_C_mul_X_pow_le _ _).trans k.2.le
    simpa using Polynomial.natDegree_sub_le_of_le (Polynomial.natDegree_X_pow_le b) h₁
  have hedeg : eΛ.natDegree ≤ b - 1 :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ ↦
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ ↦
        (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := k.2; omega)
  set Res := Polynomial.resultant ωΛ eΛ b (b - 1) with hRes
  /- The coefficients of the resultant lie in `Q`. -/
  let _ : CommRing (convergent (Option τ) 𝕜 ⧸ P) := Ideal.Quotient.commRing P
  let κ' : R →+* convergent (Option τ) 𝕜 ⧸ P := (Ideal.Quotient.mk P).comp
    ((algebraMap (convergent τ 𝕜) (convergent (Option τ) 𝕜)).comp incl)
  let yq : convergent (Option τ) 𝕜 ⧸ P := Ideal.Quotient.mk P (yVar τ 𝕜)
  let Θ : Polynomial (Polynomial R) →+* Polynomial (convergent (Option τ) 𝕜 ⧸ P) :=
    Polynomial.eval₂RingHom (Polynomial.mapRingHom κ') (Polynomial.C yq)
  have hΘω : Θ ωΛ = 0 := by
    have h₁ : Polynomial.eval₂ κ' yq ωR = Ideal.Quotient.mk P ω := by
      simp only [ωR, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, hω_def, weierstrassPoly, map_sub, map_pow,
        map_sum, map_mul, κ', yq, RingHom.comp_apply]
      rfl
    have h₂ : (Polynomial.mapRingHom κ').comp Polynomial.C = Polynomial.C.comp κ' :=
      RingHom.ext fun x ↦ by simp
    change Polynomial.eval₂ (Polynomial.mapRingHom κ') (Polynomial.C yq)
      (ωR.map Polynomial.C) = 0
    rw [Polynomial.eval₂_map, h₂, ← Polynomial.hom_eval₂, h₁,
      Ideal.Quotient.eq_zero_iff_mem.mpr hω, map_zero]
  have hΘe : Θ eΛ = 0 := by
    have h₁ : ∀ i, ∑ k : Fin b, κ' (yR i k) * yq ^ (k : ℕ) = 0 := fun i ↦ by
      have h := Ideal.Quotient.eq_zero_iff_mem.mpr (hrP i)
      rw [hry i, map_sum] at h
      simp only [map_mul, map_pow] at h
      exact h
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have h₂ : Θ (∑ k : Fin b, Polynomial.C (Polynomial.C (yR i k) * Polynomial.X ^ j i) *
        Polynomial.X ^ (k : ℕ)) =
        Polynomial.C (∑ k : Fin b, κ' (yR i k) * yq ^ (k : ℕ)) * Polynomial.X ^ j i := by
      simp only [Θ, map_sum, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_X_pow, Polynomial.coe_mapRingHom,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Polynomial.C_mul, Polynomial.C_pow]
      ring
    rw [h₂, h₁ i, map_zero, zero_mul]
  have hResmap : Res.map κ' = 0 := by
    obtain ⟨p, p', -, -, hpq⟩ :=
      Polynomial.exists_mul_add_mul_eq_C_resultant ωΛ eΛ hωdeg hedeg (Or.inl (by omega))
    have h := congrArg Θ hpq
    rw [map_add, map_mul, map_mul, hΘω, hΘe, zero_mul, zero_mul, add_zero] at h
    have h₃ : Θ (Polynomial.C Res) = Res.map κ' := by
      simp [Θ]
    rw [← h₃]
    exact h.symm
  have hResQ : ∀ n, incl (Res.coeff n) ∈
      P.comap (algebraMap (convergent τ 𝕜) (convergent (Option τ) 𝕜)) := fun n ↦ by
    have h := congrArg (Polynomial.coeff · n) hResmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h
    exact Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp h)
  /- Identities near `0` in `𝕜^{Option τ}`. -/
  have hE : ∀ᶠ z in 𝓝 (0 : Option τ → 𝕜), z ∈ W ∧
      tsumEval ω.1 z = z none ^ b -
        ∑ k : Fin b, tsumEval (a k).1 (fun i ↦ z (some i)) * z none ^ (k : ℕ) ∧
      (∀ i, tsumEval (s i).1 z = tsumEval ω.1 z * tsumEval (qc i).1 z + tsumEval (rc i).1 z) ∧
      (∀ i, tsumEval (rc i).1 z =
        ∑ k : Fin b, tsumEval (y i k).1 (fun i ↦ z (some i)) * z none ^ (k : ℕ)) := by
    have h₁ : ∀ i, ∀ᶠ z in 𝓝 (0 : Option τ → 𝕜), tsumEval (s i).1 z =
        tsumEval ω.1 z * tsumEval (qc i).1 z + tsumEval (rc i).1 z := fun i ↦ by
      rw [hsqr i]
      exact eventually_tsumEval_mul_add _ _ _
    have h₂ : ∀ i, ∀ᶠ z in 𝓝 (0 : Option τ → 𝕜), tsumEval (rc i).1 z =
        ∑ k : Fin b, tsumEval (y i k).1 (fun i ↦ z (some i)) * z none ^ (k : ℕ) := fun i ↦ by
      rw [hry i]
      exact eventually_tsumEval_poly (y i)
    filter_upwards [hW, eventually_tsumEval_weierstrassPoly a, eventually_all.mpr h₁,
      eventually_all.mpr h₂] with z h₀ h₁ h₂ h₃
    exact ⟨h₀, h₁, h₂, h₃⟩
  obtain ⟨δ, hδ, hδE⟩ := Metric.eventually_nhds_iff.mp hE
  set δ' : ℝ := min (δ / 2) 1 with hδ'_def
  have hδ' : 0 < δ' := lt_min (by linarith) one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'δ : δ' < δ := (min_le_left _ _).trans_lt (by linarith)
  set ε : ℝ := δ' ^ b / (2 * b) with hε_def
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hε : 0 < ε := div_pos (pow_pos hδ' b) (by linarith)
  have hεb : ε * b < δ' ^ b := by
    rw [hε_def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith [pow_pos hδ' b]
  /- Conditions on the point `z ∈ 𝕜^τ`. -/
  have hF₁ : ∀ᶠ z in 𝓝 (0 : τ → 𝕜), ∀ i, ‖z i‖ < δ' := by
    filter_upwards [Metric.ball_mem_nhds (0 : τ → 𝕜) hδ'] with z hz i
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact (norm_le_pi_norm z i).trans_lt hz
  have hF₃ : ∀ᶠ z in 𝓝 (0 : τ → 𝕜), ∀ k, ‖tsumEval (a k).1 z‖ ≤ ε := by
    refine eventually_all.mpr fun k ↦ ?_
    have hc := (analyticAt_tsumEval (a k).2).continuousAt
    rw [ContinuousAt, tsumEval_zero_eq_constantCoeff, ha k] at hc
    filter_upwards [hc (Metric.closedBall_mem_nhds 0 hε)] with z hz
    simpa using hz
  have hF₄ : ∀ᶠ z in 𝓝 (0 : τ → 𝕜), ZeroLocus sQ z →
      ∀ n ∈ Finset.range (Res.natDegree + 1), tsumEval (Res.coeff n).1 z = 0 := by
    have : ∀ n ∈ Finset.range (Res.natDegree + 1), ∀ᶠ z in 𝓝 (0 : τ → 𝕜),
        ZeroLocus sQ z → tsumEval (Res.coeff n).1 z = 0 := fun n _ ↦
      span_le_vanishingIdeal sQ (hsQ (hResQ n))
    filter_upwards [(eventually_all_finset _).mpr this] with z hz hZ n hn
    exact hz n hn hZ
  filter_upwards [hF₁, eventually_nnnorm_le_const (σ := τ) (𝕜 := 𝕜) hρ, hF₃, hF₄]
    with z h₁ h₂ h₃ h₄ hZ
  /- The Weierstrass polynomial at `z`. -/
  let ev : R →+* 𝕜 := evalPolydisc (fun _ ↦ ρ) z h₂
  set ω' : Polynomial 𝕜 := ωR.map ev with hω'_def
  have hω' : ω' = Polynomial.X ^ b -
      ∑ k : Fin b, Polynomial.C (tsumEval (a k).1 z) * Polynomial.X ^ (k : ℕ) := by
    simp only [hω'_def, ωR, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hω'monic : ω'.Monic := hω' ▸ Polynomial.monic_X_pow_sub (Polynomial.degree_sum_fin_lt _)
  have hω'nat : ω'.natDegree = b := by
    refine Polynomial.natDegree_eq_of_degree_eq_some ?_
    rw [hω', Polynomial.degree_sub_eq_left_of_degree_lt] <;>
      rw [Polynomial.degree_X_pow]
    exact Polynomial.degree_sum_fin_lt _
  /- For every `c`, `ω(z, ·)` and `∑ c^{jᵢ} rᵢ(z, ·)` have a common root. -/
  let v : 𝕜 → ι → 𝕜 := fun t i ↦ ∑ k : Fin b, tsumEval (y i k).1 z * t ^ (k : ℕ)
  have hcommon : ∀ c : 𝕜, ∃ t ∈ ω'.roots.toFinset, ∑ i, c ^ j i * v t i = 0 := by
    intro c
    let φ : Polynomial R →+* 𝕜 := Polynomial.eval₂RingHom ev c
    have h₅ : ωΛ.map φ = ω' := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext fun x ↦ by simp [φ]
    have h₆ : Polynomial.resultant ω' (eΛ.map φ) b (b - 1) = 0 := by
      rw [← h₅, Polynomial.resultant_map_map]
      change Polynomial.eval₂ ev c Res = 0
      rw [Polynomial.eval₂_eq_sum_range]
      refine Finset.sum_eq_zero fun n hn ↦ ?_
      rw [show ev (Res.coeff n) = 0 from h₄ hZ n hn, zero_mul]
    have h₇ := Polynomial.resultant_eq_prod_eval ω' (eΛ.map φ) (b - 1)
      (Polynomial.natDegree_map_le.trans hedeg) (IsAlgClosed.splits ω')
    rw [hω'nat, h₆, hω'monic.leadingCoeff, one_pow, one_mul] at h₇
    obtain ⟨t, ht, hte⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h₇.symm)
    refine ⟨t, Multiset.mem_toFinset.mpr ht, ?_⟩
    rw [← hte, Polynomial.eval_map]
    simp only [eΛ, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow, φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X_pow,
      v, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    change c ^ j i * (tsumEval (y i k).1 z * t ^ (k : ℕ)) = (ev (yR i k) * c ^ j i) * t ^ (k : ℕ)
    rw [show ev (yR i k) = tsumEval (y i k).1 z from rfl]
    ring
  obtain ⟨t, ht, hv⟩ := exists_forall_eq_zero_of_forall_exists hj _ v hcommon
  have hroot : Polynomial.eval t ω' = 0 :=
    (Polynomial.mem_roots hω'monic.ne_zero).mp (Multiset.mem_toFinset.mp ht)
  have hteq : t ^ b = ∑ k : Fin b, tsumEval (a k).1 z * t ^ (k : ℕ) := by
    rw [hω'] at hroot
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C] at hroot
    exact sub_eq_zero.mp hroot
  have htsmall : ‖t‖ < δ' := norm_lt_of_pow_eq_sum hb hδ' hδ'1 hεb h₃ hteq
  /- The lift `(z, t)`. -/
  have hball : dist (optionPoint z t) 0 < δ := by
    rw [dist_zero_right, pi_norm_lt_iff hδ]
    rintro (_ | i)
    · exact htsmall.trans hδ'δ
    · exact (h₁ i).trans hδ'δ
  obtain ⟨hW', hωz, hsz, hrz⟩ := hδE hball
  refine ⟨t, hW', fun i ↦ ?_⟩
  rw [hsz i, hωz, hrz i]
  have e : (fun i ↦ optionPoint z t (some i)) = z := rfl
  simp only [e, optionPoint_none]
  rw [← hteq, sub_self, zero_mul, zero_add]
  exact hv i

end LyingOver

end MvPowerSeries
