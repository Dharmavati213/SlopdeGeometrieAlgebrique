/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.MvPolynomial
import SGA.SGA1.ExposeXII.SimpleRoot
import SGA.SGA1.ExposeXII.EntirePolynomial
import SGA.SGA1.ExposeXII.PolynomialLines
import SGA.SGA1.ExposeXII.RootFunctions

/-!
# SGA 1, Exposé XII, 2.4: connectedness of the root locus of an irreducible polynomial

Let `P ∈ ℂ[z₁, …, zₙ][T]` be monic and irreducible and `h ≠ 0` a polynomial in `z` such that
`P(z, ·)` has simple roots when `h(z) ≠ 0`. The root locus
`Σ = {(z, t) ∈ ℂⁿ × ℂ | h(z) ≠ 0, P(z, t) = 0}` is connected
(`RootLocus.isPreconnected_rootLocus`). This is the analytic core of XII.2.4 (an irreducible
variety has connected space of complex points), avoiding GAGA:

given a clopen subset `U ⊆ Σ`, the polynomial `∏_{(z, t) ∈ U} (T - t)` (`RootLocus.piU`) is
locally `∏ (T - rᵢ(z))` for continuous local roots `rᵢ` (`exists_local_piU`), so its coefficients
are complex differentiable along complex lines (`differentiableAt_coeff_piU`); they have
polynomial growth (Cauchy's bound), hence are polynomials along lines (Riemann's removable
singularities and Liouville, `exists_polynomial_of_differentiableOn`), hence polynomials
(`exists_mvPolynomial_eq_of_forall_line`). This gives a factorization `P = Π_U · Π_{Uᶜ}` in
`ℂ[z][T]` (`exists_eq_mul`), so `U = ∅` or `U = Σ` by irreducibility.
-/

open Polynomial Filter Topology Set Metric

namespace SGA.SGA1.ExposeXII

namespace RootLocus

variable {n : ℕ}

/-- The polynomial `P(z, ·)` for `P ∈ ℂ[z₁, …, zₙ][T]` and `z ∈ ℂⁿ`. -/
noncomputable abbrev specAt (P : (MvPolynomial (Fin n) ℂ)[X]) (z : Fin n → ℂ) : ℂ[X] :=
  P.map (MvPolynomial.eval z)

/-- The root locus `{(z, t) | h(z) ≠ 0, P(z, t) = 0}` in `ℂⁿ × ℂ`. -/
def rootLocus (P : (MvPolynomial (Fin n) ℂ)[X]) (h : MvPolynomial (Fin n) ℂ) :
    Set ((Fin n → ℂ) × ℂ) :=
  {x | MvPolynomial.eval x.1 h ≠ 0 ∧ (specAt P x.1).IsRoot x.2}

section

variable {P : (MvPolynomial (Fin n) ℂ)[X]} (hP : P.Monic) {h : MvPolynomial (Fin n) ℂ}
  (hs : ∀ z, MvPolynomial.eval z h ≠ 0 → ∀ t, (specAt P z).IsRoot t →
    (specAt P z).derivative.eval t ≠ 0)

include hP

lemma monic_specAt (z : Fin n → ℂ) : (specAt P z).Monic := hP.map _

lemma natDegree_specAt (z : Fin n → ℂ) : (specAt P z).natDegree = P.natDegree :=
  hP.natDegree_map _

lemma card_rootsF_le (z : Fin n → ℂ) : (specAt P z).roots.toFinset.card ≤ P.natDegree :=
  (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_specAt hP z).le)

include hs

lemma nodup_roots {z : Fin n → ℂ} (hz : MvPolynomial.eval z h ≠ 0) : (specAt P z).roots.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro t
  rw [count_roots]
  by_contra H
  push Not at H
  have := (one_lt_rootMultiplicity_iff_isRoot (monic_specAt hP z).ne_zero).mp H
  exact hs z hz t this.1 this.2

lemma prod_roots_eq {z : Fin n → ℂ} (hz : MvPolynomial.eval z h ≠ 0) :
    ∏ t ∈ (specAt P z).roots.toFinset, (X - C t) = specAt P z := by
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, (nodup_roots hP hs hz).dedup]
  exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_specAt hP z)
    IsAlgClosed.card_roots_eq_natDegree

lemma card_rootsF {z : Fin n → ℂ} (hz : MvPolynomial.eval z h ≠ 0) :
    (specAt P z).roots.toFinset.card = P.natDegree := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hP hs hz),
    IsAlgClosed.card_roots_eq_natDegree, natDegree_specAt hP]

/-- Near a point `z₀` with `h(z₀) ≠ 0`, the roots of `P(z, ·)` are given by continuous functions. -/
lemma exists_local_roots {z₀ : Fin n → ℂ} (hz₀ : MvPolynomial.eval z₀ h ≠ 0) :
    ∃ (r : ℂ → (Fin n → ℂ) → ℂ) (δ : ℝ), 0 < δ ∧
      (∀ z ∈ ball z₀ δ, MvPolynomial.eval z h ≠ 0) ∧
      (∀ t ∈ (specAt P z₀).roots.toFinset, ContinuousOn (r t) (ball z₀ δ)) ∧
      (∀ t ∈ (specAt P z₀).roots.toFinset, r t z₀ = t) ∧
      (∀ z ∈ ball z₀ δ, Set.InjOn (fun t ↦ r t z) (specAt P z₀).roots.toFinset) ∧
      (∀ z ∈ ball z₀ δ, (specAt P z).roots.toFinset =
        (specAt P z₀).roots.toFinset.image (fun t ↦ r t z)) := by
  classical
  set S₀ := (specAt P z₀).roots.toFinset with hS₀
  have hroot (t : ℂ) (ht : t ∈ S₀) : (specAt P z₀).IsRoot t := by
    rw [Multiset.mem_toFinset, mem_roots (monic_specAt hP z₀).ne_zero] at ht
    exact ht
  have key (t : ℂ) (ht : t ∈ S₀) := exists_continuousOn_simpleRoot (specAt P)
    (monic_specAt hP) (natDegree_specAt hP)
    (fun i ↦ by
      simp only [coeff_map]
      exact MvPolynomial.continuous_eval _)
    (hroot t ht) (hs z₀ hz₀ t (hroot t ht))
  choose! Ut Vt hUo hVo hz₀U htV rt hrc hrmaps hruniq using key
  have hr0 (t : ℂ) (ht : t ∈ S₀) : rt t z₀ = t :=
    (hruniq t ht z₀ (hz₀U t ht) t (htV t ht)).mp (hroot t ht)
  have hrca (t : ℂ) (ht : t ∈ S₀) : ContinuousAt (rt t) z₀ :=
    (hrc t ht).continuousAt ((hUo t ht).mem_nhds (hz₀U t ht))
  have e1 : ∀ᶠ z in 𝓝 z₀, ∀ t ∈ S₀, z ∈ Ut t :=
    (eventually_all_finset S₀).mpr fun t ht ↦ (hUo t ht).mem_nhds (hz₀U t ht)
  have e2 : ∀ᶠ z in 𝓝 z₀, ∀ t ∈ S₀, ∀ t' ∈ S₀, t ≠ t' → rt t z ≠ rt t' z :=
    (eventually_all_finset S₀).mpr fun t ht ↦ (eventually_all_finset S₀).mpr fun t' ht' ↦ by
      by_cases htt : t = t'
      · exact Eventually.of_forall fun _ h' ↦ (h' htt).elim
      · have hc : ContinuousAt (fun z ↦ rt t z - rt t' z) z₀ := (hrca t ht).sub (hrca t' ht')
        have := hc.eventually_ne (by
          rw [hr0 t ht, hr0 t' ht']; exact sub_ne_zero.mpr htt)
        filter_upwards [this] with z hz _
        exact sub_ne_zero.mp hz
  have e3 : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval z h ≠ 0 :=
    (MvPolynomial.continuous_eval h).continuousAt.eventually_ne hz₀
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (e1.and (e2.and e3))
  refine ⟨rt, δ, hδ, fun z hz ↦ (hball z hz).2.2, fun t ht ↦ (hrc t ht).mono fun z hz ↦
    (hball z hz).1 t ht, hr0, fun z hz t ht t' ht' htt ↦ ?_, fun z hz ↦ ?_⟩
  · by_contra hne
    exact (hball z hz).2.1 t ht t' ht' hne htt
  · have hsub : S₀.image (fun t ↦ rt t z) ⊆ (specAt P z).roots.toFinset := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      rw [Multiset.mem_toFinset, mem_roots (monic_specAt hP z).ne_zero]
      exact (hruniq t ht z ((hball z hz).1 t ht) (rt t z)
        (hrmaps t ht ((hball z hz).1 t ht))).mpr rfl
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [Finset.card_image_of_injOn fun t ht t' ht' htt ↦ by
      by_contra hne; exact (hball z hz).2.1 t ht t' ht' hne htt]
    rw [card_rootsF hP hs (hball z hz).2.2, card_rootsF hP hs hz₀]

/-- A point `(z, t)` lies in the subset `U` of the root locus. -/
def InU (U : Set (rootLocus P h)) (z : Fin n → ℂ) (t : ℂ) : Prop :=
  ∃ hx : (z, t) ∈ rootLocus P h, (⟨(z, t), hx⟩ : rootLocus P h) ∈ U

open scoped Classical in
/-- `∏ (T - t)` over the roots `t` of `P(z, ·)` with `(z, t) ∈ U`. -/
noncomputable def piU (U : Set (rootLocus P h)) (z : Fin n → ℂ) : ℂ[X] :=
  ∏ t ∈ (specAt P z).roots.toFinset.filter (InU U z), (X - C t)

omit hs in
open scoped Classical in
lemma natDegree_piU_le (U : Set (rootLocus P h)) (z : Fin n → ℂ) :
    (piU U z).natDegree ≤ P.natDegree := by
  rw [piU, natDegree_finsetProd_X_sub_C_eq_card]
  exact (Finset.card_filter_le _ _).trans (card_rootsF_le hP z)

omit hP hs in
/-- Near a point `z₀`, `(z, rₜ(z)) ∈ U` if and only if `(z₀, t) ∈ U`, for `U` clopen. -/
lemma inU_iff_of_isClopen {U : Set (rootLocus P h)} (hU : IsClopen U) {z₀ : Fin n → ℂ} {δ : ℝ}
    (hW : ∀ z ∈ ball z₀ δ, MvPolynomial.eval z h ≠ 0) {r : (Fin n → ℂ) → ℂ}
    (hr : ContinuousOn r (ball z₀ δ)) (hroot : ∀ z ∈ ball z₀ δ, (specAt P z).IsRoot (r z))
    (hz₀ : 0 < δ) {z : Fin n → ℂ} (hz : z ∈ ball z₀ δ) :
    InU U z (r z) ↔ InU U z₀ (r z₀) := by
  let B := ball z₀ δ
  have : PreconnectedSpace B :=
    isPreconnected_iff_preconnectedSpace.mp (convex_ball z₀ δ).isPreconnected
  let φ : B → rootLocus P h := fun y ↦ ⟨(y.1, r y.1), hW y.1 y.2, hroot y.1 y.2⟩
  have hφ : Continuous φ := (continuous_subtype_val.prodMk
    (hr.comp_continuous continuous_subtype_val fun y ↦ y.2)).subtype_mk _
  have hiff (y : B) : InU U y.1 (r y.1) ↔ φ y ∈ U :=
    ⟨fun ⟨_, hy⟩ ↦ hy, fun hy ↦ ⟨_, hy⟩⟩
  rw [show z = (⟨z, hz⟩ : B).1 from rfl, show z₀ = (⟨z₀, mem_ball_self hz₀⟩ : B).1 from rfl,
    hiff, hiff]
  rcases isClopen_iff.mp (hU.preimage hφ) with h0 | h1
  · simp only [Set.ext_iff, mem_preimage, mem_empty_iff_false, iff_false] at h0
    simp [h0]
  · simp only [Set.ext_iff, mem_preimage, mem_univ, iff_true] at h1
    simp [h1]

/-- The local form of `piU`: near `z₀`, it is `∏ (T - rₜ(z))` over the roots `t` of `P(z₀, ·)`
with `(z₀, t) ∈ U`. -/
lemma exists_local_piU {U : Set (rootLocus P h)} (hU : IsClopen U) {z₀ : Fin n → ℂ}
    (hz₀ : MvPolynomial.eval z₀ h ≠ 0) :
    ∃ (r : ℂ → (Fin n → ℂ) → ℂ) (δ : ℝ), 0 < δ ∧
      (∀ z ∈ ball z₀ δ, MvPolynomial.eval z h ≠ 0) ∧
      (∀ t ∈ (specAt P z₀).roots.toFinset, ContinuousOn (r t) (ball z₀ δ)) ∧
      (∀ t ∈ (specAt P z₀).roots.toFinset, r t z₀ = t) ∧
      (∀ t ∈ (specAt P z₀).roots.toFinset, ∀ z ∈ ball z₀ δ, (specAt P z).IsRoot (r t z)) ∧
      ∃ I ⊆ (specAt P z₀).roots.toFinset,
        ∀ z ∈ ball z₀ δ, piU U z = ∏ t ∈ I, (X - C (r t z)) := by
  open scoped Classical in
  obtain ⟨r, δ, hδ, hW, hrc, hr0, hinj, himage⟩ := exists_local_roots hP hs hz₀
  have hroot (t) (ht : t ∈ (specAt P z₀).roots.toFinset) (z) (hz : z ∈ ball z₀ δ) :
      (specAt P z).IsRoot (r t z) := by
    have : r t z ∈ (specAt P z).roots.toFinset := by
      rw [himage z hz]; exact Finset.mem_image_of_mem _ ht
    rw [Multiset.mem_toFinset, mem_roots (monic_specAt hP z).ne_zero] at this
    exact this
  refine ⟨r, δ, hδ, hW, hrc, hr0, hroot,
    (specAt P z₀).roots.toFinset.filter (InU U z₀), Finset.filter_subset _ _, fun z hz ↦ ?_⟩
  rw [piU, himage z hz, Finset.filter_image, Finset.prod_image]
  · refine Finset.prod_congr (Finset.filter_congr fun t ht ↦ ?_) fun _ _ ↦ rfl
    have := inU_iff_of_isClopen hU hW (hrc t ht) (hroot t ht) hδ hz
    rw [hr0 t ht] at this
    exact this
  · exact fun t ht t' ht' htt ↦ hinj z hz (Finset.mem_of_mem_filter _ ht)
      (Finset.mem_of_mem_filter _ ht') htt

/-- The coefficients of `piU U (a + s • v)` are complex differentiable in `s` where
`h(a + s • v) ≠ 0`. -/
lemma differentiableAt_coeff_piU {U : Set (rootLocus P h)} (hU : IsClopen U) (a v : Fin n → ℂ)
    {s₀ : ℂ} (hs₀ : MvPolynomial.eval (a + s₀ • v) h ≠ 0) (m : ℕ) :
    DifferentiableAt ℂ (fun s ↦ (piU U (a + s • v)).coeff m) s₀ := by
  set z₀ := a + s₀ • v
  obtain ⟨r, δ, hδ, hW, hrc, hr0, hroot, I, hI, hloc⟩ := exists_local_piU hP hs hU hs₀
  have hℓ : Continuous fun s : ℂ ↦ a + s • v :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hev : ∀ᶠ s in 𝓝 s₀, a + s • v ∈ ball z₀ δ :=
    hℓ.continuousAt.preimage_mem_nhds (ball_mem_nhds z₀ hδ)
  have hρ (t : ℂ) (ht : t ∈ I) : DifferentiableAt ℂ (fun s ↦ r t (a + s • v)) s₀ := by
    have ht' := hI ht
    refine differentiableAt_of_isRoot (p := fun s ↦ specAt P (a + s • v)) (d := P.natDegree)
      (fun s ↦ (natDegree_specAt hP _).le) (fun k ↦ ?_) ?_ ?_ ?_
    · have : (fun s ↦ (specAt P (a + s • v)).coeff k) =
          fun s ↦ (lineRestrict (P.coeff k) a v).eval s := by
        funext s
        rw [coeff_map, eval_lineRestrict]
      rw [this]
      exact Polynomial.differentiableAt _
    · exact ((hrc t ht').continuousAt (isOpen_ball.mem_nhds (mem_ball_self hδ))).comp
        hℓ.continuousAt
    · filter_upwards [hev] with s hs
      exact hroot t ht' _ hs
    · change (specAt P z₀).derivative.eval (r t z₀) ≠ 0
      rw [hr0 t ht']
      refine hs z₀ hs₀ t ?_
      rw [Multiset.mem_toFinset, mem_roots (monic_specAt hP z₀).ne_zero] at ht'
      exact ht'
  have heq : (fun s ↦ (piU U (a + s • v)).coeff m) =ᶠ[𝓝 s₀]
      fun s ↦ (∏ t ∈ I, (X - C (r t (a + s • v)))).coeff m := by
    filter_upwards [hev] with s hs
    rw [hloc _ hs]
  exact (differentiableAt_coeff_prod_X_sub_C I hρ m).congr_of_eventuallyEq heq

omit hs in
/-- Polynomial growth of the coefficients of `piU U` along a line. -/
lemma exists_norm_coeff_piU_le (U : Set (rootLocus P h)) (a v : Fin n → ℂ) : ∃ C : ℝ, ∀ s : ℂ,
    ∀ m, ‖(piU U (a + s • v)).coeff m‖ ≤ C * (1 + ‖s‖) ^
      ((∑ i ∈ Finset.range P.natDegree, (P.coeff i).totalDegree) * P.natDegree) := by
  classical
  set M := ∑ i ∈ Finset.range P.natDegree, (P.coeff i).totalDegree
  have hC (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      ‖MvPolynomial.eval (a + s • v) (P.coeff i)‖ ≤ C * (1 + ‖s‖) ^ (P.coeff i).totalDegree := by
    obtain ⟨C, hC⟩ := exists_norm_eval_line_le (P.coeff i) a v
    refine ⟨C, ?_, hC⟩
    have := (norm_nonneg _).trans (hC 0)
    simpa using this
  choose C hC0 hC using hC
  set K := ∑ i ∈ Finset.range P.natDegree, C i
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ ↦ hC0 i
  refine ⟨(2 + K) ^ P.natDegree, fun s m ↦ ?_⟩
  set z := a + s • v
  have h1 : (1 : ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hR : 2 + ∑ i ∈ Finset.range P.natDegree, ‖(specAt P z).coeff i‖ ≤
      (2 + K) * (1 + ‖s‖) ^ M := by
    have : ∑ i ∈ Finset.range P.natDegree, ‖(specAt P z).coeff i‖ ≤ K * (1 + ‖s‖) ^ M := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [coeff_map]
      refine (hC i s).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ h1 (Finset.single_le_sum (f := fun i ↦ (P.coeff i).totalDegree)
          (fun _ _ ↦ Nat.zero_le _) hi)) (hC0 i))
    have h2 : (1 : ℝ) ≤ (1 + ‖s‖) ^ M := one_le_pow₀ h1
    nlinarith
  have hroots : ∀ t ∈ (specAt P z).roots.toFinset, 1 + ‖t‖ ≤ (2 + K) * (1 + ‖s‖) ^ M := by
    intro t ht
    rw [Multiset.mem_toFinset, mem_roots (monic_specAt hP z).ne_zero] at ht
    have := norm_le_of_isRoot_of_monic (monic_specAt hP z) ht
    rw [natDegree_specAt hP] at this
    linarith
  calc ‖(piU U z).coeff m‖
      ≤ ∏ t ∈ (specAt P z).roots.toFinset.filter (InU U z), (1 + ‖t‖) := by
        rw [piU]
        exact norm_coeff_prod_X_sub_C_le _ id m
    _ ≤ ∏ t ∈ (specAt P z).roots.toFinset.filter (InU U z), ((2 + K) * (1 + ‖s‖) ^ M) :=
        Finset.prod_le_prod (fun t _ ↦ by positivity)
          fun t ht ↦ hroots t (Finset.mem_of_mem_filter t ht)
    _ = ((2 + K) * (1 + ‖s‖) ^ M) ^ ((specAt P z).roots.toFinset.filter (InU U z)).card :=
        Finset.prod_const _
    _ ≤ ((2 + K) * (1 + ‖s‖) ^ M) ^ P.natDegree := by
        refine pow_le_pow_right₀ ?_ ((Finset.card_filter_le _ _).trans (card_rootsF_le hP z))
        have h2 : (1 : ℝ) ≤ (1 + ‖s‖) ^ M := one_le_pow₀ h1
        nlinarith
    _ = (2 + K) ^ P.natDegree * (1 + ‖s‖) ^ (M * P.natDegree) := by
        rw [mul_pow, ← pow_mul]

/-- The coefficients of `piU U` are polynomial functions of `z` on `{h ≠ 0}`. -/
lemma exists_mvPolynomial_coeff_piU (hh : h ≠ 0) {U : Set (rootLocus P h)} (hU : IsClopen U)
    (m : ℕ) : ∃ G : MvPolynomial (Fin n) ℂ, ∀ z, MvPolynomial.eval z h ≠ 0 →
      (piU U z).coeff m = MvPolynomial.eval z G := by
  refine exists_mvPolynomial_eq_of_forall_line
    ((∑ i ∈ Finset.range P.natDegree, (P.coeff i).totalDegree) * P.natDegree) h hh
    (fun z ↦ (piU U z).coeff m) fun a v ha ↦ ?_
  have hfin := finite_setOf_eval_line_eq_zero ha v
  obtain ⟨C, hC⟩ := exists_norm_coeff_piU_le hP U a v
  have hdiff : DifferentiableOn ℂ (fun s ↦ (piU U (a + s • v)).coeff m)
      ((hfin.toFinset : Set ℂ))ᶜ := by
    intro s hsE
    have hne : MvPolynomial.eval (a + s • v) h ≠ 0 := by simpa using hsE
    exact (differentiableAt_coeff_piU hP hs hU a v hne m).differentiableWithinAt
  obtain ⟨q, hq, hFq⟩ := exists_polynomial_of_differentiableOn hfin.toFinset hdiff
    (fun s _ ↦ hC s m)
  exact ⟨q, hq, fun s hne ↦ hFq s (by simpa using hne)⟩

/-- There is `Π_U ∈ ℂ[z][T]` with `Π_U(z, ·) = piU U z` on `{h ≠ 0}`. -/
lemma exists_polynomial_piU (hh : h ≠ 0) {U : Set (rootLocus P h)} (hU : IsClopen U) :
    ∃ Q : (MvPolynomial (Fin n) ℂ)[X], ∀ z, MvPolynomial.eval z h ≠ 0 →
      Q.map (MvPolynomial.eval z) = piU U z := by
  choose G hG using exists_mvPolynomial_coeff_piU hP hs hh hU
  refine ⟨∑ m ∈ Finset.range (P.natDegree + 1), monomial m (G m), fun z hz ↦ ?_⟩
  ext m
  rw [coeff_map, finsetSum_coeff]
  simp only [coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hm
  · exact (hG m z hz).symm
  · rw [map_zero, coeff_eq_zero_of_natDegree_lt]
    exact (natDegree_piU_le hP U z).trans_lt (by omega)

open scoped Classical in
lemma piU_mul_piU_compl {U : Set (rootLocus P h)} {z : Fin n → ℂ}
    (hz : MvPolynomial.eval z h ≠ 0) : piU U z * piU Uᶜ z = specAt P z := by
  rw [piU, piU]
  conv_rhs => rw [← prod_roots_eq hP hs hz,
    ← Finset.prod_filter_mul_prod_filter_not (specAt P z).roots.toFinset (InU U z)]
  congr 1
  refine Finset.prod_congr (Finset.filter_congr fun t ht ↦ ?_) fun _ _ ↦ rfl
  rw [Multiset.mem_toFinset, mem_roots (monic_specAt hP z).ne_zero] at ht
  have hx : (z, t) ∈ rootLocus P h := ⟨hz, ht⟩
  exact ⟨fun ⟨_, h'⟩ h'' ↦ h' h''.2, fun h' ↦ ⟨hx, fun h'' ↦ h' ⟨hx, h''⟩⟩⟩

/-- `P = Π_U · Π_{Uᶜ}` for a clopen subset `U` of the root locus. -/
lemma exists_eq_mul (hh : h ≠ 0) {U : Set (rootLocus P h)} (hU : IsClopen U) :
    ∃ Q Q' : (MvPolynomial (Fin n) ℂ)[X], P = Q * Q' ∧
      (∀ z, MvPolynomial.eval z h ≠ 0 → Q.map (MvPolynomial.eval z) = piU U z) ∧
      (∀ z, MvPolynomial.eval z h ≠ 0 → Q'.map (MvPolynomial.eval z) = piU Uᶜ z) := by
  obtain ⟨Q, hQ⟩ := exists_polynomial_piU hP hs hh hU
  obtain ⟨Q', hQ'⟩ := exists_polynomial_piU hP hs hh hU.compl
  refine ⟨Q, Q', ?_, hQ, hQ'⟩
  rw [← sub_eq_zero]
  refine Polynomial.ext fun m ↦ ?_
  rw [coeff_zero]
  set c := (P - Q * Q').coeff m
  have hc (z : Fin n → ℂ) (hz : MvPolynomial.eval z h ≠ 0) : MvPolynomial.eval z c = 0 := by
    have := congrArg (fun p ↦ p.coeff m) (congrArg (Polynomial.map (MvPolynomial.eval z))
      (show P - Q * Q' = P - Q * Q' from rfl))
    simp only [c, ← coeff_map, Polynomial.map_sub, Polynomial.map_mul, hQ z hz, hQ' z hz,
      piU_mul_piU_compl hP hs hz, sub_self, coeff_zero]
  have hch : c * h = 0 := MvPolynomial.funext fun z ↦ by
    rw [map_mul, map_zero]
    by_cases hz : MvPolynomial.eval z h = 0
    · rw [hz, mul_zero]
    · rw [hc z hz, zero_mul]
  exact (mul_eq_zero.mp hch).resolve_right hh

omit hs in
open scoped Classical in
lemma eq_empty_of_isUnit {U : Set (rootLocus P h)} {Q : (MvPolynomial (Fin n) ℂ)[X]}
    (hQ : ∀ z, MvPolynomial.eval z h ≠ 0 → Q.map (MvPolynomial.eval z) = piU U z)
    (hu : IsUnit Q) : U = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun ⟨⟨z, t⟩, hz, ht⟩ hx ↦ ?_
  have hunit : IsUnit (piU U z) := hQ z hz ▸ hu.map (Polynomial.mapRingHom (MvPolynomial.eval z))
  have hdeg := natDegree_eq_zero_of_isUnit hunit
  rw [piU, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_eq_zero] at hdeg
  have : t ∈ (specAt P z).roots.toFinset.filter (InU U z) := by
    rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots (monic_specAt hP z).ne_zero]
    exact ⟨ht, ⟨hz, ht⟩, hx⟩
  rw [hdeg] at this
  exact Finset.notMem_empty t this

omit hs

/-- **XII.2.4, analytic core.** Let `P ∈ ℂ[z₁, …, zₙ][T]` be monic and irreducible, and `h ≠ 0` a
polynomial such that `P(z, ·)` has simple roots when `h(z) ≠ 0`. Then the root locus
`{(z, t) ∈ ℂⁿ × ℂ | h(z) ≠ 0, P(z, t) = 0}` is connected (preconnected). Given a clopen subset
`U`, the polynomial `∏_{(z, t) ∈ U} (T - t)` has coefficients which are complex analytic along
lines, of polynomial growth, hence polynomials (Riemann's removable singularities and Liouville);
this gives a factorization of `P`. -/
theorem isPreconnected_rootLocus (hs : ∀ z, MvPolynomial.eval z h ≠ 0 → ∀ t,
      (specAt P z).IsRoot t → (specAt P z).derivative.eval t ≠ 0)
    (hirr : Irreducible P) (hh : h ≠ 0) : IsPreconnected (rootLocus P h) := by
  rw [isPreconnected_iff_preconnectedSpace, preconnectedSpace_iff_clopen]
  intro U hU
  obtain ⟨Q, Q', hPQ, hQ, hQ'⟩ := exists_eq_mul hP hs hh hU
  rcases hirr.isUnit_or_isUnit hPQ with hu | hu
  · exact Or.inl (eq_empty_of_isUnit hP hQ hu)
  · exact Or.inr (compl_empty_iff.mp (eq_empty_of_isUnit hP hQ' hu))

end

end RootLocus

end SGA.SGA1.ExposeXII
