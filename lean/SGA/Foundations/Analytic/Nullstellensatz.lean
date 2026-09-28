/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.LyingOver
import SGA.Foundations.Analytic.LocalModel
import SGA.Foundations.Analytic.Stalk
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Rückert's Nullstellensatz

Let `𝕜` be an algebraically closed complete nontrivially normed field (e.g. `ℂ`). **Rückert's
Nullstellensatz**: if a convergent power series `h ∈ 𝕜{z₁, …, zₙ}` vanishes, near `0`, on the
common zero set of `s₁, …, sₘ ∈ 𝕜{z}`, then some power of `h` lies in the ideal `(s₁, …, sₘ)`
(`MvPowerSeries.mem_radical_of_eventually`). Equivalently, for a local model `Z(D) ⊆ 𝕜ⁿ` and a
point `x ∈ Z(D)`, a function analytic at `x` vanishing on `Z(D)` near `x` has nilpotent class in
the local ring `𝒪_{Z(D),x} = 𝒪_{𝕜ⁿ,x}/(f)`
(`AnalyticGeometry.LocalModelData.isNilpotent_classOf_of_eventually_eq_zero`).

## Proof

As the radical of an ideal is the intersection of the prime ideals containing it, it suffices to
show, for a prime ideal `P = (s₁, …, sₘ)` and `h ∉ P`, that `h` does not vanish identically on the
zero set of `P` near `0` (`MvPowerSeries.rueckertPrime`). We argue by induction on the number of
variables ([Gunning–Rossi, III.A–B], [de Jong–Pfister, *Local analytic geometry*, 3.4, 4.1]):

* if `P = 0` this is the identity theorem;
* otherwise, after a linear change of coordinates (`shearEquiv`), `P` contains an element regular in
  the last variable `y`, hence (Weierstrass preparation) a Weierstrass polynomial `ω`. The
  quotient `𝕜{z, y}/P` is finite over `𝕜{z}`, so `h` satisfies a monic equation
  `hᴺ + c_{N-1} hᴺ⁻¹ + ⋯ + c₀ ∈ P` over `𝕜{z}`; choosing `N` minimal, `c₀ ∉ Q = P ∩ 𝕜{z}` since `P`
  is prime and `h ∉ P`. By induction, `c₀` does not vanish identically on the zero set of `Q`
  near `0`; at such a point `z` with `c₀(z) ≠ 0`, the lying over theorem (`lyingOver`) provides a
  point `(z, t)` of the zero set of `P` close to `0`, at which `h(z, t) ≠ 0` since otherwise
  `c₀(z) = 0`.
-/

open scoped NNReal ENNReal Topology
open Filter Finset

noncomputable section

namespace MvPowerSeries

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-! ### The statement -/

variable (𝕜) in
/-- Rückert's Nullstellensatz for prime ideals of `𝕜{z_σ}`: a convergent power series not in a
prime ideal `P = (s₁, …, sₘ)` does not vanish identically on the zero set of `P` near `0`. -/
def RueckertPrime (σ : Type) [Fintype σ] : Prop :=
  ∀ (P : Ideal (convergent σ 𝕜)), P.IsPrime → ∀ (ι : Type) [Fintype ι]
    (s : ι → convergent σ 𝕜), Ideal.span (Set.range s) = P → ∀ h ∉ P,
      ∃ᶠ z in 𝓝 (0 : σ → 𝕜), ZeroLocus s z ∧ tsumEval h.1 z ≠ 0

/-! ### Changes of coordinates -/

/-- Frequent non-vanishing can be transported along a substitution `φ` with `φ(0) = 0`. -/
lemma frequently_of_substAnalytic {σ τ : Type} [Fintype σ] [Fintype τ]
    {φ : (τ → 𝕜) → σ → 𝕜} (hφ : AnalyticAt 𝕜 φ 0) (hφ0 : φ 0 = 0) {ι : Type} [Finite ι]
    (s : ι → convergent σ 𝕜) (h : convergent σ 𝕜)
    (H : ∃ᶠ w in 𝓝 (0 : τ → 𝕜), (∀ i, tsumEval (substAnalytic φ (s i).1) w = 0) ∧
      tsumEval (substAnalytic φ h.1) w ≠ 0) :
    ∃ᶠ z in 𝓝 (0 : σ → 𝕜), ZeroLocus s z ∧ tsumEval h.1 z ≠ 0 := by
  have hs : ∀ i, ∀ᶠ w in 𝓝 (0 : τ → 𝕜),
      tsumEval (s i).1 (φ w) = tsumEval (substAnalytic φ (s i).1) w := fun i ↦
    tsumEval_substAnalytic hφ hφ0 (s i).2
  have hh := tsumEval_substAnalytic hφ hφ0 h.2
  have H' : ∃ᶠ w in 𝓝 (0 : τ → 𝕜), ZeroLocus s (φ w) ∧ tsumEval h.1 (φ w) ≠ 0 := by
    refine H.mp ?_
    filter_upwards [eventually_all.mpr hs, hh] with w h₁ h₂ h₃
    refine ⟨fun i ↦ (h₁ i).trans (h₃.1 i), ?_⟩
    rw [h₂]
    exact h₃.2
  exact (Filter.frequently_map.mpr H').filter_mono (tendsto_zero_of_analyticAt hφ hφ0)

/-- `RueckertPrime` is invariant under changes of coordinates. -/
lemma rueckertPrime_of_equiv {σ τ : Type} [Fintype σ] [Fintype τ]
    (Φ : convergent σ 𝕜 ≃+* convergent τ 𝕜) {φ : (τ → 𝕜) → σ → 𝕜}
    (hφ : AnalyticAt 𝕜 φ 0) (hφ0 : φ 0 = 0) (hΦ : ∀ f, (Φ f).1 = substAnalytic φ f.1)
    (H : RueckertPrime 𝕜 τ) : RueckertPrime 𝕜 σ := by
  intro P hP ι _ s hs h hh
  have hP' : (P.map Φ).IsPrime := Ideal.map_isPrime_of_equiv Φ
  have hs' : Ideal.span (Set.range (Φ ∘ s)) = P.map Φ := by
    rw [Set.range_comp, ← Ideal.map_span, hs]
  have hh' : Φ h ∉ P.map Φ := by
    rw [Ideal.mem_map_of_equiv]
    rintro ⟨x, hx, hxh⟩
    exact hh (Φ.injective hxh ▸ hx)
  have := H _ hP' ι (Φ ∘ s) hs' (Φ h) hh'
  simp only [ZeroLocus, Function.comp_apply, hΦ] at this
  exact frequently_of_substAnalytic hφ hφ0 s h this

/-! ### The zero ideal -/

/-- **Identity theorem**: a non-zero convergent power series does not vanish identically near
`0`. -/
lemma frequently_tsumEval_ne_zero {σ : Type} [Finite σ] {h : convergent σ 𝕜} (hh : h ≠ 0) :
    ∃ᶠ z in 𝓝 (0 : σ → 𝕜), tsumEval h.1 z ≠ 0 := by
  by_contra H
  rw [not_frequently] at H
  exact hh (Subtype.ext (eq_zero_of_tsumEval_eventuallyEq_zero h.2 (H.mono fun z hz ↦ by
    simpa using hz)))

lemma frequently_of_eq_bot {σ : Type} [Finite σ] {ι : Type} (s : ι → convergent σ 𝕜)
    (hs : Ideal.span (Set.range s) = ⊥) {h : convergent σ 𝕜} (hh : h ≠ 0) :
    ∃ᶠ z in 𝓝 (0 : σ → 𝕜), ZeroLocus s z ∧ tsumEval h.1 z ≠ 0 := by
  have hs0 : ∀ i, s i = 0 := fun i ↦ by
    have : s i ∈ Ideal.span (Set.range s) := Ideal.subset_span ⟨i, rfl⟩
    rwa [hs, Ideal.mem_bot] at this
  refine (frequently_tsumEval_ne_zero hh).mono fun z hz ↦ ⟨fun i ↦ ?_, hz⟩
  rw [hs0 i]
  simp [tsumEval]

/-- In `𝕜{z_σ}` with no variables, every prime ideal is zero. -/
lemma eq_bot_of_isPrime_of_isEmpty {σ : Type} [IsEmpty σ] (P : Ideal (convergent σ 𝕜))
    [hP : P.IsPrime] : P = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  by_contra hf0
  have hunit : IsUnit f := by
    rw [isUnit_convergent_iff]
    intro h
    apply hf0
    rw [Ideal.mem_bot]
    apply Subtype.ext
    ext α
    rw [Subsingleton.elim α 0, coeff_zero_eq_constantCoeff_apply, h]
    rfl
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P hf hunit)

lemma rueckertPrime_of_isEmpty {σ : Type} [Fintype σ] [IsEmpty σ] : RueckertPrime 𝕜 σ := by
  intro P hP ι _ s hs h hh
  have hP0 := eq_bot_of_isPrime_of_isEmpty P
  refine frequently_of_eq_bot s (hs.trans hP0) ?_
  rintro rfl
  exact hh P.zero_mem

/-! ### The inductive step -/

section Step

variable [IsAlgClosed 𝕜]

omit [CompleteSpace 𝕜] [IsAlgClosed 𝕜] in
lemma constantCoeff_yCoeff {τ : Type} {r : MvPowerSeries (Option τ) 𝕜}
    (hr0 : ∀ j, coeff (Finsupp.single none j) r = 0) (k : ℕ) : constantCoeff (yCoeff k r) = 0 := by
  have e : (0 : τ →₀ ℕ).optionElim k = Finsupp.single none k := by
    ext o
    cases o <;> simp
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_yCoeff, e]
  exact hr0 k

/-- The inductive step of Rückert's Nullstellensatz: the case of a prime ideal containing an
element regular in the last variable. -/
theorem frequently_of_isRegularOfOrder {τ : Type} [Fintype τ] (H : RueckertPrime 𝕜 τ)
    {P : Ideal (convergent (Option τ) 𝕜)} [hP : P.IsPrime] {g : convergent (Option τ) 𝕜}
    (hgP : g ∈ P) {b : ℕ} (hreg : IsRegularOfOrder b g.1) {ι : Type} [Finite ι]
    (s : ι → convergent (Option τ) 𝕜) (hs : Ideal.span (Set.range s) = P)
    {h : convergent (Option τ) 𝕜} (hh : h ∉ P) :
    ∃ᶠ z in 𝓝 (0 : Option τ → 𝕜), ZeroLocus s z ∧ tsumEval h.1 z ≠ 0 := by
  classical
  /- A Weierstrass polynomial in `P`. -/
  obtain ⟨u, hu, -, r, hr, hlow, hr0, hgu⟩ := exists_weierstrassPreparation g.2 hreg
  let a : Fin b → convergent τ 𝕜 := fun k ↦ ⟨yCoeff k r, yCoeff_mem_convergent k hr⟩
  have ha : ∀ k, constantCoeff (a k).1 = 0 := fun k ↦ constantCoeff_yCoeff hr0 k
  have hωg : weierstrassPoly a = g * ⟨u, hu⟩ := by
    apply Subtype.ext
    rw [coe_weierstrassPoly, MulMemClass.coe_mul, hgu, hlow.eq_sum, Finset.sum_range]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have hωP : weierstrassPoly a ∈ P := hωg ▸ P.mul_mem_right _ hgP
  have hb : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0
      exfalso
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      simpa [weierstrassPoly] using hωP
    · exact hb0
  /- The ideal `Q = P ∩ 𝕜{z}` and its generators. -/
  set Q := P.comap (algebraMap (convergent τ 𝕜) (convergent (Option τ) 𝕜)) with hQ
  have hQprime : Q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian Q : Q.FG)
  let sQ : S → convergent τ 𝕜 := Subtype.val
  have hsQ : Ideal.span (Set.range sQ) = Q := by
    rw [← hS]
    congr 1
    ext x
    simp [sQ]
  /- `h` is integral over `𝕜{z}` modulo `P`: a monic equation of minimal degree. -/
  have hfin : Module.Finite (convergent τ 𝕜) (convergent (Option τ) 𝕜 ⧸ P) := by
    have h₁ := module_finite_quotient (weierstrassPoly a) (isRegularOfOrder_weierstrassPoly a ha)
    have hle : Ideal.span {weierstrassPoly a} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr hωP
    refine Module.Finite.of_surjective (Ideal.Quotient.factorₐ (convergent τ 𝕜) hle).toLinearMap
      fun x ↦ ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hex : ∃ N, ∃ p : Polynomial (convergent τ 𝕜), p.Monic ∧ p.natDegree = N ∧
      Polynomial.aeval h p ∈ P := by
    have : Algebra.IsIntegral (convergent τ 𝕜) (convergent (Option τ) 𝕜 ⧸ P) :=
      Algebra.IsIntegral.of_finite _ _
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := convergent τ 𝕜)
      (A := convergent (Option τ) 𝕜 ⧸ P) (Ideal.Quotient.mk P h)
    refine ⟨p.natDegree, p, hpm, rfl, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ (convergent τ 𝕜) P) h p
    rw [Ideal.Quotient.mkₐ_eq_mk] at e
    rw [← e, Polynomial.aeval_def]
    exact hp
  obtain ⟨p, hpm, hpN, hpP⟩ := Nat.find_spec hex
  have hN₀ : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hpN
    rw [Polynomial.eq_one_of_monic_natDegree_zero hpm hpN, map_one] at hpP
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr hpP)
  set c₀ := p.coeff 0 with hc₀_def
  have hc₀ : c₀ ∉ Q := by
    intro hc
    have hdecomp : Polynomial.aeval h p =
        h * Polynomial.aeval h p.divX + algebraMap _ _ c₀ := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add p]
      rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
    have h₁ : h * Polynomial.aeval h p.divX ∈ P := by
      have := P.sub_mem hpP (Ideal.mem_comap.mp hc)
      rwa [hdecomp, add_sub_cancel_right] at this
    have h₂ : Polynomial.aeval h p.divX ∈ P := (hP.mem_or_mem h₁).resolve_left hh
    have h₃ : p.divX.Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff,
        Polynomial.natDegree_divX_eq_natDegree_tsub_one, Polynomial.coeff_divX,
        Nat.sub_add_cancel (by omega)]
      exact hpm
    exact Nat.find_min hex (show p.divX.natDegree < Nat.find hex by
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hpN]
      omega) ⟨p.divX, h₃, rfl, h₂⟩
  /- By induction, `c₀` does not vanish identically on the zero set of `Q`. -/
  have HQ := H Q hQprime S sQ hsQ c₀ hc₀
  /- The equation of `h`, near `0`. -/
  have hF : ∀ᶠ z in 𝓝 (0 : Option τ → 𝕜), ZeroLocus s z →
      ∑ k ∈ Finset.range (p.natDegree + 1),
        tsumEval (p.coeff k).1 (fun i ↦ z (some i)) * tsumEval h.1 z ^ k = 0 := by
    have h₁ : Polynomial.aeval h p ∈ vanishingIdeal _ 𝕜 (ZeroLocus s) :=
      span_le_vanishingIdeal s (hs ▸ hpP)
    have h₂ : germEval (Option τ) 𝕜 (Polynomial.aeval h p) =
        Germ.coeRingHom _ (∑ k ∈ Finset.range (p.natDegree + 1),
          (fun z : Option τ → 𝕜 ↦ tsumEval (p.coeff k).1 fun i ↦ z (some i)) *
            tsumEval h.1 ^ k) := by
      rw [Polynomial.aeval_eq_sum_range]
      simp only [Algebra.smul_def, map_sum, map_mul, map_pow, germEval_algebraMap]
      simp only [germEval_apply]
    filter_upwards [h₁, eventually_of_germEval_eq h₂] with z hz₁ hz₂ hZ
    rw [← hz₁ hZ, hz₂]
    simp [Finset.sum_apply]
  /- Lying over. -/
  rw [Filter.frequently_iff]
  intro W hW
  have hLO := lyingOver hb a ha hωP s (fun i ↦ hs ▸ Ideal.subset_span ⟨i, rfl⟩) sQ hsQ.ge
    (inter_mem hW hF)
  obtain ⟨z', ⟨hz'Q, hz'c⟩, hz'LO⟩ := (HQ.and_eventually hLO).exists
  obtain ⟨t, htW, htZ⟩ := hz'LO hz'Q
  refine ⟨optionPoint z' t, htW.1, htZ, fun hzero ↦ hz'c ?_⟩
  have := htW.2 htZ
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun k _ ↦ by
    rw [hzero, zero_pow (Nat.succ_ne_zero k), mul_zero], zero_add, pow_zero, mul_one] at this
  exact this

/-- The inductive step of Rückert's Nullstellensatz. -/
theorem rueckertPrime_option {τ : Type} [Fintype τ] (H : RueckertPrime 𝕜 τ) :
    RueckertPrime 𝕜 (Option τ) := by
  classical
  intro P hP ι _ s hs h hh
  by_cases hP0 : P = ⊥
  · refine frequently_of_eq_bot s (hs.trans hP0) ?_
    rintro rfl
    exact hh P.zero_mem
  obtain ⟨g, hgP, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨v, hv, b, hreg⟩ := exists_isRegularOfOrder_shearEquiv hg0
  let Φ : convergent (Option τ) 𝕜 ≃+* convergent (Option τ) 𝕜 := (shearEquiv hv).toRingEquiv
  have hP' : (P.map Φ).IsPrime := Ideal.map_isPrime_of_equiv Φ
  have hs' : Ideal.span (Set.range (Φ ∘ s)) = P.map Φ := by
    rw [Set.range_comp, ← Ideal.map_span, hs]
  have hh' : Φ h ∉ P.map Φ := by
    rw [Ideal.mem_map_of_equiv]
    rintro ⟨x, hx, hxh⟩
    exact hh (Φ.injective hxh ▸ hx)
  have H' := frequently_of_isRegularOfOrder H (P := P.map Φ) (Ideal.mem_map_of_mem _ hgP) hreg
    (Φ ∘ s) hs' hh'
  exact frequently_of_substAnalytic (analyticAt_shear v) (shear_zero v) s h H'

theorem rueckertPrime_fin (n : ℕ) : RueckertPrime 𝕜 (Fin n) := by
  induction n with
  | zero => exact rueckertPrime_of_isEmpty
  | succ n ih =>
    exact rueckertPrime_of_equiv (convergentCongr (_root_.finSuccEquiv n)).toRingEquiv
      (φ := fun z i ↦ z (_root_.finSuccEquiv n i)) (AnalyticAt.pi fun _ ↦ analyticAt_apply _ 0) rfl
      (fun _ ↦ rfl) (rueckertPrime_option ih)

/-- **Rückert's Nullstellensatz, prime case**: a convergent power series not in a prime ideal
`P = (s₁, …, sₘ)` of `𝕜{z}` does not vanish identically on the zero set of `P` near `0`. -/
theorem rueckertPrime (σ : Type) [Fintype σ] : RueckertPrime 𝕜 σ :=
  rueckertPrime_of_equiv (convergentCongr (Fintype.equivFin σ)).toRingEquiv
    (φ := fun z i ↦ z (Fintype.equivFin σ i)) (AnalyticAt.pi fun _ ↦ analyticAt_apply _ 0) rfl
    (fun _ ↦ rfl) (rueckertPrime_fin _)

/-- **Rückert's Nullstellensatz**: if `h ∈ 𝕜{z}` vanishes near `0` on the common zero set of
`s₁, …, sₘ`, then some power of `h` lies in the ideal `(s₁, …, sₘ)`. -/
theorem mem_radical_of_eventually {σ : Type} [Finite σ] {ι : Type} [Finite ι]
    (s : ι → convergent σ 𝕜) (h : convergent σ 𝕜)
    (H : ∀ᶠ z in 𝓝 (0 : σ → 𝕜), ZeroLocus s z → tsumEval h.1 z = 0) :
    h ∈ (Ideal.span (Set.range s)).radical := by
  classical
  have := Fintype.ofFinite σ
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hIP, hP⟩
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian P : P.FG)
  let t : S → convergent σ 𝕜 := Subtype.val
  have ht : Ideal.span (Set.range t) = P := by
    rw [← hS]
    congr 1
    ext x
    simp [t]
  by_contra hhP
  have h₁ := rueckertPrime σ P hP S t ht h hhP
  have h₂ : ∀ᶠ z in 𝓝 (0 : σ → 𝕜), ZeroLocus t z → ZeroLocus s z := by
    refine eventually_zeroLocus_of_le ?_
    rw [ht]
    rintro _ ⟨i, rfl⟩
    exact hIP (Ideal.subset_span ⟨i, rfl⟩)
  obtain ⟨z, ⟨hz₁, hz₂⟩, hz₃, hz₄⟩ := (h₁.and_eventually (h₂.and H)).exists
  exact hz₂ (hz₄ (hz₃ hz₁))

end Step

end MvPowerSeries

namespace AnalyticGeometry

open MvPowerSeries

namespace LocalModelData

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n : ℕ}

omit [CompleteSpace 𝕜] in
/-- The convergent power series of a function analytic at `x`, recentred at `x`. -/
lemma eventually_tsumEval_convergentStalkEquiv_symm [CompleteSpace 𝕜] (x : Fin n → 𝕜)
    {F : (Fin n → 𝕜) → 𝕜} (hF : AnalyticAt 𝕜 F x) :
    ∀ᶠ w in 𝓝 (0 : Fin n → 𝕜),
      tsumEval ((convergentStalkEquiv x).symm (germOf F hF)).1 w = F (w + x) := by
  set f := (convergentStalkEquiv x).symm (germOf F hF)
  have hf : convergentStalkEquiv x f = germOf F hF := RingEquiv.apply_symm_apply _ _
  rw [convergentStalkEquiv_apply, convergentToStalk_apply, germOf_eq_germOf_iff] at hf
  filter_upwards [(tendsto_add_nhds x).eventually hf] with w hw
  simpa using hw

/-- **Rückert's Nullstellensatz for local models**: if a function `G` analytic at a point `x` of a
local model `Z(D) ⊆ 𝕜ⁿ` (`𝕜` algebraically closed, e.g. `ℂ`) vanishes on `Z(D)` near `x`, then its
class in the local ring `𝒪_{Z(D),x} = 𝒪_{𝕜ⁿ,x}/(f)` is nilpotent. -/
theorem isNilpotent_classOf_of_eventually_eq_zero [IsAlgClosed 𝕜]
    (D : LocalModelData 𝕜 (Fin n → 𝕜)) (x : D.zeroSet) (G : (Fin n → 𝕜) → 𝕜)
    (hG : AnalyticAt 𝕜 G x) (h : ∀ᶠ y in 𝓝 x, G ((y : D.zeroSet) : Fin n → 𝕜) = 0) :
    IsNilpotent (D.classOf x G hG) := by
  set E := convergentStalkEquiv (x : Fin n → 𝕜)
  let s : Fin D.k → convergent (Fin n) 𝕜 := fun i ↦
    E.symm (germOf (D.f i) (D.analyticAt_f i x (D.mem_U x)))
  let H := E.symm (germOf G hG)
  have hideal : D.ideal x (D.mem_U x) = (Ideal.span (Set.range s)).map E := by
    have e : (E : convergent (Fin n) 𝕜 → _) ∘ s =
        fun i ↦ germOf (D.f i) (D.analyticAt_f i x (D.mem_U x)) :=
      funext fun i ↦ RingEquiv.apply_symm_apply _ _
    rw [Ideal.map_span, ← Set.range_comp, e]
    rfl
  have hvan : ∀ᶠ w in 𝓝 (0 : Fin n → 𝕜), ZeroLocus s w → tsumEval H.1 w = 0 := by
    have hU : ∀ᶠ w in 𝓝 (0 : Fin n → 𝕜), w + (x : Fin n → 𝕜) ∈ D.U :=
      (tendsto_add_nhds (x : Fin n → 𝕜)).eventually (D.isOpen_U.mem_nhds (D.mem_U x))
    have hG' : ∀ᶠ w in 𝓝 (0 : Fin n → 𝕜), w + (x : Fin n → 𝕜) ∈ D.zeroSet →
        G (w + x) = 0 := by
      have h' := eventually_nhdsWithin_iff.mp
        ((eventually_nhds_subtype_iff D.zeroSet x (fun z ↦ G z = 0)).mp h)
      exact (tendsto_add_nhds (x : Fin n → 𝕜)).eventually h'
    have hs : ∀ i, ∀ᶠ w in 𝓝 (0 : Fin n → 𝕜), tsumEval (s i).1 w = D.f i (w + x) := fun i ↦
      eventually_tsumEval_convergentStalkEquiv_symm _ _
    filter_upwards [hU, hG', eventually_all.mpr hs,
      eventually_tsumEval_convergentStalkEquiv_symm _ hG] with w hwU hwG hws hwH hZ
    rw [hwH]
    exact hwG ⟨hwU, fun i ↦ (hws i).symm.trans (hZ i)⟩
  have hrad : H ∈ (Ideal.span (Set.range s)).radical := mem_radical_of_eventually s H hvan
  obtain ⟨N, hN⟩ := hrad
  refine ⟨N, ?_⟩
  have hGH : germOf G hG = E H := (RingEquiv.apply_symm_apply _ _).symm
  rw [classOf, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, hideal, hGH, ← map_pow]
  exact Ideal.mem_map_of_mem _ hN

end LocalModelData

end AnalyticGeometry
