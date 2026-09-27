/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import SGA.Foundations.CommAlg.RegularLocalRing

/-!
# Normality and associated primes of principal ideals

For a noetherian domain `R`, normality is controlled by the associated primes of the modules
`R/bR` (the "S₂ + R₁" part of Serre's criterion, Stacks 031S):

* `mem_span_singleton_of_forall_associatedPrimes`: if `a/b ∈ R_P` for every associated prime
  `P` of `R/bR`, then `b ∣ a`.
* `IsIntegrallyClosed.of_forall_associatedPrimes`: if `R_P` is integrally closed for every
  associated prime `P` of every `R/bR` (`b ≠ 0`), then `R` is integrally closed.
* `IsIntegrallyClosed.isDiscreteValuationRing_localization`: conversely, if `R` is integrally
  closed, then `R_P` is a discrete valuation ring for every such `P`; in particular these primes
  have height one (Stacks 0310, the S₂ and R₁ properties of normal rings).

Applied to regular rings, whose localizations at the associated primes of `R/bR` have
dimension `≤ 1` because regular local rings are Cohen–Macaulay, this gives:

* `IsRegularRing.isIntegrallyClosed`, `IsRegularLocalRing.isIntegrallyClosed`: a regular domain,
  in particular a regular local ring, is integrally closed (Stacks 0567).
-/

universe u

open IsLocalRing

variable {R : Type u} [CommRing R]

/-- Membership in the annihilator of the class of `a` in `R/bR`. -/
theorem mem_colon_mk_span_singleton {a b r : R} :
    r ∈ (⊥ : Submodule R (R ⧸ Ideal.span {b})).colon {Ideal.Quotient.mk _ a} ↔
      r * a ∈ Ideal.span {b} := by
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem]
  rfl

/-- If `a/b` lies in `R_P` (i.e. `sa ∈ bR` for some `s ∉ P`) for every associated prime `P` of
`R/bR`, then `a ∈ bR`. -/
theorem mem_span_singleton_of_forall_associatedPrimes [IsNoetherianRing R] {a b : R}
    (h : ∀ P ∈ associatedPrimes R (R ⧸ Ideal.span {b}), ∃ s ∉ P, s * a ∈ Ideal.span {b}) :
    a ∈ Ideal.span {b} := by
  by_contra ha
  have hne : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hne
  obtain ⟨s, hsP, hs⟩ := h P hP
  exact hsP (hle (mem_colon_mk_span_singleton.mpr hs))

/-- An associated prime of `R/bR` in a noetherian ring is the annihilator of the class of some
`a ∉ bR`. -/
theorem exists_eq_colon_of_mem_associatedPrimes [IsNoetherianRing R] {b : R} {P : Ideal R}
    (hP : P ∈ associatedPrimes R (R ⧸ Ideal.span {b})) :
    ∃ a : R, a ∉ Ideal.span {b} ∧ ∀ r, r ∈ P ↔ r * a ∈ Ideal.span {b} := by
  obtain ⟨hPp, x, hx⟩ := (isAssociatedPrime_iff).mp hP
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨a, fun ha ↦ hPp.ne_top ?_, fun r ↦ by rw [hx, mem_colon_mk_span_singleton]⟩
  rw [hx, Ideal.eq_top_iff_one, mem_colon_mk_span_singleton, one_mul]
  exact ha

section Domain

variable [IsDomain R]

/-- A noetherian domain `R` is integrally closed if the localizations `R_P` are integrally closed
for the associated primes `P` of all the modules `R/bR`, `b ≠ 0` (Stacks 031S). -/
theorem IsIntegrallyClosed.of_forall_associatedPrimes [IsNoetherianRing R]
    (h : ∀ b : R, b ≠ 0 → ∀ (P : Ideal R) [P.IsPrime],
      P ∈ associatedPrimes R (R ⧸ Ideal.span {b}) → IsIntegrallyClosed (Localization.AtPrime P)) :
    IsIntegrallyClosed R := by
  let K := FractionRing R
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hab : a ∈ Ideal.span {b} := by
    refine mem_span_singleton_of_forall_associatedPrimes fun P hP ↦ ?_
    have := hP.isPrime
    have := h b hb0 P hP
    have hxP : IsIntegral (Localization.AtPrime P) (IsLocalization.mk' K a ⟨b, hb⟩) :=
      hx.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxP
    obtain ⟨⟨c, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    refine ⟨s, hs, Ideal.mem_span_singleton'.mpr ⟨c, ?_⟩⟩
    change algebraMap _ K (IsLocalization.mk' _ c ⟨s, hs⟩) = IsLocalization.mk' K a ⟨b, hb⟩ at hy
    have e1 := congrArg (algebraMap (Localization.AtPrime P) K)
      (IsLocalization.mk'_spec (Localization.AtPrime P) c ⟨s, hs⟩)
    rw [map_mul, hy, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e1
    have e2 := IsLocalization.mk'_spec K a ⟨b, hb⟩
    have e3 : algebraMap R K (a * s) = algebraMap R K (c * b) := by
      rw [map_mul, map_mul, ← e1, ← e2]
      ring
    have := IsFractionRing.injective R K e3
    linear_combination -this
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hab
  exact ⟨c, (IsLocalization.mk'_eq_iff_eq_mul.mpr (map_mul _ _ _)).symm⟩

omit [IsDomain R] in
/-- The two facts about `a/b` in `R_P` used below: `m_P · a ⊆ b R_P` and `a ∉ b R_P`, when `P` is
the annihilator of the class of `a` in `R/bR`. -/
private theorem localization_facts [IsNoetherianRing R] {a b : R} {P : Ideal R} [P.IsPrime]
    (hPa : ∀ r, r ∈ P ↔ r * a ∈ Ideal.span {b}) :
    (∀ u ∈ maximalIdeal (Localization.AtPrime P), ∃ c : Localization.AtPrime P,
        u * algebraMap R _ a = algebraMap R _ b * c) ∧
      ¬ ∃ c : Localization.AtPrime P, algebraMap R _ a = algebraMap R _ b * c := by
  constructor
  · intro u hu
    obtain ⟨⟨r, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl u
    change IsLocalization.mk' _ r ⟨s, hs⟩ ∈ _ at hu
    have hr : r ∈ P := by
      rwa [IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime P) P] at hu
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((hPa r).mp hr)
    refine ⟨IsLocalization.mk' _ c ⟨s, hs⟩, ?_⟩
    change IsLocalization.mk' _ r ⟨s, hs⟩ * _ = _
    rw [mul_comm (IsLocalization.mk' _ r _), IsLocalization.mul_mk'_eq_mk'_of_mul,
      IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm a r, ← hc, mul_comm c b]
  · rintro ⟨c, hc⟩
    obtain ⟨⟨d, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    change _ = _ * IsLocalization.mk' _ d ⟨s, hs⟩ at hc
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.eq_mk'_iff_mul_eq, ← map_mul,
      IsLocalization.eq_iff_exists P.primeCompl] at hc
    obtain ⟨⟨t, ht⟩, htc⟩ := hc
    refine P.primeCompl.mul_mem ht hs ((hPa _).mpr ?_)
    exact Ideal.mem_span_singleton'.mpr ⟨t * d, by linear_combination -htc⟩

/-- In a regular local ring of dimension at least two, the maximal ideal is not an associated
prime of `R/bR` for `b ≠ 0`: an element `a` with `m a ⊆ bR` lies in `bR`. This is the depth
statement `depth R/bR = depth R - 1 ≥ 1`. -/
theorem IsRegularLocalRing.exists_eq_mul_of_forall_maximalIdeal {S : Type u} [CommRing S]
    [IsRegularLocalRing S] (hdim : 2 ≤ ringKrullDim S) {a b : S} (hb : b ≠ 0)
    (hbm : b ∈ maximalIdeal S) (h : ∀ u ∈ maximalIdeal S, ∃ c, u * a = b * c) :
    ∃ c, a = b * c := by
  have hdepth : (2 : ℕ∞) ≤ (maximalIdeal S).depth S := by
    have := IsRegularLocalRing.depth_eq_ringKrullDim (R := S)
    rw [← this] at hdim
    exact WithBot.coe_le_coe.mp hdim
  have hreg : IsSMulRegular S b := (IsRegular.of_ne_zero hb).left
  have hQ := Ideal.depth_quotSMulTop_add_one hbm hreg
  have h1 : 1 ≤ (maximalIdeal S).depth (QuotSMulTop b S) := by
    rw [← hQ] at hdepth
    have : (1 : ℕ∞) + 1 ≤ (maximalIdeal S).depth (QuotSMulTop b S) + 1 := hdepth
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  obtain ⟨y, hy, hyreg⟩ := Ideal.one_le_depth_iff.mp h1
  obtain ⟨c, hc⟩ := h y hy
  have hmk : y • (Submodule.Quotient.mk a : QuotSMulTop b S) = y • 0 := by
    rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul, hc]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  have := hyreg hmk
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at this
  obtain ⟨c, -, hc⟩ := this
  exact ⟨c, hc.symm⟩

/-- A regular domain is integrally closed (Stacks 0567). -/
@[stacks 0567]
theorem IsRegularRing.isIntegrallyClosed [IsRegularRing R] : IsIntegrallyClosed R := by
  refine IsIntegrallyClosed.of_forall_associatedPrimes fun b hb P _ hP ↦ ?_
  apply IsRegularLocalRing.isIntegrallyClosed_of_ringKrullDim_le_one
  by_contra! hdim
  obtain ⟨a, ha, hPa⟩ := exists_eq_colon_of_mem_associatedPrimes hP
  obtain ⟨h1, h2⟩ := localization_facts hPa
  have hbP : b ∈ P := (hPa b).mpr (Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self b))
  refine h2 (IsRegularLocalRing.exists_eq_mul_of_forall_maximalIdeal ?_ ?_ ?_ h1)
  · have := (ENat.WithBot.add_one_le_iff (n := 1)).mpr (by exact_mod_cast hdim)
    exact_mod_cast this
  · exact (map_ne_zero_iff _ (IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors)).mpr hb
  · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P b).mpr hbP

/-- In an integrally closed noetherian domain `R`, the localization at an associated prime `P`
of `R/bR` (`b ≠ 0`) is a discrete valuation ring (Stacks 0310). -/
theorem IsIntegrallyClosed.isDiscreteValuationRing_localization [IsNoetherianRing R]
    [IsIntegrallyClosed R] {b : R} (hb : b ≠ 0) (P : Ideal R) [P.IsPrime]
    (hP : P ∈ associatedPrimes R (R ⧸ Ideal.span {b})) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  let S := Localization.AtPrime P
  have : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S P.primeCompl P.primeCompl_le_nonZeroDivisors
  obtain ⟨a, ha, hPa⟩ := exists_eq_colon_of_mem_associatedPrimes hP
  obtain ⟨h1, h2⟩ := localization_facts hPa
  set a' := algebraMap R S a
  set b' := algebraMap R S b
  have hbP : b ∈ P := (hPa b).mpr (Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self b))
  have hb' : b' ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors)).mpr hb
  have hbm : b' ∈ maximalIdeal S := (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P b).mpr hbP
  have hnf : ¬ IsField S := fun hf ↦ hb' (by
    let := hf.toField
    simpa using hbm)
  have ha' : a' ≠ 0 := fun h0 ↦ h2 ⟨0, by rw [h0, mul_zero]⟩
  choose! c hc using h1
  by_cases hunit : ∃ u ∈ maximalIdeal S, c u ∉ maximalIdeal S
  · -- `m = u S`: the maximal ideal is principal.
    obtain ⟨u, hu, hcu⟩ := hunit
    have hcu' : IsUnit (c u) := by rwa [← IsLocalRing.notMem_maximalIdeal]
    have hprinc : (maximalIdeal S).IsPrincipal := by
      refine ⟨⟨u, le_antisymm (fun v hv ↦ ?_) ?_⟩⟩
      · refine Ideal.mem_span_singleton'.mpr ⟨c v * ↑hcu'.unit⁻¹, ?_⟩
        apply mul_right_cancel₀ ha'
        have e1 := hc v hv
        have e2 := hc u hu
        calc c v * ↑hcu'.unit⁻¹ * u * a' = c v * ↑hcu'.unit⁻¹ * (b' * c u) := by
              rw [mul_assoc, e2]
          _ = b' * c v * (↑hcu'.unit⁻¹ * c u) := by ring
          _ = v * a' := by rw [IsUnit.val_inv_mul, mul_one, e1]
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hu
    exact ((IsDiscreteValuationRing.TFAE S hnf).out 1 5).mpr hprinc
  · -- Otherwise `a/b` stabilizes `m`, hence is integral over `S`, hence lies in `S`.
    push Not at hunit
    exfalso
    let K := FractionRing S
    let N : Submodule S K := Submodule.map (Algebra.linearMap S K) (maximalIdeal S)
    have hN : N ≠ ⊥ := by
      intro h0
      have : algebraMap S K b' ∈ N := Submodule.mem_map_of_mem hbm
      rw [h0, Submodule.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective S K)] at this
      exact hb' this
    have hNfg : N.FG := Submodule.FG.map _ (maximalIdeal S).fg_of_isNoetherianRing
    let x : K := algebraMap S K a' / algebraMap S K b'
    have hb'K : algebraMap S K b' ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S K)).mpr hb'
    have hx : ∀ n ∈ N, x • n ∈ N := by
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨c v, hunit v hv, ?_⟩
      simp only [Algebra.linearMap_apply, smul_eq_mul, x]
      rw [div_mul_eq_mul_div, eq_div_iff hb'K, ← map_mul, ← map_mul, mul_comm (a'), hc v hv,
        mul_comm]
    have hint : IsIntegral S x := isIntegral_of_smul_mem_submodule N hN hNfg x hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    apply h2 ⟨y, IsFractionRing.injective S K ?_⟩
    rw [map_mul, hy, mul_div_cancel₀ _ hb'K]

/-- In an integrally closed noetherian domain, the associated primes of `R/bR` (`b ≠ 0`) have
height one (Stacks 0310). -/
theorem IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes [IsNoetherianRing R]
    [IsIntegrallyClosed R] {b : R} (hb : b ≠ 0) {P : Ideal R}
    (hP : P ∈ associatedPrimes R (R ⧸ Ideal.span {b})) : P.height = 1 := by
  have := hP.isPrime
  have := isDiscreteValuationRing_localization hb P hP
  have h := IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime P)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)] at h
  exact_mod_cast h

end Domain

/-- A regular local ring is integrally closed (Stacks 0567). -/
instance IsRegularLocalRing.isIntegrallyClosed [IsRegularLocalRing R] : IsIntegrallyClosed R :=
  IsRegularRing.isIntegrallyClosed
