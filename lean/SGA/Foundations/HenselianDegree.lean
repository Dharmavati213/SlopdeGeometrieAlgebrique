/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Etale.Descent
import SGA.Foundations.HenselianFinite

/-!
# The geometric number of points of the closed fibre of a finite algebra

Let `A` be a local domain with fraction field `K` and residue field `k`, and `B` a finite
torsion-free `A`-algebra. Let `n'` be the number of geometric points of the closed fibre of
`B` (the `A`-algebra maps `B → k̄`) and `n = [K ⊗_A B : K]` the degree of its generic fibre.
When the strict henselization `A^{sh}` of `A` is a normal domain (for instance, `A` normal),
`n' ≤ n`, with equality if and only if `B` is étale over `A` (EGA IV 18.10.16; SGA 1 I.10.12).

The proof passes to `B' = A^{sh} ⊗_A B`, which is torsion-free over `A^{sh}`
(`IsLocalRing.StrictHenselization.exists_dvd_algebraMap`: every nonzero element of `A^{sh}`
divides a nonzero element of `A`). Over the henselian `A^{sh}`, `B'` is the product of its
localizations at the `m ≥ n'` points over the closed point (Stacks 04GG), each of which has a
nonzero generic fibre: `m ≤ n`. If `m = n`, each factor has rank one over the normal domain
`A^{sh}`, hence is `A^{sh}`: `B'` is étale over `A^{sh}`, so `B` is étale over `A` (étaleness
descends along the faithfully flat `A → A^{sh}`).

## Main results

* `IsIntegral.exists_dvd_algebraMap`: a nonzero element integral over `R` in a domain divides a
  nonzero element of `R`.
* `IsLocalRing.StrictHenselization.exists_dvd_algebraMap`.
* `IsLocalRing.card_algHom_le_finrank`, `IsLocalRing.card_algHom_eq_finrank_iff_etale`.
-/

universe u v

open Polynomial TensorProduct

noncomputable section

/-- A nonzero element `w` of a domain, integral over `R`, divides a
nonzero element of `R`: the constant coefficient of a relation `w^m q(w) = 0` with `q(0) ≠ 0`. -/
theorem IsIntegral.exists_dvd_algebraMap {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] {w : S} (hw : IsIntegral R w) (hw0 : w ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ w ∣ algebraMap R S r := by
  have : Nontrivial R := (algebraMap R S).domain_nontrivial
  obtain ⟨p, hpm, hp⟩ := hw
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpm.ne_zero 0
  rw [map_zero, sub_zero, X_dvd_iff] at hq
  have hq0 : aeval w q = 0 := by
    have h : aeval w p = 0 := hp
    rw [hpq] at h
    simp only [map_mul, map_pow, aeval_X, map_zero, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hw0)
  refine ⟨q.coeff 0, hq, -aeval w q.divX, ?_⟩
  have h := congrArg (aeval w) (divX_mul_X_add q)
  rw [map_add, map_mul, aeval_X, aeval_C, hq0] at h
  linear_combination h

/-- Clearing denominators in a monic relation: if `b x = a` then
`b^d (x^d + ∑ cᵢ xⁱ) = a^d + ∑ cᵢ aⁱ b^{d-i}`. -/
lemma pow_mul_add_sum_eq {F : Type*} [CommRing F] {a b x : F} (hx : b * x = a) (d : ℕ)
    (c : Fin d → F) :
    b ^ d * (x ^ d + ∑ i : Fin d, c i * x ^ (i : ℕ)) =
      a ^ d + ∑ i : Fin d, c i * a ^ (i : ℕ) * b ^ (d - i) := by
  rw [mul_add, Finset.mul_sum, ← hx, mul_pow]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hd : b ^ d = b ^ (i : ℕ) * b ^ (d - i) := by rw [← pow_add, Nat.add_sub_cancel' i.2.le]
  rw [hd]
  ring

/-- In an integrally closed domain, `b` divides `a` if `a/b` satisfies a monic equation:
`a^d + ∑ cᵢ aⁱ b^{d-i} = 0`. -/
lemma IsIntegrallyClosed.dvd_of_eq_zero {D : Type*} [CommRing D] [IsDomain D]
    [IsIntegrallyClosed D] {a b : D} (hb : b ≠ 0) (d : ℕ) (c : Fin d → D)
    (h : a ^ d + ∑ i : Fin d, c i * a ^ (i : ℕ) * b ^ (d - i) = 0) : b ∣ a := by
  let F := FractionRing D
  have hinj := IsFractionRing.injective D F
  have hbF : algebraMap D F b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
  let x : F := algebraMap D F a / algebraMap D F b
  have hx : algebraMap D F b * x = algebraMap D F a := mul_div_cancel₀ _ hbF
  let P : D[X] := X ^ d + ∑ i : Fin d, C (c i) * X ^ (i : ℕ)
  have hPm : P.Monic := monic_X_pow_add (degree_sum_fin_lt _)
  have hP : aeval x P = 0 := by
    have h' := pow_mul_add_sum_eq hx d (fun i ↦ algebraMap D F (c i))
    have h'' : algebraMap D F (a ^ d + ∑ i : Fin d, c i * a ^ (i : ℕ) * b ^ (d - i)) = 0 := by
      rw [h, map_zero]
    simp only [map_add, map_sum, map_mul, map_pow] at h''
    rw [h''] at h'
    have hval : aeval x P = x ^ d + ∑ i : Fin d, algebraMap D F (c i) * x ^ (i : ℕ) := by
      simp [P, map_sum]
    rw [hval]
    exact (mul_eq_zero.mp h').resolve_left (pow_ne_zero _ hbF)
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff F).mp inferInstance ⟨P, hPm, hP⟩
  exact ⟨y, hinj (by rw [map_mul, hy, hx])⟩

namespace IsLocalRing.StrictHenselization

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]

/-- A strict henselization is a domain if the local rings of all the pointed étale
neighbourhoods are domains (a filtered colimit of domains). -/
theorem isDomain_of_forall (h : ∀ N : EtaleNbhd R K, IsDomain N.Stalk) :
    IsDomain (StrictHenselization R K) := by
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {a b} hab ↦ ?_⟩
  obtain ⟨N, x, hx⟩ := exists_of_finite ![a, b]
  have ha : of N (x 0) = a := hx 0
  have hb : of N (x 1) = b := hx 1
  rw [← ha, ← hb, ← map_mul, of_eq_zero_iff] at hab
  obtain ⟨N', h', hN'⟩ := hab
  rw [map_mul] at hN'
  have := h N'
  rcases mul_eq_zero.mp hN' with h0 | h0
  · left
    rw [← ha, ← of_transition h', h0, map_zero]
  · right
    rw [← hb, ← of_transition h', h0, map_zero]

/-- A strict henselization is integrally closed if the local rings of all the pointed étale
neighbourhoods are integrally closed domains (EGA IV 18.8.12): a monic relation satisfied by a
fraction `a/b` already holds in one of these local rings. -/
theorem isIntegrallyClosed_of_forall
    (h : ∀ N : EtaleNbhd R K, IsDomain N.Stalk ∧ IsIntegrallyClosed N.Stalk) :
    IsIntegrallyClosed (StrictHenselization R K) := by
  have : IsDomain (StrictHenselization R K) := isDomain_of_forall fun N ↦ (h N).1
  let S := StrictHenselization R K
  let F := FractionRing S
  refine (isIntegrallyClosed_iff F).mpr fun {x} ⟨p, hpm, hp⟩ ↦ ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj := IsFractionRing.injective S F
  have hbF : algebraMap S F b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  set d := p.natDegree
  -- the relation `a^d + ∑ pᵢ aⁱ b^{d-i} = 0` in `S`
  have hrel : a ^ d + ∑ i : Fin d, p.coeff i * a ^ (i : ℕ) * b ^ (d - i) = 0 := by
    apply hinj
    have hx : algebraMap S F b * (algebraMap S F a / algebraMap S F b) = algebraMap S F a :=
      mul_div_cancel₀ _ hbF
    have h' := pow_mul_add_sum_eq hx d (fun i ↦ algebraMap S F (p.coeff i))
    have hval : aeval (algebraMap S F a / algebraMap S F b) p =
        (algebraMap S F a / algebraMap S F b) ^ d + ∑ i : Fin d,
          algebraMap S F (p.coeff i) * (algebraMap S F a / algebraMap S F b) ^ (i : ℕ) := by
      rw [aeval_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, one_smul, add_comm,
        Finset.sum_range (fun i ↦ p.coeff i • (algebraMap S F a / algebraMap S F b) ^ i)]
      simp only [Algebra.smul_def]
      rfl
    have hp' : aeval (algebraMap S F a / algebraMap S F b) p = 0 := hp
    rw [← hval, hp', mul_zero] at h'
    simp only [map_add, map_sum, map_mul, map_pow, map_zero]
    exact h'.symm
  -- it already holds in the local ring of some neighbourhood
  obtain ⟨N, y, hy⟩ := exists_of_finite (Fin.cons a (Fin.cons b (fun i : Fin d ↦ p.coeff i)))
  have ha : of N (y 0) = a := hy 0
  have hbN : of N (y 1) = b := hy 1
  have hc (i : Fin d) : of N (y i.succ.succ) = p.coeff i := hy i.succ.succ
  have hrelN : of N (y 0 ^ d + ∑ i : Fin d, y i.succ.succ * y 0 ^ (i : ℕ) * y 1 ^ (d - i)) =
      0 := by
    simp only [map_add, map_sum, map_mul, map_pow, ha, hbN, hc]
    exact hrel
  obtain ⟨N', hNN', hN'⟩ := (of_eq_zero_iff _).mp hrelN
  have := (h N').1
  have := (h N').2
  let tr := EtaleNbhd.transition N N' hNN'
  have hb' : tr (y 1) ≠ 0 := fun h0 ↦ hb0 (by rw [← hbN, ← of_transition hNN', h0, map_zero])
  simp only [map_add, map_sum, map_mul, map_pow] at hN'
  obtain ⟨c, hc'⟩ := IsIntegrallyClosed.dvd_of_eq_zero hb' d (fun i ↦ tr (y i.succ.succ)) hN'
  refine ⟨of N' c, ?_⟩
  have hac : a = b * of N' c := by
    rw [← ha, ← hbN, ← of_transition hNN', ← of_transition hNN' (y 1), ← map_mul]
    exact congrArg (of N') hc'
  rw [hac, map_mul, mul_div_cancel_left₀ _ hbF]

/-- Every nonzero element of a strict henselization `R^{sh}` which is a domain divides a nonzero
element of `R`. Each element is `x = s/t` in the local ring of a
standard étale neighbourhood `R[X, 1/g]/(f)`, and `s g^n` is integral over `R`. In particular the
generic fibre of `Spec R^{sh} → Spec R` is a single point. -/
theorem exists_dvd_algebraMap [IsDomain (StrictHenselization R K)]
    {z : StrictHenselization R K} (hz : z ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ z ∣ algebraMap R (StrictHenselization R K) r := by
  obtain ⟨N, x, rfl⟩ := exists_of z
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj N.prime.primeCompl x
  let Pr : StandardEtalePresentation R N.pair.Ring :=
    ⟨N.pair, N.pair.X, N.pair.hasMap_X, by
      simpa [StandardEtalePair.lift_X_left] using Function.bijective_id⟩
  obtain ⟨p, n, hp⟩ := Pr.exists_mul_aeval_x_g_pow_eq_aeval_x s
  let φ : N.pair.Ring →ₐ[R] StrictHenselization R K :=
    (of N).comp (IsScalarTower.toAlgHom R N.pair.Ring N.Stalk)
  let u := φ t * φ (aeval N.pair.X N.pair.g) ^ n
  have hu : IsUnit u := by
    refine .mul ?_ (.pow _ (N.pair.hasMap_X.2.map φ))
    exact (IsLocalization.map_units N.Stalk t).map (of N)
  have hw : φ (aeval N.pair.X p) = of N x * u := by
    have h := congrArg (of N) hst
    change φ (aeval Pr.x p) = _
    rw [← hp, map_mul, map_pow]
    change _ = of N x * (φ t * φ (aeval Pr.x Pr.g) ^ n)
    simp only [φ, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h ⊢
    rw [← h, map_mul]
    ring
  have hX : IsIntegral R N.pair.X := ⟨N.pair.f, N.pair.monic_f, N.pair.hasMap_X.1⟩
  have hint : IsIntegral R (φ (aeval N.pair.X p)) :=
    (adjoin_le_integralClosure hX (aeval_mem_adjoin_singleton R N.pair.X)).map φ
  have hw0 : φ (aeval N.pair.X p) ≠ 0 := by
    rw [hw]
    exact mul_ne_zero hz hu.ne_zero
  obtain ⟨r, hr0, hr⟩ := hint.exists_dvd_algebraMap hw0
  exact ⟨r, hr0, (Dvd.intro u hw.symm).trans hr⟩

end IsLocalRing.StrictHenselization

namespace IsLocalRing

/-- The kernel of a local homomorphism from a local ring to a field is the maximal ideal. -/
lemma ker_eq_maximalIdeal_of_isLocalHom {R F : Type*} [CommRing R] [IsLocalRing R] [Field F]
    (f : R →+* F) [IsLocalHom f] : RingHom.ker f = maximalIdeal R := by
  ext r
  rw [RingHom.mem_ker, mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h hr
    exact (hr.map f).ne_zero h
  · intro h
    by_contra h'
    exact h (isUnit_of_map_unit f r (isUnit_iff_ne_zero.mpr h'))

/-- The points of the closed fibre of an `A'`-algebra `B'`: the primes of `B'` over the maximal
ideal of `A'`. -/
abbrev ClosedFibre (A' : Type u) [CommRing A'] [IsLocalRing A'] (B' : Type*) [CommRing B']
    [Algebra A' B'] : Type _ :=
  {q : PrimeSpectrum B' // q.asIdeal.comap (algebraMap A' B') = maximalIdeal A'}

section Fibre

variable {A' : Type u} [CommRing A'] {B' : Type v} [CommRing B'] [Algebra A' B']

/-- An idempotent of an integral algebra over a local ring lying in all the primes over the
maximal ideal vanishes. -/
lemma eq_zero_of_isIdempotentElem_of_forall_mem [IsLocalRing A'] [Algebra.IsIntegral A' B']
    {ε : B'}
    (hε : IsIdempotentElem ε) (h : ∀ q : ClosedFibre A' B', ε ∈ q.1.asIdeal) : ε = 0 := by
  have hu : IsUnit (1 - ε) := by
    by_contra hu
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_eq_top.not.mpr hu)
    have hq : M.comap (algebraMap A' B') = maximalIdeal A' :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
    have h1 : 1 - ε ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : ε ∈ M := h ⟨⟨M, hM.isPrime⟩, hq⟩
    exact hM.ne_top ((Ideal.eq_top_iff_one M).mpr (by simpa using M.add_mem h1 h2))
  have h0 : ε * (1 - ε) = 0 := by rw [mul_sub, mul_one, hε.eq, sub_self]
  exact hu.mul_left_eq_zero.mp h0

set_option backward.isDefEq.respectTransparency false in
/-- Over a strictly henselian local ring `A'`, an `A'`-algebra map from an integral algebra `B'`
to a field `Ω` over the residue field is determined by its kernel, a point of the closed fibre
(the residue fields of the closed fibre are purely inseparable over that of `A'`). Hence the
number of such maps is at most the number of points of the closed fibre. -/
theorem card_algHom_le_card_closedFibre [IsStrictlyHenselian A'] [Algebra.IsIntegral A' B']
    (Ω : Type*) [Field Ω] [Algebra A' Ω] [IsLocalHom (algebraMap A' Ω)]
    [Finite (ClosedFibre A' B')] :
    Finite (B' →ₐ[A'] Ω) ∧ Nat.card (B' →ₐ[A'] Ω) ≤ Nat.card (ClosedFibre A' B') := by
  have hker (ψ : B' →ₐ[A'] Ω) :
      (RingHom.ker ψ).comap (algebraMap A' B') = maximalIdeal A' := by
    rw [← ker_eq_maximalIdeal_of_isLocalHom (algebraMap A' Ω)]
    ext a
    simp [RingHom.mem_ker]
  let κ : (B' →ₐ[A'] Ω) → ClosedFibre A' B' :=
    fun ψ ↦ ⟨⟨RingHom.ker ψ, RingHom.ker_isPrime _⟩, hker ψ⟩
  have hκ : Function.Injective κ := by
    intro ψ₁ ψ₂ h
    have hk : RingHom.ker ψ₁ = RingHom.ker ψ₂ :=
      congrArg (fun q : ClosedFibre A' B' ↦ q.1.asIdeal) h
    let P := RingHom.ker ψ₁
    have : P.IsPrime := RingHom.ker_isPrime _
    have : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P (by rw [hker ψ₁]; infer_instance)
    let k' := ResidueField A'
    let : Algebra k' Ω := (ResidueField.lift (algebraMap A' Ω)).toAlgebra
    have : IsScalarTower A' k' Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let : Algebra k' (B' ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap (hker ψ₁).ge
    have : IsScalarTower A' k' (B' ⧸ P) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have : Algebra.IsIntegral k' (B' ⧸ P) := Algebra.IsIntegral.tower_top A'
    let : Field (B' ⧸ P) := Ideal.Quotient.field P
    have : IsPurelyInseparable k' (B' ⧸ P) := inferInstance
    let φ (ψ : B' →ₐ[A'] Ω) (hψ : P ≤ RingHom.ker ψ) : B' ⧸ P →ₐ[k'] Ω :=
      AlgHom.extendScalarsOfSurjective residue_surjective
        (Ideal.Quotient.liftₐ P ψ fun b hb ↦ hψ hb)
    have h' := Subsingleton.elim (φ ψ₁ le_rfl) (φ ψ₂ hk.le)
    ext b
    exact congrArg (fun χ : B' ⧸ P →ₐ[k'] Ω ↦ χ (Ideal.Quotient.mk P b)) h'
  exact ⟨.of_injective κ hκ, Nat.card_le_card_of_injective κ hκ⟩

variable (A') in
/-- The number of `A'`-algebra maps from a finite algebra `B'` to a field `Ω'` over a field
`K'` over `A'` is at most `[K' ⊗_{A'} B' : K']`. -/
theorem finite_algHom_and_card_le_finrank [Module.Finite A' B'] (K' Ω' : Type*) [Field K']
    [Algebra A' K'] [Field Ω'] [Algebra K' Ω'] [Algebra A' Ω'] [IsScalarTower A' K' Ω'] :
    Finite (B' →ₐ[A'] Ω') ∧ Nat.card (B' →ₐ[A'] Ω') ≤ Module.finrank K' (K' ⊗[A'] B') := by
  let e := Algebra.TensorProduct.liftEquivRight (R := A') (S := K') (B := B') Ω'
  have h := cardinalMk_algHom K' (K' ⊗[A'] B') Ω'
  rw [Module.finrank_linearMap_self] at h
  have hfin : Finite (K' ⊗[A'] B' →ₐ[K'] Ω') :=
    Cardinal.mk_lt_aleph0_iff.mp (h.trans_lt (Cardinal.natCast_lt_aleph0))
  refine ⟨.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, ← Nat.cast_le (α := Cardinal), Nat.cast_card]
  exact h

/-- A torsion-free module over a domain embeds into its base change to the fraction field. -/
lemma injective_includeRight_of_isTorsionFree [IsDomain A'] [Module.IsTorsionFree A' B'] :
    Function.Injective
      (Algebra.TensorProduct.includeRight : B' →ₐ[A'] FractionRing A' ⊗[A'] B') := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  have hb' : TensorProduct.mk A' (FractionRing A') B' 1 b = 0 := hb
  rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors A')] at hb'
  obtain ⟨⟨s, hs⟩, hsb⟩ := hb'
  exact (smul_eq_zero.mp hsb).resolve_left (nonZeroDivisors.ne_zero hs)

/-- A nonzero idempotent `ε` of a finite torsion-free algebra over a domain `A'` is not killed by
some `A'`-algebra map to an algebraically closed field over the fraction field of `A'`. -/
lemma exists_algHom_ne_zero [IsDomain A'] [Module.Finite A' B'] [Module.IsTorsionFree A' B']
    (Ω' : Type*) [Field Ω'] [IsAlgClosed Ω'] [Algebra (FractionRing A') Ω'] [Algebra A' Ω']
    [IsScalarTower A' (FractionRing A') Ω'] {ε : B'} (hε : IsIdempotentElem ε) (hε0 : ε ≠ 0) :
    ∃ χ : B' →ₐ[A'] Ω', χ ε ≠ 0 := by
  let K' := FractionRing A'
  let R := K' ⊗[A'] B'
  let ι : B' →ₐ[A'] R := Algebra.TensorProduct.includeRight
  have hιε : ¬ IsNilpotent (ι ε) := fun h ↦ hε0
    (injective_includeRight_of_isTorsionFree (A' := A') (B' := B')
      (by rw [map_zero]; exact (hε.map ι).eq_zero_of_isNilpotent h))
  obtain ⟨P, hP, hεP⟩ : ∃ P : Ideal R, P.IsPrime ∧ ι ε ∉ P := by
    by_contra! h
    exact hιε ((nilpotent_iff_mem_prime (x := ι ε)).mpr fun J hJ ↦ h J hJ)
  have : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P (by
    rw [Ideal.eq_bot_of_prime (P.comap (algebraMap K' R))]
    exact Ideal.bot_isMaximal)
  let : Field (R ⧸ P) := Ideal.Quotient.field P
  let χ' : R ⧸ P →ₐ[K'] Ω' := IsAlgClosed.lift
  refine ⟨((χ'.comp (Ideal.Quotient.mkₐ K' P)).restrictScalars A').comp ι, ?_⟩
  change χ' (Ideal.Quotient.mk P (ι ε)) ≠ 0
  intro h0
  apply hεP
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact χ'.toRingHom.injective (h0.trans (map_zero χ').symm)

set_option backward.isDefEq.respectTransparency false in
/-- Over a henselian local domain `A'`, the points of the closed fibre of a finite torsion-free
`A'`-algebra `B'` are finite in number and at most as many as the `A'`-algebra maps from `B'` to
an algebraically closed field over the fraction field: each point has a neighbourhood
`Spec B' e`, `e` idempotent (Stacks 04GG), which has a point over the generic point. -/
theorem finite_closedFibre_and_card_le [IsDomain A'] [HenselianLocalRing A'] [Module.Finite A' B']
    [Module.IsTorsionFree A' B'] (Ω' : Type*) [Field Ω'] [IsAlgClosed Ω']
    [Algebra (FractionRing A') Ω'] [Algebra A' Ω'] [IsScalarTower A' (FractionRing A') Ω']
    [Finite (B' →ₐ[A'] Ω')] :
    Finite (ClosedFibre A' B') ∧ Nat.card (ClosedFibre A' B') ≤ Nat.card (B' →ₐ[A'] Ω') := by
  choose e he hq using fun q : ClosedFibre A' B' ↦
    HenselianLocalRing.exists_isIdempotentElem_notMem_iff q.1 q.2
  have hmem (q q' : ClosedFibre A' B') : e q ∈ q'.1.asIdeal ↔ q' ≠ q := by
    rw [← not_iff_not, not_not, hq q q'.1 q'.2, Subtype.ext_iff]
  have he0 (q : ClosedFibre A' B') : e q ≠ 0 := fun h ↦
    (hmem q q).mp (h ▸ zero_mem _) rfl
  have horth (q q' : ClosedFibre A' B') (hne : q ≠ q') : e q * e q' = 0 := by
    refine eq_zero_of_isIdempotentElem_of_forall_mem (A' := A') ((he q).mul (he q'))
      fun q'' ↦ ?_
    by_cases h : q'' = q
    · subst h
      exact Ideal.mul_mem_left _ _ ((hmem q' q'').mpr hne)
    · exact Ideal.mul_mem_right _ _ ((hmem q q'').mpr h)
  choose χ hχ using fun q ↦ exists_algHom_ne_zero (A' := A') Ω' (he q) (he0 q)
  have hχ1 (q : ClosedFibre A' B') : χ q (e q) = 1 :=
    (IsIdempotentElem.iff_eq_zero_or_one.mp ((he q).map (χ q))).resolve_left (hχ q)
  have hinj : Function.Injective χ := by
    intro q q' h
    by_contra hne
    have h0 := congrArg (χ q) (horth q q' hne)
    rw [map_mul, map_zero, hχ1, one_mul, h, hχ1] at h0
    exact one_ne_zero h0
  exact ⟨.of_injective χ hinj, Nat.card_le_card_of_injective χ hinj⟩

/-- A finite torsion-free algebra `P` of rank one over an integrally closed domain `A'` is `A'`. -/
lemma bijective_algebraMap_of_finrank_eq_one [IsDomain A'] [IsIntegrallyClosed A']
    (P : Type*) [CommRing P] [Algebra A' P] [Module.Finite A' P] [Module.IsTorsionFree A' P]
    [Nontrivial P] (h : Module.finrank (FractionRing A') (FractionRing A' ⊗[A'] P) = 1) :
    Function.Bijective (algebraMap A' P) := by
  let K' := FractionRing A'
  let ι : P →ₐ[A'] K' ⊗[A'] P := Algebra.TensorProduct.includeRight
  have hι : Function.Injective ι := injective_includeRight_of_isTorsionFree
  have : Nontrivial (K' ⊗[A'] P) := hι.nontrivial
  refine ⟨FaithfulSMul.algebraMap_injective A' P, fun p ↦ ?_⟩
  have htop : (⊥ : Subalgebra K' (K' ⊗[A'] P)) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  obtain ⟨c, hc⟩ : ι p ∈ (⊥ : Subalgebra K' (K' ⊗[A'] P)) := htop ▸ Algebra.mem_top
  have hint : IsIntegral A' c := by
    have hp : IsIntegral A' (ι p) := (Algebra.IsIntegral.isIntegral p).map ι
    rw [← hc] at hp
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A' K' (K' ⊗[A'] P))
      (algebraMap K' (K' ⊗[A'] P)).injective).mp hp
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a, hι ?_⟩
  rw [← hc, ← ha, AlgHom.commutes, IsScalarTower.algebraMap_apply A' K' (K' ⊗[A'] P)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Over a henselian local integrally closed domain `A'`, a finite torsion-free `A'`-algebra `B'`
whose closed fibre has at least `[K' ⊗_{A'} B' : K']` points is étale: it is the product of its
localizations at these points (Stacks 04GG), each of rank one, hence isomorphic to `A'`. -/
theorem etale_of_finrank_le_card_closedFibre [IsDomain A'] [IsIntegrallyClosed A']
    [HenselianLocalRing A'] [Module.Finite A' B'] [Module.IsTorsionFree A' B']
    [Finite (ClosedFibre A' B')]
    (h : Module.finrank (FractionRing A') (FractionRing A' ⊗[A'] B') ≤
      Nat.card (ClosedFibre A' B')) :
    Algebra.Etale A' B' := by
  classical
  let K' := FractionRing A'
  let Q := ClosedFibre A' B'
  have : Fintype Q := Fintype.ofFinite Q
  choose e he hq using fun q : Q ↦ HenselianLocalRing.exists_isIdempotentElem_notMem_iff q.1 q.2
  have hmem (q q' : Q) : e q ∈ q'.1.asIdeal ↔ q' ≠ q := by
    rw [← not_iff_not, not_not, hq q q'.1 q'.2, Subtype.ext_iff]
  have horth (q q' : Q) (hne : q ≠ q') : e q * e q' = 0 := by
    refine eq_zero_of_isIdempotentElem_of_forall_mem (A' := A') ((he q).mul (he q'))
      fun q'' ↦ ?_
    by_cases h : q'' = q
    · subst h
      exact Ideal.mul_mem_left _ _ ((hmem q' q'').mpr hne)
    · exact Ideal.mul_mem_right _ _ ((hmem q q'').mpr h)
  have hortho : OrthogonalIdempotents e := ⟨he, fun q q' hne ↦ horth q q' hne⟩
  have hcomplete : ∑ q, e q = 1 := by
    have hid : IsIdempotentElem (1 - ∑ q, e q) := hortho.isIdempotentElem_sum.one_sub
    refine (sub_eq_zero.mp (eq_zero_of_isIdempotentElem_of_forall_mem (A' := A') hid
      fun q'' ↦ ?_)).symm
    have hsplit : ∑ q, e q = e q'' + ∑ q ∈ Finset.univ.erase q'', e q :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ q'')).symm
    have hrest : ∑ q ∈ Finset.univ.erase q'', e q ∈ q''.1.asIdeal :=
      Ideal.sum_mem _ fun q hq' ↦ (hmem q q'').mpr (Finset.ne_of_mem_erase hq').symm
    have hone : 1 - e q'' ∈ q''.1.asIdeal := by
      have h0 : e q'' * (1 - e q'') = 0 := by rw [mul_sub, mul_one, (he q'').eq, sub_self]
      have hnot : e q'' ∉ q''.1.asIdeal := fun hm ↦ (hmem q'' q'').mp hm rfl
      exact (q''.1.2.mem_or_mem (h0 ▸ zero_mem _)).resolve_left hnot
    rw [hsplit, sub_add_eq_sub_sub]
    exact Ideal.sub_mem _ hone hrest
  have hc : CompleteOrthogonalIdempotents e := ⟨hortho, hcomplete⟩
  let P (q : Q) := B' ⧸ Ideal.span {1 - e q}
  let E : B' ≃ₐ[A'] ∀ q, P q := AlgEquiv.ofBijective
    (AlgHom.pi fun q ↦ Ideal.Quotient.mkₐ A' (Ideal.span {1 - e q})) hc.bijective_pi
  -- each factor is nontrivial, finite and torsion-free
  have hPnt (q : Q) : Nontrivial (P q) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h0 : e q * (1 - e q) = 0 := by rw [mul_sub, mul_one, (he q).eq, sub_self]
    have hnot : e q ∉ q.1.asIdeal := fun hm ↦ (hmem q q).mp hm rfl
    exact q.1.2.ne_top (Ideal.eq_top_of_isUnit_mem _
      ((q.1.2.mem_or_mem (h0 ▸ zero_mem _)).resolve_left hnot) hu))
  have hPtf (q : Q) : Module.IsTorsionFree A' (P q) := by
    refine .of_smul_eq_zero fun a x hax ↦ or_iff_not_imp_left.mpr fun ha ↦ ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : a • b ∈ Ideal.span {1 - e q} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      rw [← hax]
      rfl
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
    have h2 : a • (e q * b) = 0 := by
      rw [← mul_smul_comm, ← hc, mul_left_comm, mul_sub, mul_one, (he q).eq, sub_self, mul_zero]
    have h3 : e q * b = 0 := (smul_eq_zero.mp h2).resolve_left ha
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    exact ⟨b, by rw [mul_sub, mul_one, mul_comm, h3, sub_zero]⟩
  -- ranks
  have hrk (q : Q) : 1 ≤ Module.finrank K' (K' ⊗[A'] P q) := by
    have : Nontrivial (K' ⊗[A'] P q) :=
      (injective_includeRight_of_isTorsionFree (A' := A') (B' := P q)).nontrivial
    exact Module.finrank_pos
  have hsum : Module.finrank K' (K' ⊗[A'] B') = ∑ q, Module.finrank K' (K' ⊗[A'] P q) := by
    rw [← Module.finrank_pi_fintype]
    exact ((Algebra.TensorProduct.congr AlgEquiv.refl E).trans
      (Algebra.TensorProduct.piRight A' K' K' P)).toLinearEquiv.finrank_eq
  have hone (q : Q) : Module.finrank K' (K' ⊗[A'] P q) = 1 := by
    have hle : ∑ q, Module.finrank K' (K' ⊗[A'] P q) ≤ ∑ _q : Q, 1 := by
      rw [← hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
        ← Nat.card_eq_fintype_card]
      exact h
    have heq : ∑ _q : Q, 1 = ∑ q, Module.finrank K' (K' ⊗[A'] P q) :=
      le_antisymm (Finset.sum_le_sum fun q _ ↦ hrk q) hle
    exact ((Finset.sum_eq_sum_iff_of_le fun q _ ↦ hrk q).mp heq q (Finset.mem_univ q)).symm
  have hetale (q : Q) : Algebra.Etale A' (P q) :=
    .of_equiv (AlgEquiv.ofBijective (Algebra.ofId A' (P q))
      (bijective_algebraMap_of_finrank_eq_one (P q) (hone q)))
  exact .of_equiv E.symm

end Fibre

section BaseChange

/-- Let `A → A'` be flat, with `A`, `A'` domains, such that every nonzero element of `A'`
divides a nonzero element of `A`. The base change to `A'` of a torsion-free `A`-module is
torsion-free. -/
theorem _root_.Module.IsTorsionFree.tensorProduct_of_dvd {A A' : Type*} [CommRing A]
    [CommRing A'] [Algebra A A'] [IsDomain A] [IsDomain A'] [Module.Flat A A']
    (hdvd : ∀ z : A', z ≠ 0 → ∃ r : A, r ≠ 0 ∧ z ∣ algebraMap A A' r)
    (B : Type*) [AddCommGroup B] [Module A B] [Module.IsTorsionFree A B] :
    Module.IsTorsionFree A' (A' ⊗[A] B) := by
  refine .of_smul_eq_zero fun z x hzx ↦ or_iff_not_imp_left.mpr fun hz ↦ ?_
  obtain ⟨r, hr, c, hc⟩ := hdvd z hz
  have h1 : r • x = 0 := by
    rw [← algebraMap_smul A' r x, hc, mul_comm, mul_smul, hzx, smul_zero]
  have hinjB : Function.Injective (LinearMap.lsmul A B r) :=
    Module.IsTorsionFree.isSMulRegular (isRegular_iff_ne_zero.mpr hr)
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := A') _ hinjB
  have heq : (LinearMap.lsmul A B r).lTensor A' = LinearMap.lsmul A (A' ⊗[A] B) r :=
    TensorProduct.ext' fun a b ↦ by simp [TensorProduct.tmul_smul]
  apply hinj
  rw [heq, map_zero]
  exact h1

end BaseChange

section Main

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] (K : Type*) [Field K]
  [Algebra A K] [IsFractionRing A K] (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B]

set_option backward.isDefEq.respectTransparency false in
/-- **The number of geometric points of the closed fibre** (EGA IV 18.10.16; SGA 1 I.10.12).
Let `A` be a local domain with fraction field `K` and residue field `k`, whose strict
henselization `A^{sh}` (with respect to `k̄`) is a domain, and `B` a finite torsion-free
`A`-algebra. The number `n'` of geometric points `B → k̄` of the closed fibre is at most the
number of `A`-algebra maps from `B` to an algebraic closure of the fraction field of `A^{sh}`,
which is at most `[K ⊗_A B : K]`. -/
theorem card_algHom_le_finrank
    [IsDomain (StrictHenselization A (AlgebraicClosure (ResidueField A)))] :
    Nat.card (B →ₐ[A] AlgebraicClosure (ResidueField A)) ≤
        Nat.card (B →ₐ[A] AlgebraicClosure
          (FractionRing (StrictHenselization A (AlgebraicClosure (ResidueField A))))) ∧
      Nat.card (B →ₐ[A] AlgebraicClosure
          (FractionRing (StrictHenselization A (AlgebraicClosure (ResidueField A))))) ≤
        Module.finrank K (K ⊗[A] B) := by
  let Ω := AlgebraicClosure (ResidueField A)
  let A' := StrictHenselization A Ω
  let K' := FractionRing A'
  let Ω' := AlgebraicClosure K'
  have : IsLocalHom (algebraMap A Ω) := isLocalHom_algebraMap_of_isScalarTower (R := A) (K := Ω)
  let : Algebra A' Ω := (StrictHenselization.pointHom : A' →ₐ[A] Ω).toRingHom.toAlgebra
  have : IsScalarTower A A' Ω :=
    .of_algebraMap_eq fun a ↦ ((StrictHenselization.pointHom : A' →ₐ[A] Ω).commutes a).symm
  have : IsLocalHom (algebraMap A' Ω) :=
    ⟨fun z hz ↦ (StrictHenselization.isUnit_iff_pointHom_ne_zero z).mpr hz.ne_zero⟩
  have hinjA : Function.Injective (algebraMap A A') := FaithfulSMul.algebraMap_injective A A'
  have : Module.IsTorsionFree A' (A' ⊗[A] B) :=
    Module.IsTorsionFree.tensorProduct_of_dvd
      (fun z hz ↦ StrictHenselization.exists_dvd_algebraMap hz) B
  obtain ⟨hfin', hD⟩ := finite_algHom_and_card_le_finrank A' (B' := A' ⊗[A] B) K' Ω'
  obtain ⟨hfinQ, hC⟩ := finite_closedFibre_and_card_le (A' := A') (B' := A' ⊗[A] B) Ω'
  obtain ⟨hfinΩ, hB⟩ := card_algHom_le_card_closedFibre (A' := A') (B' := A' ⊗[A] B) Ω
  have e₁ := Algebra.TensorProduct.liftEquivRight (R := A) (S := A') (B := B) Ω
  have e₂ := Algebra.TensorProduct.liftEquivRight (R := A) (S := A') (B := B) Ω'
  -- the degree of the generic fibre does not change
  have hinjK : Function.Injective (algebraMap A K') := by
    rw [IsScalarTower.algebraMap_eq A A' K']
    exact (IsFractionRing.injective A' K').comp hinjA
  let : Algebra K K' := (IsFractionRing.lift hinjK).toAlgebra
  have : IsScalarTower A K K' :=
    .of_algebraMap_eq fun a ↦ (IsFractionRing.lift_algebraMap hinjK a).symm
  have hE : Module.finrank K' (K' ⊗[A'] (A' ⊗[A] B)) = Module.finrank K (K ⊗[A] B) :=
    (Algebra.TensorProduct.cancelBaseChange A A' K' K' B).toLinearEquiv.finrank_eq.trans
      ((Algebra.TensorProduct.cancelBaseChange A K K' K' B).symm.toLinearEquiv.finrank_eq.trans
        Module.finrank_baseChange)
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr e₁, Nat.card_congr e₂]
    exact hB.trans hC
  · rw [Nat.card_congr e₂, ← hE]
    exact hD

set_option backward.isDefEq.respectTransparency false in
/-- **The étale criterion** (EGA IV 18.10.16; SGA 1 I.10.12). Let `A` be a local domain with
fraction field `K` and residue field `k`, whose strict henselization `A^{sh}` is an integrally
closed domain (for instance `A` integrally closed), and `B` a finite torsion-free `A`-algebra.
Then the number `n'` of geometric points of the closed fibre of `B` equals `[K ⊗_A B : K]` if and
only if `B` is étale over `A`. -/
theorem card_algHom_eq_finrank_iff_etale
    [IsDomain (StrictHenselization A (AlgebraicClosure (ResidueField A)))]
    [IsIntegrallyClosed (StrictHenselization A (AlgebraicClosure (ResidueField A)))] :
    Nat.card (B →ₐ[A] AlgebraicClosure (ResidueField A)) = Module.finrank K (K ⊗[A] B) ↔
      Algebra.Etale A B := by
  let Ω := AlgebraicClosure (ResidueField A)
  let A' := StrictHenselization A Ω
  let K' := FractionRing A'
  let Ω' := AlgebraicClosure K'
  have : IsLocalHom (algebraMap A Ω) := isLocalHom_algebraMap_of_isScalarTower (R := A) (K := Ω)
  let : Algebra A' Ω := (StrictHenselization.pointHom : A' →ₐ[A] Ω).toRingHom.toAlgebra
  have : IsScalarTower A A' Ω :=
    .of_algebraMap_eq fun a ↦ ((StrictHenselization.pointHom : A' →ₐ[A] Ω).commutes a).symm
  have : IsLocalHom (algebraMap A' Ω) :=
    ⟨fun z hz ↦ (StrictHenselization.isUnit_iff_pointHom_ne_zero z).mpr hz.ne_zero⟩
  have hinjA : Function.Injective (algebraMap A A') := FaithfulSMul.algebraMap_injective A A'
  have : Module.IsTorsionFree A' (A' ⊗[A] B) :=
    Module.IsTorsionFree.tensorProduct_of_dvd
      (fun z hz ↦ StrictHenselization.exists_dvd_algebraMap hz) B
  obtain ⟨hfin', hD⟩ := finite_algHom_and_card_le_finrank A' (B' := A' ⊗[A] B) K' Ω'
  obtain ⟨hfinQ, hC⟩ := finite_closedFibre_and_card_le (A' := A') (B' := A' ⊗[A] B) Ω'
  obtain ⟨hfinΩ, hB⟩ := card_algHom_le_card_closedFibre (A' := A') (B' := A' ⊗[A] B) Ω
  have e₁ := Algebra.TensorProduct.liftEquivRight (R := A) (S := A') (B := B) Ω
  have hinjK : Function.Injective (algebraMap A K') := by
    rw [IsScalarTower.algebraMap_eq A A' K']
    exact (IsFractionRing.injective A' K').comp hinjA
  let : Algebra K K' := (IsFractionRing.lift hinjK).toAlgebra
  have : IsScalarTower A K K' :=
    .of_algebraMap_eq fun a ↦ (IsFractionRing.lift_algebraMap hinjK a).symm
  have hE : Module.finrank K' (K' ⊗[A'] (A' ⊗[A] B)) = Module.finrank K (K ⊗[A] B) :=
    (Algebra.TensorProduct.cancelBaseChange A A' K' K' B).toLinearEquiv.finrank_eq.trans
      ((Algebra.TensorProduct.cancelBaseChange A K K' K' B).symm.toLinearEquiv.finrank_eq.trans
        Module.finrank_baseChange)
  have hle := (card_algHom_le_finrank (A := A) K B).1.trans (card_algHom_le_finrank (A := A) K B).2
  constructor
  · intro h
    have : Algebra.Etale A' (A' ⊗[A] B) := by
      refine etale_of_finrank_le_card_closedFibre (A' := A') ?_
      rw [hE, ← h, Nat.card_congr e₁]
      exact hB
    exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat A'
  · intro _
    obtain ⟨r, ⟨e⟩⟩ := IsStrictlyHenselian.exists_algEquiv_pi A' (A' ⊗[A] B)
    have : Module.Free A' (A' ⊗[A] B) := .of_equiv e.symm.toLinearEquiv
    have hr : Module.finrank K (K ⊗[A] B) = r := by
      rw [← hE, Module.finrank_baseChange, e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
    let ι (i : Fin r) : A' ⊗[A] B →ₐ[A'] Ω :=
      (Algebra.ofId A' Ω).comp ((Pi.evalAlgHom A' (fun _ ↦ A') i).comp e.toAlgHom)
    have hι : Function.Injective ι := by
      intro i j hij
      by_contra hne
      have h := congrArg (fun χ : A' ⊗[A] B →ₐ[A'] Ω ↦ χ (e.symm (Pi.single i 1))) hij
      simp [ι, Ne.symm hne] at h
    have hge : r ≤ Nat.card (A' ⊗[A] B →ₐ[A'] Ω) := by
      simpa using Nat.card_le_card_of_injective ι hι
    rw [Nat.card_congr e₁]
    rw [Nat.card_congr e₁] at hle
    omega

end Main

end IsLocalRing
