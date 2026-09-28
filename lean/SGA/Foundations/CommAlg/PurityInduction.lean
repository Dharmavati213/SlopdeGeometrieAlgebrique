/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.PurityHull
import SGA.Foundations.CommAlg.PurityCompletion
import SGA.Foundations.Formal.FiniteEtale

/-!
# Purity of the branch locus in all dimensions

The purity theorem of Zariski–Nagata (SGA 2 X.3.4, SGA 1 X.3.2–3.3, Stacks 0BMB) in algebraic
form: if `A` is a regular local ring of dimension `≥ 2` and `B` a finite `A`-algebra of depth `≥ 2`
(witnessed by a regular sequence `x, y ∈ 𝔪` on `A` and `B`) which is étale over the punctured
spectrum of `A`, then `B` is étale over `A`
(`IsRegularLocalRing.etale_of_isWeaklyRegular_of_two_le_ringKrullDim`).

The proof is by induction on `dim A`, the case of dimension `2` being
`IsRegularLocalRing.etale_of_isWeaklyRegular_of_isEtaleAt`. For `dim A ≥ 3` we may assume `A`
complete. Choose `f ∈ 𝔪 \ 𝔪²` such that `x, y, f` is regular
(`IsRegularLocalRing.exists_isWeaklyRegular_notMem_sq`), so that `A₀ = A/f` is regular of
dimension `dim A - 1`. The S₂-hull `H` of `B/fB` over `D(x) ∪ D(y)` is finite étale over `A₀` by
induction; it lifts to a finite étale `A`-algebra `C` (`A` is `f`-adically complete). The natural
map `B → C/fC = H` lifts to `Φ : B → C` (`Algebra.exists_algHom_mkₐ_comp_eq_of_isAdicComplete`:
`B` is étale over `D(x)` and `D(y)`, and `C/fⁿC` has depth `2`). By Nakayama `Φ` is an isomorphism
at the primes of `V(f)` other than `𝔪`; hence `Φ` is injective (`B` is torsion free) and, since
the locus where `Φ` is not surjective is a divisor which would meet `V(f) \ {𝔪}` when `dim A ≥ 3`
(`IsRegularLocalRing.surjective_of_forall_notMem`), `Φ` is an isomorphism. This is the
Lefschetz-type argument of SGA 2 X.3.4, with the formal geometry replaced by the depth `≥ 3` of
`C`.
-/

open RingTheory.Sequence IsLocalRing TensorProduct

universe u

section Choice

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- In a regular local ring of dimension `≥ 3`, a regular sequence `x, y` in `𝔪` extends to a
regular sequence `x, y, f` with `f ∈ 𝔪 \ 𝔪²` (prime avoidance). -/
theorem IsRegularLocalRing.exists_isWeaklyRegular_notMem_sq (hd : 3 ≤ ringKrullDim A) {x y : A}
    (hx : x ∈ maximalIdeal A) (hy : y ∈ maximalIdeal A) (hreg : IsWeaklyRegular A [x, y]) :
    ∃ f ∈ maximalIdeal A, f ∉ maximalIdeal A ^ 2 ∧ IsWeaklyRegular A [x, y, f] := by
  classical
  let Q := A ⧸ (Ideal.ofList [x, y] • ⊤ : Submodule A A)
  have key : ∀ f : A, IsSMulRegular Q f → IsWeaklyRegular A [x, y, f] := by
    intro f hf
    have := (isWeaklyRegular_append_iff (M := A) [x, y] [f]).mpr
      ⟨hreg, (isWeaklyRegular_singleton_iff _ _).mpr hf⟩
    simpa using this
  -- `depth A ≥ 3`, so `x, y` extends to a regular sequence `x, y, f₀`
  have hdepth : ((3 : ℕ) : ℕ∞) ≤ (maximalIdeal A).depth A := by
    have := IsRegularLocalRing.depth_eq_ringKrullDim (R := A)
    rw [← this] at hd
    exact WithBot.coe_le_coe.mp hd
  have hxy : ∀ r ∈ [x, y], r ∈ maximalIdeal A := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hx, hy]
  obtain ⟨ts, hlen, hmem, hts⟩ := Ideal.exists_isWeaklyRegular_append (I := maximalIdeal A)
    (M := A) (rs := [x, y]) hxy hreg (n := 3) (by simp) hdepth
  obtain ⟨f₀, rfl⟩ : ∃ f₀, ts = [f₀] := by
    have : ts.length = 1 := by simpa using hlen
    exact List.length_eq_one_iff.mp this
  have hf₀ : IsSMulRegular Q f₀ :=
    (isWeaklyRegular_singleton_iff _ _).mp ((isWeaklyRegular_append_iff (M := A) [x, y] [f₀]).mp
      hts).2
  have hf₀m : f₀ ∈ maximalIdeal A := hmem f₀ (by simp)
  -- zero divisors on `Q` lie in associated primes, and `𝔪` is not one of them
  have hass : ∀ r : A, ¬ IsSMulRegular Q r → r ∈ ⋃ p ∈ associatedPrimes A Q, (p : Set A) := by
    intro r hr
    rw [biUnion_associatedPrimes_eq_zero_divisors]
    rw [isSMulRegular_iff_right_eq_zero_of_smul] at hr
    push Not at hr
    obtain ⟨m, hm, hm0⟩ := hr
    exact ⟨m, hm0, hm⟩
  have hmAss : maximalIdeal A ∉ associatedPrimes A Q := by
    intro hm
    obtain ⟨hmp, q, hq⟩ := (isAssociatedPrime_iff).mp hm
    have hq0 : f₀ • q = 0 := by
      have : f₀ ∈ (⊥ : Submodule A Q).colon {q} := hq ▸ hf₀m
      simpa [Submodule.mem_colon_singleton] using this
    have hq' : q = 0 := (isSMulRegular_iff_right_eq_zero_of_smul.mp hf₀) q hq0
    apply hmp.ne_top
    rw [hq, hq']
    ext r
    simp [Submodule.mem_colon_singleton]
  by_contra! H
  let s : Set (Ideal A) := insert (maximalIdeal A ^ 2) (associatedPrimes A Q)
  have hs : s.Finite := (associatedPrimes.finite A Q).insert _
  have hp : ∀ I ∈ s, I ≠ maximalIdeal A ^ 2 → I ≠ maximalIdeal A ^ 2 → (id I).IsPrime :=
    fun I hI h _ ↦ ((Set.mem_insert_iff.mp hI).resolve_left h).isPrime
  have hsub : (maximalIdeal A : Set A) ⊆ ⋃ I ∈ s, ((id I : Ideal A) : Set A) := by
    intro f hf
    by_cases hf2 : f ∈ maximalIdeal A ^ 2
    · exact Set.mem_biUnion (Set.mem_insert _ _) hf2
    · have hnreg : ¬ IsSMulRegular Q f := fun h ↦ H f hf hf2 (key f h)
      obtain ⟨P, hP, hfP⟩ := Set.mem_iUnion₂.mp (hass f hnreg)
      exact Set.mem_biUnion (Set.mem_insert_of_mem _ hP) hfP
  obtain ⟨I, hI, hle⟩ := (Ideal.subset_union_prime_finite hs _ _ hp).mp hsub
  rcases Set.mem_insert_iff.mp hI with rfl | hI
  · change maximalIdeal A ≤ maximalIdeal A ^ 2 at hle
    have : IsIdempotentElem (maximalIdeal A) := by
      rw [IsIdempotentElem, ← pow_two]
      exact le_antisymm (Ideal.pow_le_self two_ne_zero) hle
    have := (Ideal.cotangent_subsingleton_iff _).mpr this
    have hfield : IsField A := subsingleton_cotangentSpace_iff.mp this
    rw [ringKrullDim_eq_zero_of_isField hfield] at hd
    have h0 : ((3 : ℕ) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hd
    have : (3 : ℕ) ≤ 0 := by exact_mod_cast h0
    omega
  · change maximalIdeal A ≤ I at hle
    have hIm : I = maximalIdeal A :=
      ((maximalIdeal.isMaximal A).eq_of_le hI.isPrime.ne_top hle).symm
    exact hmAss (hIm ▸ hI)

/-- A prime `p ≠ 𝔪` of height `≥ 2` of a regular local ring contains `x', y'` which form a regular
sequence on `A_h` for some `h ∈ 𝔪 \ p`. -/
theorem IsRegularLocalRing.exists_isWeaklyRegular_away_of_two_le_height (p : Ideal A) [p.IsPrime]
    (hp : p ≠ maximalIdeal A) (h2 : 2 ≤ p.height) :
    ∃ x' ∈ p, ∃ y' ∈ p, ∃ h ∈ maximalIdeal A, h ∉ p ∧
      IsWeaklyRegular (Localization.Away h)
        [algebraMap A (Localization.Away h) x', algebraMap A (Localization.Away h) y'] := by
  let Ap := Localization.AtPrime p
  have hdim : ringKrullDim Ap = p.height := IsLocalization.AtPrime.ringKrullDim_eq_height p Ap
  have hdepth : ((2 : ℕ) : ℕ∞) ≤ (maximalIdeal Ap).depth Ap := by
    have h := IsRegularLocalRing.depth_eq_ringKrullDim (R := Ap)
    rw [hdim] at h
    rw [WithBot.coe_injective h]
    exact_mod_cast h2
  obtain ⟨rs, hlen, hmem, hrs⟩ := (Ideal.le_depth_iff (maximalIdeal Ap) Ap 2).mp hdepth
  obtain ⟨u, v, rfl⟩ : ∃ u v, rs = [u, v] := List.length_eq_two.mp hlen
  obtain ⟨⟨x', s⟩, hu⟩ := IsLocalization.surj p.primeCompl u
  obtain ⟨⟨y', t⟩, hv⟩ := IsLocalization.surj p.primeCompl v
  have hreg' : IsWeaklyRegular Ap [algebraMap A Ap x', algebraMap A Ap y'] := by
    change IsWeaklyRegular Ap [algebraMap A Ap (x', s).1, algebraMap A Ap (y', t).1]
    rw [← hu, ← hv]
    exact hrs.pair_mul_isUnit (IsLocalization.map_units Ap s) (IsLocalization.map_units Ap t)
  have hx'p : x' ∈ p := by
    have : algebraMap A Ap x' ∈ maximalIdeal Ap := by
      change algebraMap A Ap (x', s).1 ∈ _
      rw [← hu]
      exact Ideal.mul_mem_right _ _ (hmem u (by simp))
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Ap p x').mp this
  have hy'p : y' ∈ p := by
    have : algebraMap A Ap y' ∈ maximalIdeal Ap := by
      change algebraMap A Ap (y', t).1 ∈ _
      rw [← hv]
      exact Ideal.mul_mem_right _ _ (hmem v (by simp))
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Ap p y').mp this
  obtain ⟨g, hgp, hg⟩ := exists_isWeaklyRegular_of_isWeaklyRegular_atPrime p hreg'
  obtain ⟨z, hzm, hzp⟩ : ∃ z ∈ maximalIdeal A, z ∉ p :=
    SetLike.exists_of_lt (lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) hp)
  refine ⟨x', hx'p, y', hy'p, g * z, Ideal.mul_mem_left _ _ hzm, fun h ↦ ?_,
    hg (Submonoid.powers (g * z)) (Localization.Away (g * z)) ?_⟩
  · rcases (inferInstance : p.IsPrime).mem_or_mem h with h | h
    exacts [hgp h, hzp h]
  · have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (g * z)) (g * z)
    rw [map_mul] at this
    exact isUnit_of_mul_isUnit_left this

end Choice

section Divisor

variable {A B C : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Module.Flat A C]

/-- The non-surjectivity locus of a map into a flat algebra is a divisor. Let `A` be a regular local
ring of dimension `≥ 3`, `x, y ∈ 𝔪` a regular sequence on `A` and on the `A`-algebra `B`, which is
flat over `D(h)` for `h ∈ 𝔪`, and `φ : B → C` an injective map to a finite flat `A`-algebra. If `φ`
is surjective at every prime `q ≠ 𝔪` containing `f ∈ 𝔪`, then `φ` is surjective.

The associated primes of `C / φ(B)` have height `≤ 1` (Hartogs, using depth `≥ 2` of `B` and `C`
at primes of height `≥ 2`), and a prime of height `≤ 1` is contained in a prime `q ≠ 𝔪` containing
`f` (Krull's height theorem; `A` is factorial). -/
theorem IsRegularLocalRing.surjective_of_forall_notMem (hd : 3 ≤ ringKrullDim A) {f x y : A}
    (hf : f ∈ maximalIdeal A) (hx : x ∈ maximalIdeal A) (hy : y ∈ maximalIdeal A)
    (hA : IsWeaklyRegular A [x, y]) (hB : IsWeaklyRegular B [x, y])
    (hBflat : ∀ h ∈ maximalIdeal A, Module.Flat A (Localization.Away (algebraMap A B h)))
    (φ : B →ₐ[A] C) (hφ : Function.Injective φ)
    (hN : ∀ q : Ideal A, q.IsPrime → q ≠ maximalIdeal A → f ∈ q →
      ∀ c : C, ∃ s ∉ q, s • c ∈ φ.range) :
    Function.Surjective φ := by
  classical
  let N := C ⧸ LinearMap.range φ.toLinearMap
  have hmemN : ∀ c : C, (Submodule.Quotient.mk c : N) = 0 ↔ c ∈ φ.range := fun c ↦
    Submodule.Quotient.mk_eq_zero _
  by_contra hsurj
  obtain ⟨c₀, hc₀⟩ : ∃ c, c ∉ φ.range := by
    by_contra! h
    exact hsurj fun c ↦ h c
  have : Nontrivial N := ⟨⟨Submodule.Quotient.mk c₀, 0, fun h ↦ hc₀ ((hmemN c₀).mp h)⟩⟩
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty A N
  obtain ⟨hpp, n, hn⟩ := (isAssociatedPrime_iff).mp hp
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ n
  have hpc : ∀ r : A, r ∈ p ↔ r • c ∈ φ.range := by
    intro r
    rw [hn, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      hmemN]
  -- `x` is regular on the localizations of `C`
  have hxC : IsSMulRegular C x := by
    have := ((isWeaklyRegular_cons_iff _ _ _).mp (hA.of_flat (S := C))).1
    exact (isSMulRegular_algebraMap_iff (R := A) (A := C) (M := C) (r := x)).mp this
  -- the maximal ideal has height `≥ 3`
  have hm3 : ((3 : ℕ) : ℕ∞) ≤ (maximalIdeal A).height := by
    have := maximalIdeal_height_eq_ringKrullDim (R := A)
    rw [← this] at hd
    exact WithBot.coe_le_coe.mp hd
  have hqm : ∀ q : Ideal A, q.height ≤ 2 → q ≠ maximalIdeal A := by
    rintro q hq rfl
    have h32 : ((3 : ℕ) : ℕ∞) ≤ ((2 : ℕ) : ℕ∞) := hm3.trans (by exact_mod_cast hq)
    have : (3 : ℕ) ≤ 2 := by exact_mod_cast h32
    omega
  by_cases hp2 : 2 ≤ p.height
  · by_cases hpm : p = maximalIdeal A
    · -- Hartogs with `x, y`
      have hxc : x • c ∈ φ.range := (hpc x).mp (hpm ▸ hx)
      have hyc : y • c ∈ φ.range := (hpc y).mp (hpm ▸ hy)
      have hcr := mem_range_of_isWeaklyRegular φ hφ hB hxC hxc hyc
      exact hpp.ne_top ((Ideal.eq_top_iff_one _).mpr ((hpc 1).mpr (by rwa [one_smul])))
    · -- Hartogs at `p`, over `D(h)`
      obtain ⟨x', hx', y', hy', h, hhm, hhp, hreg⟩ :=
        IsRegularLocalRing.exists_isWeaklyRegular_away_of_two_le_height p hpm hp2
      have := hBflat h hhm
      have hBh := isWeaklyRegular_away_of_flat (S := B) h (rs := [x', y']) hreg
      have hCh := isWeaklyRegular_away_of_flat (S := C) h (rs := [x']) (by
        have := ((isWeaklyRegular_cons_iff _ _ _).mp hreg).1
        simpa using this)
      have hCh' := (isWeaklyRegular_singleton_iff _ _).mp (by simpa using hCh)
      obtain ⟨k, hk⟩ := exists_pow_smul_mem_range_of_isWeaklyRegular_away φ hφ
        (by simpa using hBh) hCh' ((hpc x').mp hx') ((hpc y').mp hy')
      exact hhp (hpp.mem_of_pow_mem k ((hpc _).mpr hk))
  · -- height `≤ 1`: `p` lies in a prime `q ≠ 𝔪` containing `f`
    have hp1 : p.height ≤ 1 := by
      by_contra h
      push Not at h
      exact hp2 (by simpa [one_add_one_eq_two] using Order.add_one_le_of_lt h)
    have hne : ∀ s : Set A, s ⊆ maximalIdeal A → Ideal.span s ≠ ⊤ := fun s hs h ↦
      (maximalIdeal.isMaximal A).ne_top (eq_top_iff.mpr (h ▸ Ideal.span_le.mpr hs))
    obtain ⟨q, hq, hqm, hfq, hpq⟩ : ∃ q : Ideal A, q.IsPrime ∧ q ≠ maximalIdeal A ∧ f ∈ q ∧
        p ≤ q := by
      by_cases hp0 : p = ⊥
      · obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes (hne {f} (by simpa using hf))
        have hht : q.height ≤ 1 := by
          have := Ideal.height_le_card_of_mem_minimalPrimes_span_finset (s := {f})
            (by simpa using hq)
          simpa using this
        exact ⟨q, hq.1.1, hqm q (hht.trans (by norm_num)),
          hq.1.2 (Ideal.subset_span rfl), hp0 ▸ bot_le⟩
      · obtain ⟨π, hπp, hπ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hpp hp0
        have hπ1 : (Ideal.span {π}).height = 1 :=
          Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
            (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero) hπ.not_isUnit
        have : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
        have : (Ideal.span {π}).FiniteHeight :=
          (Ideal.finiteHeight_iff _).mpr (Or.inr (by rw [hπ1]; exact ENat.one_ne_top))
        have hπeq : Ideal.span {π} = p :=
          Ideal.eq_of_le_of_height_le (I := Ideal.span {π}) (J := p)
            (h := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπp)) (h_height := hπ1 ▸ hp1)
        obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes (hne {π, f} (by
          rintro z (rfl | rfl)
          · exact le_maximalIdeal hpp.ne_top hπp
          · exact hf))
        have hht : q.height ≤ 2 := by
          have := Ideal.height_le_card_of_mem_minimalPrimes_span_finset (s := {π, f})
            (by simpa using hq)
          exact this.trans (by exact_mod_cast Finset.card_le_two)
        refine ⟨q, hq.1.1, hqm q hht,
          hq.1.2 (Ideal.subset_span (by simp)), ?_⟩
        rw [← hπeq]
        exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hq.1.2 (Ideal.subset_span
          (by simp))))
    obtain ⟨s, hsq, hs⟩ := hN q hq hqm hfq c
    exact hsq (hpq ((hpc s).mpr hs))

end Divisor

section AdicLift

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-- Lifting to a complete algebra. Let `C` be an `A`-algebra complete for an ideal `I`, such that
`x, y` is a regular sequence on every `C ⧸ Iⁿ⁺¹` and `x` is regular on `C ⧸ I`. If `B_x` and `B_y`
are formally étale over `A`, every `A`-algebra map `B → C ⧸ I` lifts to `C`. -/
theorem Algebra.exists_algHom_mkₐ_comp_eq_of_isAdicComplete {x y : A}
    [FormallyEtale A (Localization.Away (algebraMap A B x))]
    [FormallyEtale A (Localization.Away (algebraMap A B y))]
    (I : Ideal C) [IsAdicComplete I C]
    (hreg : ∀ n : ℕ, IsWeaklyRegular (C ⧸ I ^ (n + 1))
      ([algebraMap A _ x, algebraMap A _ y] : List (C ⧸ I ^ (n + 1))))
    (hreg₀ : IsSMulRegular (C ⧸ I) (algebraMap A (C ⧸ I) x))
    (ρ : B →ₐ[A] C ⧸ I) : ∃ Φ : B →ₐ[A] C, (Ideal.Quotient.mkₐ A I).comp Φ = ρ := by
  classical
  have hle : ∀ n : ℕ, I ^ (n + 1) ≤ I := fun n ↦ Ideal.pow_le_self (Nat.succ_ne_zero n)
  let π : ∀ n : ℕ, C ⧸ I ^ (n + 1) →ₐ[A] C ⧸ I := fun n ↦ Ideal.Quotient.factorₐ A (hle n)
  have hπ : ∀ n, Function.Surjective (π n) := fun n ↦ Ideal.Quotient.factor_surjective (hle n)
  have hker : ∀ n, RingHom.ker (π n) ≤ I.map (Ideal.Quotient.mk (I ^ (n + 1))) := by
    intro n z hz
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    have : c ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
    exact Ideal.mem_map_of_mem _ this
  have hnil : ∀ n, IsNilpotent (RingHom.ker (π n)) := by
    intro n
    refine ⟨n + 1, eq_bot_iff.mpr ((Ideal.pow_right_mono (hker n) (n + 1)).trans ?_)⟩
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
  choose φ hφ using fun n ↦
    exists_algHom_comp_eq_of_isWeaklyRegular (hreg n) (π n) (hπ n) (hnil n) hreg₀ ρ
  have hcompat : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right (Nat.succ_le_succ h) : I ^ (n + 1) ≤ I ^ (m + 1))).comp (φ n) =
        φ m := by
    intro m n h
    have hreg1 : IsSMulRegular (C ⧸ I ^ (m + 1)) (algebraMap A _ x) :=
      ((isWeaklyRegular_cons_iff _ _ _).mp (hreg m)).1
    refine algHom_ext_of_isSMulRegular hreg1 (RingHom.ker (π m)) (hnil m) fun b ↦ ?_
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    have e1 : π m (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (Nat.succ_le_succ h) :
        I ^ (n + 1) ≤ I ^ (m + 1)) (φ n b)) = π n (φ n b) := by
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (φ n b)
      rw [← hc]
      rfl
    rw [AlgHom.comp_apply, e1]
    exact (congr($(hφ n) b)).trans (congr($(hφ m) b)).symm
  have hmono : StrictMono (fun n : ℕ ↦ n + 1) := fun a b h ↦ Nat.succ_lt_succ h
  let Φ₀ : B →+* C := IsAdicComplete.StrictMono.liftRingHom I hmono (fun n ↦ (φ n).toRingHom)
    (fun {m} ↦ by
      ext b
      exact congr($(hcompat (Nat.le_succ m)) b))
  have hΦ₀ : ∀ n b, Ideal.Quotient.mk (I ^ (n + 1)) (Φ₀ b) = φ n b := fun n b ↦
    IsAdicComplete.StrictMono.mk_liftRingHom I hmono _ _ b
  have hcomm : ∀ r : A, Φ₀ (algebraMap A B r) = algebraMap A C r := by
    intro r
    rw [← sub_eq_zero]
    refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := I) (M := C)) _ fun n ↦ ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    apply Ideal.pow_le_pow_right (Nat.le_succ n)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hΦ₀, AlgHom.commutes,
      Ideal.Quotient.mk_algebraMap, sub_self]
  let Φ : B →ₐ[A] C := { Φ₀ with commutes' := hcomm }
  refine ⟨Φ, AlgHom.ext fun b ↦ ?_⟩
  have : Ideal.Quotient.mkₐ A I (Φ₀ b) = π 0 (Ideal.Quotient.mk (I ^ (0 + 1)) (Φ₀ b)) := rfl
  change Ideal.Quotient.mkₐ A I (Φ₀ b) = ρ b
  rw [this, hΦ₀]
  exact congr($(hφ 0) b)

end AdicLift

section Step

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- The inductive step of purity, for `A` complete of dimension `≥ 3`: purity over the regular local
rings of dimension `dim A - 1` implies purity over `A`.

Choose `f ∈ 𝔪 \ 𝔪²` with `x, y, f` regular; `A₀ = A/f` is regular of dimension `dim A - 1`.
The hull `H` of `B₀ = A₀ ⊗_A B` over `D(x) ∪ D(y)` is finite étale over `A₀` by induction, and
lifts to a finite étale `A`-algebra `C` since `A` is `f`-adically complete. The map
`B → H = C/fC` lifts to `Φ : B → C` (formal smoothness of `B_x`, `B_y` and Hartogs on the
`C/fⁿC`, which have depth `2` since `C` has depth `≥ 3`). `Φ` is an isomorphism at the primes
of `V(f)` outside `𝔪` (Nakayama), hence injective, and surjective by
`IsRegularLocalRing.surjective_of_forall_notMem`. -/
theorem IsRegularLocalRing.etale_of_isAdicComplete_of_isWeaklyRegular
    [IsAdicComplete (maximalIdeal A) A] (hd : 3 ≤ ringKrullDim A)
    (IH : ∀ (A₀ : Type u) [CommRing A₀] [IsRegularLocalRing A₀],
      ringKrullDim A₀ + 1 = ringKrullDim A →
      ∀ (B₀ : Type u) [CommRing B₀] [Algebra A₀ B₀] [Module.Finite A₀ B₀] {x₀ y₀ : A₀},
        x₀ ∈ maximalIdeal A₀ → y₀ ∈ maximalIdeal A₀ → IsWeaklyRegular A₀ [x₀, y₀] →
        IsWeaklyRegular B₀ [x₀, y₀] →
        (∀ (Q : Ideal B₀) [Q.IsPrime], Q.comap (algebraMap A₀ B₀) ≠ maximalIdeal A₀ →
          Algebra.IsEtaleAt A₀ Q) → Algebra.Etale A₀ B₀)
    {B : Type u} [CommRing B] [Algebra A B] [Module.Finite A B] {x y : A}
    (hx : x ∈ maximalIdeal A) (hy : y ∈ maximalIdeal A) (hA : IsWeaklyRegular A [x, y])
    (hB : IsWeaklyRegular B [x, y])
    (hU : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) ≠ maximalIdeal A →
      Algebra.IsEtaleAt A Q) :
    Algebra.Etale A B := by
  classical
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  -- ideals of height `≤ 2` are not maximal
  have hm3 : ((3 : ℕ) : ℕ∞) ≤ (maximalIdeal A).height := by
    have := maximalIdeal_height_eq_ringKrullDim (R := A)
    rw [← this] at hd
    exact WithBot.coe_le_coe.mp hd
  have hqm : ∀ q : Ideal A, q.height ≤ 2 → q ≠ maximalIdeal A := by
    rintro q hq rfl
    have h32 : ((3 : ℕ) : ℕ∞) ≤ ((2 : ℕ) : ℕ∞) := hm3.trans (by exact_mod_cast hq)
    have : (3 : ℕ) ≤ 2 := by exact_mod_cast h32
    omega
  -- a hypersurface section `f` with `f, x, y` regular
  obtain ⟨f, hfm, hf2, hxyf⟩ := IsRegularLocalRing.exists_isWeaklyRegular_notMem_sq hd hx hy hA
  have hfxy : ∀ n : ℕ, IsWeaklyRegular A [f ^ (n + 1), x, y] := by
    intro n
    have h1 : IsWeaklyRegular A ([x, y] ++ [f ^ (n + 1)]) := by
      have := (isWeaklyRegular_append_iff (M := A) [x, y] [f]).mp hxyf
      refine (isWeaklyRegular_append_iff (M := A) [x, y] [f ^ (n + 1)]).mpr ⟨this.1, ?_⟩
      rw [isWeaklyRegular_singleton_iff] at this ⊢
      exact this.2.pow (n + 1)
    refine IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal h1 List.perm_append_comm ?_
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hx, hy, Ideal.pow_mem_of_mem _ hfm _ (Nat.succ_pos n)]
  -- `A₀ = A / f`
  obtain ⟨-, hA₀reg, hA₀dim⟩ := IsRegularLocalRing.quotient_span_singleton hfm hf2
  let A₀ := A ⧸ Ideal.span {f}
  have : IsRegularLocalRing A₀ := hA₀reg
  have hmem₀ : ∀ a ∈ maximalIdeal A, algebraMap A A₀ a ∈ maximalIdeal A₀ := by
    intro a ha
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : a * b' - 1 ∈ Ideal.span {f} := by
      rw [← Ideal.Quotient.eq, map_mul, map_one]
      exact hb
    have h2 : a * b' - 1 ∈ maximalIdeal A :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfm) h1
    have : (1 : A) ∈ maximalIdeal A := by
      simpa using sub_mem (Ideal.mul_mem_right b' _ ha) h2
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  let x₀ : A₀ := algebraMap A A₀ x
  let y₀ : A₀ := algebraMap A A₀ y
  have hx₀ : x₀ ∈ maximalIdeal A₀ := hmem₀ x hx
  have hy₀ : y₀ ∈ maximalIdeal A₀ := hmem₀ y hy
  have hA₀ : IsWeaklyRegular A₀ [x₀, y₀] := by
    have := isWeaklyRegular_quotient_of_cons (S := A) (J := Ideal.span {f}) (hfxy 0) (by simp)
    exact this
  -- `B₀ = A₀ ⊗_A B` is étale over the punctured spectrum of `A₀`
  let B₀ := A₀ ⊗[A] B
  have hU₀ : ∀ (Q : Ideal B₀) [Q.IsPrime], Q.comap (algebraMap A₀ B₀) ≠ maximalIdeal A₀ →
      Algebra.IsEtaleAt A₀ Q := by
    intro Q _ hQ
    let P := Q.comap (Algebra.TensorProduct.includeRight (R := A) (A := A₀) (B := B)).toRingHom
    have hP : P.comap (algebraMap A B) ≠ maximalIdeal A := by
      intro h
      apply hQ
      have e : (Q.comap (algebraMap A₀ B₀)).comap (algebraMap A A₀) = maximalIdeal A := by
        rw [← h, Ideal.comap_comap, Ideal.comap_comap]
        congr 1
        ext a
        simp [B₀, ← IsScalarTower.algebraMap_apply]
      refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) fun a₀ ha₀ ↦ ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a₀
      have ha : a ∈ maximalIdeal A := by
        by_contra ha
        exact (mem_maximalIdeal _).mp ha₀
          ((IsLocalRing.notMem_maximalIdeal.mp ha).map (Ideal.Quotient.mk _))
      rw [← e] at ha
      exact ha
    have := hU P hP
    exact Algebra.IsEtaleAt.baseChange A₀ P Q rfl
  have hE₀ : ∀ g ∈ maximalIdeal A₀, Algebra.Etale A₀ (Localization.Away (algebraMap A₀ B₀ g)) :=
    fun g hg ↦ etale_away_of_mem_maximalIdeal hU₀ hg
  have hF₀ : ∀ g ∈ maximalIdeal A₀, (Localization.awayMap (algebraMap A₀ B₀) g).Finite :=
    fun g _ ↦ finite_awayMap_of_finite (S := B₀) g
  -- the hull `H` of `B₀` is finite étale over `A₀`, by induction
  let H := Localization.pairSections (algebraMap A₀ B₀ x₀) (algebraMap A₀ B₀ y₀)
  have : Module.Finite A₀ H := finite_pairSections hA₀ hE₀ hF₀ hx₀ hy₀
  have hHreg : IsWeaklyRegular H [x₀, y₀] :=
    isWeaklyRegular_pairSections_of_forall_isEtaleAt hA₀ hE₀ hy₀
  have hHet : Algebra.Etale A₀ H :=
    IH A₀ hA₀dim H hx₀ hy₀ hA₀ hHreg fun Q _ hQ ↦ isEtaleAt_pairSections hA₀ hE₀ Q hQ
  -- `H` lifts to a finite étale `A`-algebra `C`
  have : IsAdicComplete (Ideal.span {f}) A :=
    IsAdicComplete.of_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfm))
  obtain ⟨C, _, _, hCfin, hCet, ⟨e⟩⟩ :=
    Algebra.Etale.exists_finite_etale_tensorQuotient_equiv (Ideal.span {f}) H
  have : Module.Finite A C := hCfin
  have : Algebra.Etale A C := hCet
  let I : Ideal C := (Ideal.span {f}).map (algebraMap A C)
  have hIspan : ∀ n : ℕ, I ^ n = Ideal.span {algebraMap A C (f ^ n)} := by
    intro n
    change ((Ideal.span {f}).map (algebraMap A C)) ^ n = _
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow, map_pow]
  have : IsAdicComplete I C :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr (IsAdicComplete.of_finite (Ideal.span {f}) C)
  have hCreg : ∀ n : ℕ, IsWeaklyRegular C [f ^ (n + 1), x, y] := fun n ↦
    (isWeaklyRegular_map_algebraMap_iff C C _).mp ((hfxy n).of_flat (S := C))
  have hregn : ∀ n : ℕ, IsWeaklyRegular (C ⧸ I ^ (n + 1))
      ([algebraMap A _ x, algebraMap A _ y] : List (C ⧸ I ^ (n + 1))) := fun n ↦ by
    have := isWeaklyRegular_quotient_of_cons (hCreg n) (J := I ^ (n + 1)) (hIspan (n + 1))
    simpa using this
  have hreg₀ : IsSMulRegular (C ⧸ I) (algebraMap A (C ⧸ I) x) := by
    have := isWeaklyRegular_quotient_of_cons (hCreg 0) (J := I)
      (by rw [← hIspan (0 + 1), zero_add, pow_one])
    exact ((isWeaklyRegular_cons_iff _ _ _).mp this).1
  have hfC : IsSMulRegular C f := by
    have := ((isWeaklyRegular_cons_iff _ _ _).mp (hCreg 0)).1
    simpa using this
  -- the map `ρ₀ : B → B₀ → H ≅ C / f C`
  let θC : (C ⧸ I) ≃ₐ[A₀] A₀ ⊗[A] C :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor C (Ideal.span {f})
  let θB : (B ⧸ (Ideal.span {f}).map (algebraMap A B)) ≃ₐ[A₀] B₀ :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (Ideal.span {f})
  let ιH : B₀ →ₐ[A₀] H := IsScalarTower.toAlgHom A₀ B₀ H
  let ρ₀' : B₀ →ₐ[A₀] C ⧸ I := (θC.symm.toAlgHom.comp e.symm.toAlgHom).comp ιH
  let ρ₀ : B →ₐ[A] C ⧸ I := (ρ₀'.restrictScalars A).comp Algebra.TensorProduct.includeRight
  have hρ₀ : ∀ b, ρ₀ b = θC.symm (e.symm (algebraMap B₀ H (1 ⊗ₜ b))) := fun b ↦ rfl
  -- lift `ρ₀` to `Φ : B → C`
  have : Algebra.Etale A (Localization.Away (algebraMap A B x)) :=
    etale_away_of_mem_maximalIdeal hU hx
  have : Algebra.Etale A (Localization.Away (algebraMap A B y)) :=
    etale_away_of_mem_maximalIdeal hU hy
  obtain ⟨Φ, hΦ⟩ := Algebra.exists_algHom_mkₐ_comp_eq_of_isAdicComplete I hregn hreg₀ ρ₀
  have hΦ' : ∀ b, Ideal.Quotient.mk I (Φ b) = ρ₀ b := fun b ↦ congr($hΦ b)
  -- `B` is torsion free
  have hBtf : ∀ s : A, s ≠ 0 → IsSMulRegular B s := by
    intro s hs
    have hxB : IsSMulRegular B x := ((isWeaklyRegular_cons_iff _ _ _).mp hB).1
    let Bx := Localization.Away (algebraMap A B x)
    have hsx : IsSMulRegular Bx s :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs)
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro b hb
    have h1 : algebraMap B Bx b = 0 := by
      refine hsx.right_eq_zero_of_smul ?_
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B Bx, ← map_mul, ← Algebra.smul_def,
        hb, map_zero]
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap A B x))
      Bx b).mp h1
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
    rw [← hk, ← map_pow, ← Algebra.smul_def] at hc
    exact (hxB.pow k).right_eq_zero_of_smul hc
  -- over `D(g)`, `g ∈ 𝔪`, the kernel of `ρ₀` is divisible by `f`
  have hker : ∀ g ∈ maximalIdeal A, ∀ b : B, ρ₀ b = 0 →
      ∃ (j : ℕ) (b' : B), g ^ j • b = f • b' := by
    intro g hg b hb
    have hH0 : algebraMap B₀ H (1 ⊗ₜ b) = 0 := by
      rwa [hρ₀, EmbeddingLike.map_eq_zero_iff, EmbeddingLike.map_eq_zero_iff] at hb
    obtain ⟨j, hj⟩ :=
      exists_pow_mul_eq_zero_of_algebraMap_pairSections_eq_zero hA₀ hE₀ (hmem₀ g hg) hH0
    have h2 : Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap A B)) (g ^ j • b) = 0 := by
      apply θB.injective
      rw [map_zero, Algebra.smul_def, map_mul, map_mul, Ideal.Quotient.mk_algebraMap,
        IsScalarTower.algebraMap_apply A A₀, AlgEquiv.commutes]
      simp only [map_pow]
      exact hj
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton'] at h2
    obtain ⟨b', hb'⟩ := h2
    exact ⟨j, b', by rw [← hb', Algebra.smul_def, mul_comm]⟩
  -- `Φ` is injective
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    let K := LinearMap.ker Φ.toLinearMap
    have : IsNoetherian A B := isNoetherian_of_isNoetherianRing_of_finite A B
    let q : Ideal A := Ideal.span {f}
    have hq : q.IsPrime := (Ideal.Quotient.isDomain_iff_prime q).mp inferInstance
    have hqm' : q ≠ maximalIdeal A :=
      hqm q ((Ideal.height_span_singleton_le_one ((mem_maximalIdeal f).mp hfm)).trans
        (by norm_num))
    obtain ⟨g, hgm, hgq⟩ : ∃ g ∈ maximalIdeal A, g ∉ q :=
      SetLike.exists_of_lt (lt_of_le_of_ne (le_maximalIdeal hq.ne_top) hqm')
    obtain ⟨s, hsq, hs⟩ := exists_notMem_forall_smul_eq_zero_of_pow_smul_eq q (M := K)
      (Ideal.mem_span_singleton_self f) hgq fun k ↦ by
        obtain ⟨k, hk⟩ := k
        have hk0 : Φ k = 0 := hk
        have hρ : ρ₀ k = 0 := by rw [← hΦ', hk0, map_zero]
        obtain ⟨j, b', hb'⟩ := hker g hgm k hρ
        have hb'K : b' ∈ K := by
          change Φ b' = 0
          apply hfC.right_eq_zero_of_smul
          rw [← map_smul, ← hb', map_smul, hk0, smul_zero]
        exact ⟨j, ⟨b', hb'K⟩, Subtype.ext hb'⟩
    have hs0 : s ≠ 0 := fun h ↦ hsq (h ▸ q.zero_mem)
    exact (hBtf s hs0).right_eq_zero_of_smul (congrArg Subtype.val (hs ⟨b, hb⟩))
  -- `Φ` is surjective at the primes of `V(f)` other than `𝔪`
  have hN : ∀ q : Ideal A, q.IsPrime → q ≠ maximalIdeal A → f ∈ q →
      ∀ c : C, ∃ s ∉ q, s • c ∈ Φ.range := by
    intro q hq hqm' hfq c
    obtain ⟨g, hgm, hgq⟩ : ∃ g ∈ maximalIdeal A, g ∉ q :=
      SetLike.exists_of_lt (lt_of_le_of_ne (le_maximalIdeal hq.ne_top) hqm')
    let N := C ⧸ LinearMap.range Φ.toLinearMap
    obtain ⟨s, hsq, hs⟩ := exists_notMem_forall_smul_eq_zero_of_pow_smul_eq q (M := N) hfq hgq
      fun n ↦ by
        obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ n
        obtain ⟨j, s₀, hs₀⟩ := exists_pow_mul_eq_algebraMap_pairSections hA₀ hE₀ (hmem₀ g hgm)
          (e (θC (Ideal.Quotient.mk I c)))
        obtain ⟨z, hz⟩ := θB.surjective s₀
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
        have hb : ρ₀ b = Ideal.Quotient.mk I (g ^ j • c) := by
          rw [hρ₀]
          have : (1 : A₀) ⊗ₜ[A] b = s₀ := hz
          rw [this, ← hs₀, map_mul, map_mul, map_pow, map_pow, AlgEquiv.commutes,
            AlgEquiv.commutes, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply,
            Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap, map_pow,
            IsScalarTower.algebraMap_apply A A₀ (C ⧸ I)]
        have hmem : g ^ j • c - Φ b ∈ I := by
          rw [← Ideal.Quotient.eq, hΦ', hb]
        rw [← pow_one I, hIspan 1, pow_one, Ideal.mem_span_singleton'] at hmem
        obtain ⟨c', hc'⟩ := hmem
        refine ⟨j, Submodule.Quotient.mk c', ?_⟩
        rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
        refine ⟨b, ?_⟩
        change Φ b = _
        rw [Algebra.smul_def f c', mul_comm, hc']
        ring
    refine ⟨s, hsq, ?_⟩
    have := hs (Submodule.Quotient.mk c)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    obtain ⟨b, hb⟩ := this
    exact ⟨b, hb⟩
  -- conclusion
  have hBflat : ∀ h ∈ maximalIdeal A, Module.Flat A (Localization.Away (algebraMap A B h)) :=
    fun h hh ↦ by
      have := etale_away_of_mem_maximalIdeal hU hh
      infer_instance
  have hsurj := IsRegularLocalRing.surjective_of_forall_notMem hd hfm hx hy hA hB hBflat Φ hinj hN
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm

end Step

section Main

private theorem WithBot.eq_natCast_of_add_one_eq {a : WithBot ℕ∞} {n : ℕ}
    (h : a + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) : a = (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add] at h
    exact absurd h (WithBot.bot_ne_natCast _)
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [h'] at h
      have h2 : (⊤ : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
      exact ENat.top_ne_natCast _ h2
    | coe a =>
      have h1 : ((a + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← h]
        norm_cast
      have : a + 1 = n + 1 := by exact_mod_cast h1
      have : a = n := by omega
      subst this
      norm_cast

private theorem etale_of_ringKrullDim_eq_add_two : ∀ (n : ℕ) (A : Type u) [CommRing A]
    [IsRegularLocalRing A], ringKrullDim A = ((n + 2 : ℕ) : WithBot ℕ∞) →
    ∀ (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] {x y : A},
      x ∈ maximalIdeal A → y ∈ maximalIdeal A → IsWeaklyRegular A [x, y] →
      IsWeaklyRegular B [x, y] →
      (∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) ≠ maximalIdeal A →
        Algebra.IsEtaleAt A Q) → Algebra.Etale A B := by
  intro n
  induction n with
  | zero =>
    intro A _ _ hdim B _ _ _ x y hx hy _ hB hU
    exact IsRegularLocalRing.etale_of_isWeaklyRegular_of_isEtaleAt (by rw [hdim]; rfl) hx hy hB hU
  | succ n ih =>
    intro A _ _ hdim B _ _ _ x y hx hy hA hB hU
    let Â := AdicCompletion (maximalIdeal A) A
    obtain ⟨hÂreg, hÂdim⟩ := IsRegularLocalRing.adicCompletion A
    have : IsRegularLocalRing Â := hÂreg
    have : Module.FaithfullyFlat A Â := Module.FaithfullyFlat.of_flat_of_isLocalHom
    have : Algebra.FinitePresentation A B :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have hmÂ : ∀ a ∈ maximalIdeal A, algebraMap A Â a ∈ maximalIdeal Â := fun a ha ↦ by
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem _ ha
    have hÂA : IsWeaklyRegular Â [algebraMap A Â x, algebraMap A Â y] := hA.of_flat
    have hBc : IsWeaklyRegular (Â ⊗[A] B) [algebraMap A Â x, algebraMap A Â y] :=
      (isWeaklyRegular_map_algebraMap_iff Â (Â ⊗[A] B) [x, y]).mpr
        (hB.isWeaklyRegular_lTensor (M₂ := Â))
    have hUc : ∀ (Q : Ideal (Â ⊗[A] B)) [Q.IsPrime],
        Q.comap (algebraMap Â (Â ⊗[A] B)) ≠ maximalIdeal Â → Algebra.IsEtaleAt Â Q := by
      intro Q _ hQ
      let P := Q.comap (Algebra.TensorProduct.includeRight (R := A) (A := Â) (B := B)).toRingHom
      have hP : P.comap (algebraMap A B) ≠ maximalIdeal A := fun h ↦
        hQ (comap_algebraMap_eq_maximalIdeal_of_comap_includeRight Q h)
      have := hU P hP
      exact Algebra.IsEtaleAt.baseChange Â P Q rfl
    have hd : 3 ≤ ringKrullDim Â := by
      rw [hÂdim, hdim]
      exact_mod_cast (by omega : 3 ≤ n + 1 + 2)
    have : Algebra.Etale Â (Â ⊗[A] B) :=
      IsRegularLocalRing.etale_of_isAdicComplete_of_isWeaklyRegular hd
        (fun A₀ _ _ hA₀ B₀ _ _ _ _ _ hx₀ hy₀ hA₀' hB₀ hU₀ ↦ by
          have hA₀dim : ringKrullDim A₀ = ((n + 2 : ℕ) : WithBot ℕ∞) := by
            rw [hÂdim, hdim] at hA₀
            exact WithBot.eq_natCast_of_add_one_eq (n := n + 2) (by rw [hA₀])
          exact ih A₀ hA₀dim B₀ hx₀ hy₀ hA₀' hB₀ hU₀)
        (hmÂ x hx) (hmÂ y hy) hÂA hBc hUc
    exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat Â

/-- **Purity of the branch locus** (Zariski–Nagata; SGA 2 X.3.4; SGA 1 X.3.2 and X.3.3 for finite
algebras; Stacks 0BMB), algebraic form. Let `A` be a regular local ring of dimension `≥ 2`,
`x, y ∈ 𝔪` a regular sequence on `A`, and `B` a finite `A`-algebra on which `x, y` is a regular
sequence (so `B` has depth `≥ 2`). If `B` is étale over the punctured spectrum of `A`, then `B` is
étale over `A`.

By induction on `dim A`: dimension `2` is `IsRegularLocalRing.etale_of_isWeaklyRegular_of_isEtaleAt`
(Auslander–Buchsbaum and the discriminant); in dimension `≥ 3` one passes to the completion and
applies `IsRegularLocalRing.etale_of_isAdicComplete_of_isWeaklyRegular` (a hypersurface section,
lifting of finite étale algebras and a divisor argument). -/
theorem IsRegularLocalRing.etale_of_isWeaklyRegular_of_two_le_ringKrullDim {A B : Type u}
    [CommRing A] [IsRegularLocalRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (hdim : 2 ≤ ringKrullDim A) {x y : A} (hx : x ∈ maximalIdeal A) (hy : y ∈ maximalIdeal A)
    (hA : IsWeaklyRegular A [x, y]) (hB : IsWeaklyRegular B [x, y])
    (hU : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) ≠ maximalIdeal A →
      Algebra.IsEtaleAt A Q) :
    Algebra.Etale A B := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim A = ((n + 2 : ℕ) : WithBot ℕ∞) := by
    have h := IsRegularLocalRing.ringKrullDim_eq_spanFinrank (R := A)
    rw [h] at hdim ⊢
    have : 2 ≤ (maximalIdeal A).spanFinrank := by exact_mod_cast hdim
    exact ⟨(maximalIdeal A).spanFinrank - 2, by congr 1; omega⟩
  exact etale_of_ringKrullDim_eq_add_two n A hn B hx hy hA hB hU

end Main

section Normal

/-- **Zariski–Nagata purity for finite normal algebras** (SGA 1 X.3.2 for `B` finite over `A`;
SGA 2 X.3.4; Stacks 0BMB). Let `A` be a regular local ring of dimension `≥ 2` and `B` a finite
`A`-algebra which is a normal domain containing `A`. If `B` is étale over `A` at every prime not
lying over the maximal ideal of `A`, then `B` is étale over `A`.

`B` and `A` are normal of dimension `≥ 2`, so a nonzero `x ∈ 𝔪` extends to a sequence `x, y`
regular on both (prime avoidance over the height-one primes containing `x`), and
`IsRegularLocalRing.etale_of_isWeaklyRegular_of_two_le_ringKrullDim` applies. -/
theorem IsRegularLocalRing.etale_of_isIntegrallyClosed_of_two_le_ringKrullDim {A B : Type u}
    [CommRing A] [IsRegularLocalRing A] [CommRing B] [Algebra A B] [IsDomain B]
    [IsIntegrallyClosed B] [Module.Finite A B] (hinj : Function.Injective (algebraMap A B))
    (hdim : 2 ≤ ringKrullDim A)
    (hU : ∀ (q : Ideal B) [q.IsPrime], q.comap (algebraMap A B) ≠ maximalIdeal A →
      Algebra.IsEtaleAt A q) :
    Algebra.Etale A B := by
  classical
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have hm : (2 : ℕ∞) ≤ (maximalIdeal A).height := by
    have := maximalIdeal_height_eq_ringKrullDim (R := A)
    rw [← this] at hdim
    exact WithBot.coe_le_coe.mp hdim
  -- a nonzero element of the maximal ideal
  obtain ⟨x, hxm, hx0⟩ : ∃ x ∈ maximalIdeal A, x ≠ 0 := by
    by_contra! h
    have : maximalIdeal A = ⊥ := eq_bot_iff.mpr fun x hx ↦ h x hx
    rw [this, Ideal.height_bot] at hm
    exact absurd hm (by decide)
  -- height-one primes of `B` and of `A` do not lie over `𝔪_A`
  have h1B : ∀ P : Ideal B, P.IsPrime → P.height = 1 →
      P.comap (algebraMap A B) ≠ maximalIdeal A := by
    intro P _ hP hPm
    have : P.LiesOver (maximalIdeal A) := ⟨hPm.symm⟩
    have := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) P
    rw [hP] at this
    have h2 : (maximalIdeal A).height ≤ 1 := this ▸ le_self_add
    exact absurd (hm.trans h2) (by decide)
  have h1A : ∀ P : Ideal A, P.IsPrime → P.height = 1 →
      P.comap (algebraMap A A) ≠ maximalIdeal A := by
    intro P _ hP hPm
    rw [Algebra.algebraMap_self, Ideal.comap_id] at hPm
    rw [hPm] at hP
    rw [hP] at hm
    exact absurd hm (by decide)
  obtain ⟨SA, hSA, hregA⟩ := exists_finset_isWeaklyRegular_pair_of_isIntegrallyClosed (B := A)
    (x := x) (by simpa using hx0) h1A
  obtain ⟨SB, hSB, hregB⟩ := exists_finset_isWeaklyRegular_pair_of_isIntegrallyClosed (B := B)
    ((map_ne_zero_iff _ hinj).mpr hx0) h1B
  obtain ⟨y, hym, hyS⟩ := IsLocalRing.exists_mem_maximalIdeal_forall_notMem (SA ∪ SB)
    fun P hP ↦ (Finset.mem_union.mp hP).elim (hSA P) (hSB P)
  exact IsRegularLocalRing.etale_of_isWeaklyRegular_of_two_le_ringKrullDim hdim hxm hym
    (hregA y fun P hP ↦ hyS P (Finset.mem_union_left _ hP))
    (hregB y fun P hP ↦ hyS P (Finset.mem_union_right _ hP)) hU

end Normal

section Localized

/-- Zariski–Nagata purity at a prime of a non-local ring (Stacks 0BMB). Let `p` be a prime of `A`
with `A_p` regular of dimension `≥ 2`, `B` a finite `A`-algebra and `x, y ∈ p` a regular sequence
on `A` and on `B`. If `B` is étale over `A` at every prime lying over a prime strictly contained
in `p`, then `B` is étale over `A` at every prime lying over `p`: localize at `p` and apply
`IsRegularLocalRing.etale_of_isWeaklyRegular_of_two_le_ringKrullDim`. -/
theorem Algebra.isEtaleAt_of_isWeaklyRegular {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (p : Ideal A) [p.IsPrime] [IsRegularLocalRing (Localization.AtPrime p)]
    (hdim : 2 ≤ ringKrullDim (Localization.AtPrime p)) {x y : A} (hx : x ∈ p) (hy : y ∈ p)
    (hA : IsWeaklyRegular A [x, y]) (hreg : IsWeaklyRegular B [x, y])
    (hU : ∀ (q : Ideal B) [q.IsPrime], q.comap (algebraMap A B) ≤ p →
      q.comap (algebraMap A B) ≠ p → Algebra.IsEtaleAt A q)
    (q : Ideal B) [q.IsPrime] (hq : q.comap (algebraMap A B) = p) : Algebra.IsEtaleAt A q := by
  let M := p.primeCompl
  let Ap := Localization.AtPrime p
  let Bp := Localization (Algebra.algebraMapSubmonoid B M)
  -- `[x, y]` stays regular on `Bp`
  have hloc : IsLocalizedModule M (IsScalarTower.toAlgHom A B Bp).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have hregp : IsWeaklyRegular Bp [algebraMap A Ap x, algebraMap A Ap y] :=
    hreg.of_isLocalizedModule Ap M (IsScalarTower.toAlgHom A B Bp).toLinearMap
  have hmem : ∀ z ∈ p, algebraMap A Ap z ∈ maximalIdeal Ap := fun z hz ↦
    (IsLocalization.AtPrime.to_map_mem_maximal_iff Ap p z).mpr hz
  have hEt : Algebra.Etale Ap Bp := by
    refine IsRegularLocalRing.etale_of_isWeaklyRegular_of_two_le_ringKrullDim hdim (hmem x hx)
      (hmem y hy) (hA.of_isLocalization Ap M) hregp fun Q _ hQ ↦ ?_
    let q' := Q.comap (algebraMap B Bp)
    let P := Q.comap (algebraMap Ap Bp)
    have hq' : q'.comap (algebraMap A B) = P.comap (algebraMap A Ap) := by
      simp only [q', P, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    have hPle : P.comap (algebraMap A Ap) ≤ p := by
      exact (Ideal.comap_mono (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))).trans
        (IsLocalization.AtPrime.under_maximalIdeal Ap p).le
    have hPne : P.comap (algebraMap A Ap) ≠ p := by
      intro h
      apply hQ
      change P = _
      have h' : Ideal.map (algebraMap A Ap) (Ideal.comap (algebraMap A Ap) P) = P :=
        IsLocalization.map_under M Ap P
      rw [h] at h'
      rw [← h']
      exact IsLocalization.AtPrime.map_eq_maximalIdeal p Ap
    have := hU q' (hq' ▸ hPle) (hq' ▸ hPne)
    have e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Algebra.algebraMapSubmonoid B M) Q
    have : Algebra.FormallyEtale A (Localization.AtPrime Q) :=
      Algebra.FormallyEtale.of_equiv (e.restrictScalars A)
    have : Algebra.FormallyUnramified A Ap :=
      Algebra.FormallyUnramified.of_isLocalization M
    exact Algebra.FormallyEtale.of_restrictScalars (R := A)
  -- conclusion at `q`
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid B M : Set B) q := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsq
    apply hs
    rw [← hq]
    exact hsq
  let Q := q.map (algebraMap B Bp)
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Bp q ‹_› hdisj
  have hQq : Q.comap (algebraMap B Bp) = q :=
    IsLocalization.under_map_of_isPrime_disjoint _ Bp ‹_› hdisj
  have : Algebra.FormallyEtale A Ap := Algebra.FormallyEtale.of_isLocalization M
  have : Algebra.FormallyEtale A (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.comp A Ap _
  have e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Algebra.algebraMapSubmonoid B M) Q
  have hL : IsLocalization.AtPrime (Localization.AtPrime Q) (Q.comap (algebraMap B Bp)) :=
    inferInstance
  have : IsLocalization.AtPrime (Localization.AtPrime Q) q := by
    convert hL using 2; exact hQq.symm
  let e' : Localization.AtPrime q ≃ₐ[B] Localization.AtPrime Q :=
    IsLocalization.algEquiv q.primeCompl _ _
  exact Algebra.FormallyEtale.of_equiv (e'.restrictScalars A).symm

/-- Purity along a closed subset of codimension `≥ 2` of a noetherian ring (SGA 1 X.3.3 in algebraic
form). Let `x, y` be a regular sequence on the noetherian ring `A` and on the finite `A`-algebra
`B`, and `T` a set of primes of `A` such that `B` is étale over `A` above `T`, while every prime
`p ∉ T` contains `x, y` and has `A_p` regular of dimension `≥ 2`. Then `B` is étale over `A`.

By induction on the height of `p ∉ T`, using `Algebra.isEtaleAt_of_isWeaklyRegular`. -/
theorem Algebra.etale_of_isWeaklyRegular_of_forall_notMem {A B : Type u} [CommRing A]
    [IsNoetherianRing A] [CommRing B] [Algebra A B] [Module.Finite A B] {x y : A}
    (hA : IsWeaklyRegular A [x, y]) (hB : IsWeaklyRegular B [x, y]) (T : Set (Ideal A))
    (hT : ∀ (q : Ideal B) [q.IsPrime], q.comap (algebraMap A B) ∈ T → Algebra.IsEtaleAt A q)
    (hnT : ∀ (p : Ideal A) [p.IsPrime], p ∉ T → x ∈ p ∧ y ∈ p ∧
      IsRegularLocalRing (Localization.AtPrime p) ∧ 2 ≤ ringKrullDim (Localization.AtPrime p)) :
    Algebra.Etale A B := by
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have key : ∀ n : ℕ, ∀ (q : Ideal B) [q.IsPrime],
      (q.comap (algebraMap A B)).height = n → Algebra.IsEtaleAt A q := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro q _ hqn
      by_cases hpT : q.comap (algebraMap A B) ∈ T
      · exact hT q hpT
      obtain ⟨hx, hy, hreg, hdim⟩ := hnT _ hpT
      have := hreg
      refine Algebra.isEtaleAt_of_isWeaklyRegular _ hdim hx hy hA hB (fun q' _ hle hne ↦ ?_) q rfl
      have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle hne)
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
        (Ideal.height_ne_top_of_isPrime (I := q'.comap (algebraMap A B)))
      rw [← hm, hqn] at hlt
      exact ih m (by exact_mod_cast hlt) q' hm.symm
  refine Algebra.etaleLocus_eq_univ_iff_etale.mp (Set.eq_univ_of_forall fun q ↦ ?_)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ideal.height_ne_top_of_isPrime (I := q.asIdeal.comap (algebraMap A B)))
  exact key n q.asIdeal hn.symm

end Localized
