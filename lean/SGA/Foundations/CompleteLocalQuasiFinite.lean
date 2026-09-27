/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.ZariskisMainTheorem
import SGA.Foundations.Formal.AdicRing

/-!
# Quasi-finite algebras over a complete noetherian local ring

Let `A` be a complete noetherian local ring.

* A finite `A`-algebra `T` is complete (`IsAdicComplete.of_finite`, in
  `SGA.Foundations.Formal.AdicRing`), hence henselian along `𝔪_A T`
  (`IsAdicComplete.henselianRing_of_finite`), so idempotents lift modulo `𝔪_A T`
  (`HenselianRing.exists_isIdempotentElem_sub_mem`).
* `IsLocalRing.exists_isIdempotentElem_forall_le_of_finite`: a finite `A`-algebra splits off its
  local factor at a maximal ideal (Stacks 04GG (10)).
* `IsLocalRing.exists_notMem_forall_le_and_finite`: if `S` is an `A`-algebra of finite type,
  quasi-finite at a prime `q` over `𝔪_A`, the generizations of `q` form an open subset `D(e)` of
  `Spec S` with `S_e` finite over `A` (Stacks 04GJ, EGA IV 18.5.11 and 18.12.1). The proof
  combines Zariski's main theorem (mathlib's
  `Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`) with the splitting of
  finite algebras.
* `Ideal.IsPrime.isMaximal_of_forall_ne_bot`: in a noetherian domain whose generic point is open,
  nonzero primes are maximal (Krull's principal ideal theorem).
-/

open IsLocalRing Polynomial

universe u

namespace IsAdicComplete

/-- A finite algebra `T` over a noetherian `I`-adically complete ring is henselian along `I T`. -/
theorem henselianRing_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (T : Type*) [CommRing T] [Algebra R T] [Module.Finite R T] :
    HenselianRing T (I.map (algebraMap R T)) :=
  have : IsAdicComplete I T := of_finite I T
  have : IsAdicComplete (I.map (algebraMap R T)) T := (map_algebraMap_iff ..).mpr this
  inferInstance

end IsAdicComplete

/-- In a ring henselian along `I`, idempotents lift modulo `I`. -/
theorem HenselianRing.exists_isIdempotentElem_sub_mem {R : Type*} [CommRing R] {I : Ideal R}
    [HenselianRing R I] {a : R} (ha : a * a - a ∈ I) :
    ∃ e : R, IsIdempotentElem e ∧ e - a ∈ I := by
  have hmonic : (X ^ 2 - X : R[X]).Monic :=
    monic_X_pow_sub (degree_X_le.trans_lt (by exact_mod_cast one_lt_two))
  obtain ⟨e, he, hea⟩ := HenselianRing.is_henselian (X ^ 2 - X : R[X]) hmonic a
    (by simpa [sq] using ha) (by
      have : (Ideal.Quotient.mk I (derivative (X ^ 2 - X : R[X]) |>.eval a)) ^ 2 = 1 := by
        rw [← map_pow, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
        have : (derivative (X ^ 2 - X : R[X])).eval a ^ 2 - 1 = 4 * (a * a - a) := by
          simp; ring
        rw [this]
        exact I.mul_mem_left _ ha
      exact IsUnit.of_pow_eq_one this two_ne_zero)
  refine ⟨e, ?_, hea⟩
  simpa [IsIdempotentElem, sub_eq_zero, sq] using he

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (maximalIdeal A) A]

/-- Over a complete noetherian local ring `A`, a finite `A`-algebra `T` splits off the local
factor at a maximal ideal `q`: there is an idempotent `e ∉ q` such that every prime of `T` not
containing `e` is contained in `q` (Stacks 04GG (10), EGA IV 18.5.11). -/
theorem exists_isIdempotentElem_forall_le_of_finite (T : Type*) [CommRing T] [Algebra A T]
    [Module.Finite A T] (q : Ideal T) [q.IsMaximal] :
    ∃ e : T, IsIdempotentElem e ∧ e ∉ q ∧ ∀ P : Ideal T, P.IsPrime → e ∉ P → P ≤ q := by
  classical
  have : IsNoetherianRing T := isNoetherian_of_tower A inferInstance
  set I := (maximalIdeal A).map (algebraMap A T)
  -- maximal ideals of `T` contain `I`
  have hmax (n : Ideal T) (hn : n.IsMaximal) : I ≤ n := by
    rw [Ideal.map_le_iff_le_comap]
    exact (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n)).ge
  -- primes containing `I` are maximal
  have hprime (P : Ideal T) (hP : P.IsPrime) (hIP : I ≤ P) : P.IsMaximal := by
    have : (P.comap (algebraMap A T)).IsMaximal := by
      rw [show P.comap (algebraMap A T) = maximalIdeal A from
        (le_maximalIdeal (Ideal.comap_ne_top _ hP.ne_top)).antisymm
          (Ideal.map_le_iff_le_comap.mp hIP)]
      infer_instance
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P this
  have hfin := I.finite_minimalPrimes_of_isNoetherianRing
  have hmin (n : Ideal T) (hn : n.IsMaximal) : n ∈ I.minimalPrimes :=
    ⟨⟨hn.isPrime, hmax n hn⟩, fun P ⟨hP, hIP⟩ hPn ↦ ((hprime P hP hIP).eq_of_le hn.ne_top hPn).ge⟩
  let s := (hfin.toFinset.erase q)
  have hs : q ⊔ ⨅ P ∈ s, P = ⊤ := by
    refine Ideal.sup_iInf_eq_top fun P hP ↦ ?_
    simp only [s, Finset.mem_erase, Set.Finite.mem_toFinset] at hP
    have := hprime P hP.2.1.1 hP.2.1.2
    exact Ideal.IsMaximal.coprime_of_ne ‹_› this (Ne.symm hP.1)
  obtain ⟨x, hx, a, ha, hxa⟩ := Submodule.mem_sup.mp (hs.ge (Submodule.mem_top (x := 1)))
  have ha' (n : Ideal T) (hn : n.IsMaximal) (hnq : n ≠ q) : a ∈ n := by
    simp only [Submodule.mem_iInf] at ha
    exact ha n (by simp [s, hnq, hmin n hn])
  have h1a : 1 - a ∈ q := by rw [← hxa]; simpa using hx
  -- `a (1 - a)` lies in every prime containing `I`, hence in the radical of `I`
  have hrad : a * (1 - a) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hIP, hP⟩
    have := hprime P hP hIP
    by_cases hPq : P = q
    · subst hPq; exact Ideal.mul_mem_left _ _ h1a
    · exact Ideal.mul_mem_right _ _ (ha' P this hPq)
  obtain ⟨N, hN⟩ := hrad
  have hN0 : 0 < N := by
    refine Nat.pos_of_ne_zero fun h ↦ ?_
    rw [h, pow_zero] at hN
    exact (Ideal.IsMaximal.ne_top ‹q.IsMaximal›)
      (q.eq_top_of_isUnit_mem (hmax q inferInstance hN) isUnit_one)
  obtain ⟨u, v, huv⟩ := (show IsCoprime a (1 - a) from ⟨1, 1, by ring⟩).pow (m := N) (n := N)
  have hε : u * a ^ N * (u * a ^ N) - u * a ^ N ∈ I := by
    have : u * a ^ N * (u * a ^ N) - u * a ^ N = -(u * v * (a * (1 - a)) ^ N) := by
      rw [mul_pow]; linear_combination (u * a ^ N) * huv
    rw [this]
    exact I.neg_mem (Ideal.mul_mem_left _ _ hN)
  have := IsAdicComplete.henselianRing_of_finite (maximalIdeal A) T
  obtain ⟨e, he, heε⟩ := HenselianRing.exists_isIdempotentElem_sub_mem hε
  have he_n (n : Ideal T) (hn : n.IsMaximal) (hnq : n ≠ q) : e ∈ n := by
    have : e = (e - u * a ^ N) + u * a ^ N := by ring
    rw [this]
    exact n.add_mem (hmax n hn heε)
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (ha' n hn hnq) _ hN0))
  have he_q : 1 - e ∈ q := by
    have : 1 - e = v * (1 - a) ^ N - (e - u * a ^ N) := by linear_combination -huv
    rw [this]
    exact q.sub_mem (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ h1a _ hN0))
      (hmax q inferInstance heε)
  have he_q' : e ∉ q := fun h ↦ (Ideal.IsMaximal.ne_top inferInstance)
    (q.eq_top_of_isUnit_mem (by simpa using q.add_mem h he_q) isUnit_one)
  refine ⟨e, he, he_q', fun P hP heP ↦ ?_⟩
  obtain ⟨n, hn, hPn⟩ := P.exists_le_maximal hP.ne_top
  by_cases hnq : n = q
  · exact hnq ▸ hPn
  · have h1e : 1 - e ∈ P := (hP.mem_or_mem (show e * (1 - e) ∈ P by
      rw [mul_sub, mul_one, he.eq, sub_self]; exact P.zero_mem)).resolve_left heP
    exact absurd (n.eq_top_of_isUnit_mem (by simpa using n.add_mem (he_n n hn hnq) (hPn h1e))
      isUnit_one) hn.ne_top

/-- Over a complete noetherian local ring `A`, let `S` be an `A`-algebra of finite type and `q` a
prime of `S` over the maximal ideal of `A` at which `S` is quasi-finite. Then there is `e ∈ S`,
`e ∉ q`, such that every prime of `S` not containing `e` is contained in `q` and the localization
`S_e` is finite over `A`. Geometrically: the generizations of `q` form the open subset
`D(e) = Spec S_e`, which is finite over `A`; in particular `S_q = S_e` is finite over `A`
(Stacks 04GG (10) and 04GJ, EGA IV 18.5.11 and 18.12.1). -/
theorem exists_notMem_forall_le_and_finite {S : Type u} [CommRing S] [Algebra A S]
    [Algebra.FiniteType A S] (q : Ideal S) [q.IsPrime] [q.LiesOver (maximalIdeal A)]
    [Algebra.QuasiFiniteAt A q] :
    ∃ e : S, e ∉ q ∧ (∀ P : Ideal S, P.IsPrime → e ∉ P → P ≤ q) ∧
      ∀ (L : Type u) [CommRing L] [Algebra S L] [IsLocalization.Away e L] [Algebra A L]
        [IsScalarTower A S L], Module.Finite A L := by
  classical
  obtain ⟨S', hS', r, hrq, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := A) q
  have : Module.Finite A S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  let q' : Ideal S' := q.comap S'.val
  have hq' : q'.IsMaximal := by
    have : (q'.comap (algebraMap A S')).IsMaximal := by
      rw [show q'.comap (algebraMap A S') = maximalIdeal A from
        (Ideal.over_def q (maximalIdeal A)).symm]
      infer_instance
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q' this
  obtain ⟨e, he, heq', hle⟩ := exists_isIdempotentElem_forall_le_of_finite (A := A) S' q'
  -- `r` is invertible on `D(e)`
  obtain ⟨r', hr'⟩ : ∃ r' : S', r * r' * e = e := by
    have htop : Ideal.span {r, 1 - e} = ⊤ := by
      by_contra h
      obtain ⟨n, hn, hle'⟩ := Ideal.exists_le_maximal _ h
      have h1e : 1 - e ∈ n := hle' (Ideal.subset_span (by simp))
      have hen : e ∉ n := fun h ↦ hn.ne_top
        (n.eq_top_of_isUnit_mem (by simpa using n.add_mem h h1e) isUnit_one)
      exact hrq (hle n hn.isPrime hen (hle' (Ideal.subset_span (by simp))))
    obtain ⟨a, b, hab⟩ : ∃ a b : S', a * r + b * (1 - e) = 1 := by
      have := htop.ge (Submodule.mem_top (x := 1))
      rw [Ideal.span_insert, Submodule.mem_sup] at this
      obtain ⟨x, hx, y, hy, hxy⟩ := this
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      exact ⟨a, b, hxy⟩
    refine ⟨a, ?_⟩
    have : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
    linear_combination e * hab - b * this
  set E : S := e.1
  have hE : E * E = E := congrArg Subtype.val he.eq
  have hrE (j : ℕ) : (r.1 * r'.1) ^ j * E = E := by
    induction j with
    | zero => simp
    | succ j ih =>
      have : r.1 * r'.1 * E = E := congrArg Subtype.val hr'
      rw [pow_succ, mul_assoc, this, ih]
  -- `e S ⊆ S'`
  have key (s : S) : ∃ t : S', E * s = E * t := by
    obtain ⟨x, hx⟩ := hbij.2 (algebraMap S (Localization.Away r.1) s)
    obtain ⟨⟨t, _, m, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) x
    have hx' : algebraMap S (Localization.Away r.1) t.1 =
        algebraMap S (Localization.Away r.1) (s * r.1 ^ m) := by
      rw [map_mul, ← IsLocalization.mk'_eq_iff_eq_mul (M := Submonoid.powers r.1)
        (y := ⟨r.1 ^ m, m, rfl⟩), ← hx]
      simp only [Localization.awayMap, IsLocalization.Away.map]
      rw [IsLocalization.map_mk']
      rfl
    rw [IsLocalization.eq_iff_exists (Submonoid.powers r.1)] at hx'
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := hx'
    refine ⟨r' ^ m * t, ?_⟩
    have h1 := hrE (k + m)
    have h2 := hrE k
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
    linear_combination -(r'.1 ^ (k + m) * E) * hk - s * h1 + (r'.1 ^ m * t.1) * h2
  refine ⟨E, heq', fun P hP hEP ↦ ?_, fun L _ _ _ _ _ ↦ ?_⟩
  · intro s hs
    obtain ⟨t, ht⟩ := key s
    have htP : t ∈ P.comap S'.val := by
      have : E * t ∈ P := ht ▸ Ideal.mul_mem_left _ _ hs
      exact (hP.mem_or_mem this).resolve_left hEP
    have := hle (P.comap S'.val) (Ideal.comap_isPrime _ _) hEP htP
    have : E * s ∈ q := ht ▸ Ideal.mul_mem_left _ _ this
    exact ((inferInstance : q.IsPrime).mem_or_mem this).resolve_left heq'
  · have hunit : IsUnit (algebraMap S L E) := IsLocalization.Away.algebraMap_isUnit E
    have h1 : algebraMap S L E = 1 :=
      (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp (by
        rw [IsIdempotentElem, ← map_mul, hE])
    let f : S' →ₗ[A] L := (IsScalarTower.toAlgHom A S L).toLinearMap ∘ₗ S'.val.toLinearMap
    refine Module.Finite.of_surjective f fun l ↦ ?_
    obtain ⟨⟨s, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers E) l
    obtain ⟨t, ht⟩ := key s
    refine ⟨e * t, ?_⟩
    simp only [f, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      Subalgebra.coe_val, Subalgebra.coe_mul, IsScalarTower.coe_toAlgHom']
    rw [← ht, eq_comm, IsLocalization.mk'_eq_iff_eq_mul, map_mul]
    simp [h1]

end IsLocalRing

/-- In a noetherian domain whose generic point is open, i.e. which has an element `f ≠ 0` lying
in every nonzero prime, every nonzero prime is maximal. (A consequence of Krull's principal ideal
theorem and prime avoidance: such a domain has dimension at most one.) -/
theorem Ideal.IsPrime.isMaximal_of_forall_ne_bot {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsDomain R] {f : R} (hf : f ≠ 0) (H : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ → f ∈ P)
    {P : Ideal R} (hP : P.IsPrime) (hP0 : P ≠ ⊥) : P.IsMaximal := by
  classical
  by_contra hmax
  obtain ⟨M, hM, hPM⟩ := P.exists_le_maximal hP.ne_top
  have hPM' : P < M := lt_of_le_of_ne hPM fun h ↦ hmax (h ▸ hM)
  have hfin := (Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  -- `M` has height at least two
  have h2 : (2 : ℕ∞) ≤ M.height := by
    have h₁ := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hP0)
    have h₂ := Ideal.height_add_one_le_of_lt_of_isPrime hPM'
    rw [Ideal.height_bot, zero_add] at h₁
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ P.height + 1 := by gcongr
      _ ≤ M.height := h₂
  -- prime avoidance
  have hav : ¬ ((M : Set R) ⊆
      ⋃ Q ∈ (↑hfin.toFinset : Set (Ideal R)), ((id Q : Ideal R) : Set R)) := by
    rw [Ideal.subset_union_prime (f := id) ⊤ ⊤ fun Q hQ _ _ ↦ by
      simp only [Set.Finite.mem_toFinset] at hQ; exact hQ.1.1]
    rintro ⟨Q, hQ, hMQ⟩
    simp only [Set.Finite.mem_toFinset] at hQ
    have hQM : Q = M := (hM.eq_of_le hQ.1.1.ne_top hMQ).symm
    have := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
    rw [hQM] at this
    exact absurd (h2.trans this) (by norm_num)
  obtain ⟨a, haM, ha⟩ := Set.not_subset.mp hav
  simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, id, SetLike.mem_coe,
    not_exists] at ha
  have hf_top : Ideal.span {f} ≠ ⊤ := fun h ↦ hP.ne_top (Ideal.eq_top_iff_one _ |>.mpr <|
    (Ideal.span_singleton_le_iff_mem _).mpr (H P hP hP0) (h ▸ Submodule.mem_top))
  obtain ⟨⟨Q₁, hQ₁⟩⟩ := Ideal.nonempty_minimalPrimes hf_top
  have ha0 : a ≠ 0 := fun h ↦ ha Q₁ hQ₁ (h ▸ Q₁.zero_mem)
  obtain ⟨Q₀, hQ₀, hQ₀M⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem M).mpr haM)
  have haQ₀ : a ∈ Q₀ := hQ₀.1.2 (Ideal.mem_span_singleton_self a)
  have hQ₀0 : Q₀ ≠ ⊥ := fun h ↦ ha0 (by simpa [h] using haQ₀)
  have := hQ₀.1.1
  have hfQ₀ : f ∈ Q₀ := H Q₀ this hQ₀0
  obtain ⟨Q₂, hQ₂, hQ₂Q₀⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem Q₀).mpr hfQ₀)
  have := hQ₂.1.1
  have hQ₂0 : Q₂ ≠ ⊥ := fun h ↦ hf (by simpa [h] using hQ₂.1.2 (Ideal.mem_span_singleton_self f))
  have hQ₀h := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q₀ hQ₀
  rcases eq_or_lt_of_le hQ₂Q₀ with h | h
  · exact ha Q₂ hQ₂ (h ▸ haQ₀)
  · have h₁ := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hQ₂0)
    have h₂ := Ideal.height_add_one_le_of_lt_of_isPrime h
    rw [Ideal.height_bot, zero_add] at h₁
    have : (2 : ℕ∞) ≤ Q₀.height := calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ Q₂.height + 1 := by gcongr
      _ ≤ Q₀.height := h₂
    exact absurd (this.trans hQ₀h) (by norm_num)
