/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import SGA.Foundations.CommAlg.BasicOpenHartogs
import SGA.Foundations.CommAlg.RegularPair

/-!
# Sections over `D(a) ∪ D(b)`

For a commutative ring `R` and `a, b ∈ R`, the sections of the structure sheaf of `Spec R` over
`D(a) ∪ D(b)` are the pairs `(s, t) ∈ R_a × R_b` which agree in `R_{ab}`
(`Localization.pairSections a b`). This file studies this `R`-algebra algebraically:

* `Localization.bijective_algebraMap_pairSections`: if `a, b` is a regular sequence on `R`, the
  map `R → pairSections a b` is bijective (Hartogs extension across `V(a, b)`).
* `Localization.isLocalization_pairSectionsFst`, `Localization.isLocalization_pairSectionsSnd`:
  the localizations of `pairSections a b` at `a` and `b` are `R_a` and `R_b`;
  `Localization.exists_isLocalization_pairSections_away`: more generally its localization at any
  `g` such that `a, b` is regular on `R_g` is `R_g`.
* `Localization.isWeaklyRegular_pairSections`: `a, b` is a regular sequence on
  `pairSections a b` as soon as `a` is a nonzerodivisor on `R_b`.

These are used for the "S₂-hull" of a module over a regular local ring in the proof of purity.
-/

open RingTheory.Sequence

namespace Localization

variable {R : Type*} [CommRing R] (a b : R)

/-- The restriction `R_a → R_{ab}`. -/
noncomputable def awayToMulRight : Localization.Away a →ₐ[R] Localization.Away (a * b) where
  __ := IsLocalization.Away.awayToAwayRight (S := Localization.Away a) a b
  commutes' r := IsLocalization.Away.awayToAwayRight_eq a b r

/-- The restriction `R_b → R_{ab}`. -/
noncomputable def awayToMulLeft : Localization.Away b →ₐ[R] Localization.Away (a * b) where
  __ := IsLocalization.Away.awayToAwayLeft (S := Localization.Away b) b a
  commutes' r := IsLocalization.Away.awayToAwayLeft_eq b a r

@[simp]
lemma awayToMulRight_algebraMap (r : R) :
    awayToMulRight a b (algebraMap R _ r) = algebraMap R _ r :=
  (awayToMulRight a b).commutes r

@[simp]
lemma awayToMulLeft_algebraMap (r : R) :
    awayToMulLeft a b (algebraMap R _ r) = algebraMap R _ r :=
  (awayToMulLeft a b).commutes r

/-- The sections of `Spec R` over `D(a) ∪ D(b)`: pairs `(s, t) ∈ R_a × R_b` agreeing in
`R_{ab}`. -/
noncomputable def pairSections : Subalgebra R (Localization.Away a × Localization.Away b) :=
  AlgHom.equalizer ((awayToMulRight a b).comp (AlgHom.fst R _ _))
    ((awayToMulLeft a b).comp (AlgHom.snd R _ _))

lemma mem_pairSections {p : Localization.Away a × Localization.Away b} :
    p ∈ pairSections a b ↔ awayToMulRight a b p.1 = awayToMulLeft a b p.2 := Iff.rfl

@[simp]
lemma algebraMap_pairSections_fst (r : R) :
    (algebraMap R (pairSections a b) r).1.1 = algebraMap R _ r := rfl

@[simp]
lemma algebraMap_pairSections_snd (r : R) :
    (algebraMap R (pairSections a b) r).1.2 = algebraMap R _ r := rfl

/-- **Hartogs extension across `V(a, b)`**: if `a, b` is a regular sequence on `R`, every
section over `D(a) ∪ D(b)` comes from a unique element of `R`. -/
theorem bijective_algebraMap_pairSections (hab : IsWeaklyRegular R [a, b]) :
    Function.Bijective (algebraMap R (pairSections a b)) := by
  have ha : IsSMulRegular R a := ((isWeaklyRegular_cons_iff R a [b]).mp hab).1
  constructor
  · intro r₁ r₂ h
    have h1 := congrArg (fun p : pairSections a b ↦ p.1.1) h
    simp only [algebraMap_pairSections_fst] at h1
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers a) h1
    exact (ha.pow n) (by simpa [smul_eq_mul] using hn)
  · rintro ⟨⟨s, t⟩, hst⟩
    rw [mem_pairSections] at hst
    simp only at hst
    obtain ⟨⟨r₁, ⟨_, n, rfl⟩⟩, hs⟩ := IsLocalization.surj (Submonoid.powers a) s
    obtain ⟨⟨r₂, ⟨_, m, rfl⟩⟩, ht⟩ := IsLocalization.surj (Submonoid.powers b) t
    simp only at hs ht
    -- in `R_{ab}`, `b^m r₁ = a^n r₂`
    have h1 := congrArg (awayToMulRight a b) hs
    have h2 := congrArg (awayToMulLeft a b) ht
    simp only [map_mul, awayToMulRight_algebraMap, awayToMulLeft_algebraMap] at h1 h2
    have h3 : algebraMap R (Localization.Away (a * b)) (b ^ m * r₁) =
        algebraMap R (Localization.Away (a * b)) (a ^ n * r₂) := by
      rw [map_mul, map_mul, ← h1, ← h2, hst]
      ring
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (a * b)) h3
    simp only at hk
    -- cancel the powers of `a`
    have hk' : b ^ (k + m) * r₁ = a ^ n * (b ^ k * r₂) := by
      apply ha.pow k
      simp only [smul_eq_mul]
      linear_combination hk
    obtain ⟨e, rfl⟩ := hab.pow_dvd_of_pow_dvd_pow_mul n (k + m) ⟨_, hk'⟩
    have he : b ^ (k + m) * e = b ^ k * r₂ := by
      apply ha.pow n
      simp only [smul_eq_mul]
      linear_combination hk'
    refine ⟨e, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change algebraMap R _ e = s
      have hu : IsUnit (algebraMap R (Localization.Away a) (a ^ n)) :=
        IsLocalization.map_units _ (⟨a ^ n, n, rfl⟩ : Submonoid.powers a)
      apply hu.mul_left_injective
      simp only [hs, ← map_mul, mul_comm]
    · change algebraMap R _ e = t
      have hu : IsUnit (algebraMap R (Localization.Away b) (b ^ (k + m))) :=
        IsLocalization.map_units _ (⟨b ^ (k + m), k + m, rfl⟩ : Submonoid.powers b)
      apply hu.mul_left_injective
      simp only [← map_mul]
      rw [mul_comm, he, pow_add, map_mul, map_mul, ← ht]
      ring

/-- If the restriction to `R_{ab}` of `t ∈ R_b` vanishes, `t` is killed by a power of `a`. -/
lemma exists_pow_mul_eq_zero_of_awayToMulLeft {t : Localization.Away b}
    (ht : awayToMulLeft a b t = 0) : ∃ n : ℕ, algebraMap R _ (a ^ n) * t = 0 := by
  obtain ⟨⟨r, ⟨_, m, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers b) t
  simp only at hr
  have h := congrArg (awayToMulLeft a b) hr
  rw [map_mul, ht, zero_mul, awayToMulLeft_algebraMap, eq_comm] at h
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (a * b)) _ r).mp h
  simp only at hk
  refine ⟨k, ?_⟩
  have hu : IsUnit (algebraMap R (Localization.Away b) (b ^ (k + m))) :=
    IsLocalization.map_units _ (⟨b ^ (k + m), k + m, rfl⟩ : Submonoid.powers b)
  apply hu.mul_left_injective
  simp only [zero_mul]
  calc algebraMap R _ (a ^ k) * t * algebraMap R _ (b ^ (k + m))
      = algebraMap R _ (a ^ k * b ^ k) * (t * algebraMap R _ (b ^ m)) := by
        simp only [map_mul, map_pow, pow_add]; ring
    _ = 0 := by rw [hr, ← map_mul, ← mul_pow, hk, map_zero]

/-- If the restriction to `R_{ab}` of `s ∈ R_a` vanishes, `s` is killed by a power of `b`. -/
lemma exists_pow_mul_eq_zero_of_awayToMulRight {s : Localization.Away a}
    (hs : awayToMulRight a b s = 0) : ∃ n : ℕ, algebraMap R _ (b ^ n) * s = 0 := by
  obtain ⟨⟨r, ⟨_, m, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers a) s
  simp only at hr
  have h := congrArg (awayToMulRight a b) hr
  rw [map_mul, hs, zero_mul, awayToMulRight_algebraMap, eq_comm] at h
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (a * b)) _ r).mp h
  simp only at hk
  refine ⟨k, ?_⟩
  have hu : IsUnit (algebraMap R (Localization.Away a) (a ^ (k + m))) :=
    IsLocalization.map_units _ (⟨a ^ (k + m), k + m, rfl⟩ : Submonoid.powers a)
  apply hu.mul_left_injective
  simp only [zero_mul]
  calc algebraMap R _ (b ^ k) * s * algebraMap R _ (a ^ (k + m))
      = algebraMap R _ (a ^ k * b ^ k) * (s * algebraMap R _ (a ^ m)) := by
        simp only [map_mul, map_pow, pow_add]; ring
    _ = 0 := by rw [hr, ← map_mul, ← mul_pow, hk, map_zero]

/-- The first projection `pairSections a b → R_a`. -/
noncomputable def pairSectionsFst : pairSections a b →ₐ[R] Localization.Away a :=
  (AlgHom.fst R _ _).comp (pairSections a b).val

/-- The second projection `pairSections a b → R_b`. -/
noncomputable def pairSectionsSnd : pairSections a b →ₐ[R] Localization.Away b :=
  (AlgHom.snd R _ _).comp (pairSections a b).val

/-- `R_a` is the localization of `pairSections a b` at `a`. -/
theorem isLocalization_pairSectionsFst :
    letI := (pairSectionsFst a b).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (pairSections a b) a) (Localization.Away a) := by
  let _ := (pairSectionsFst a b).toRingHom.toAlgebra
  have hfst : ∀ r : R, algebraMap (pairSections a b) (Localization.Away a)
      (algebraMap R _ r) = algebraMap R _ r := fun r ↦ (pairSectionsFst a b).commutes r
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, n, rfl⟩
    change IsUnit (algebraMap (pairSections a b) (Localization.Away a)
      (algebraMap R _ a ^ n))
    rw [← map_pow, hfst, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit a).pow n
  · intro z
    obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers a) z
    refine ⟨⟨algebraMap R _ r, ⟨algebraMap R _ a ^ n, n, rfl⟩⟩, ?_⟩
    simp only [← map_pow, hfst]
    exact hr
  · intro p₁ p₂ h
    suffices H : ∀ p : pairSections a b, algebraMap _ (Localization.Away a) p = 0 →
        ∃ n : ℕ, algebraMap R (pairSections a b) a ^ n * p = 0 by
      obtain ⟨n, hn⟩ := H (p₁ - p₂) (by rw [map_sub, h, sub_self])
      exact ⟨⟨_, n, rfl⟩, by rw [← sub_eq_zero, ← mul_sub]; exact hn⟩
    rintro ⟨⟨s, t⟩, hst⟩ hs
    change s = 0 at hs
    subst hs
    rw [mem_pairSections, map_zero, eq_comm] at hst
    obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_awayToMulLeft a b hst
    refine ⟨n, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change (algebraMap R _ a ^ n : pairSections a b).1.1 * 0 = 0
      rw [mul_zero]
    · change (algebraMap R (pairSections a b) a ^ n).1.2 * t = 0
      rw [← map_pow]
      exact hn

/-- `R_b` is the localization of `pairSections a b` at `b`. -/
theorem isLocalization_pairSectionsSnd :
    letI := (pairSectionsSnd a b).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (pairSections a b) b) (Localization.Away b) := by
  let _ := (pairSectionsSnd a b).toRingHom.toAlgebra
  have hsnd : ∀ r : R, algebraMap (pairSections a b) (Localization.Away b)
      (algebraMap R _ r) = algebraMap R _ r := fun r ↦ (pairSectionsSnd a b).commutes r
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, n, rfl⟩
    change IsUnit (algebraMap (pairSections a b) (Localization.Away b)
      (algebraMap R _ b ^ n))
    rw [← map_pow, hsnd, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit b).pow n
  · intro z
    obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers b) z
    refine ⟨⟨algebraMap R _ r, ⟨algebraMap R _ b ^ n, n, rfl⟩⟩, ?_⟩
    simp only [← map_pow, hsnd]
    exact hr
  · intro p₁ p₂ h
    suffices H : ∀ p : pairSections a b, algebraMap _ (Localization.Away b) p = 0 →
        ∃ n : ℕ, algebraMap R (pairSections a b) b ^ n * p = 0 by
      obtain ⟨n, hn⟩ := H (p₁ - p₂) (by rw [map_sub, h, sub_self])
      exact ⟨⟨_, n, rfl⟩, by rw [← sub_eq_zero, ← mul_sub]; exact hn⟩
    rintro ⟨⟨s, t⟩, hst⟩ ht
    change t = 0 at ht
    subst ht
    rw [mem_pairSections, map_zero] at hst
    obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_awayToMulRight a b hst
    refine ⟨n, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change (algebraMap R (pairSections a b) b ^ n).1.1 * s = 0
      rw [← map_pow]
      exact hn
    · change (algebraMap R _ b ^ n : pairSections a b).1.2 * 0 = 0
      rw [mul_zero]

/-- `a, b` is a regular sequence on `pairSections a b` as soon as `a` is a nonzerodivisor on
`R_b`. -/
theorem isWeaklyRegular_pairSections (ha : IsSMulRegular (Localization.Away b)
    (algebraMap R (Localization.Away b) a)) :
    IsWeaklyRegular (pairSections a b)
      [algebraMap R (pairSections a b) a, algebraMap R (pairSections a b) b] := by
  rw [isWeaklyRegular_pair_iff]
  have hau : IsUnit (algebraMap R (Localization.Away a) a) :=
    IsLocalization.Away.algebraMap_isUnit a
  have hbu : IsUnit (algebraMap R (Localization.Away b) b) :=
    IsLocalization.Away.algebraMap_isUnit b
  constructor
  · intro z₁ z₂ hz
    rw [← sub_eq_zero]
    have h : algebraMap R (pairSections a b) a * (z₁ - z₂) = 0 := by
      rw [mul_sub, sub_eq_zero]; exact hz
    generalize z₁ - z₂ = z at h ⊢
    obtain ⟨⟨s, t⟩, hst⟩ := z
    have h1 := congrArg (fun p : pairSections a b ↦ p.1.1) h
    have h2 := congrArg (fun p : pairSections a b ↦ p.1.2) h
    change algebraMap R _ a * s = 0 at h1
    change algebraMap R _ a * t = 0 at h2
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact (hau.mul_right_eq_zero).mp h1
    · change t = 0
      exact ha (show algebraMap R _ a • t = algebraMap R _ a • 0 by
        rw [smul_zero, smul_eq_mul]; exact h2)
  · rintro ⟨⟨s, t⟩, hst⟩ ⟨⟨⟨s', t'⟩, hst'⟩, hw⟩
    have h1 := congrArg (fun p : pairSections a b ↦ p.1.1) hw
    have h2 := congrArg (fun p : pairSections a b ↦ p.1.2) hw
    change algebraMap R _ b * s = algebraMap R _ a * s' at h1
    change algebraMap R _ b * t = algebraMap R _ a * t' at h2
    rw [mem_pairSections] at hst hst'
    simp only at hst hst'
    let e₁ : Localization.Away a := s * ↑hau.unit⁻¹
    let e₂ : Localization.Away b := t' * ↑hbu.unit⁻¹
    have hR : awayToMulRight a b e₁ * algebraMap R _ a = awayToMulRight a b s := by
      rw [← awayToMulRight_algebraMap, ← map_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]
    have hL : awayToMulLeft a b e₂ * algebraMap R _ b = awayToMulLeft a b t' := by
      rw [← awayToMulLeft_algebraMap, ← map_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]
    have hab' : IsUnit (algebraMap R (Localization.Away (a * b)) (a * b)) :=
      IsLocalization.Away.algebraMap_isUnit (a * b)
    have he : (e₁, e₂) ∈ pairSections a b := by
      rw [mem_pairSections]
      apply hab'.mul_left_injective
      simp only [map_mul]
      have h1' := congrArg (awayToMulRight a b) h1
      simp only [map_mul, awayToMulRight_algebraMap] at h1'
      calc awayToMulRight a b e₁ * (algebraMap R _ a * algebraMap R _ b)
          = algebraMap R _ b * (awayToMulRight a b e₁ * algebraMap R _ a) := by ring
        _ = algebraMap R _ a * awayToMulRight a b s' := by rw [hR, h1']
        _ = algebraMap R _ a * awayToMulLeft a b t' := by rw [hst']
        _ = awayToMulLeft a b e₂ * (algebraMap R _ a * algebraMap R _ b) := by rw [← hL]; ring
    refine ⟨⟨(e₁, e₂), he⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change s = algebraMap R _ a * (s * ↑hau.unit⁻¹)
      rw [mul_left_comm, IsUnit.mul_val_inv, mul_one]
    · change t = algebraMap R _ a * (t' * ↑hbu.unit⁻¹)
      apply hbu.mul_left_injective
      simp only
      rw [mul_comm t, h2, mul_assoc, mul_assoc, IsUnit.val_inv_mul, mul_one]

section Localize

variable (g : R)

/-- Localization of the ring of sections over `D(a) ∪ D(b)` at a further element `g`: if `a, b`
is a regular sequence on `R_g`, then `R_g` is the localization of `pairSections a b` at `g`. -/
theorem exists_isLocalization_pairSections_away
    (hreg : IsWeaklyRegular (Localization.Away g)
      [algebraMap R (Localization.Away g) a, algebraMap R (Localization.Away g) b]) :
    ∃ φ : pairSections a b →ₐ[R] Localization.Away g,
      letI := φ.toRingHom.toAlgebra
      IsLocalization.Away (algebraMap R (pairSections a b) g) (Localization.Away g) := by
  let S := Localization.Away g
  let a' := algebraMap R S a
  let b' := algebraMap R S b
  let ma : Localization.Away a →ₐ[R] Localization.Away a' :=
    Localization.awayMapₐ (Algebra.ofId R S) a
  let mb : Localization.Away b →ₐ[R] Localization.Away b' :=
    Localization.awayMapₐ (Algebra.ofId R S) b
  have hmab : IsUnit (algebraMap R (Localization.Away (a' * b')) (a * b)) := by
    rw [IsScalarTower.algebraMap_apply R S, map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (a' * b')
  let κ : Localization.Away (a * b) →+* Localization.Away (a' * b') :=
    IsLocalization.Away.lift (a * b) hmab
  have hκa : ∀ s, κ (awayToMulRight a b s) = awayToMulRight a' b' (ma s) := by
    intro s
    have : κ.comp (awayToMulRight a b).toRingHom =
        (awayToMulRight a' b').toRingHom.comp ma.toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers a)
      ext r
      change κ (awayToMulRight a b (algebraMap R _ r)) =
        awayToMulRight a' b' (ma (algebraMap R _ r))
      rw [awayToMulRight_algebraMap, ma.commutes,
        IsScalarTower.algebraMap_apply R S (Localization.Away a'), awayToMulRight_algebraMap,
        show κ (algebraMap R _ r) = algebraMap R (Localization.Away (a' * b')) r from
          IsLocalization.Away.lift_eq _ _ _,
        IsScalarTower.algebraMap_apply R S (Localization.Away (a' * b'))]
    exact congrArg (fun φ ↦ φ s) this
  have hκb : ∀ t, κ (awayToMulLeft a b t) = awayToMulLeft a' b' (mb t) := by
    intro t
    have : κ.comp (awayToMulLeft a b).toRingHom =
        (awayToMulLeft a' b').toRingHom.comp mb.toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers b)
      ext r
      change κ (awayToMulLeft a b (algebraMap R _ r)) =
        awayToMulLeft a' b' (mb (algebraMap R _ r))
      rw [awayToMulLeft_algebraMap, mb.commutes,
        IsScalarTower.algebraMap_apply R S (Localization.Away b'), awayToMulLeft_algebraMap,
        show κ (algebraMap R _ r) = algebraMap R (Localization.Away (a' * b')) r from
          IsLocalization.Away.lift_eq _ _ _,
        IsScalarTower.algebraMap_apply R S (Localization.Away (a' * b'))]
    exact congrArg (fun φ ↦ φ t) this
  -- the componentwise map `pairSections a b → pairSections a' b'`
  let Φ : pairSections a b →+* pairSections a' b' :=
    { toFun := fun p ↦ ⟨(ma p.1.1, mb p.1.2), by
        rw [mem_pairSections]
        simp only
        rw [← hκa, ← hκb]
        exact congrArg κ p.2⟩
      map_one' := Subtype.ext (Prod.ext (map_one ma) (map_one mb))
      map_mul' := fun p q ↦ Subtype.ext (Prod.ext (map_mul ma _ _) (map_mul mb _ _))
      map_zero' := Subtype.ext (Prod.ext (map_zero ma) (map_zero mb))
      map_add' := fun p q ↦ Subtype.ext (Prod.ext (map_add ma _ _) (map_add mb _ _)) }
  let e : S ≃+* pairSections a' b' :=
    RingEquiv.ofBijective (algebraMap S (pairSections a' b'))
      (bijective_algebraMap_pairSections a' b' hreg)
  let φ₀ : pairSections a b →+* S := e.symm.toRingHom.comp Φ
  have hφ₀ : ∀ r : R, φ₀ (algebraMap R _ r) = algebraMap R S r := by
    intro r
    apply e.injective
    change e (e.symm (Φ _)) = _
    rw [RingEquiv.apply_symm_apply]
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change ma (algebraMap R _ r) = algebraMap S (Localization.Away a') (algebraMap R S r)
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R S]
    · change mb (algebraMap R _ r) = algebraMap S (Localization.Away b') (algebraMap R S r)
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R S]
  let φ : pairSections a b →ₐ[R] S := { φ₀ with commutes' := hφ₀ }
  refine ⟨φ, ?_⟩
  let _ := φ.toRingHom.toAlgebra
  have hφ : ∀ r : R, algebraMap (pairSections a b) S (algebraMap R _ r) = algebraMap R S r := hφ₀
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, n, rfl⟩
    change IsUnit (algebraMap (pairSections a b) S (algebraMap R _ g ^ n))
    rw [← map_pow, hφ, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit g).pow n
  · intro z
    obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers g) z
    simp only at hr
    refine ⟨⟨algebraMap R _ r, ⟨algebraMap R _ g ^ n, n, rfl⟩⟩, ?_⟩
    change z * algebraMap (pairSections a b) S (algebraMap R _ g ^ n) =
      algebraMap (pairSections a b) S (algebraMap R _ r)
    rw [← map_pow, hφ, hφ]
    exact hr
  · intro p₁ p₂ h
    suffices H : ∀ p : pairSections a b, algebraMap _ S p = 0 →
        ∃ n : ℕ, algebraMap R (pairSections a b) g ^ n * p = 0 by
      obtain ⟨n, hn⟩ := H (p₁ - p₂) (by rw [map_sub, h, sub_self])
      exact ⟨⟨_, n, rfl⟩, by rw [← sub_eq_zero, ← mul_sub]; exact hn⟩
    intro p hp
    have hΦ : Φ p = 0 := by
      have : e (φ₀ p) = Φ p := by simp [φ₀]
      rw [← this]
      change e (algebraMap (pairSections a b) S p) = 0
      rw [hp, map_zero]
    have h1 : ma p.1.1 = 0 := congrArg (fun q : pairSections a' b' ↦ q.1.1) hΦ
    have h2 : mb p.1.2 = 0 := congrArg (fun q : pairSections a' b' ↦ q.1.2) hΦ
    -- elements of `R_a` killed in `R_{ga}` are killed by a power of `g`
    have key : ∀ (c : R) (x : Localization.Away c),
        Localization.awayMapₐ (Algebra.ofId R S) c x = 0 →
          ∃ n : ℕ, algebraMap R _ (g ^ n) * x = 0 := by
      intro c x hx
      obtain ⟨⟨r, ⟨_, m, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers c) x
      simp only at hr
      have h := congrArg (Localization.awayMapₐ (Algebra.ofId R S) c) hr
      rw [map_mul, hx, zero_mul, AlgHom.commutes, eq_comm,
        IsScalarTower.algebraMap_apply R S] at h
      change algebraMap S (Localization.Away (algebraMap R S c)) (algebraMap R S r) = 0 at h
      obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
        (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R S c))
          (Localization.Away (algebraMap R S c)) _).mp h
      simp only [← map_pow, ← map_mul] at hk
      obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp hk
      simp only at hj
      refine ⟨j, ?_⟩
      have hu : IsUnit (algebraMap R (Localization.Away c) (c ^ (k + m))) :=
        IsLocalization.map_units _ (⟨c ^ (k + m), k + m, rfl⟩ : Submonoid.powers c)
      apply hu.mul_left_injective
      simp only [zero_mul]
      calc algebraMap R _ (g ^ j) * x * algebraMap R _ (c ^ (k + m))
          = algebraMap R _ (g ^ j * c ^ k) * (x * algebraMap R _ (c ^ m)) := by
            simp only [map_mul, map_pow, pow_add]; ring
        _ = 0 := by rw [hr, ← map_mul, mul_assoc, hj, map_zero]
    obtain ⟨n₁, hn₁⟩ := key a _ h1
    obtain ⟨n₂, hn₂⟩ := key b _ h2
    refine ⟨n₁ + n₂, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change (algebraMap R (pairSections a b) g ^ (n₁ + n₂)).1.1 * p.1.1 = 0
      rw [← map_pow]
      change algebraMap R _ (g ^ (n₁ + n₂)) * p.1.1 = 0
      rw [pow_add, map_mul, mul_right_comm, hn₁, zero_mul]
    · change (algebraMap R (pairSections a b) g ^ (n₁ + n₂)).1.2 * p.1.2 = 0
      rw [← map_pow]
      change algebraMap R _ (g ^ (n₁ + n₂)) * p.1.2 = 0
      rw [pow_add, map_mul, mul_assoc, hn₂, mul_zero]

end Localize

end Localization
