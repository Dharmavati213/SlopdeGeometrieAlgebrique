/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.Deformation
import Mathlib.RingTheory.RingHom.Smooth

/-!
# SGA 1, Exposé III, 6.8: existence of smooth lifts of affine schemes

Let `J` be a nilpotent ideal of a ring `R`. SGA 1 III.6.8 states that every smooth
`R ⧸ J`-algebra `S₀` is the reduction of a smooth `R`-algebra. SGA obtains it by gluing local
lifts (III.4.1), the obstruction lying in `H²(X₀, 𝒢)`, which vanishes on the affine `X₀`.

We glue the local lifts two at a time. Two lifts over basic opens `D(a)`, `D(b)` with
`(a, b) = S₀` are isomorphic over `D(ab)` (III.4.1), and their fibre product is a lift over
`D(a) ∪ D(b)`; no cocycle condition arises for two opens, and the only cohomological input is
the vanishing of `H¹` for the cover `{D(a), D(b)}` with coefficients in `J 𝒪`, which makes the
fibre product affine (its ring contains lifts of `a` and `b`). Induction on the number of basic
opens of a cover then replaces the `H²` argument of SGA.

* `IsSmoothLift`: a smooth lift `π : S → S₀` (a surjection from a smooth `R`-algebra with
  kernel `J S`); `IsSmoothLift.away` (lifts localize) and `IsSmoothLift.exists_algEquiv`
  (lifts are unique up to isomorphism, III.4.1);
* `isLocalization_away_fst`, `isLocalization_away_snd`: Milnor patching for fibre products of
  localizations; `existsUnique_glue`: the sheaf property of `S₀` for two basic opens;
* `hasSmoothLift_of_away`: the gluing step; `hasSmoothLift_of_span`: gluing along a finite cover
  by basic opens;
* `hasSmoothLift_of_sq_eq_bot`, `hasSmoothLift_of_pow_eq_bot`, `smoothLiftAffineStatement`:
  III.6.8 (existence), which proves `SmoothLiftAffineStatement`.
-/

universe u

open TensorProduct

namespace SGA.SGA1.ExposeIII

section Lift

variable {R : Type u} [CommRing R] (J : Ideal R)

/-- `π : S → S₀` is a smooth lift of `S₀` over `R`: `S` is a smooth `R`-algebra and `π` is a
surjection with kernel `J S`. -/
structure IsSmoothLift {S S₀ : Type*} [CommRing S] [CommRing S₀] [Algebra R S] [Algebra R S₀]
    (π : S →ₐ[R] S₀) : Prop where
  smooth : Algebra.Smooth R S
  surjective : Function.Surjective π
  ker_eq : RingHom.ker π = J.map (algebraMap R S)

/-- `S₀` has a smooth lift over `R` (in the same universe). -/
def HasSmoothLift (S₀ : Type u) [CommRing S₀] [Algebra R S₀] : Prop :=
  ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (π : S →ₐ[R] S₀), IsSmoothLift J π

variable {J}

namespace IsSmoothLift

variable {S S₀ : Type u} [CommRing S] [CommRing S₀] [Algebra R S] [Algebra R S₀]
  {π : S →ₐ[R] S₀} (h : IsSmoothLift J π)
include h

lemma algebraMap_eq_zero {j : R} (hj : j ∈ J) : algebraMap R S₀ j = 0 := by
  rw [← π.commutes, ← RingHom.mem_ker, h.ker_eq]
  exact Ideal.mem_map_of_mem _ hj

lemma mem_ker_iff (x : S) : π x = 0 ↔ x ∈ J.map (algebraMap R S) := by
  rw [← h.ker_eq, RingHom.mem_ker]

/-- Transport of a smooth lift along an isomorphism of `S₀`. -/
lemma trans_algEquiv {S₀' : Type u} [CommRing S₀'] [Algebra R S₀'] (e : S₀ ≃ₐ[R] S₀') :
    IsSmoothLift J ((e : S₀ →ₐ[R] S₀').comp π) where
  smooth := h.smooth
  surjective := e.surjective.comp h.surjective
  ker_eq := by
    ext x
    rw [RingHom.mem_ker]
    change e (π x) = 0 ↔ _
    rw [map_eq_zero_iff _ e.injective, h.mem_ker_iff]

/-- III.4.1 (uniqueness, affine case): two smooth lifts of the same algebra are isomorphic by
an isomorphism compatible with the reductions. -/
lemma exists_algEquiv (hJ : IsNilpotent J) {S' : Type u} [CommRing S'] [Algebra R S']
    {π' : S' →ₐ[R] S₀} (h' : IsSmoothLift J π') : ∃ e : S ≃ₐ[R] S', ∀ s, π' (e s) = π s := by
  have := h.smooth
  have := h'.smooth
  let q : (S ⧸ J.map (algebraMap R S)) ≃ₐ[R] S₀ :=
    (Ideal.quotientEquivAlgOfEq R h.ker_eq.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective h.surjective)
  let q' : (S' ⧸ J.map (algebraMap R S')) ≃ₐ[R] S₀ :=
    (Ideal.quotientEquivAlgOfEq R h'.ker_eq.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective h'.surjective)
  obtain ⟨e, he⟩ := exists_algEquiv_lift hJ (q.trans q'.symm)
  refine ⟨e, fun s ↦ ?_⟩
  calc π' (e s) = q' (Ideal.Quotient.mk _ (e s)) := rfl
    _ = q' ((q.trans q'.symm) (Ideal.Quotient.mk _ s)) := by rw [he s]
    _ = q (Ideal.Quotient.mk _ s) := q'.apply_symm_apply _
    _ = π s := rfl

/-- Smooth lifts localize: if `π : S → S₀` is a smooth lift, `x ∈ S` and `S₀'` is the localization
of `S₀` away from `π x`, then `S_x → S₀'` is a smooth lift, compatible with `π`. -/
lemma away (x : S) (S₀' : Type u) [CommRing S₀'] [Algebra R S₀'] [Algebra S₀ S₀']
    [IsScalarTower R S₀ S₀'] [IsLocalization.Away (π x) S₀'] :
    ∃ π' : Localization.Away x →ₐ[R] S₀', IsSmoothLift J π' ∧
      ∀ s, π' (algebraMap S _ s) = algebraMap S₀ S₀' (π s) := by
  let f : S →ₐ[R] S₀' := (IsScalarTower.toAlgHom R S₀ S₀').comp π
  have hf : IsUnit (f x) := IsLocalization.Away.algebraMap_isUnit (π x)
  let π' : Localization.Away x →ₐ[R] S₀' := IsLocalization.Away.liftAlgHom x hf
  have hπ' (s : S) : π' (algebraMap S _ s) = algebraMap S₀ S₀' (π s) :=
    IsLocalization.Away.lift_eq x hf s
  refine ⟨π', ⟨?_, ?_, ?_⟩, hπ'⟩
  · have := h.smooth
    have : Algebra.Etale S (Localization.Away x) := Algebra.Etale.of_isLocalizationAway x
    exact Algebra.Smooth.comp R S (Localization.Away x)
  · intro z
    obtain ⟨⟨y, _, n, rfl⟩, hy⟩ := IsLocalization.surj (Submonoid.powers (π x)) z
    obtain ⟨y', rfl⟩ := h.surjective y
    obtain ⟨v, hv⟩ := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x)
      x).exists_left_inv
    refine ⟨algebraMap S _ y' * v ^ n, ?_⟩
    have hx : π' v * f x = 1 := by
      rw [show f x = π' (algebraMap S _ x) from (hπ' x).symm, ← map_mul, hv, map_one]
    simp only at hy
    rw [map_mul, map_pow, hπ', ← hy, map_pow, mul_assoc, ← mul_pow]
    change z * (f x * π' v) ^ n = z
    rw [mul_comm (f x), hx, one_pow, mul_one]
  · ext z
    refine ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
    · obtain ⟨⟨s, _, n, rfl⟩, hs⟩ := IsLocalization.surj (Submonoid.powers x) z
      simp only at hs
      have h₁ : algebraMap S₀ S₀' (π s) = 0 := by
        rw [← hπ', ← hs, map_mul, RingHom.mem_ker.mp hz, zero_mul]
      obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
        (IsLocalization.map_eq_zero_iff (Submonoid.powers (π x)) S₀' _).mp h₁
      have h₂ : x ^ m * s ∈ J.map (algebraMap R S) := by
        rw [← h.mem_ker_iff, map_mul, map_pow]
        exact hm
      have h₃ : algebraMap S (Localization.Away x) (x ^ m * s) ∈
          J.map (algebraMap R (Localization.Away x)) := by
        rw [IsScalarTower.algebraMap_eq R S (Localization.Away x), ← Ideal.map_map]
        exact Ideal.mem_map_of_mem _ h₂
      have hu : IsUnit (algebraMap S (Localization.Away x) (x ^ m * x ^ n)) := by
        rw [map_mul, map_pow, map_pow]
        exact ((IsLocalization.Away.algebraMap_isUnit x).pow m).mul
          ((IsLocalization.Away.algebraMap_isUnit x).pow n)
      have h₄ : z * algebraMap S (Localization.Away x) (x ^ m * x ^ n) ∈
          J.map (algebraMap R (Localization.Away x)) := by
        rw [map_mul, ← mul_assoc, mul_comm z, mul_assoc, hs, ← map_mul]
        exact h₃
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have := Ideal.mul_mem_right v _ h₄
      rwa [mul_assoc, hv, mul_one] at this
    · have hle : J.map (algebraMap R (Localization.Away x)) ≤
          RingHom.ker (π' : Localization.Away x →+* S₀') := by
        refine Ideal.map_le_iff_le_comap.mpr fun j hj ↦ ?_
        rw [Ideal.mem_comap, RingHom.mem_ker]
        change π' (algebraMap R _ j) = 0
        rw [π'.commutes, IsScalarTower.algebraMap_apply R S₀ S₀', h.algebraMap_eq_zero hj,
          map_zero]
      exact hle hz

end IsSmoothLift

end Lift

section Localization

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- If `B` is the localization of `A` away from `x`, `y` becomes a unit in `B` and `x` divides a
power of `y`, then `B` is also the localization away from `y`. -/
lemma isLocalization_away_of_dvd_pow {x y : A} [IsLocalization.Away x B]
    (hyu : IsUnit (algebraMap A B y)) {m : ℕ} {d : A} (hd : y ^ m = x * d) :
    IsLocalization.Away y B := by
  refine (isLocalization_iff _ _).mpr ⟨?_, fun b ↦ ?_, fun {c₁ c₂} h ↦ ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [map_pow]
    exact hyu.pow k
  · obtain ⟨⟨c, _, k, rfl⟩, hc⟩ := IsLocalization.surj (Submonoid.powers x) b
    refine ⟨⟨c * d ^ k, y ^ (m * k), m * k, rfl⟩, ?_⟩
    simp only at hc ⊢
    rw [pow_mul, hd, mul_pow, map_mul, ← mul_assoc, hc, map_mul]
  · obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers x) h
    refine ⟨⟨y ^ (m * k), m * k, rfl⟩, ?_⟩
    simp only at hk ⊢
    rw [pow_mul, hd, mul_pow, mul_comm (x ^ k), mul_assoc, mul_assoc, hk]

/-- Localizations away from elements differing by a nilpotent agree. -/
lemma isLocalization_away_of_isNilpotent_sub {x y : A} [IsLocalization.Away x B]
    (hxy : IsNilpotent (y - x)) : IsLocalization.Away y B := by
  have hyu : IsUnit (algebraMap A B y) := by
    have := (hxy.map (algebraMap A B)).isUnit_add_left_of_commute
      (IsLocalization.Away.algebraMap_isUnit x) (Commute.all _ _)
    rwa [map_sub, add_sub_cancel] at this
  obtain ⟨n, hn⟩ := hxy
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow y (y - x) n
  rw [hn, sub_zero, sub_sub_cancel] at hd
  exact isLocalization_away_of_dvd_pow hyu hd

end Localization

section FibreProduct

variable {R P Q T : Type*} [CommRing R] [CommRing P] [CommRing Q] [CommRing T] [Algebra R P]
  [Algebra R Q] (A : Subalgebra R (P × Q))

/-- Milnor patching: in the fibre product `A = P ×_T Q`, if `α = (p₀, q₀) ∈ A` with `p₀` a unit
and `T` the localization of `Q` away from `q₀`, then `P` is the localization of `A` away from
`α`. -/
lemma isLocalization_away_fst [Algebra Q T] (f : P →+* T)
    (hA : ∀ z, z ∈ A ↔ f z.1 = algebraMap Q T z.2) (α : A) (hα : IsUnit (α : P × Q).1)
    [IsLocalization.Away (α : P × Q).2 T] :
    letI := ((RingHom.fst P Q).comp A.val.toRingHom).toAlgebra
    IsLocalization.Away α P := by
  let _ := ((RingHom.fst P Q).comp A.val.toRingHom).toAlgebra
  have hαA := (hA α).mp α.2
  refine (isLocalization_iff _ _).mpr ⟨?_, fun p ↦ ?_, fun {z z'} h ↦ ?_⟩
  · rintro ⟨_, k, rfl⟩
    change IsUnit ((α ^ k : A) : P × Q).1
    rw [SubmonoidClass.coe_pow, Prod.pow_fst]
    exact hα.pow k
  · obtain ⟨⟨q, _, n, rfl⟩, hq⟩ := IsLocalization.surj (Submonoid.powers (α : P × Q).2) (f p)
    simp only at hq
    have hmem : (p * (α : P × Q).1 ^ n, q) ∈ A := by
      rw [hA]
      change f (p * (α : P × Q).1 ^ n) = algebraMap Q T q
      rw [map_mul, map_pow, hαA, ← map_pow]
      exact hq
    exact ⟨⟨⟨_, hmem⟩, α ^ n, n, rfl⟩, by
      change p * ((α ^ n : A) : P × Q).1 = p * (α : P × Q).1 ^ n
      rw [SubmonoidClass.coe_pow, Prod.pow_fst]⟩
  · have h₁ : (z : P × Q).1 = (z' : P × Q).1 := h
    have h₂ : algebraMap Q T (z : P × Q).2 = algebraMap Q T (z' : P × Q).2 := by
      rw [← (hA z).mp z.2, ← (hA z').mp z'.2, h₁]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq
      (M := Submonoid.powers (α : P × Q).2) (S := T) h₂
    refine ⟨⟨α ^ k, k, rfl⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp [h₁]
    · simpa using hk

/-- Milnor patching, second factor. -/
lemma isLocalization_away_snd [Algebra P T] (g : Q →+* T)
    (hA : ∀ z, z ∈ A ↔ algebraMap P T z.1 = g z.2) (β : A) (hβ : IsUnit (β : P × Q).2)
    [IsLocalization.Away (β : P × Q).1 T] :
    letI := ((RingHom.snd P Q).comp A.val.toRingHom).toAlgebra
    IsLocalization.Away β Q := by
  let _ := ((RingHom.snd P Q).comp A.val.toRingHom).toAlgebra
  have hβA := (hA β).mp β.2
  refine (isLocalization_iff _ _).mpr ⟨?_, fun q ↦ ?_, fun {z z'} h ↦ ?_⟩
  · rintro ⟨_, k, rfl⟩
    change IsUnit ((β ^ k : A) : P × Q).2
    rw [SubmonoidClass.coe_pow, Prod.pow_snd]
    exact hβ.pow k
  · obtain ⟨⟨p, _, n, rfl⟩, hp⟩ := IsLocalization.surj (Submonoid.powers (β : P × Q).1) (g q)
    simp only at hp
    have hmem : (p, q * (β : P × Q).2 ^ n) ∈ A := by
      rw [hA]
      change algebraMap P T p = g (q * (β : P × Q).2 ^ n)
      rw [map_mul, map_pow, ← hβA, ← map_pow]
      exact hp.symm
    exact ⟨⟨⟨_, hmem⟩, β ^ n, n, rfl⟩, by
      change q * ((β ^ n : A) : P × Q).2 = q * (β : P × Q).2 ^ n
      rw [SubmonoidClass.coe_pow, Prod.pow_snd]⟩
  · have h₁ : (z : P × Q).2 = (z' : P × Q).2 := h
    have h₂ : algebraMap P T (z : P × Q).1 = algebraMap P T (z' : P × Q).1 := by
      rw [(hA z).mp z.2, (hA z').mp z'.2, h₁]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq
      (M := Submonoid.powers (β : P × Q).1) (S := T) h₂
    refine ⟨⟨β ^ k, k, rfl⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simpa using hk
    · simp [h₁]

end FibreProduct

section TwoCover

variable {S₀ A₀ B₀ C₀ : Type*} [CommRing S₀] [CommRing A₀] [CommRing B₀] [CommRing C₀]
  [Algebra S₀ A₀] [Algebra S₀ B₀] [Algebra S₀ C₀] {a b : S₀}

lemma exists_mul_pow_add_mul_pow_eq_one (hab : Ideal.span {a, b} = ⊤) (n m : ℕ) :
    ∃ u v : S₀, u * a ^ n + v * b ^ m = 1 := by
  have := Ideal.span_pow_eq_top _ hab (n + m)
  rw [Set.image_pair] at this
  have h1 : (1 : S₀) ∈ Ideal.span {a ^ (n + m), b ^ (n + m)} := by
    rw [this]; exact Submodule.mem_top
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp h1
  exact ⟨u * a ^ m, v * b ^ n, by rw [← huv]; ring⟩

/-- The structure sheaf of `Spec S₀` for the cover by `D(a)` and `D(b)`: compatible elements of
`S₀[1/a]` and `S₀[1/b]` come from a unique element of `S₀`. -/
lemma existsUnique_glue (hab : Ideal.span {a, b} = ⊤) [IsLocalization.Away a A₀]
    [IsLocalization.Away b B₀] [IsLocalization.Away (a * b) C₀] (fA : A₀ →ₐ[S₀] C₀)
    (fB : B₀ →ₐ[S₀] C₀) (x : A₀) (y : B₀) (hxy : fA x = fB y) :
    ∃! r : S₀, algebraMap S₀ A₀ r = x ∧ algebraMap S₀ B₀ r = y := by
  have hpow := exists_mul_pow_add_mul_pow_eq_one hab
  obtain ⟨⟨s, _, n, rfl⟩, hs⟩ := IsLocalization.surj (Submonoid.powers a) x
  obtain ⟨⟨t, _, m, rfl⟩, ht⟩ := IsLocalization.surj (Submonoid.powers b) y
  simp only at hs ht
  have hsx : fA x * algebraMap S₀ C₀ (a ^ n) = algebraMap S₀ C₀ s := by
    rw [← fA.commutes, ← fA.commutes, ← map_mul, hs]
  have hty : fB y * algebraMap S₀ C₀ (b ^ m) = algebraMap S₀ C₀ t := by
    rw [← fB.commutes, ← fB.commutes, ← map_mul, ht]
  have hC : algebraMap S₀ C₀ (s * b ^ m) = algebraMap S₀ C₀ (t * a ^ n) := by
    rw [map_mul, map_mul, ← hsx, ← hty, hxy]
    ring
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (a * b)) hC
  simp only at hk
  obtain ⟨u, v, huv⟩ := hpow (n + k) (m + k)
  have huniq (r r' : S₀) (hr : algebraMap S₀ A₀ r = x ∧ algebraMap S₀ B₀ r = y)
      (hr' : algebraMap S₀ A₀ r' = x ∧ algebraMap S₀ B₀ r' = y) : r' = r := by
    obtain ⟨⟨_, i, rfl⟩, hi⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers a) (S := A₀)
      (hr.1.trans hr'.1.symm)
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers b) (S := B₀)
      (hr.2.trans hr'.2.symm)
    obtain ⟨u', v', huv'⟩ := hpow i j
    simp only at hi hj
    linear_combination -(r' - r) * huv' - u' * hi - v' * hj
  have hr : algebraMap S₀ A₀ (u * (s * a ^ k) + v * (t * b ^ k)) = x ∧
      algebraMap S₀ B₀ (u * (s * a ^ k) + v * (t * b ^ k)) = y := by
    constructor
    · have hu : IsUnit (algebraMap S₀ A₀ (a ^ (n + k))) := by
        rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit a).pow _
      refine hu.mul_left_injective ?_
      change algebraMap S₀ A₀ _ * _ = x * _
      have h₁ : (u * (s * a ^ k) + v * (t * b ^ k)) * a ^ (n + k) = s * a ^ k := by
        linear_combination (s * a ^ k) * huv - v * hk
      rw [← map_mul, h₁, pow_add, map_mul, map_mul, ← mul_assoc, hs]
    · have hu : IsUnit (algebraMap S₀ B₀ (b ^ (m + k))) := by
        rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit b).pow _
      refine hu.mul_left_injective ?_
      change algebraMap S₀ B₀ _ * _ = y * _
      have h₁ : (u * (s * a ^ k) + v * (t * b ^ k)) * b ^ (m + k) = t * b ^ k := by
        linear_combination (t * b ^ k) * huv + u * hk
      rw [← map_mul, h₁, pow_add, map_mul, map_mul, ← mul_assoc, ht]
  exact ⟨_, hr, fun r' hr' ↦ huniq _ r' hr hr'⟩

end TwoCover

section Glue

variable {R : Type u} [CommRing R] {J : Ideal R}

lemma sq_map_eq_bot (hJ : J ^ 2 = ⊥) (S : Type*) [CommRing S] [Algebra R S] {x y : S}
    (hx : x ∈ J.map (algebraMap R S)) (hy : y ∈ J.map (algebraMap R S)) : x * y = 0 := by
  have : x * y ∈ (J ^ 2).map (algebraMap R S) := by
    rw [Ideal.map_pow, pow_two]; exact Ideal.mul_mem_mul hx hy
  rwa [hJ, Ideal.map_bot, Ideal.mem_bot] at this

lemma isNilpotent_of_mem_map (hJ : J ^ 2 = ⊥) {S : Type*} [CommRing S] [Algebra R S] {x : S}
    (hx : x ∈ J.map (algebraMap R S)) : IsNilpotent x :=
  ⟨2, by rw [pow_two]; exact sq_map_eq_bot hJ S hx hx⟩

/-- A unit modulo a square-zero kernel `J S` is a unit. -/
lemma IsSmoothLift.isUnit_of_isUnit (hJ : J ^ 2 = ⊥) {S S₀ : Type u} [CommRing S] [CommRing S₀]
    [Algebra R S] [Algebra R S₀] {π : S →ₐ[R] S₀} (h : IsSmoothLift J π) {x : S}
    (hx : IsUnit (π x)) : IsUnit x := by
  obtain ⟨w, hw⟩ := hx.exists_right_inv
  obtain ⟨w', rfl⟩ := h.surjective w
  have hmem : x * w' - 1 ∈ J.map (algebraMap R S) := by
    rw [← h.mem_ker_iff, map_sub, map_mul, hw, map_one, sub_self]
  have := (isNilpotent_of_mem_map hJ hmem).isUnit_add_one
  rw [sub_add_cancel] at this
  exact isUnit_of_mul_isUnit_left this

variable (hJ : J ^ 2 = ⊥) {S₀ : Type u} [CommRing S₀] [Algebra R S₀] {a b : S₀}
  (hab : Ideal.span {a, b} = ⊤)
include hJ hab

/-- III.6.8, gluing step: if `S₀[1/a]` and `S₀[1/b]` have smooth lifts and `(a, b) = S₀`, then
`S₀` has a smooth lift. The lift is the fibre product of the two lifts over their common
localization; the elements `a`, `b` lift to it since `H¹` of the cover `{D(a), D(b)}` vanishes
with coefficients in the quasi-coherent `J 𝒪`. -/
theorem hasSmoothLift_of_away (ha : HasSmoothLift J (Localization.Away a))
    (hb : HasSmoothLift J (Localization.Away b)) : HasSmoothLift J S₀ := by
  obtain ⟨Sa, _, _, πa, ha⟩ := ha
  obtain ⟨Sb, _, _, πb, hb⟩ := hb
  let A₀ := Localization.Away a
  let B₀ := Localization.Away b
  let C₀' := Localization.Away (algebraMap S₀ A₀ b)
  let C₀ := Localization.Away (algebraMap S₀ B₀ a)
  have : IsLocalization.Away (a * b) C₀ := IsLocalization.Away.mul B₀ C₀ b a
  have : IsLocalization.Away (a * b) C₀' := by
    rw [mul_comm]; exact IsLocalization.Away.mul A₀ C₀' a b
  have : IsScalarTower R S₀ C₀' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R A₀ C₀', IsScalarTower.algebraMap_apply R S₀ A₀,
      ← IsScalarTower.algebraMap_apply S₀ A₀ C₀']
  have : IsScalarTower R S₀ C₀ := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R B₀ C₀, IsScalarTower.algebraMap_apply R S₀ B₀,
      ← IsScalarTower.algebraMap_apply S₀ B₀ C₀]
  let θ : C₀' ≃ₐ[S₀] C₀ := IsLocalization.algEquiv (Submonoid.powers (a * b)) C₀' C₀
  let θR : C₀' ≃ₐ[R] C₀ := θ.restrictScalars R
  -- the local lifts over `D(ab)`
  obtain ⟨b', hb'⟩ := ha.surjective (algebraMap S₀ A₀ b)
  obtain ⟨a', ha'⟩ := hb.surjective (algebraMap S₀ B₀ a)
  have : IsLocalization.Away (πa b') C₀' := by rw [hb']; infer_instance
  have : IsLocalization.Away (πb a') C₀ := by rw [ha']; infer_instance
  obtain ⟨πa', ha'l, hca⟩ := ha.away b' C₀'
  obtain ⟨πb', hb'l, hcb⟩ := hb.away a' C₀
  have hJn : IsNilpotent J := ⟨2, by rw [hJ]; rfl⟩
  obtain ⟨ψ, hψ⟩ := (ha'l.trans_algEquiv θR).exists_algEquiv hJn hb'l
  let Sab := Localization.Away a'
  let ιa : Sa →ₐ[R] Sab := (ψ : Localization.Away b' →ₐ[R] Sab).comp
    (IsScalarTower.toAlgHom R Sa (Localization.Away b'))
  let ιb : Sb →ₐ[R] Sab := IsScalarTower.toAlgHom R Sb Sab
  have hιa (x : Sa) : πb' (ιa x) = θ (algebraMap A₀ C₀' (πa x)) := by
    change πb' (ψ (algebraMap Sa _ x)) = _
    rw [hψ]
    change θ (πa' (algebraMap Sa _ x)) = _
    rw [hca]
  have hιb (y : Sb) : πb' (ιb y) = algebraMap B₀ C₀ (πb y) := hcb y
  -- the fibre product
  let A : Subalgebra R (Sa × Sb) :=
    AlgHom.equalizer (ιa.comp (AlgHom.fst R Sa Sb)) (ιb.comp (AlgHom.snd R Sa Sb))
  have hA (z : Sa × Sb) : z ∈ A ↔ ιa z.1 = ιb z.2 := AlgHom.mem_equalizer _ _ z
  -- the reduction `A → S₀`, through `S₀ = S₀[1/a] ×_{S₀[1/ab]} S₀[1/b]`
  let fA : A₀ →ₐ[S₀] C₀ := (θ : C₀' →ₐ[S₀] C₀).comp (IsScalarTower.toAlgHom S₀ A₀ C₀')
  let fB : B₀ →ₐ[S₀] C₀ := IsScalarTower.toAlgHom S₀ B₀ C₀
  let ε : S₀ →ₐ[R] A₀ × B₀ :=
    (IsScalarTower.toAlgHom R S₀ A₀).prod (IsScalarTower.toAlgHom R S₀ B₀)
  have hfAB (r : S₀) : fA (algebraMap S₀ A₀ r) = fB (algebraMap S₀ B₀ r) := by
    change θ (algebraMap A₀ C₀' (algebraMap S₀ A₀ r)) = algebraMap B₀ C₀ (algebraMap S₀ B₀ r)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, θ.commutes]
  have hinj : Function.Injective ε := fun r r' h ↦ by
    have h₁ : algebraMap S₀ A₀ r = algebraMap S₀ A₀ r' := congrArg Prod.fst h
    have h₂ : algebraMap S₀ B₀ r = algebraMap S₀ B₀ r' := congrArg Prod.snd h
    exact ((existsUnique_glue hab fA fB _ _ (hfAB r')).unique ⟨h₁, h₂⟩ ⟨rfl, rfl⟩)
  have hcompat (z : A) : fA (πa (z : Sa × Sb).1) = fB (πb (z : Sa × Sb).2) := by
    change θ (algebraMap A₀ C₀' (πa _)) = algebraMap B₀ C₀ (πb _)
    rw [← hιa, ← hιb, (hA _).mp z.2]
  have hrange (z : A) : ((πa.prodMap πb).comp A.val) z ∈ ε.range := by
    obtain ⟨r, hr, -⟩ := existsUnique_glue hab fA fB _ _ (hcompat z)
    exact ⟨r, Prod.ext hr.1 hr.2⟩
  let πA : A →ₐ[R] S₀ := ((AlgEquiv.ofInjective ε hinj).symm : ε.range →ₐ[R] S₀).comp
    (AlgHom.codRestrict ((πa.prodMap πb).comp A.val) ε.range hrange)
  have hspec (z : A) : ε (πA z) = (πa (z : Sa × Sb).1, πb (z : Sa × Sb).2) :=
    congrArg Subtype.val ((AlgEquiv.ofInjective ε hinj).apply_symm_apply _)
  have hspec₁ (z : A) : algebraMap S₀ A₀ (πA z) = πa (z : Sa × Sb).1 :=
    congrArg Prod.fst (hspec z)
  have hspec₂ (z : A) : algebraMap S₀ B₀ (πA z) = πb (z : Sa × Sb).2 :=
    congrArg Prod.snd (hspec z)
  -- `H¹` of the cover `{D(a), D(b)}` with coefficients in `J 𝒪` vanishes
  have hH1 (d : Sab) (hd : d ∈ J.map (algebraMap R Sab)) :
      ∃ u ∈ J.map (algebraMap R Sa), ∃ v ∈ J.map (algebraMap R Sb), d = ιa u + ιb v := by
    have hd' : d ∈ (J.map (algebraMap R Sb)).map (algebraMap Sb Sab) := by
      rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    obtain ⟨⟨⟨w, hw⟩, _, k, rfl⟩, hwk⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers a') Sab).mp hd'
    have hd'' : ψ.symm d ∈ (J.map (algebraMap R Sa)).map
        (algebraMap Sa (Localization.Away b')) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      have := Ideal.mem_map_of_mem (ψ.symm : Sab →+* Localization.Away b') hd
      have e : (ψ.symm : Sab →+* Localization.Away b').comp (algebraMap R Sab) =
          algebraMap R (Localization.Away b') := RingHom.ext fun r ↦ ψ.symm.commutes r
      rwa [Ideal.map_map, e] at this
    obtain ⟨⟨⟨z', hz'⟩, _, j, rfl⟩, hzj⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers b')
        (Localization.Away b')).mp hd''
    simp only at hwk hzj
    obtain ⟨p, q, hpq⟩ := exists_mul_pow_add_mul_pow_eq_one hab (k + j) (k + j)
    obtain ⟨pb, hpb⟩ := hb.surjective (algebraMap S₀ B₀ p)
    obtain ⟨qa, hqa⟩ := ha.surjective (algebraMap S₀ A₀ q)
    set E := ιb (pb * a' ^ (k + j)) + ιa (qa * b' ^ (k + j)) with hEdef
    have hE : πb' E = 1 := by
      have e₁ : πb (pb * a' ^ (k + j)) = algebraMap S₀ B₀ (p * a ^ (k + j)) := by
        rw [map_mul, map_pow, hpb, ha', ← map_pow, ← map_mul]
      have e₂ : πa (qa * b' ^ (k + j)) = algebraMap S₀ A₀ (q * b ^ (k + j)) := by
        rw [map_mul, map_pow, hqa, hb', ← map_pow, ← map_mul]
      rw [hEdef, map_add, hιa, hιb, e₁, e₂, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply, θ.commutes, ← map_add, hpq, map_one]
    have hE1 : E - 1 ∈ J.map (algebraMap R Sab) := by
      rw [← hb'l.mem_ker_iff, map_sub, hE, map_one, sub_self]
    have hdE : d = d * E := by
      have := sq_map_eq_bot hJ Sab hd hE1
      linear_combination -this
    refine ⟨qa * b' ^ k * z', Ideal.mul_mem_left _ _ hz', pb * a' ^ j * w,
      Ideal.mul_mem_left _ _ hw, ?_⟩
    have h₁ : d * ιb (pb * a' ^ (k + j)) = ιb (pb * a' ^ j * w) := by
      change d * algebraMap Sb Sab _ = algebraMap Sb Sab _
      simp only [map_mul, map_pow] at hwk ⊢
      rw [← hwk, pow_add]
      ring
    have h₂ : d * ιa (qa * b' ^ (k + j)) = ιa (qa * b' ^ k * z') := by
      change d * ψ (algebraMap Sa _ _) = ψ (algebraMap Sa _ _)
      rw [← ψ.apply_symm_apply d, ← map_mul]
      congr 1
      simp only [map_mul, map_pow] at hzj ⊢
      rw [← hzj, pow_add]
      ring
    rw [hdE, hEdef, mul_add, h₁, h₂, add_comm]
  -- surjectivity of `A → S₀`
  have hsurj : Function.Surjective πA := by
    intro s
    obtain ⟨x₀, hx₀⟩ := ha.surjective (algebraMap S₀ A₀ s)
    obtain ⟨y₀, hy₀⟩ := hb.surjective (algebraMap S₀ B₀ s)
    have hd : ιa x₀ - ιb y₀ ∈ J.map (algebraMap R Sab) := by
      rw [← hb'l.mem_ker_iff, map_sub, hιa, hιb, hx₀, hy₀, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply, θ.commutes, sub_self]
    obtain ⟨u, hu, v, hv, huv⟩ := hH1 _ hd
    have hmem : (x₀ - u, y₀ + v) ∈ A := by
      rw [hA]
      change ιa (x₀ - u) = ιb (y₀ + v)
      rw [map_sub, map_add]
      linear_combination huv
    refine ⟨⟨_, hmem⟩, hinj ?_⟩
    rw [hspec]
    refine Prod.ext ?_ ?_
    · change πa (x₀ - u) = algebraMap S₀ A₀ s
      rw [map_sub, hx₀, (ha.mem_ker_iff u).mpr hu, sub_zero]
    · change πb (y₀ + v) = algebraMap S₀ B₀ s
      rw [map_add, hy₀, (hb.mem_ker_iff v).mpr hv, add_zero]
  have hker₁ (z : A) (hz : πA z = 0) : (z : Sa × Sb).1 ∈ J.map (algebraMap R Sa) := by
    rw [← ha.mem_ker_iff, ← hspec₁, hz, map_zero]
  have hker₂ (z : A) (hz : πA z = 0) : (z : Sa × Sb).2 ∈ J.map (algebraMap R Sb) := by
    rw [← hb.mem_ker_iff, ← hspec₂, hz, map_zero]
  -- the lifts `α` of `a` and `β` of `b`
  obtain ⟨α, hα⟩ := hsurj a
  obtain ⟨β, hβ⟩ := hsurj b
  have hα₁ : πa (α : Sa × Sb).1 = algebraMap S₀ A₀ a := by rw [← hspec₁, hα]
  have hα₂ : πb (α : Sa × Sb).2 = algebraMap S₀ B₀ a := by rw [← hspec₂, hα]
  have hβ₁ : πa (β : Sa × Sb).1 = algebraMap S₀ A₀ b := by rw [← hspec₁, hβ]
  have hβ₂ : πb (β : Sa × Sb).2 = algebraMap S₀ B₀ b := by rw [← hspec₂, hβ]
  have hαu : IsUnit (α : Sa × Sb).1 :=
    ha.isUnit_of_isUnit hJ (by rw [hα₁]; exact IsLocalization.Away.algebraMap_isUnit a)
  have hβu : IsUnit (β : Sa × Sb).2 :=
    hb.isUnit_of_isUnit hJ (by rw [hβ₂]; exact IsLocalization.Away.algebraMap_isUnit b)
  have hαloc : IsLocalization.Away (α : Sa × Sb).2 Sab :=
    isLocalization_away_of_isNilpotent_sub (x := a') (isNilpotent_of_mem_map hJ (by
      rw [← hb.mem_ker_iff, map_sub, hα₂, ha', sub_self]))
  have hβloc : IsLocalization.Away (β : Sa × Sb).1 (Localization.Away b') :=
    isLocalization_away_of_isNilpotent_sub (x := b') (isNilpotent_of_mem_map hJ (by
      rw [← ha.mem_ker_iff, map_sub, hβ₁, hb', sub_self]))
  -- Milnor patching: `Sa` and `Sb` are localizations of `A`
  have hlocα := isLocalization_away_fst A ιa.toRingHom (fun z ↦ hA z) α hαu
  have hlocβ := by
    let _ : Algebra Sa Sab := ιa.toRingHom.toAlgebra
    let e : Localization.Away b' ≃ₐ[Sa] Sab := { ψ.toRingEquiv with commutes' := fun _ ↦ rfl }
    have := IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (β : Sa × Sb).1) e
    exact isLocalization_away_snd A ιb.toRingHom (fun z ↦ hA z) β hβu
  -- `α` and `β` generate the unit ideal of `A`
  have hsq (z : A) (hz : πA z = 0) : z * z = 0 := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact sq_map_eq_bot hJ Sa (hker₁ z hz) (hker₁ z hz)
    · exact sq_map_eq_bot hJ Sb (hker₂ z hz) (hker₂ z hz)
  have hspan : Ideal.span ({α, β} : Set A) = ⊤ := by
    obtain ⟨c, e, hce⟩ := exists_mul_pow_add_mul_pow_eq_one hab 1 1
    obtain ⟨c', rfl⟩ := hsurj c
    obtain ⟨e', rfl⟩ := hsurj e
    set t := c' * α + e' * β - 1
    have ht : πA t = 0 := by
      simp only [t, map_sub, map_add, map_mul, hα, hβ, map_one, ← hce, pow_one, sub_self]
    have hu : IsUnit (c' * α + e' * β) := by
      have := IsNilpotent.isUnit_add_one (r := t) ⟨2, by rw [pow_two]; exact hsq t ht⟩
      rwa [sub_add_cancel] at this
    refine Ideal.eq_top_of_isUnit_mem _ ?_ hu
    exact Ideal.mem_span_pair.mpr ⟨c', e', rfl⟩
  -- `A` is smooth over `R`
  have hsmooth : Algebra.Smooth R A := by
    refine RingHom.smooth_algebraMap.mp (RingHom.Smooth.ofLocalizationSpanTarget.ofIsLocalization
      RingHom.Smooth.respectsIso (algebraMap R A) _ hspan fun ⟨r, hr⟩ ↦ ?_)
    rcases hr with rfl | hr
    · let _ := ((RingHom.fst Sa Sb).comp A.val.toRingHom).toAlgebra
      refine ⟨Sa, inferInstance, inferInstance, hlocα, ?_⟩
      have := ha.smooth
      exact RingHom.smooth_algebraMap.mpr this
    · rw [Set.mem_singleton_iff] at hr
      subst hr
      let _ := ((RingHom.snd Sa Sb).comp A.val.toRingHom).toAlgebra
      refine ⟨Sb, inferInstance, inferInstance, hlocβ, ?_⟩
      have := hb.smooth
      exact RingHom.smooth_algebraMap.mpr this
  -- the kernel of `A → S₀` is `J A`
  have hRA (j : R) (hj : j ∈ J) : algebraMap R S₀ j = 0 := hinj (by
    rw [map_zero]
    refine Prod.ext ?_ ?_
    · change algebraMap S₀ A₀ (algebraMap R S₀ j) = 0
      rw [← IsScalarTower.algebraMap_apply]
      exact ha.algebraMap_eq_zero hj
    · change algebraMap S₀ B₀ (algebraMap R S₀ j) = 0
      rw [← IsScalarTower.algebraMap_apply]
      exact hb.algebraMap_eq_zero hj)
  have hmemα (z : A) (hz : πA z = 0) : ∃ n, α ^ n * z ∈ J.map (algebraMap R A) := by
    let _ := ((RingHom.fst Sa Sb).comp A.val.toRingHom).toAlgebra
    have := hlocα
    have hz₁ : algebraMap A Sa z ∈ (J.map (algebraMap R A)).map (algebraMap A Sa) := by
      have e : (algebraMap A Sa).comp (algebraMap R A) = algebraMap R Sa :=
        RingHom.ext fun _ ↦ rfl
      rw [Ideal.map_map, e]
      exact hker₁ z hz
    obtain ⟨⟨⟨m, hm⟩, _, n, rfl⟩, hmn⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers α) Sa).mp hz₁
    simp only at hmn
    rw [← map_mul] at hmn
    obtain ⟨⟨_, l, rfl⟩, hl⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers α) (S := Sa) hmn
    simp only at hl
    refine ⟨l + n, ?_⟩
    have : α ^ (l + n) * z = α ^ l * m := by rw [← hl]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hm
  have hmemβ (z : A) (hz : πA z = 0) : ∃ n, β ^ n * z ∈ J.map (algebraMap R A) := by
    let _ := ((RingHom.snd Sa Sb).comp A.val.toRingHom).toAlgebra
    have := hlocβ
    have hz₂ : algebraMap A Sb z ∈ (J.map (algebraMap R A)).map (algebraMap A Sb) := by
      have e : (algebraMap A Sb).comp (algebraMap R A) = algebraMap R Sb :=
        RingHom.ext fun _ ↦ rfl
      rw [Ideal.map_map, e]
      exact hker₂ z hz
    obtain ⟨⟨⟨m, hm⟩, _, n, rfl⟩, hmn⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers β) Sb).mp hz₂
    simp only at hmn
    rw [← map_mul] at hmn
    obtain ⟨⟨_, l, rfl⟩, hl⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers β) (S := Sb) hmn
    simp only at hl
    refine ⟨l + n, ?_⟩
    have : β ^ (l + n) * z = β ^ l * m := by rw [← hl]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hm
  have hker : RingHom.ker πA = J.map (algebraMap R A) := by
    ext z
    refine ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
    · rw [RingHom.mem_ker] at hz
      obtain ⟨n, hn⟩ := hmemα z hz
      obtain ⟨m, hm⟩ := hmemβ z hz
      have htop := Ideal.span_pow_eq_top _ hspan (n + m)
      rw [Set.image_pair] at htop
      have h1 : (1 : A) ∈ Ideal.span {α ^ (n + m), β ^ (n + m)} := by
        rw [htop]; exact Submodule.mem_top
      obtain ⟨c, e, hce⟩ := Ideal.mem_span_pair.mp h1
      have : z = c * α ^ m * (α ^ n * z) + e * β ^ n * (β ^ m * z) := by
        linear_combination (-z) * hce
      rw [this]
      exact add_mem (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hm)
    · refine (Ideal.map_le_iff_le_comap.mpr fun j hj ↦ ?_) hz
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [πA.commutes, hRA j hj]
  exact ⟨A, inferInstance, inferInstance, πA, hsmooth, hsurj, hker⟩

end Glue

section Cover

variable {R : Type u} [CommRing R] {J : Ideal R}

lemma HasSmoothLift.of_algEquiv {S₀ S₀' : Type u} [CommRing S₀] [Algebra R S₀] [CommRing S₀']
    [Algebra R S₀'] (h : HasSmoothLift J S₀) (e : S₀ ≃ₐ[R] S₀') : HasSmoothLift J S₀' := by
  obtain ⟨S, _, _, π, hπ⟩ := h
  exact ⟨S, inferInstance, inferInstance, _, hπ.trans_algEquiv e⟩

lemma HasSmoothLift.away {S₀ : Type u} [CommRing S₀] [Algebra R S₀] (h : HasSmoothLift J S₀)
    (x : S₀) : HasSmoothLift J (Localization.Away x) := by
  obtain ⟨S, _, _, π, hπ⟩ := h
  obtain ⟨x', rfl⟩ := hπ.surjective x
  obtain ⟨π', hπ', -⟩ := hπ.away x' (Localization.Away (π x'))
  exact ⟨_, inferInstance, inferInstance, π', hπ'⟩

/-- `S₀[1/x][1/y] ≅ S₀[1/y][1/x]`, as `R`-algebras. -/
noncomputable def awayAwayAlgEquiv {S₀ : Type u} [CommRing S₀] [Algebra R S₀] (x y : S₀) :
    Localization.Away (algebraMap S₀ (Localization.Away x) y) ≃ₐ[R]
      Localization.Away (algebraMap S₀ (Localization.Away y) x) := by
  let X := Localization.Away (algebraMap S₀ (Localization.Away x) y)
  let Y := Localization.Away (algebraMap S₀ (Localization.Away y) x)
  have : IsLocalization.Away (y * x) X := IsLocalization.Away.mul (Localization.Away x) X x y
  have : IsLocalization.Away (y * x) Y := by
    rw [mul_comm]; exact IsLocalization.Away.mul (Localization.Away y) Y y x
  have : IsScalarTower R S₀ X := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R (Localization.Away x) X,
      IsScalarTower.algebraMap_apply R S₀ (Localization.Away x),
      ← IsScalarTower.algebraMap_apply S₀ (Localization.Away x) X]
  have : IsScalarTower R S₀ Y := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R (Localization.Away y) Y,
      IsScalarTower.algebraMap_apply R S₀ (Localization.Away y),
      ← IsScalarTower.algebraMap_apply S₀ (Localization.Away y) Y]
  exact (IsLocalization.algEquiv (Submonoid.powers (y * x)) X Y).restrictScalars R

variable (hJ : J ^ 2 = ⊥)
include hJ

/-- III.6.8, gluing: if `S₀` is covered by basic opens `D(tᵢ)` over which smooth lifts exist,
then `S₀` has a smooth lift. By induction on the number of opens, gluing two at a time. -/
theorem hasSmoothLift_of_span : ∀ (n : ℕ) {S₀ : Type u} [CommRing S₀] [Algebra R S₀]
    (t : Fin (n + 1) → S₀), Ideal.span (Set.range t) = ⊤ →
      (∀ i, HasSmoothLift J (Localization.Away (t i))) → HasSmoothLift J S₀ := by
  intro n
  induction n with
  | zero =>
    intro S₀ _ _ t ht hlift
    have hu : IsUnit (t 0) := by
      have hr : Set.range t = {t 0} := by
        ext x; simp [Fin.exists_fin_one, eq_comm]
      rw [hr, Ideal.span_singleton_eq_top] at ht
      exact ht
    exact (hlift 0).of_algEquiv ((IsLocalization.atUnit S₀ (Localization.Away (t 0)) (t 0)
      hu).symm.restrictScalars R)
  | succ n ih =>
    intro S₀ _ _ t ht hlift
    -- `D(t₀)` and `D(b)` cover, where `b` generates with `t₁, …` the unit ideal of `S₀[1/b]`
    have h1 : (1 : S₀) ∈ Ideal.span (Set.range t) := by rw [ht]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S₀).mp h1
    set a := t 0
    set b := ∑ i : Fin (n + 1), c i.succ * t i.succ
    have hab : Ideal.span {a, b} = ⊤ := by
      rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
      refine ⟨c 0, 1, ?_⟩
      rw [one_mul, ← hc, Fin.sum_univ_succ]
      simp only [smul_eq_mul, a, b]
    have hb : HasSmoothLift J (Localization.Away b) := by
      let B₀ := Localization.Away b
      refine ih (fun i ↦ algebraMap S₀ B₀ (t i.succ)) ?_ fun i ↦ ?_
      · refine Ideal.eq_top_of_isUnit_mem _ ?_ (IsLocalization.Away.algebraMap_isUnit b)
        rw [map_sum]
        refine Ideal.sum_mem _ fun i _ ↦ ?_
        rw [map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
      · exact ((hlift i.succ).away (algebraMap S₀ _ b)).of_algEquiv
          (awayAwayAlgEquiv (t i.succ) b)
    exact hasSmoothLift_of_away hJ hab (hlift 0) hb

end Cover

section Tensor

variable {R R₀ : Type u} [CommRing R] [CommRing R₀] [Algebra R R₀]
  (hR₀ : Function.Surjective (algebraMap R R₀))
include hR₀

lemma includeRight_surjective (S : Type*) [CommRing S] [Algebra R S] :
    Function.Surjective (Algebra.TensorProduct.includeRight : S →ₐ[R] R₀ ⊗[R] S) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul r₀ x =>
    obtain ⟨r, rfl⟩ := hR₀ r₀
    refine ⟨r • x, ?_⟩
    rw [Algebra.TensorProduct.includeRight_apply, ← TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]
  | add z z' hz hz' =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨x', rfl⟩ := hz'
    exact ⟨x + x', map_add _ _ _⟩

lemma ker_includeRight (S : Type*) [CommRing S] [Algebra R S] :
    RingHom.ker (Algebra.TensorProduct.includeRight : S →ₐ[R] R₀ ⊗[R] S) =
      (RingHom.ker (algebraMap R R₀)).map (algebraMap R S) := by
  let J := RingHom.ker (algebraMap R R₀)
  let e₀ : (R ⧸ J) ≃ₐ[R] R₀ :=
    AlgEquiv.ofRingEquiv (f := RingHom.quotientKerEquivOfSurjective hR₀) fun _ ↦ rfl
  let Φ : (S ⧸ J.map (algebraMap R S)) ≃ₐ[R] R₀ ⊗[R] S :=
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor S J).restrictScalars R).trans
      (Algebra.TensorProduct.congr e₀ AlgEquiv.refl)
  have hΦx (x : S) : Φ (Ideal.Quotient.mk _ x) = 1 ⊗ₜ x := by
    change Algebra.TensorProduct.congr e₀ AlgEquiv.refl
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S J (Ideal.Quotient.mk _ x)) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    change e₀ 1 ⊗ₜ x = _
    rw [map_one]
  ext x
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff Φ Φ.injective, hΦx]
  rfl

/-- A smooth lift in the tensor form `R₀ ⊗[R] S ≃ S₀` is a smooth lift. -/
lemma isSmoothLift_of_algEquiv {S L : Type u} [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    [CommRing L] [Algebra R₀ L] [Algebra R L] [IsScalarTower R R₀ L]
    (e : R₀ ⊗[R] S ≃ₐ[R₀] L) :
    IsSmoothLift (RingHom.ker (algebraMap R R₀))
      (((e.restrictScalars R : R₀ ⊗[R] S ≃ₐ[R] L) : R₀ ⊗[R] S →ₐ[R] L).comp
        Algebra.TensorProduct.includeRight) where
  smooth := inferInstance
  surjective := e.surjective.comp (includeRight_surjective hR₀ S)
  ker_eq := by
    rw [← ker_includeRight hR₀ S]
    ext x
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change e _ = 0 ↔ _
    rw [map_eq_zero_iff _ e.injective]
    rfl

/-- A smooth lift gives the tensor form `R₀ ⊗[R] S ≃ S₀`. -/
lemma IsSmoothLift.nonempty_algEquiv {S S₀ : Type u} [CommRing S] [Algebra R S] [CommRing S₀]
    [Algebra R₀ S₀] [Algebra R S₀] [IsScalarTower R R₀ S₀] {π : S →ₐ[R] S₀}
    (h : IsSmoothLift (RingHom.ker (algebraMap R R₀)) π) :
    Nonempty (R₀ ⊗[R] S ≃ₐ[R₀] S₀) := by
  let Φ : R₀ ⊗[R] S →ₐ[R₀] S₀ :=
    Algebra.TensorProduct.lift (Algebra.ofId R₀ S₀) π fun _ _ ↦ Commute.all _ _
  have hΦ (x : S) : Φ (1 ⊗ₜ x) = π x := by
    simp [Φ]
  refine ⟨AlgEquiv.ofBijective Φ ⟨(injective_iff_map_eq_zero Φ).mpr fun z hz ↦ ?_, fun y ↦ ?_⟩⟩
  · obtain ⟨x, rfl⟩ := includeRight_surjective hR₀ S z
    rw [Algebra.TensorProduct.includeRight_apply, hΦ, h.mem_ker_iff,
      ← ker_includeRight hR₀ S] at hz
    exact hz
  · obtain ⟨x, rfl⟩ := h.surjective y
    exact ⟨1 ⊗ₜ x, hΦ x⟩

end Tensor

section Existence

/-- III.6.8 (existence), square-zero case: let `R → R₀` be surjective with kernel `J`,
`J² = 0`. Every smooth `R₀`-algebra `S₀` has a smooth lift over `R`. Local lifts exist on the
basic opens of a cover (III.4.1, `exists_smooth_lift_localizationAway`), and are glued
(`hasSmoothLift_of_span`). -/
theorem hasSmoothLift_of_sq_eq_bot {R R₀ : Type u} [CommRing R] [CommRing R₀] [Algebra R R₀]
    (hR₀ : Function.Surjective (algebraMap R R₀))
    (hJ : RingHom.ker (algebraMap R R₀) ^ 2 = ⊥) (S₀ : Type u) [CommRing S₀] [Algebra R₀ S₀]
    [Algebra R S₀] [IsScalarTower R R₀ S₀] [Algebra.Smooth R₀ S₀] :
    HasSmoothLift (RingHom.ker (algebraMap R R₀)) S₀ := by
  classical
  set J := RingHom.ker (algebraMap R R₀)
  have hnil : IsNilpotent J := ⟨2, hJ⟩
  obtain ⟨s, hs, hloc⟩ := exists_smooth_lift_localizationAway (R := R) (R₀ := R₀) (S₀ := S₀)
    hR₀ hnil
  have hlift (t : S₀) (ht : t ∈ s) : HasSmoothLift J (Localization.Away t) := by
    obtain ⟨S, _, _, hS, ⟨e⟩⟩ := hloc t ht
    have : IsScalarTower R R₀ (Localization.Away t) := IsScalarTower.of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R S₀ (Localization.Away t),
        IsScalarTower.algebraMap_apply R R₀ S₀, ← IsScalarTower.algebraMap_apply]
    exact ⟨S, inferInstance, inferInstance, _, isSmoothLift_of_algEquiv hR₀ e⟩
  obtain ⟨t, hts, ht⟩ := Submodule.mem_span_finite_of_mem_span
    (show (1 : S₀) ∈ Submodule.span S₀ s by
      change (1 : S₀) ∈ Ideal.span s
      rw [hs]; exact Submodule.mem_top)
  rcases Nat.eq_zero_or_eq_succ_pred t.card with h0 | hn
  · -- `S₀` is the zero ring
    rw [Finset.card_eq_zero] at h0
    subst h0
    have : Subsingleton S₀ := subsingleton_of_zero_eq_one (by simpa using ht : (1 : S₀) = 0).symm
    let S := Localization.Away (0 : R)
    have : Subsingleton S :=
      IsLocalization.subsingleton (M := Submonoid.powers (0 : R)) ⟨1, pow_one 0⟩
    let π : S →ₐ[R] S₀ := IsLocalization.Away.liftAlgHom (0 : R) (f := Algebra.ofId R S₀)
      (isUnit_of_subsingleton _)
    refine ⟨S, inferInstance, inferInstance, π, ⟨?_, fun y ↦ ⟨0, Subsingleton.elim _ _⟩, ?_⟩⟩
    · have : Algebra.Etale R S := Algebra.Etale.of_isLocalizationAway 0
      infer_instance
    · ext x
      rw [Subsingleton.elim x 0]
      simp only [zero_mem]
  · -- a cover by finitely many basic opens with lifts
    set n := t.card.pred
    let e : t ≃ Fin (n + 1) := t.equivFin.trans (finCongr hn)
    let fk : Fin (n + 1) → S₀ := fun i ↦ (e.symm i).1
    have hrange : Set.range fk = t := by
      ext x
      refine ⟨?_, fun hx ↦ ⟨e ⟨x, hx⟩, by simp [fk]⟩⟩
      rintro ⟨i, rfl⟩
      exact (e.symm i).2
    refine hasSmoothLift_of_span hJ n fk ?_ fun i ↦ hlift _ (hts (e.symm i).2)
    rw [hrange, Ideal.eq_top_iff_one]
    exact ht

/-- III.6.8 (existence), nilpotent case, by induction on the nilpotency index. -/
theorem hasSmoothLift_of_pow_eq_bot (n : ℕ) : ∀ {R R₀ : Type u} [CommRing R] [CommRing R₀]
    [Algebra R R₀], Function.Surjective (algebraMap R R₀) →
      RingHom.ker (algebraMap R R₀) ^ (n + 1) = ⊥ → ∀ (S₀ : Type u) [CommRing S₀]
        [Algebra R₀ S₀] [Algebra R S₀] [IsScalarTower R R₀ S₀] [Algebra.Smooth R₀ S₀],
          HasSmoothLift (RingHom.ker (algebraMap R R₀)) S₀ := by
  induction n with
  | zero =>
    intro R R₀ _ _ _ hR₀ hJ S₀ _ _ _ _ _
    refine hasSmoothLift_of_sq_eq_bot hR₀ (eq_bot_iff.mpr ?_) S₀
    rw [← hJ]
    exact Ideal.pow_le_pow_right (by norm_num)
  | succ n ih =>
    intro R R₀ _ _ _ hR₀ hJ S₀ _ _ _ _ _
    set J := RingHom.ker (algebraMap R R₀)
    set K := J ^ (n + 1)
    have hKJ : K ≤ J := Ideal.pow_le_self (Nat.succ_ne_zero n)
    have hK2 : K ^ 2 = ⊥ := by
      rw [← pow_mul, eq_bot_iff, ← hJ]
      exact Ideal.pow_le_pow_right (by omega)
    let R' := R ⧸ K
    let φ : R' →+* R₀ := Ideal.Quotient.lift K (algebraMap R R₀) fun x hx ↦ hKJ hx
    let _ : Algebra R' R₀ := φ.toAlgebra
    let _ : Algebra R' S₀ := ((algebraMap R₀ S₀).comp φ).toAlgebra
    have : IsScalarTower R' R₀ S₀ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have : IsScalarTower R R' S₀ := IsScalarTower.of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R R₀ S₀]
      rfl
    have hφs : Function.Surjective (algebraMap R' R₀) := fun y ↦ by
      obtain ⟨r, rfl⟩ := hR₀ y
      exact ⟨Ideal.Quotient.mk K r, rfl⟩
    have hker' : RingHom.ker (algebraMap R' R₀) = J.map (Ideal.Quotient.mk K) :=
      Ideal.ker_quotient_lift _ _
    have hJ' : RingHom.ker (algebraMap R' R₀) ^ (n + 1) = ⊥ := by
      rw [hker', ← Ideal.map_pow, Ideal.map_quotient_self]
    obtain ⟨S', _, _, π', hπ'⟩ := ih hφs hJ' S₀
    let _ : Algebra R S' := ((algebraMap R' S').comp (Ideal.Quotient.mk K)).toAlgebra
    have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have := hπ'.smooth
    have hmk : RingHom.ker (algebraMap R R') = K := Ideal.mk_ker
    obtain ⟨S, _, _, π₁, hπ₁⟩ := hasSmoothLift_of_sq_eq_bot (R₀ := R')
      Ideal.Quotient.mk_surjective (by rw [hmk]; exact hK2) S'
    refine ⟨S, inferInstance, inferInstance, (π'.restrictScalars R).comp π₁,
      ⟨hπ₁.smooth, hπ'.surjective.comp hπ₁.surjective, ?_⟩⟩
    ext x
    rw [RingHom.mem_ker]
    change π' (π₁ x) = 0 ↔ _
    constructor
    · intro hx
      have h₀ : π₁ x ∈ J.map (algebraMap R S') := by
        have := (hπ'.mem_ker_iff (π₁ x)).mp hx
        rwa [hker', Ideal.map_map] at this
      have e : J.map (algebraMap R S') = (J.map (algebraMap R S)).map (π₁ : S →+* S') := by
        rw [Ideal.map_map]
        congr 1
        ext r
        exact (π₁.commutes r).symm
      rw [e] at h₀
      obtain ⟨y, hy, hyx⟩ :=
        (Ideal.mem_map_iff_of_surjective (π₁ : S →+* S') hπ₁.surjective).mp h₀
      have h₂ : x - y ∈ J.map (algebraMap R S) := by
        have : x - y ∈ K.map (algebraMap R S) := by
          rw [← hmk, ← hπ₁.mem_ker_iff, map_sub]
          exact sub_eq_zero.mpr hyx.symm
        exact Ideal.map_mono hKJ this
      simpa using add_mem h₂ hy
    · intro hx
      have hle : J.map (algebraMap R S) ≤ RingHom.ker ((π'.restrictScalars R).comp π₁) := by
        refine Ideal.map_le_iff_le_comap.mpr fun j hj ↦ ?_
        rw [Ideal.mem_comap, RingHom.mem_ker]
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R R₀ S₀, RingHom.mem_ker.mp hj,
          map_zero]
      exact hle hx

/-- III.6.8 (existence): let `R → R₀` be surjective with nilpotent kernel. Every smooth
`R₀`-algebra is the reduction of a smooth `R`-algebra; that is, a smooth affine scheme over
`Y₀ = Spec R₀` lifts to a smooth scheme over `Y = Spec R`. -/
theorem smoothLiftAffineStatement : SmoothLiftAffineStatement.{u} := by
  intro R R₀ S₀ _ _ _ _ _ hsurj hnil hsm
  let _ : Algebra R S₀ := ((algebraMap R₀ S₀).comp (algebraMap R R₀)).toAlgebra
  have : IsScalarTower R R₀ S₀ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨m, hm⟩ := hnil
  have hm' : RingHom.ker (algebraMap R R₀) ^ (m + 1) = ⊥ := by
    rw [pow_succ, hm, Ideal.zero_eq_bot, Ideal.bot_mul]
  obtain ⟨S, _, _, π, hπ⟩ := hasSmoothLift_of_pow_eq_bot m hsurj hm' S₀
  exact ⟨S, inferInstance, inferInstance, hπ.smooth, hπ.nonempty_algEquiv hsurj⟩

end Existence

end SGA.SGA1.ExposeIII
