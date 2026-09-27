/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import SGA.Foundations.Dimension.Integral

/-!
# Dimension of algebras of finite type over a field

Let `k` be a field and `A` a `k`-algebra of finite type which is a domain. We prove:

* `Algebra.FiniteType.ringKrullDim_eq_trdeg`: `dim A = trdeg_k A` (Stacks Project, Tag 00P0;
  the transcendence degree of `A` is that of its fraction field, see
  `Algebra.FiniteType.trdeg_fractionRing`);
* `Algebra.FiniteType.height_add_ringKrullDim_quotient`: `ht p + dim A/p = dim A` for every
  prime `p` (Stacks Project, Tags 00OS–00P6);
* `Algebra.FiniteType.height_eq_ringKrullDim_of_isMaximal`: every maximal ideal has height
  `dim A` (equicodimensionality);
* `Algebra.FiniteType.length_add_coheight_last_of_covBy`: `Spec A` is catenary: a saturated
  chain of primes `p₀ ⋖ ⋯ ⋖ pₗ` has length `dim A/p₀ - dim A/pₗ`; in particular all maximal
  chains of primes of `A` have length `dim A`.

For an arbitrary `k`-algebra of finite type `A` and a prime `q` we deduce
`ht q + trdeg_k κ(q) = max {dim A/p | p minimal, p ⊆ q}`
(`Algebra.FiniteType.height_add_trdeg_residueField`); geometrically, for a point `x` of an
affine scheme of finite type over `k`, `dim 𝒪_x + trdeg_k κ(x)` is the maximum of the
dimensions of the irreducible components through `x`.

The proofs follow the classical route: Noether normalization reduces everything to the
polynomial ring (integral extensions preserve dimension, heights and coheights, using going
down over the normal ring `k[X₁, …, Xₙ]`), where one argues by induction on `n` using a prime
element of a nonzero prime ideal.
-/

universe u v

open Order Cardinal PrimeSpectrum

section Order

variable {α β : Type*} [Preorder α] [Preorder β]

/-- If `f : α → β` is strictly monotone and every value of `f` lies strictly above a fixed
`b₀`, then `f` raises heights by at least one. -/
theorem Order.height_add_one_le_height_of_strictMono {f : α → β} (hf : StrictMono f) {b₀ : β}
    (hb : ∀ a, b₀ < f a) (a : α) : height a + 1 ≤ height (f a) := by
  let F : WithBot α → β := fun x ↦ WithBot.recBotCoe b₀ f x
  have hF : StrictMono F := by
    intro x y hxy
    induction x using WithBot.recBotCoe with
    | bot =>
      induction y using WithBot.recBotCoe with
      | bot => exact absurd hxy (lt_irrefl _)
      | coe b => exact hb b
    | coe a =>
      induction y using WithBot.recBotCoe with
      | bot => exact absurd hxy (WithBot.not_lt_bot _)
      | coe b => exact hf (WithBot.coe_lt_coe.mp hxy)
  simpa [F] using height_le_height_apply_of_strictMono F hF (a : WithBot α)

end Order

section IntegralExtension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If `S` is a domain, integral over its integrally closed subring `R`, and `ht q + dim R/q`
is the same number `n` for every prime `q` of `R`, then `ht P + dim S/P = n` for every prime `P`
of `S`. -/
theorem PrimeSpectrum.height_add_coheight_eq_of_isIntegral [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [Algebra.IsIntegral R S] [FaithfulSMul R S] {n : ℕ∞}
    (H : ∀ q : PrimeSpectrum R, height q + coheight q = n) (P : PrimeSpectrum S) :
    height P + coheight P = n := by
  rw [← height_comap_of_isIntegral_of_hasGoingDown (R := R) (S := S),
    ← coheight_comap_of_isIntegral (R := R) (S := S)]
  exact H _

end IntegralExtension

namespace Algebra.FiniteType

variable (k : Type*) [Field k] {A : Type*} [CommRing A] [Algebra k A]

section Normalization

variable {s : ℕ} {g : MvPolynomial (Fin s) k →ₐ[k] A}

/-- If `A` is integral over a polynomial subring `k[X₁, …, Xₛ]`, then `dim A = s`. -/
theorem ringKrullDim_eq_of_isIntegral_mvPolynomial (hinj : Function.Injective g)
    (hint : g.IsIntegral) : ringKrullDim A = s := by
  algebraize [g.toRingHom]
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  rw [ringKrullDim_eq_of_isIntegral (R := MvPolynomial (Fin s) k),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- If the domain `A` is integral over a polynomial subring `k[X₁, …, Xₛ]`, then
`trdeg_k A = s`. -/
theorem trdeg_eq_of_isIntegral_mvPolynomial [IsDomain A] (hinj : Function.Injective g)
    (hint : g.IsIntegral) : trdeg k A = s := by
  algebraize [g.toRingHom]
  have : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    .of_algebraMap_eq' g.comp_algebraMap.symm
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have h := lift_trdeg_add_eq k (MvPolynomial (Fin s) k) A
  rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero, lift_zero, add_zero] at h
  simpa using h.symm

end Normalization

/-- A nonzero algebra of finite type over a field has finite Krull dimension, given by any
Noether normalization. -/
theorem exists_ringKrullDim_eq [Nontrivial A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, ringKrullDim A = n := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  exact ⟨s, ringKrullDim_eq_of_isIntegral_mvPolynomial k hinj hint⟩

theorem finiteRingKrullDim [Nontrivial A] [Algebra.FiniteType k A] : FiniteRingKrullDim A := by
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq k (A := A)
  rw [finiteRingKrullDim_iff_ne_bot_and_top, hn]
  exact ⟨WithBot.coe_ne_bot, fun h ↦ ENat.natCast_ne_top n (WithBot.coe_eq_coe.mp h)⟩

/-- **Dimension equals transcendence degree** (Stacks Project, Tag 00P0): for a domain `A` of
finite type over a field `k`, `dim A = trdeg_k A`, and both are finite. -/
theorem exists_ringKrullDim_eq_trdeg [IsDomain A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, ringKrullDim A = n ∧ trdeg k A = n := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  exact ⟨s, ringKrullDim_eq_of_isIntegral_mvPolynomial k hinj hint,
    trdeg_eq_of_isIntegral_mvPolynomial k hinj hint⟩

/-- **Dimension equals transcendence degree** (Stacks Project, Tag 00P0). -/
theorem ringKrullDim_eq_trdeg [IsDomain A] [Algebra.FiniteType k A] :
    ringKrullDim A = (trdeg k A).toENat := by
  obtain ⟨n, h₁, h₂⟩ := exists_ringKrullDim_eq_trdeg k (A := A)
  rw [h₁, h₂]
  simp

/-- The transcendence degree of a domain is that of its fraction field. -/
theorem trdeg_fractionRing [IsDomain A] : trdeg k (FractionRing A) = trdeg k A := by
  have : Algebra.IsAlgebraic A (FractionRing A) := IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have h := lift_trdeg_add_eq k A (FractionRing A)
  rw [trdeg_eq_zero (R := A) (A := FractionRing A), lift_zero, add_zero, lift_id, lift_id] at h
  exact h.symm

end Algebra.FiniteType

namespace MvPolynomial

open Algebra.FiniteType

variable (k : Type*) [Field k]

/-- If `f` involves the variable `Xᵢ`, the images of the other variables in `k[X] ⧸ (f)` are
algebraically independent. -/
theorem algebraicIndependent_mk_X_of_degreeOf_ne_zero {σ : Type*} {f : MvPolynomial σ k} {i : σ}
    (hi : f.degreeOf i ≠ 0) :
    AlgebraicIndependent k
      (fun j : {j // j ≠ i} ↦ Ideal.Quotient.mk (Ideal.span {f}) (X (j : σ))) := by
  classical
  rw [algebraicIndependent_iff_injective_aeval]
  have hφ : (aeval fun j : {j // j ≠ i} ↦ Ideal.Quotient.mk (Ideal.span {f}) (X (j : σ))) =
      (Ideal.Quotient.mkₐ k (Ideal.span {f})).comp (rename Subtype.val) := by
    ext j
    simp
  rw [hφ, injective_iff_map_eq_zero]
  intro g hg
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hg
  obtain ⟨h, hh⟩ := hg
  by_contra hg0
  have hr : rename Subtype.val g ≠ 0 := fun h0 ↦
    hg0 (rename_injective _ Subtype.val_injective (h0.trans (map_zero _).symm))
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hr (by rw [hh, mul_zero])
  have hdeg := degreeOf_mul_eq (n := i) (ne_zero_of_degreeOf_ne_zero hi) hh0
  rw [← hh] at hdeg
  have hi' : i ∉ (rename Subtype.val g).vars := by
    intro hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (vars_rename Subtype.val g hmem)
    exact j.2 hj
  rw [mem_vars_iff_degreeOf_ne_zero, not_not] at hi'
  omega

/-- A prime element of a polynomial ring over a field involves at least one variable. -/
theorem exists_degreeOf_ne_zero_of_prime {σ : Type*} {f : MvPolynomial σ k} (hf : Prime f) :
    ∃ i, f.degreeOf i ≠ 0 := by
  by_contra! h
  have hv : f.vars = ∅ := Finset.eq_empty_of_forall_notMem fun i hi ↦
    (mem_vars_iff_degreeOf_ne_zero.mp hi) (h i)
  rw [vars_eq_empty_iff_eq_C] at hv
  apply hf.not_isUnit
  rw [hv]
  refine (IsUnit.mk0 _ fun h0 ↦ hf.ne_zero ?_).map C
  rw [hv, h0, map_zero]

variable {k} {n : ℕ}

/-- A hypersurface `f = 0` in affine `n`-space (`f` prime) has dimension `n - 1`. -/
theorem ringKrullDim_quotient_span_singleton_add_one {f : MvPolynomial (Fin n) k}
    (hf : Prime f) : ringKrullDim (MvPolynomial (Fin n) k ⧸ Ideal.span {f}) + 1 = n := by
  have : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr hf
  obtain ⟨s, hs, ht⟩ := exists_ringKrullDim_eq_trdeg k
    (A := MvPolynomial (Fin n) k ⧸ Ideal.span {f})
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_of_ne_zero hf.ne_zero)
  rw [ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin, hs] at hle
  obtain ⟨i, hi⟩ := exists_degreeOf_ne_zero_of_prime k hf
  have hcard := (algebraicIndependent_mk_X_of_degreeOf_ne_zero k hi).lift_cardinalMk_le_trdeg
  rw [ht, mk_fintype, Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
    at hcard
  rw [lift_natCast, lift_natCast] at hcard
  have hge : n - 1 ≤ s := by exact_mod_cast hcard
  have hle' : s + 1 ≤ n := by exact_mod_cast hle
  rw [hs, show n = s + 1 by omega]
  norm_cast

/-- `ht q + dim k[X₁, …, Xₙ]/q = n` for every prime `q` of the polynomial ring. -/
theorem height_add_coheight_eq (q : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    height q + coheight q = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hdim : ringKrullDim (MvPolynomial (Fin n) k) = n := by
    rw [ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  refine le_antisymm ?_ ?_
  · have h := Order.height_add_coheight_le_krullDim q
    rw [← ringKrullDim, hdim] at h
    exact_mod_cast h
  by_cases hq : q.asIdeal = ⊥
  · have h := coheight_eq_ringKrullDim_quotient q
    rw [hq, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), hdim] at h
    have h' : coheight q = n := by exact_mod_cast h
    rw [h']
    exact le_add_self
  obtain ⟨f, hfq, hf⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot q.isPrime hq
  set I := Ideal.span {f}
  have hIq : I ≤ q.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hfq
  have : I.IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr hf
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k (MvPolynomial (Fin n) k ⧸ I)
  have hsn : s + 1 = n := by
    have h := ringKrullDim_quotient_span_singleton_add_one hf
    rw [ringKrullDim_eq_of_isIntegral_mvPolynomial k hinj hint] at h
    exact_mod_cast h
  let q' : PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I) :=
    ⟨q.asIdeal.map (Ideal.Quotient.mk I),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩
  have hq' : comap (algebraMap (MvPolynomial (Fin n) k) _) q' = q := by
    ext1
    change (q.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = q.asIdeal
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hIq]
  have key : height q' + coheight q' = s := by
    algebraize [g.toRingHom]
    have : Algebra.IsIntegral (MvPolynomial (Fin s) k) (MvPolynomial (Fin n) k ⧸ I) := ⟨hint⟩
    have : FaithfulSMul (MvPolynomial (Fin s) k) (MvPolynomial (Fin n) k ⧸ I) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    exact height_add_coheight_eq_of_isIntegral (R := MvPolynomial (Fin s) k)
      (fun q ↦ ih s (by omega) q) q'
  have h1 : height q' + 1 ≤ height q := by
    rw [← hq']
    refine height_add_one_le_height_of_strictMono comap_strictMono_of_isIntegral
      (b₀ := ⟨⊥, Ideal.isPrime_bot⟩) (fun b ↦ lt_of_le_of_ne bot_le fun h ↦ hf.ne_zero ?_) q'
    have hfb : f ∈ (comap (algebraMap (MvPolynomial (Fin n) k) _) b).asIdeal := by
      change Ideal.Quotient.mk I f ∈ b.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
      exact b.asIdeal.zero_mem
    rwa [← h] at hfb
  have h2 : coheight q' = coheight q := by
    rw [← hq', coheight_comap_of_isIntegral]
  calc (n : ℕ∞) = s + 1 := by exact_mod_cast hsn.symm
    _ = height q' + coheight q' + 1 := by rw [key]
    _ = height q' + 1 + coheight q' := add_right_comm _ _ _
    _ ≤ height q + coheight q := by rw [h2]; gcongr

end MvPolynomial

namespace Algebra.FiniteType

open MvPolynomial

variable (k : Type*) [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- `ht p + dim A/p = dim A` for every prime `p` of a domain `A` of finite type over a field,
in terms of the height and coheight of `p` in `Spec A`. -/
theorem height_add_coheight_eq [IsDomain A] [Algebra.FiniteType k A] (p : PrimeSpectrum A) :
    ((height p + coheight p : ℕ∞) : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  rw [ringKrullDim_eq_of_isIntegral_mvPolynomial k hinj hint]
  algebraize [g.toRingHom]
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  rw [height_add_coheight_eq_of_isIntegral (R := MvPolynomial (Fin s) k)
    (fun q ↦ MvPolynomial.height_add_coheight_eq q) p]
  rfl

/-- **The dimension formula** (Stacks Project, Tags 00OS–00P6): for a prime `p` of a domain `A`
of finite type over a field, `ht p + dim A/p = dim A`. -/
theorem height_add_ringKrullDim_quotient [IsDomain A] [Algebra.FiniteType k A] (p : Ideal A)
    [p.IsPrime] : (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) = ringKrullDim A := by
  rw [ringKrullDim_quotient_eq_coheight,
    show p.height = Order.height (⟨p, ‹_›⟩ : PrimeSpectrum A) from
      height_eq_orderHeight ⟨p, ‹_›⟩, ← WithBot.coe_add]
  exact height_add_coheight_eq k _

/-- Equicodimensionality: every maximal ideal of a domain of finite type over a field has
height `dim A`. -/
theorem height_eq_ringKrullDim_of_isMaximal [IsDomain A] [Algebra.FiniteType k A] (m : Ideal A)
    [m.IsMaximal] : (m.height : WithBot ℕ∞) = ringKrullDim A := by
  rw [← height_add_ringKrullDim_quotient k m, ringKrullDim_eq_zero_of_isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp ‹_›), add_zero]

/-- If `p ⋖ q` are primes of a domain of finite type over a field (`q` minimal among the
primes strictly containing `p`), then `dim A/p = dim A/q + 1`. -/
theorem coheight_eq_coheight_add_one_of_covBy [IsDomain A] [Algebra.FiniteType k A]
    {p q : PrimeSpectrum A} (h : p ⋖ q) : coheight p = coheight q + 1 := by
  let φ := comap (algebraMap A (A ⧸ p.asIdeal))
  have hφinj : Function.Injective φ :=
    comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  have hφ : ∀ x, p ≤ φ x := fun x a ha ↦ by
    change Ideal.Quotient.mk _ a ∈ x.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact x.asIdeal.zero_mem
  let p' : PrimeSpectrum (A ⧸ p.asIdeal) := ⟨⊥, Ideal.isPrime_bot⟩
  have hp' : φ p' = p := by
    ext1
    exact Ideal.mk_ker
  let q' : PrimeSpectrum (A ⧸ p.asIdeal) :=
    ⟨q.asIdeal.map (Ideal.Quotient.mk _),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact h.le)⟩
  have hq' : φ q' = q := by
    ext1
    change (q.asIdeal.map (Ideal.Quotient.mk _)).comap (Ideal.Quotient.mk _) = q.asIdeal
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr h.le]
  have hmin : IsMin p' := fun x _ ↦ show (⊥ : _root_.Ideal _) ≤ x.asIdeal from bot_le
  have hht : height q' = 1 := by
    apply le_antisymm
    · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, height_le_coe_iff]
      intro y hy
      have hy' : φ y = p := by
        by_contra hne
        exact h.2 (lt_of_le_of_ne (hφ y) (Ne.symm hne)) (hq' ▸ comap_strictMono_of_isIntegral hy)
      rw [← hp'] at hy'
      rw [hφinj hy', height_eq_zero.mpr hmin]
      exact zero_lt_one
    · have hlt : p' < q' := lt_of_le_of_ne (fun a ha ↦ by simp_all [p'])
        (fun e ↦ h.ne (by rw [← hp', ← hq', e]))
      simpa [height_eq_zero.mpr hmin] using height_add_one_le hlt
  have e1 := height_add_coheight_eq k q'
  rw [← height_add_coheight_eq k p', height_eq_zero.mpr hmin, zero_add, hht,
    WithBot.coe_inj] at e1
  rw [← hp', ← hq', coheight_comap_of_isIntegral, coheight_comap_of_isIntegral, ← e1, add_comm]

/-- **Catenarity** of domains of finite type over a field: along a saturated chain of primes
`p₀ ⋖ p₁ ⋖ ⋯ ⋖ pₗ`, the length is `dim A/p₀ - dim A/pₗ`. -/
theorem length_add_coheight_last_of_covBy [IsDomain A] [Algebra.FiniteType k A]
    (l : LTSeries (PrimeSpectrum A)) (hl : ∀ i : Fin l.length, l i.castSucc ⋖ l i.succ) :
    l.length + coheight l.last = coheight l.head := by
  have key : ∀ i : Fin (l.length + 1), coheight (l i) = coheight l.last + (l.length - i : ℕ) := by
    intro i
    induction i using Fin.reverseInduction with
    | last => simp [RelSeries.last]
    | cast i ih =>
      rw [coheight_eq_coheight_add_one_of_covBy k (hl i), ih, add_assoc]
      congr 1
      have : (i : ℕ) < l.length := i.2
      simp only [Fin.val_succ, Fin.val_castSucc]
      norm_cast
      omega
  rw [RelSeries.head, key 0, add_comm]
  simp

/-- All maximal chains of primes in a domain `A` of finite type over a field have the same
length `dim A`: a saturated chain from `(0)` to a maximal ideal has length `dim A`. -/
theorem length_eq_ringKrullDim_of_covBy [IsDomain A] [Algebra.FiniteType k A]
    (l : LTSeries (PrimeSpectrum A)) (hl : ∀ i : Fin l.length, l i.castSucc ⋖ l i.succ)
    (hhead : l.head.asIdeal = ⊥) (hlast : l.last.asIdeal.IsMaximal) :
    (l.length : WithBot ℕ∞) = ringKrullDim A := by
  have h := length_add_coheight_last_of_covBy k l hl
  have h0 : coheight l.last = 0 := by
    have := coheight_eq_ringKrullDim_quotient l.last
    rw [ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hlast)] at this
    exact_mod_cast this
  have h1 : (coheight l.head : WithBot ℕ∞) = ringKrullDim A := by
    rw [coheight_eq_ringKrullDim_quotient, hhead,
      ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A)]
  rw [h0, add_zero] at h
  rw [← h1, ← h]
  rfl

section General

/-- The transcendence degree of a domain is that of its field of fractions. -/
theorem trdeg_eq_of_isFractionRing {B : Type u} {K : Type v} [CommRing B] [IsDomain B] [Field K]
    [Algebra B K] [IsFractionRing B K] [Algebra k B] [Algebra k K] [IsScalarTower k B K] :
    lift.{u} (trdeg k K) = lift.{v} (trdeg k B) := by
  have : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr
    (IsFractionRing.injective B K)
  have h := lift_trdeg_add_eq k B K
  rw [trdeg_eq_zero (R := B) (A := K), lift_zero, add_zero] at h
  exact h.symm

/-- `trdeg_k κ(q) = dim A/q` for a prime `q` of an algebra of finite type over `k`. -/
theorem trdeg_residueField [Algebra.FiniteType k A] (q : Ideal A) [q.IsPrime] :
    ((trdeg k q.ResidueField).toENat : WithBot ℕ∞) = ringKrullDim (A ⧸ q) := by
  have h := trdeg_eq_of_isFractionRing k (B := A ⧸ q) (K := q.ResidueField)
  rw [lift_id, lift_id] at h
  rw [h, ringKrullDim_eq_trdeg k]

/-- Catenarity, general form: for primes `p ≤ q` of an algebra of finite type over a field,
`dim A/p = ht(q/p) + dim A/q`; moreover `ht(q/p) ≤ ht q`, and every chain of primes above `p`
ending at `q` has length at most `ht(q/p)`. -/
private lemma exists_coheight_eq_add [Algebra.FiniteType k A] {p q : PrimeSpectrum A}
    (hpq : p ≤ q) : ∃ h : ℕ∞, h + coheight q = coheight p ∧ h ≤ height q ∧
      ∀ l : LTSeries (PrimeSpectrum A), p ≤ l.head → l.last = q → l.length ≤ h := by
  let e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus p.asIdeal
  have he : ∀ x, (e x : PrimeSpectrum A) = comap (algebraMap A (A ⧸ p.asIdeal)) x := fun _ ↦ rfl
  let q' := e.symm ⟨q, (mem_zeroLocus _ _).mpr hpq⟩
  let p' := e.symm ⟨p, (mem_zeroLocus _ _).mpr le_rfl⟩
  have hq' : comap (algebraMap A _) q' = q := by rw [← he, e.apply_symm_apply]
  have hp' : comap (algebraMap A _) p' = p := by rw [← he, e.apply_symm_apply]
  have hmin : IsMin p' := by
    intro x _
    rw [← e.le_iff_le, e.apply_symm_apply]
    exact (mem_zeroLocus _ _).mp (e x).2
  refine ⟨height q', ?_, ?_, fun l hl hlast ↦ ?_⟩
  · have h1 := height_add_coheight_eq k q'
    rw [← height_add_coheight_eq k p', height_eq_zero.mpr hmin, zero_add, WithBot.coe_inj] at h1
    rwa [(coheight_comap_of_isIntegral q').symm.trans (congrArg coheight hq'),
      (coheight_comap_of_isIntegral p').symm.trans (congrArg coheight hp')] at h1
  · rw [← hq']
    exact height_le_height_comap_of_isIntegral q'
  · have hmem : ∀ i, l i ∈ zeroLocus (p.asIdeal : Set A) := fun i ↦
      (mem_zeroLocus _ _).mpr (hl.trans (l.monotone (Fin.zero_le i)))
    let l' : LTSeries (zeroLocus (p.asIdeal : Set A)) :=
      LTSeries.mk l.length (fun i ↦ ⟨l i, hmem i⟩) (fun _ _ h ↦ l.strictMono h)
    have h := length_le_height_last (p := l'.map e.symm e.symm.strictMono)
    have hl' : (l'.map e.symm e.symm.strictMono).last = q' := by
      simp only [LTSeries.last_map, q']
      congr 1
      exact Subtype.ext hlast
    rwa [hl'] at h

/-- For primes `p ⊆ q` of an algebra of finite type over a field, `dim A/p = ht(q/p) + dim A/q`
(Stacks Project, Tag 00OS–00P6: finite type algebras over fields are catenary). -/
theorem ringKrullDim_quotient_eq_height_add [Algebra.FiniteType k A] {p q : Ideal A} [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) :
    ringKrullDim (A ⧸ p) = (q.map (Ideal.Quotient.mk p)).height + ringKrullDim (A ⧸ q) := by
  have : (q.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hq : Ideal.comap (Ideal.Quotient.mk p) (q.map (Ideal.Quotient.mk p)) = q := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hpq]
  have h := height_add_ringKrullDim_quotient k (q.map (Ideal.Quotient.mk p))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq)] at h
  exact h.symm

/-- For a prime `q` of an algebra `A` of finite type over a field, `ht q + dim A/q` is the
supremum (in fact the maximum) of `dim A/p` over the minimal primes `p ⊆ q`, i.e. the maximal
dimension of an irreducible component of `Spec A` through `q`. -/
theorem height_add_coheight_eq_iSup [Algebra.FiniteType k A] (q : PrimeSpectrum A) :
    height q + coheight q = ⨆ (p : PrimeSpectrum A) (_ : IsMin p) (_ : p ≤ q), coheight p := by
  apply le_antisymm
  · have : Nontrivial A := nonempty_iff_nontrivial.mp ⟨q⟩
    have := finiteRingKrullDim k (A := A)
    have hfin : height q ≠ ⊤ := by
      rw [← height_eq_orderHeight]
      exact Ideal.height_ne_top_of_isPrime
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
    obtain ⟨l, hl, hlen⟩ := exists_series_of_height_eq_coe q hn.symm
    obtain ⟨p₀, hp₀, hp₀le⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ l.head.asIdeal)
    let p : PrimeSpectrum A := ⟨p₀, hp₀.1.1⟩
    have hpmin : IsMin p := fun x hx ↦ hp₀.2 ⟨x.2, bot_le⟩ hx
    have hpq : p ≤ q := (show p ≤ l.head from hp₀le).trans (hl ▸ l.head_le_last)
    obtain ⟨h, hsum, -, hchain⟩ := exists_coheight_eq_add k hpq
    refine le_iSup₂_of_le p hpmin (le_iSup_of_le hpq ?_)
    rw [← hn, ← hlen, ← hsum]
    gcongr
    exact hchain l hp₀le hl
  · refine iSup₂_le fun p _ ↦ iSup_le fun hpq ↦ ?_
    obtain ⟨h, hsum, hle, -⟩ := exists_coheight_eq_add k hpq
    rw [← hsum]
    gcongr

/-- **`dim 𝒪_x + trdeg κ(x) = dim_x X`**, algebraic form: for a prime `q` of an algebra `A` of
finite type over a field `k`, `ht q + trdeg_k κ(q)` is the supremum (in fact the maximum) of
`dim A/p` over the minimal primes `p ⊆ q`. -/
theorem height_add_trdeg_residueField_eq_iSup [Algebra.FiniteType k A] (q : Ideal A)
    [q.IsPrime] : q.height + (trdeg k q.ResidueField).toENat =
      ⨆ (p : PrimeSpectrum A) (_ : IsMin p) (_ : p.asIdeal ≤ q), coheight p := by
  have h : (trdeg k q.ResidueField).toENat = coheight (⟨q, ‹_›⟩ : PrimeSpectrum A) := by
    rw [← WithBot.coe_inj, trdeg_residueField k, coheight_eq_ringKrullDim_quotient]
  rw [h, height_eq_orderHeight ⟨q, ‹_›⟩]
  exact height_add_coheight_eq_iSup k ⟨q, ‹_›⟩

/-- For a prime `q` of a domain `A` of finite type over `k`, `ht q + trdeg_k κ(q) = dim A`. -/
theorem height_add_trdeg_residueField [IsDomain A] [Algebra.FiniteType k A] (q : Ideal A)
    [q.IsPrime] : (q.height : WithBot ℕ∞) + (trdeg k q.ResidueField).toENat = ringKrullDim A := by
  rw [trdeg_residueField k, height_add_ringKrullDim_quotient k]

/-- If `φ : A → B` is a morphism of algebras of finite type over `k` and `Q` is a prime of `B`,
then `dim A/φ⁻¹(Q) ≤ dim B/Q`: the closure of the image of an irreducible closed subset has at
most its dimension. -/
theorem coheight_comap_le [Algebra.FiniteType k A] {B : Type*} [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (φ : A →ₐ[k] B) (Q : PrimeSpectrum B) :
    coheight (comap (φ : A →+* B) Q) ≤ coheight Q := by
  let ψ : A ⧸ (comap (φ : A →+* B) Q).asIdeal →ₐ[k] B ⧸ Q.asIdeal :=
    Ideal.quotientMapₐ Q.asIdeal φ le_rfl
  have h := lift_trdeg_le_of_injective ψ (Ideal.quotientMap_injective' (H := le_rfl) le_rfl)
  obtain ⟨m, hm₁, hm₂⟩ := exists_ringKrullDim_eq_trdeg k (A := A ⧸ (comap (φ : A →+* B) Q).asIdeal)
  obtain ⟨n, hn₁, hn₂⟩ := exists_ringKrullDim_eq_trdeg k (A := B ⧸ Q.asIdeal)
  rw [hm₂, hn₂, lift_natCast, lift_natCast, Nat.cast_le] at h
  have e₁ := coheight_eq_ringKrullDim_quotient (comap (φ : A →+* B) Q)
  have e₂ := coheight_eq_ringKrullDim_quotient Q
  rw [hm₁] at e₁
  rw [hn₁] at e₂
  have e₁' : coheight (comap (φ : A →+* B) Q) = m := by exact_mod_cast e₁
  have e₂' : coheight Q = n := by exact_mod_cast e₂
  rw [e₁', e₂']
  exact_mod_cast h

end General

end Algebra.FiniteType
