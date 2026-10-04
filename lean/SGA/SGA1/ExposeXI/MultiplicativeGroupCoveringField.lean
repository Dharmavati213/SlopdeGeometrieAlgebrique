/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.MultiplicativeGroupCoveringKummer
import SGA.SGA1.ExposeXI.TameGaloisCovering
import SGA.SGA1.ExposeXIII.AbhyankarBasic

/-!
# Function fields of coverings of `𝔾_m` (for XIII.2.12)

Let `A` be a finite étale `k[T, T⁻¹]`-algebra which is a domain (a connected covering of
`𝔾_{m,k}`). We place its function field `L = Frac A` over `K = k(T) = Frac k[T]` and record:

* `k[T, T⁻¹] → k(T)` makes `k(T)` a fraction field of `k[T, T⁻¹]` (`isFractionRing_laurent`);
* if `A` has at least `[A : k[T, T⁻¹]]` automorphisms, `L/K` is Galois with group
  `Aut_{k[T,T⁻¹]}(A)` (`isGaloisGroup_algEquiv`);
* the local rings `k[T]_(T - a)` of `𝔸¹` (`localRingAt a`) are discrete valuation rings with
  fraction field `K`.

That a Galois extension of degree prime to the residue characteristic of a discrete valuation ring
`R ⊆ K` is tamely ramified over `R`, with ramification indices dividing the degree, is
`ExposeXIII.isTameExtension_of_isGalois` and `ExposeXIII.ramificationIdx_dvd_finrank`
(`SGA.SGA1.ExposeXIII.TameRamification`).
-/

universe u

open Polynomial Module
open scoped LaurentPolynomial

namespace SGA.SGA1.ExposeXI.MultiplicativeGroupCovering

section Base

variable (k : Type u) [Field k]

/-- `T` as a unit of `k(T)`. -/
noncomputable def unitT : (FractionRing k[X])ˣ :=
  Units.mk0 (algebraMap k[X] (FractionRing k[X]) X)
    ((map_ne_zero_iff _ (IsFractionRing.injective k[X] _)).mpr X_ne_zero)

/-- The inclusion `k[T, T⁻¹] → k(T)`. -/
noncomputable def laurentToFrac : k[T;T⁻¹] →+* FractionRing k[X] :=
  LaurentPolynomial.eval₂ (algebraMap k (FractionRing k[X])) (unitT k)

/-- `k(T)` as a `k[T, T⁻¹]`-algebra (scoped: an ad hoc structure for this construction). -/
noncomputable scoped instance algebraLaurentFrac : Algebra k[T;T⁻¹] (FractionRing k[X]) :=
  (laurentToFrac k).toAlgebra

lemma algebraMap_laurent_toLaurent (p : k[X]) :
    algebraMap k[T;T⁻¹] (FractionRing k[X]) (toLaurent p) = algebraMap k[X] _ p := by
  change laurentToFrac k (toLaurent p) = _
  rw [laurentToFrac, LaurentPolynomial.eval₂_toLaurent]
  have : (Polynomial.eval₂RingHom (algebraMap k (FractionRing k[X])) (unitT k : FractionRing k[X]))
      = algebraMap k[X] (FractionRing k[X]) := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp [IsScalarTower.algebraMap_apply k k[X] (FractionRing k[X])]
    · simp [unitT]
  exact congrArg (fun φ : k[X] →+* FractionRing k[X] ↦ φ p) this

scoped instance isScalarTower_polynomial_laurent_frac :
    IsScalarTower k[X] k[T;T⁻¹] (FractionRing k[X]) :=
  .of_algebraMap_eq fun p ↦ by
    rw [LaurentPolynomial.algebraMap_eq_toLaurent, algebraMap_laurent_toLaurent]

scoped instance isFractionRing_laurent : IsFractionRing k[T;T⁻¹] (FractionRing k[X]) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (X : k[X]))
    k[T;T⁻¹] (FractionRing k[X])

end Base

section Cover

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {k : Type u} [Field k] (A : Type u) [CommRing A] [IsDomain A] [Algebra k[T;T⁻¹] A]
  [Algebra k[X] A] [IsScalarTower k[X] k[T;T⁻¹] A] [Module.Finite k[T;T⁻¹] A]
  [FaithfulSMul k[T;T⁻¹] A]

scoped instance faithfulSMul_polynomial : FaithfulSMul k[X] A := by
  refine (faithfulSMul_iff_algebraMap_injective _ _).mpr ?_
  rw [IsScalarTower.algebraMap_eq k[X] k[T;T⁻¹] A]
  exact (FaithfulSMul.algebraMap_injective k[T;T⁻¹] A).comp
    (IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero))

scoped instance faithfulSMul_polynomial_fractionRing : FaithfulSMul k[X] (FractionRing A) := by
  refine (faithfulSMul_iff_algebraMap_injective _ _).mpr ?_
  rw [IsScalarTower.algebraMap_eq k[X] A (FractionRing A)]
  exact (IsFractionRing.injective A _).comp (FaithfulSMul.algebraMap_injective k[X] A)

/-- `k[T, T⁻¹] → k(T) → Frac A` is the structure map of `Frac A`. -/
scoped instance isScalarTower_laurent_frac_fractionRing :
    IsScalarTower k[T;T⁻¹] (FractionRing k[X]) (FractionRing A) := by
  refine .of_algebraMap_eq' (IsLocalization.ringHom_ext (Submonoid.powers (X : k[X])) ?_)
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq k[X] k[T;T⁻¹] (FractionRing k[X]),
    ← IsScalarTower.algebraMap_eq k[X] (FractionRing k[X]) (FractionRing A),
    IsScalarTower.algebraMap_eq k[X] A (FractionRing A),
    IsScalarTower.algebraMap_eq k[X] k[T;T⁻¹] A, ← RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq k[T;T⁻¹] A (FractionRing A)]

omit [Module.Finite k[T;T⁻¹] A] in
/-- `[Frac A : k(T)] = [A : k[T, T⁻¹]]`. -/
lemma finrank_fractionRing :
    finrank (FractionRing k[X]) (FractionRing A) = finrank k[T;T⁻¹] A :=
  IsFractionRing.finrank_eq k[T;T⁻¹] _ A _

lemma finiteDimensional_fractionRing [Module.Free k[T;T⁻¹] A] :
    FiniteDimensional (FractionRing k[X]) (FractionRing A) :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_fractionRing]; exact Module.finrank_pos)

/-- Artin's theorem for a covering of `𝔾_m`: if `A` has at least `[A : k[T, T⁻¹]]`
automorphisms, they form a Galois group of `Frac A / k(T)`. -/
theorem isGaloisGroup_algEquiv [Module.Free k[T;T⁻¹] A] [Finite (A ≃ₐ[k[T;T⁻¹]] A)]
    (hG : finrank k[T;T⁻¹] A ≤ Nat.card (A ≃ₐ[k[T;T⁻¹]] A)) :
    letI := IsFractionRing.mulSemiringAction (A ≃ₐ[k[T;T⁻¹]] A) A (FractionRing A)
    IsGaloisGroup (A ≃ₐ[k[T;T⁻¹]] A) (FractionRing k[X]) (FractionRing A) := by
  let := IsFractionRing.mulSemiringAction (A ≃ₐ[k[T;T⁻¹]] A) A (FractionRing A)
  have : FaithfulSMul (A ≃ₐ[k[T;T⁻¹]] A) (FractionRing A) :=
    IsFractionRing.faithfulSMul _ A _
  have : SMulCommClass (A ≃ₐ[k[T;T⁻¹]] A) (FractionRing k[X]) (FractionRing A) :=
    IsFractionRing.smulCommClass _ k[T;T⁻¹] A _ _
  have := finiteDimensional_fractionRing (k := k) A
  exact isGaloisGroup_of_finrank_le ((finrank_fractionRing (k := k) A).symm ▸ hG)

end Cover

section LocalRings

variable {k : Type u} [Field k]

instance isPrime_span_X_sub_C (a : k) : (Ideal.span {X - C a} : Ideal k[X]).IsPrime :=
  (Ideal.span_singleton_prime (X_sub_C_ne_zero a)).mpr (prime_X_sub_C a)

variable (k) in
/-- The local ring `k[T]_(T - a)` of `𝔸¹_k` at `a`, a discrete valuation ring with fraction field
`k(T)`. -/
abbrev localRingAt (a : k) : Type u := Localization.AtPrime (Ideal.span {X - C a} : Ideal k[X])

instance isDiscreteValuationRing_localRingAt (a : k) : IsDiscreteValuationRing (localRingAt k a) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain k[X]
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero a) _

/-- The uniformizer `T - a` of `k[T]_(T - a)`. -/
noncomputable def uniformizer (a : k) : localRingAt k a := algebraMap k[X] _ (X - C a)

instance fact_irreducible_uniformizer (a : k) : Fact (Irreducible (uniformizer a)) := by
  refine ⟨(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr ?_⟩
  have h := IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {X - C a} : Ideal k[X])
    (localRingAt k a)
  rw [Ideal.map_span, Set.image_singleton] at h
  exact h.symm

lemma ringChar_residueField_localRing (a : k) :
    ringChar (IsLocalRing.ResidueField (localRingAt k a)) = ringChar k :=
  (Algebra.ringChar_eq k (IsLocalRing.ResidueField (localRingAt k a))).symm

end LocalRings

section Unramified

/-- Normalization commutes with localization, for étaleness: if the normalization of `R₁` in a
field `L` is formally étale over `R₁`, the normalization of a localization `R₂ = N⁻¹R₁` in `L` is
formally étale over `R₂`. -/
theorem formallyEtale_integralClosure_of_isLocalization {R₁ R₂ L : Type*} [CommRing R₁]
    [CommRing R₂] [Field L] [Algebra R₁ R₂] [Algebra R₁ L] [Algebra R₂ L] [IsScalarTower R₁ R₂ L]
    (N : Submonoid R₁) [IsLocalization N R₂] (hN : ∀ n ∈ N, algebraMap R₁ L n ≠ 0)
    [Algebra.FormallyEtale R₁ (integralClosure R₁ L)] :
    Algebra.FormallyEtale R₂ (integralClosure R₂ L) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid L N) L := by
    refine IsLocalization.self ?_
    rintro _ ⟨n, hn, rfl⟩
    exact (hN n hn).isUnit
  let ψ : integralClosure R₁ L →+* integralClosure R₂ L :=
    { toFun x := ⟨x.1, x.2.tower_top⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  let : Algebra (integralClosure R₁ L) (integralClosure R₂ L) := ψ.toAlgebra
  have : IsScalarTower (integralClosure R₁ L) (integralClosure R₂ L) L :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R₁ R₂ (integralClosure R₂ L) :=
    .of_algebraMap_eq fun r ↦ Subtype.ext (by
      change algebraMap R₁ L r = algebraMap R₂ L (algebraMap R₁ R₂ r)
      rw [← IsScalarTower.algebraMap_apply])
  have : IsScalarTower R₁ (integralClosure R₁ L) (integralClosure R₂ L) :=
    .of_algebraMap_eq fun r ↦ Subtype.ext (by
      rw [IsScalarTower.algebraMap_apply R₁ R₂ (integralClosure R₂ L)]
      change algebraMap R₂ L (algebraMap R₁ R₂ r) = algebraMap R₁ L r
      rw [← IsScalarTower.algebraMap_apply])
  have h := IsLocalization.integralClosure (R := R₁) (S := L) (Rf := R₂) (Sf := L) N
  have : IsLocalization (N.map (algebraMap R₁ (integralClosure R₁ L))) (integralClosure R₂ L) :=
    h
  exact Algebra.FormallyEtale.localization_map N (Rₘ := R₂) (S := integralClosure R₁ L)
    (Sₘ := integralClosure R₂ L)

/-- An étale prime has ramification index `1`. -/
theorem ramificationIdx_eq_one_of_formallyEtale {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.FormallyEtale R B] [Algebra.EssFiniteType R B] (Q : Ideal B)
    [Q.IsPrime] : Q.ramificationIdx R = 1 := by
  have : Algebra.FormallyUnramified B (Localization.AtPrime Q) :=
    Algebra.FormallyUnramified.of_isLocalization Q.primeCompl
  have : Algebra.IsUnramifiedAt R Q := Algebra.FormallyUnramified.comp R B _
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

end Unramified

section UnramifiedAway

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

open IsLocalRing

variable {k : Type u} [Field k] (A : Type u) [CommRing A] [IsDomain A] [Algebra k[T;T⁻¹] A]
  [Algebra k[X] A] [IsScalarTower k[X] k[T;T⁻¹] A] [Module.Finite k[T;T⁻¹] A]
  [FaithfulSMul k[T;T⁻¹] A] [Algebra.Etale k[T;T⁻¹] A]

/-- A connected étale covering of `𝔾_m` is unramified over the points `a ≠ 0` of `𝔸¹`: the
normalization of `k[T]_(T - a)` in `Frac A` is étale over `k[T]_(T - a)`, so its ramification
indices are `1`. -/
theorem ramificationIdx_eq_one_of_ne_zero (a : k) (ha : a ≠ 0)
    [Algebra.IsSeparable (FractionRing k[X]) (FractionRing A)]
    [Algebra (localRingAt k a) (FractionRing A)]
    [IsScalarTower (localRingAt k a) (FractionRing k[X]) (FractionRing A)]
    (Q : Ideal (integralClosure (localRingAt k a) (FractionRing A))) [Q.IsPrime] :
    Q.ramificationIdx (localRingAt k a) = 1 := by
  set Ra := localRingAt k a
  set L := FractionRing A
  -- `k[T]_(T - a)` is a localization of `k[T, T⁻¹]`
  have hXu : IsUnit (algebraMap k[X] Ra X) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff Ra (Ideal.span {X - C a} : Ideal k[X])]
    intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
    have := congrArg (Polynomial.eval a) hc
    simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero] at this
    exact ha this.symm
  let φ : k[T;T⁻¹] →+* Ra := LaurentPolynomial.eval₂ (algebraMap k Ra) hXu.unit
  let : Algebra k[T;T⁻¹] Ra := φ.toAlgebra
  have hφ : (algebraMap k[T;T⁻¹] Ra).comp (algebraMap k[X] k[T;T⁻¹]) = algebraMap k[X] Ra := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp [φ, RingHom.algebraMap_toAlgebra, Polynomial.toLaurent_C,
        IsScalarTower.algebraMap_apply k k[X] Ra]
    · simp [φ, RingHom.algebraMap_toAlgebra, Polynomial.toLaurent_X]
  have : IsScalarTower k[X] k[T;T⁻¹] Ra := .of_algebraMap_eq' hφ.symm
  have hle : Submonoid.powers (X : k[X]) ≤ (Ideal.span {X - C a} : Ideal k[X]).primeCompl := by
    rw [Submonoid.powers_le]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff Ra _ X).mp hXu
  have := IsLocalization.isLocalization_of_submonoid_le k[T;T⁻¹] Ra _ _ hle
  have : IsScalarTower k[T;T⁻¹] Ra L := by
    refine .of_algebraMap_eq' (IsLocalization.ringHom_ext (Submonoid.powers (X : k[X])) ?_)
    rw [IsScalarTower.algebraMap_eq k[T;T⁻¹] (FractionRing k[X]) L,
      IsScalarTower.algebraMap_eq Ra (FractionRing k[X]) L, RingHom.comp_assoc,
      RingHom.comp_assoc, RingHom.comp_assoc, hφ,
      ← IsScalarTower.algebraMap_eq k[X] Ra (FractionRing k[X]),
      ← IsScalarTower.algebraMap_eq k[X] k[T;T⁻¹] (FractionRing k[X])]
  -- the normalization of `k[T, T⁻¹]` in `Frac A` is `A`, which is étale
  have : IsIntegrallyClosed A := ExposeI.isIntegrallyClosed_of_etale (A := k[T;T⁻¹])
  let e : integralClosure k[T;T⁻¹] L ≃ₐ[k[T;T⁻¹]] A :=
    (IsIntegralClosure.equiv k[T;T⁻¹] A L (integralClosure k[T;T⁻¹] L)).symm
  have : Algebra.FormallyEtale k[T;T⁻¹] (integralClosure k[T;T⁻¹] L) :=
    Algebra.FormallyEtale.of_equiv e.symm
  have : Algebra.FormallyEtale Ra (integralClosure Ra L) :=
    formallyEtale_integralClosure_of_isLocalization
      ((Ideal.span {X - C a} : Ideal k[X]).primeCompl.map (algebraMap k[X] k[T;T⁻¹]))
      (fun n hn ↦ ?_)
  · have := finiteDimensional_fractionRing (k := k) A
    have : Module.Finite Ra (integralClosure Ra L) := by
      have := integralClosure.finite Ra (FractionRing k[X]) L
      exact this
    exact ramificationIdx_eq_one_of_formallyEtale Q
  · obtain ⟨m, hm, rfl⟩ := hn
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k[X] A L]
    refine (map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr ?_
    refine (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective k[X] A)).mpr ?_
    rintro rfl
    exact hm (zero_mem _)

end UnramifiedAway

end SGA.SGA1.ExposeXI.MultiplicativeGroupCovering
