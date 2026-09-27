/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeXI.TameCovering

/-!
# Galois coverings of `𝔸¹` of degree prime to `p` (for XIII.2.12)

Let `k` be algebraically closed and `A` a finite étale `k[T]`-algebra which is a domain, with at
least `[A : k[T]]` automorphisms (a connected Galois covering of `𝔸¹_k`, with group
`G = Aut_{k[T]} A`), of degree prime to the characteristic. Then `A = k[T]`
(`finrank_eq_one_of_le_card`). This is the case `g = 0`, `n = 1` of XIII.2.12, proved without
Riemann's existence theorem by reduction to the lattice argument `finrank_eq_one_of_tame`:

* Artin's theorem (`isGaloisGroup_of_finrank_le`): `G` is a Galois group of `Frac A / k(T)`;
* the normalization at `∞`: on `FieldAtInf k A`, a copy of `Frac A` on which `k[X]` acts through
  `X ↦ T⁻¹`, the integral closures `RingGm` of `k[T, T⁻¹]` and `RingInf` of `k[T⁻¹]` satisfy
  `RingGm = A[1/T] = RingInf[T]` (`isLocalization_A_ringGm`, `isLocalization_ringInf_ringGm`);
  `G` is a Galois group of `Frac A / k(T⁻¹)` (`FieldAtInf.isGaloisGroup`), so `RingInf` is a
  Dedekind domain, finite and separable over `k[T⁻¹]`;
* tameness at `∞` (`FieldAtInf.tame_ringInf`): if `x ≡ 1 mod P` lies in the other primes over
  `T⁻¹`, then `Tr(x) = ∑_g g x ≡ |D_P| mod P` (`sum_smul_sub_card_stabilizer_mem`), where the
  decomposition group `D_P` has order dividing `|G|`, prime to the characteristic;
* a rational point over `T = 0` (`exists_ringHom_eval_zero`).
-/

open Polynomial LaurentPolynomial Module

namespace SGA.SGA1.ExposeXI

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Artin

variable {G K L : Type*} [Group G] [Field K] [Field L] [Algebra K L] [MulSemiringAction G L]

/-- Artin's theorem, in the form used here: a finite group acting faithfully on `L` by
`K`-automorphisms, with at least `[L : K]` elements, is a Galois group of `L/K`. -/
theorem isGaloisGroup_of_finrank_le [Finite G] [SMulCommClass G K L] [FaithfulSMul G L]
    [FiniteDimensional K L] (h : finrank K L ≤ Nat.card G) : IsGaloisGroup G K L := by
  classical
  have := Fintype.ofFinite G
  let F := FixedPoints.intermediateField G (F := K) (E := L)
  have h1 : finrank F L = Nat.card G := by
    rw [Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card G L
  have h2 : finrank K F * finrank F L = finrank K L := Module.finrank_mul_finrank K F L
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hF : 0 < finrank K F := Module.finrank_pos
  have h3 : finrank K F = 1 := by
    rw [h1] at h2
    have : finrank K F * Nat.card G ≤ 1 * Nat.card G := by rw [h2, one_mul]; exact h
    have := Nat.le_of_mul_le_mul_right this hpos
    omega
  have hbot : F = ⊥ := IntermediateField.finrank_eq_one_iff.mp h3
  refine ⟨inferInstance, inferInstance, ⟨fun x hx ↦ ?_⟩⟩
  have hx' : x ∈ F := hx
  rw [hbot, IntermediateField.mem_bot] at hx'
  exact hx'

/-- For a finite Galois group `G` of `L/K`, the trace is the sum of the conjugates. -/
theorem algebraMap_trace_eq_sum_smul [Fintype G] [IsGaloisGroup G K L] (x : L) :
    algebraMap K L (Algebra.trace K L x) = ∑ g : G, g • x := by
  have := IsGaloisGroup.finiteDimensional G K L
  have := IsGaloisGroup.isGalois G K L
  rw [trace_eq_sum_automorphisms]
  exact (Fintype.sum_equiv (IsGaloisGroup.mulEquivAlgEquiv G K L).toEquiv _ _
    (fun g ↦ rfl)).symm

end Artin

section Symmetrization

open scoped Pointwise

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {G : Type*} [Group G] [Fintype G]
  [MulSemiringAction G B] [SMulCommClass G R B]

/-- Symmetrization over a prime `P` of `B` lying over `π`: if `x ≡ 1 mod P` and `x` lies in every
other prime over `π`, then `∑_g g x ≡ |D_P| mod P`, where `D_P` is the stabilizer of `P`. -/
theorem sum_smul_sub_card_stabilizer_mem (P : Ideal B) [P.IsPrime] (π : R)
    (hπ : algebraMap R B π ∈ P) (x : B) (hx : x - 1 ∈ P)
    (hother : ∀ P' : Ideal B, P'.IsPrime → algebraMap R B π ∈ P' → P' ≠ P → x ∈ P') :
    ∑ g : G, g • x - (Nat.card (MulAction.stabilizer G P) : B) ∈ P := by
  classical
  have hcard : (Nat.card (MulAction.stabilizer G P) : B) =
      ∑ g : G, if g ∈ MulAction.stabilizer G P then (1 : B) else 0 := by
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun g _ ↦ ?_
  split_ifs with hg
  · have hg' : g • P = P := hg
    have : g • (x - 1) ∈ g • P := Ideal.smul_mem_pointwise_smul g _ _ hx
    rwa [hg', smul_sub, smul_one] at this
  · rw [sub_zero]
    have hπ' : algebraMap R B π ∈ g⁻¹ • P := by
      rw [Ideal.mem_inv_pointwise_smul_iff, smul_algebraMap]
      exact hπ
    have hne : g⁻¹ • P ≠ P := fun h ↦ hg (by
      have : g • (g⁻¹ • P) = g • P := by rw [h]
      rw [smul_inv_smul] at this
      exact this.symm)
    have := hother _ inferInstance hπ' hne
    rwa [Ideal.mem_inv_pointwise_smul_iff] at this

end Symmetrization

section RationalPoint

variable {k : Type*} [Field k]

/-- A finite `k[T]`-algebra `B` over an algebraically closed field `k`, with `k[T] → B`
injective, has a rational point over `T = 0`. -/
theorem exists_ringHom_eval_zero [IsAlgClosed k] (B : Type*) [CommRing B] [Algebra k[X] B]
    [Module.Finite k[X] B] [FaithfulSMul k[X] B] :
    ∃ χ : B →+* k, ∀ p : k[X], χ (algebraMap k[X] B p) = p.eval 0 := by
  classical
  let P := RingHom.ker (Polynomial.evalRingHom (0 : k))
  have hP : P.IsMaximal := RingHom.ker_isMaximal_of_surjective _ fun a ↦ ⟨C a, eval_C⟩
  obtain ⟨M, hM, hMP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) P (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective k[X] B)]
    exact bot_le)
  let : Field (B ⧸ M) := Ideal.Quotient.field M
  let : Algebra k (B ⧸ M) :=
    ((Ideal.Quotient.mk M).comp ((algebraMap k[X] B).comp C)).toAlgebra
  have hcomp : (Ideal.Quotient.mk M).comp (algebraMap k[X] B) =
      (algebraMap k (B ⧸ M)).comp (Polynomial.evalRingHom 0) := by
    refine RingHom.ext fun p ↦ ?_
    have h : p - Polynomial.C (p.eval 0) ∈ P := by simp [P, RingHom.mem_ker]
    rw [← hMP, Ideal.mem_comap, map_sub, ← Ideal.Quotient.eq_zero_iff_mem, map_sub,
      sub_eq_zero] at h
    exact h
  have : Algebra.IsIntegral k (B ⧸ M) := ⟨fun y ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨f, hf, hfb⟩ := Algebra.IsIntegral.isIntegral (R := k[X]) b
    refine ⟨f.map (Polynomial.evalRingHom 0), hf.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hcomp, ← Polynomial.hom_eval₂, hfb, map_zero]⟩
  let χ₀ : (B ⧸ M) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨χ₀.toRingHom.comp (Ideal.Quotient.mk M), fun p ↦ ?_⟩
  have := congrArg χ₀ (RingHom.congr_fun hcomp p)
  simpa using this

end RationalPoint

section Clearing

/-- Clearing denominators: if `s` is integral over the localization `R[1/r]`, then `rⁿ s` is
integral over `R` for some `n`. -/
theorem exists_isIntegralElem_pow_mul {R Rₘ S : Type*} [CommRing R] [CommRing Rₘ] [CommRing S]
    [Algebra R Rₘ] (r : R) [IsLocalization.Away r Rₘ] (g : Rₘ →+* S) {s : S}
    (hs : g.IsIntegralElem s) :
    ∃ n : ℕ, (g.comp (algebraMap R Rₘ)).IsIntegralElem (g (algebraMap R Rₘ r) ^ n * s) := by
  let := g.toAlgebra
  let := (g.comp (algebraMap R Rₘ)).toAlgebra
  have : IsScalarTower R Rₘ S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers r) (Rₘ := Rₘ) s hs
  refine ⟨n, ?_⟩
  have : ((⟨r ^ n, n, rfl⟩ : Submonoid.powers r) • s) = g (algebraMap R Rₘ r) ^ n * s := by
    rw [Submonoid.smul_def, Algebra.smul_def, ← map_pow, ← map_pow]
    rfl
  rw [← this]
  exact hm

end Clearing

section AtInfinity

/-- The function field `Frac A` of a covering `Spec A → 𝔸¹_k = Spec k[T]`, seen from the chart
`Spec k[T⁻¹]` of `ℙ¹` at `∞`: a type synonym of `FractionRing A` on which `k[X]` acts through
`X ↦ T⁻¹` (and `k[T, T⁻¹]` in the obvious way). -/
@[nolint unusedArguments]
def FieldAtInf (k : Type*) [Field k] (A : Type*) [CommRing A] [Algebra k[X] A] : Type _ :=
  FractionRing A

variable (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A] [Algebra k[X] A]

namespace FieldAtInf

noncomputable instance : Field (FieldAtInf k A) := inferInstanceAs (Field (FractionRing A))

noncomputable instance : Algebra A (FieldAtInf k A) :=
  inferInstanceAs (Algebra A (FractionRing A))

instance : IsFractionRing A (FieldAtInf k A) :=
  inferInstanceAs (IsFractionRing A (FractionRing A))

noncomputable instance : Algebra k (FieldAtInf k A) :=
  ((algebraMap A (FieldAtInf k A)).comp ((algebraMap k[X] A).comp Polynomial.C)).toAlgebra

variable {k A}

/-- The coordinate `T` of `𝔸¹` in `Frac A`. -/
noncomputable def coordT : FieldAtInf k A := algebraMap A (FieldAtInf k A) (algebraMap k[X] A X)

lemma eval₂_coordT (p : k[X]) :
    p.eval₂ (algebraMap k (FieldAtInf k A)) coordT = algebraMap A _ (algebraMap k[X] A p) := by
  let ψ := (algebraMap A (FieldAtInf k A)).comp (algebraMap k[X] A)
  change p.eval₂ (ψ.comp Polynomial.C) (ψ X) = ψ p
  rw [← Polynomial.hom_eval₂, Polynomial.eval₂_C_X]

variable [FaithfulSMul k[X] A]

lemma coordT_ne_zero : (coordT : FieldAtInf k A) ≠ 0 := by
  rw [coordT, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective A _),
    map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective k[X] A)]
  exact X_ne_zero

variable (k A) in
/-- `T` as a unit of `Frac A`. -/
noncomputable def coordTUnit : (FieldAtInf k A)ˣ := Units.mk0 coordT coordT_ne_zero

noncomputable instance : Algebra k[T;T⁻¹] (FieldAtInf k A) :=
  (LaurentPolynomial.eval₂ (algebraMap k (FieldAtInf k A)) (coordTUnit k A)).toAlgebra

lemma algebraMap_laurent_apply (f : k[T;T⁻¹]) : algebraMap k[T;T⁻¹] (FieldAtInf k A) f =
    LaurentPolynomial.eval₂ (algebraMap k (FieldAtInf k A)) (coordTUnit k A) f := rfl

instance : IsScalarTower k k[T;T⁻¹] (FieldAtInf k A) := IsScalarTower.of_algebraMap_eq fun c ↦ by
  rw [algebraMap_laurent_apply, LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, LaurentPolynomial.eval₂_C]

/-- `k[X]` acts on `Frac A` through `X ↦ T⁻¹`. -/
noncomputable instance : Algebra k[X] (FieldAtInf k A) :=
  ((algebraMap k[T;T⁻¹] (FieldAtInf k A)).comp (toLaurentInv k).toRingHom).toAlgebra

lemma algebraMap_polynomial_apply (p : k[X]) : algebraMap k[X] (FieldAtInf k A) p =
    algebraMap k[T;T⁻¹] (FieldAtInf k A) (toLaurentInv k p) := rfl

lemma algebraMap_toLaurent (p : k[X]) : algebraMap k[T;T⁻¹] (FieldAtInf k A) (toLaurent p) =
    algebraMap A (FieldAtInf k A) (algebraMap k[X] A p) := by
  rw [algebraMap_laurent_apply, eval₂_toLaurent]
  exact eval₂_coordT p

lemma algebraMap_polynomial_eq_eval₂ (p : k[X]) :
    algebraMap k[X] (FieldAtInf k A) p = p.eval₂ (algebraMap k (FieldAtInf k A)) coordT⁻¹ := by
  let φ₁ : k[X] →+* FieldAtInf k A := algebraMap k[X] (FieldAtInf k A)
  let φ₂ : k[X] →+* FieldAtInf k A := Polynomial.eval₂RingHom (algebraMap k _) coordT⁻¹
  suffices φ₁ = φ₂ from RingHom.congr_fun this p
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · simp only [φ₁, φ₂, algebraMap_polynomial_apply, coe_eval₂RingHom, Polynomial.eval₂_C]
    rw [show (Polynomial.C c : k[X]) = algebraMap k k[X] c from rfl, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply k k[T;T⁻¹] (FieldAtInf k A)]
  · simp only [φ₁, φ₂, algebraMap_polynomial_apply, coe_eval₂RingHom, eval₂_X]
    rw [toLaurentInv_apply, toLaurent_X, invert_T, algebraMap_laurent_apply, eval₂_T]
    simp [coordTUnit]

/-- `p(T) = T^N p̃(T⁻¹)` for `p̃` the reflection of `p` with respect to `N ≥ deg p`. -/
lemma algebraMap_eq_mul_reflect (p : k[X]) {N : ℕ} (hN : p.natDegree ≤ N) :
    algebraMap A (FieldAtInf k A) (algebraMap k[X] A p) =
      algebraMap k[X] (FieldAtInf k A) (reflect N p) * coordT ^ N := by
  have : Invertible (coordT : FieldAtInf k A) := invertibleOfNonzero coordT_ne_zero
  rw [← eval₂_coordT, ← eval₂_reflect_mul_pow _ _ N p hN, invOf_eq_inv,
    algebraMap_polynomial_eq_eval₂]

instance : FaithfulSMul k[X] (FieldAtInf k A) := by
  refine (faithfulSMul_iff_algebraMap_injective _ _).mpr ((injective_iff_map_eq_zero _).mpr
    fun p hp ↦ ?_)
  have : Invertible (coordT⁻¹ : FieldAtInf k A) := invertibleOfNonzero (inv_ne_zero coordT_ne_zero)
  have h := eval₂_reflect_mul_pow (algebraMap k (FieldAtInf k A)) coordT⁻¹ p.natDegree p le_rfl
  rw [← algebraMap_polynomial_eq_eval₂, hp, invOf_eq_inv, inv_inv, eval₂_coordT,
    mul_eq_zero, map_eq_zero_iff _ (IsFractionRing.injective A _),
    map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective k[X] A), reflect_eq_zero_iff] at h
  exact h.resolve_right (pow_ne_zero _ (inv_ne_zero coordT_ne_zero))

end FieldAtInf

end AtInfinity

section Rings

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k[X] A]

namespace FieldAtInf

noncomputable instance : MulSemiringAction (A ≃ₐ[k[X]] A) (FieldAtInf k A) :=
  IsFractionRing.mulSemiringAction (A ≃ₐ[k[X]] A) A (FieldAtInf k A)

instance : SMulDistribClass (A ≃ₐ[k[X]] A) A (FieldAtInf k A) :=
  IsFractionRing.smulDistribClass (A ≃ₐ[k[X]] A) A (FieldAtInf k A)

variable [FaithfulSMul k[X] A]

/-- The automorphisms of `A` over `k[T]` fix `k[T, T⁻¹]` in `Frac A`. -/
lemma smul_algebraMap_laurent (g : A ≃ₐ[k[X]] A) (f : k[T;T⁻¹]) :
    g • algebraMap k[T;T⁻¹] (FieldAtInf k A) f = algebraMap k[T;T⁻¹] (FieldAtInf k A) f := by
  suffices (MulSemiringAction.toRingHom _ (FieldAtInf k A) g).comp
      (algebraMap k[T;T⁻¹] (FieldAtInf k A)) = algebraMap k[T;T⁻¹] (FieldAtInf k A) from
    RingHom.congr_fun this f
  refine IsLocalization.ringHom_ext (Submonoid.powers (X : k[X])) (RingHom.ext fun p ↦ ?_)
  simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, algebraMap_eq_toLaurent,
    algebraMap_toLaurent]
  rw [← algebraMap.coe_smul', AlgEquiv.smul_def, AlgEquiv.commutes]

instance : SMulCommClass (A ≃ₐ[k[X]] A) k[T;T⁻¹] (FieldAtInf k A) := ⟨fun g f y ↦ by
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul', smul_algebraMap_laurent]⟩

instance : SMulCommClass (A ≃ₐ[k[X]] A) k[X] (FieldAtInf k A) := ⟨fun g p y ↦ by
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul', algebraMap_polynomial_apply,
    smul_algebraMap_laurent]⟩

variable (k A) in
/-- The coordinate ring of the covering over `𝔾ₘ = Spec k[T, T⁻¹]`: the integral closure of
`k[T, T⁻¹]` in `Frac A`. -/
noncomputable abbrev RingGm := integralClosure k[T;T⁻¹] (FieldAtInf k A)

variable (k A) in
/-- The coordinate ring of the normalization of `ℙ¹` in `Frac A` over the chart `Spec k[T⁻¹]`
at `∞`: the integral closure of `k[T⁻¹]` in `Frac A`. -/
noncomputable abbrev RingInf := integralClosure k[X] (FieldAtInf k A)

noncomputable instance : Algebra (RingInf k A) (RingGm k A) :=
  (RingHom.codRestrict (RingInf k A).val.toRingHom (RingGm k A) fun b ↦
    b.2.map_of_comp_eq (toLaurentInv k).toRingHom (RingHom.id _) rfl).toAlgebra

lemma algebraMap_ringInf_ringGm (p : k[X]) :
    algebraMap (RingInf k A) (RingGm k A) (algebraMap k[X] (RingInf k A) p) =
      algebraMap k[T;T⁻¹] (RingGm k A) (toLaurentInv k p) := rfl

variable [Module.Finite k[X] A]

lemma isIntegral_algebraMap (a : A) :
    IsIntegral k[T;T⁻¹] (algebraMap A (FieldAtInf k A) a) :=
  (Algebra.IsIntegral.isIntegral (R := k[X]) a).map_of_comp_eq (algebraMap k[X] k[T;T⁻¹])
    (algebraMap A _) (RingHom.ext fun p ↦ by
      rw [RingHom.comp_apply, algebraMap_eq_toLaurent, algebraMap_toLaurent]
      rfl)

noncomputable instance : Algebra A (RingGm k A) :=
  ((algebraMap A (FieldAtInf k A)).codRestrict (RingGm k A) isIntegral_algebraMap).toAlgebra

lemma algebraMap_A_ringGm (p : k[X]) : algebraMap A (RingGm k A) (algebraMap k[X] A p) =
    algebraMap k[T;T⁻¹] (RingGm k A) (toLaurent p) :=
  Subtype.ext (algebraMap_toLaurent p).symm

/-- `k[T, T⁻¹] ⊗ A`: the ring of the covering over `𝔾ₘ` is `A[1/T]`. -/
theorem isLocalization_A_ringGm [IsIntegrallyClosed A] :
    IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers (X : k[X]))) (RingGm k A) where
  map_units := by
    rintro ⟨_, _, ⟨n, rfl⟩, rfl⟩
    change IsUnit (algebraMap A (RingGm k A) (algebraMap k[X] A (X ^ n)))
    rw [algebraMap_A_ringGm, Polynomial.toLaurent_X_pow]
    exact (isUnit_T _).map _
  surj := by
    intro w
    obtain ⟨n, hn⟩ := exists_isIntegralElem_pow_mul (X : k[X])
      (algebraMap k[T;T⁻¹] (FieldAtInf k A)) w.2
    have hcomp : (algebraMap k[T;T⁻¹] (FieldAtInf k A)).comp (algebraMap k[X] k[T;T⁻¹]) =
        (algebraMap A (FieldAtInf k A)).comp (algebraMap k[X] A) := RingHom.ext fun p ↦ by
      rw [RingHom.comp_apply, algebraMap_eq_toLaurent, algebraMap_toLaurent]
      rfl
    rw [hcomp] at hn
    have hA : IsIntegral A ((algebraMap k[T;T⁻¹] (FieldAtInf k A)
        (algebraMap k[X] k[T;T⁻¹] X)) ^ n * (w : FieldAtInf k A)) := by
      obtain ⟨f, hf, hfx⟩ := hn
      exact ⟨f.map (algebraMap k[X] A), hf.map _, by rw [eval₂_map]; exact hfx⟩
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hA
    refine ⟨⟨a, ⟨algebraMap k[X] A (X ^ n), X ^ n, ⟨n, rfl⟩, rfl⟩⟩, Subtype.ext ?_⟩
    change (w : FieldAtInf k A) * algebraMap A (FieldAtInf k A) (algebraMap k[X] A (X ^ n)) =
      algebraMap A (FieldAtInf k A) a
    rw [ha, ← algebraMap_toLaurent, map_pow, map_pow, algebraMap_eq_toLaurent, mul_comm]
  exists_of_eq := by
    intro a b h
    refine ⟨1, ?_⟩
    have h' : algebraMap A (FieldAtInf k A) a = algebraMap A (FieldAtInf k A) b :=
      congrArg Subtype.val h
    rw [IsFractionRing.injective A (FieldAtInf k A) h']

omit [Module.Finite k[X] A] in
/-- The ring of the covering over `𝔾ₘ` is also the localization of the ring at `∞` at `T⁻¹`. -/
theorem isLocalization_ringInf_ringGm :
    IsLocalization (Algebra.algebraMapSubmonoid (RingInf k A) (Submonoid.powers (X : k[X])))
      (RingGm k A) where
  map_units := by
    rintro ⟨_, _, ⟨n, rfl⟩, rfl⟩
    change IsUnit (algebraMap (RingInf k A) (RingGm k A) (algebraMap k[X] (RingInf k A) (X ^ n)))
    rw [algebraMap_ringInf_ringGm, map_pow, toLaurentInv_apply, toLaurent_X, invert_T]
    exact ((isUnit_T _).pow n).map _
  surj := by
    intro w
    let _ : Algebra k[X] k[T;T⁻¹] := (toLaurentInv k).toRingHom.toAlgebra
    have := isLocalization_toLaurentInv k
    obtain ⟨n, hn⟩ := exists_isIntegralElem_pow_mul (X : k[X])
      (algebraMap k[T;T⁻¹] (FieldAtInf k A)) w.2
    refine ⟨⟨⟨_, hn⟩, ⟨algebraMap k[X] (RingInf k A) (X ^ n), X ^ n, ⟨n, rfl⟩, rfl⟩⟩,
      Subtype.ext ?_⟩
    change (w : FieldAtInf k A) * algebraMap k[X] (FieldAtInf k A) (X ^ n) = _
    rw [map_pow, mul_comm]
    rfl
  exists_of_eq := by
    intro a b h
    refine ⟨1, ?_⟩
    have h' : a = b :=
      Subtype.ext (congrArg (Subtype.val : RingGm k A → FieldAtInf k A) h)
    rw [h']

end FieldAtInf

end Rings

section Galois

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k[X] A]
  [FaithfulSMul k[X] A] [Module.Finite k[X] A] [Finite (A ≃ₐ[k[X]] A)]

namespace FieldAtInf

/-- Artin's theorem for the covering: if `A` has at least `[A : k[T]]` automorphisms, they form
a Galois group of `Frac A / k(T)`. -/
theorem isGaloisGroup_fractionRing (hG : finrank k[X] A ≤ Nat.card (A ≃ₐ[k[X]] A)) :
    letI := IsFractionRing.mulSemiringAction (A ≃ₐ[k[X]] A) A (FractionRing A)
    IsGaloisGroup (A ≃ₐ[k[X]] A) (FractionRing k[X]) (FractionRing A) := by
  let := IsFractionRing.mulSemiringAction (A ≃ₐ[k[X]] A) A (FractionRing A)
  have : FaithfulSMul (A ≃ₐ[k[X]] A) (FractionRing A) :=
    IsFractionRing.faithfulSMul _ A _
  have : SMulCommClass (A ≃ₐ[k[X]] A) (FractionRing k[X]) (FractionRing A) :=
    IsFractionRing.smulCommClass _ k[X] A _ _
  have hfin : finrank (FractionRing k[X]) (FractionRing A) = finrank k[X] A :=
    IsFractionRing.finrank_eq k[X] _ A _
  have : FiniteDimensional (FractionRing k[X]) (FractionRing A) :=
    FiniteDimensional.of_finrank_pos (by rw [hfin]; exact Module.finrank_pos)
  exact isGaloisGroup_of_finrank_le (hfin ▸ hG)

/-- The elements of `Frac A` fixed by the automorphisms lie in `k(T⁻¹) = k(T)`. -/
theorem exists_algebraMap_eq_of_forall_smul_eq (hG : finrank k[X] A ≤ Nat.card (A ≃ₐ[k[X]] A))
    (x : FieldAtInf k A) (hx : ∀ g : A ≃ₐ[k[X]] A, g • x = x) :
    ∃ z : FractionRing k[X], algebraMap (FractionRing k[X]) (FieldAtInf k A) z = x := by
  let := IsFractionRing.mulSemiringAction (A ≃ₐ[k[X]] A) A (FractionRing A)
  have hGal := isGaloisGroup_fractionRing hG
  obtain ⟨y, hy⟩ := hGal.isInvariant.isInvariant (x : FractionRing A) hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective k[X] y
  rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply k[X] A (FractionRing A),
    IsScalarTower.algebraMap_apply k[X] A (FractionRing A)] at hy
  change algebraMap A (FieldAtInf k A) (algebraMap k[X] A a) /
    algebraMap A (FieldAtInf k A) (algebraMap k[X] A b) = x at hy
  rw [algebraMap_eq_mul_reflect a (le_max_left a.natDegree b.natDegree),
    algebraMap_eq_mul_reflect b (le_max_right a.natDegree b.natDegree),
    mul_div_mul_right _ _ (pow_ne_zero _ coordT_ne_zero)] at hy
  refine ⟨algebraMap k[X] _ (reflect (max a.natDegree b.natDegree) a) /
    algebraMap k[X] _ (reflect (max a.natDegree b.natDegree) b), ?_⟩
  rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact hy

/-- The automorphisms of `A` form a Galois group of `Frac A` over `k(T⁻¹)`. -/
theorem isGaloisGroup (hG : finrank k[X] A ≤ Nat.card (A ≃ₐ[k[X]] A)) :
    IsGaloisGroup (A ≃ₐ[k[X]] A) (FractionRing k[X]) (FieldAtInf k A) where
  faithful := IsFractionRing.faithfulSMul _ A _
  commutes := ⟨fun g z y ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective k[X] z
    rw [map_div₀, smul_div₀', ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, smul_algebraMap, smul_algebraMap]⟩
  isInvariant := ⟨exists_algebraMap_eq_of_forall_smul_eq hG⟩

end FieldAtInf

end Galois

section AtInf

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k[X] A]
  [FaithfulSMul k[X] A] [Finite (A ≃ₐ[k[X]] A)]
  [hGal : IsGaloisGroup (A ≃ₐ[k[X]] A) (FractionRing k[X]) (FieldAtInf k A)]

namespace FieldAtInf

include hGal

theorem finiteDimensional : FiniteDimensional (FractionRing k[X]) (FieldAtInf k A) :=
  IsGaloisGroup.finiteDimensional (A ≃ₐ[k[X]] A) _ _

theorem isSeparable : Algebra.IsSeparable (FractionRing k[X]) (FieldAtInf k A) :=
  have := IsGaloisGroup.isGalois (A ≃ₐ[k[X]] A) (FractionRing k[X]) (FieldAtInf k A)
  inferInstance

theorem isFractionRing_ringInf : IsFractionRing (RingInf k A) (FieldAtInf k A) :=
  have := finiteDimensional (k := k) (A := A)
  IsIntegralClosure.isFractionRing_of_finite_extension k[X] (FractionRing k[X]) _ _

theorem isDedekindDomain_ringInf : IsDedekindDomain (RingInf k A) :=
  have := finiteDimensional (k := k) (A := A)
  have := isSeparable (k := k) (A := A)
  IsIntegralClosure.isDedekindDomain k[X] (FractionRing k[X]) (FieldAtInf k A) _

theorem finite_ringInf : Module.Finite k[X] (RingInf k A) :=
  have := finiteDimensional (k := k) (A := A)
  have := isSeparable (k := k) (A := A)
  IsIntegralClosure.finite k[X] (FractionRing k[X]) (FieldAtInf k A) _

theorem isSeparable_ringInf :
    Algebra.IsSeparable (FractionRing k[X]) (FractionRing (RingInf k A)) := by
  have := isSeparable (k := k) (A := A)
  have := isFractionRing_ringInf (k := k) (A := A)
  let e := (FractionRing.algEquiv (RingInf k A) (FieldAtInf k A)).symm
  refine Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl _) e.toRingEquiv ?_
  refine IsLocalization.ringHom_ext (nonZeroDivisors k[X]) (RingHom.ext fun p ↦ ?_)
  simp only [RingHom.comp_apply, RingEquiv.refl_apply, AlgEquiv.toRingEquiv_toRingHom,
    RingHom.coe_coe]
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply k[X] (RingInf k A) (FieldAtInf k A),
    IsScalarTower.algebraMap_apply k[X] (RingInf k A) (FractionRing (RingInf k A)), e.commutes]

end FieldAtInf

end AtInf

section Tame

open scoped Pointwise

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k[X] A]
  [FaithfulSMul k[X] A] [Finite (A ≃ₐ[k[X]] A)]
  [hGal : IsGaloisGroup (A ≃ₐ[k[X]] A) (FractionRing k[X]) (FieldAtInf k A)]

namespace FieldAtInf

include hGal

/-- The trace of `k[T⁻¹] → B∞` is the sum of the conjugates. -/
theorem algebraMap_intTrace_ringInf [Fintype (A ≃ₐ[k[X]] A)] (x : RingInf k A) :
    haveI := isDedekindDomain_ringInf (k := k) (A := A)
    haveI := finite_ringInf (k := k) (A := A)
    algebraMap k[X] (RingInf k A) (Algebra.intTrace k[X] (RingInf k A) x) =
      ∑ g : A ≃ₐ[k[X]] A, g • x := by
  have := isDedekindDomain_ringInf (k := k) (A := A)
  have := finite_ringInf (k := k) (A := A)
  have := finiteDimensional (k := k) (A := A)
  apply Subtype.ext
  change algebraMap k[X] (FieldAtInf k A) _ = ((∑ g : A ≃ₐ[k[X]] A, g • x : RingInf k A) :
    FieldAtInf k A)
  rw [IsScalarTower.algebraMap_apply k[X] (FractionRing k[X]) (FieldAtInf k A),
    Algebra.algebraMap_intTrace (L := FieldAtInf k A),
    algebraMap_trace_eq_sum_smul (G := A ≃ₐ[k[X]] A)]
  push_cast
  rfl

/-- `B∞` is tamely ramified over `T⁻¹ = 0` when the order of the Galois group is prime to the
characteristic: if `x ≡ 1 mod P` and `x ∈ Q` (`T⁻¹ B∞ = Pⁿ Q`), then `Tr(x) ≡ |D_P| mod P`
by symmetrization, `D_P` the decomposition group. -/
theorem tame_ringInf (hp : (Nat.card (A ≃ₐ[k[X]] A) : k) ≠ 0) :
    haveI := isDedekindDomain_ringInf (k := k) (A := A)
    haveI := finite_ringInf (k := k) (A := A)
    ∀ P : Ideal (RingInf k A), P.IsMaximal → algebraMap k[X] (RingInf k A) X ∈ P →
      ∀ Q : Ideal (RingInf k A), P ⊔ Q = ⊤ → ∀ n : ℕ,
        (Ideal.span {X}).map (algebraMap k[X] (RingInf k A)) = P ^ n * Q →
          ∃ x ∈ Q, Algebra.intTrace k[X] (RingInf k A) x ∉ Ideal.span {(X : k[X])} := by
  classical
  have := isDedekindDomain_ringInf (k := k) (A := A)
  have := finite_ringInf (k := k) (A := A)
  have := Fintype.ofFinite (A ≃ₐ[k[X]] A)
  intro P hP hXP Q hPQ n hn
  have h1 : (1 : RingInf k A) ∈ P ⊔ Q := hPQ ▸ Submodule.mem_top
  obtain ⟨a, ha, q, hq, haq⟩ := Submodule.mem_sup.mp h1
  refine ⟨q, hq, fun htr ↦ ?_⟩
  have hx : q - 1 ∈ P := by
    rw [← haq, sub_add_cancel_right]
    exact P.neg_mem ha
  have hother : ∀ P' : Ideal (RingInf k A), P'.IsPrime →
      algebraMap k[X] (RingInf k A) X ∈ P' → P' ≠ P → q ∈ P' := by
    intro P' hP' hXP' hne
    have hle : P ^ n * Q ≤ P' := by
      rw [← hn, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff]
      exact hXP'
    rcases hP'.mul_le.mp hle with h | h
    · exact absurd (hP.eq_of_le hP'.ne_top (hP'.le_of_pow_le h)).symm hne
    · exact h hq
  have hsum := sum_smul_sub_card_stabilizer_mem (G := A ≃ₐ[k[X]] A) P X hXP q hx hother
  rw [← algebraMap_intTrace_ringInf] at hsum
  have htrP : algebraMap k[X] (RingInf k A) (Algebra.intTrace k[X] (RingInf k A) q) ∈ P := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp htr
    rw [← hc, map_mul]
    exact P.mul_mem_left _ hXP
  have hcard : ((Nat.card (MulAction.stabilizer (A ≃ₐ[k[X]] A) P) : ℕ) : RingInf k A) ∈ P := by
    have := P.sub_mem htrP hsum
    rwa [sub_sub_cancel] at this
  have hk : ((Nat.card (MulAction.stabilizer (A ≃ₐ[k[X]] A) P) : ℕ) : k) ≠ 0 := by
    obtain ⟨c, hc⟩ := Subgroup.card_subgroup_dvd_card (MulAction.stabilizer (A ≃ₐ[k[X]] A) P)
    intro h
    apply hp
    rw [hc, Nat.cast_mul, h, zero_mul]
  have hunit : IsUnit ((Nat.card (MulAction.stabilizer (A ≃ₐ[k[X]] A) P) : ℕ) :
      RingInf k A) := by
    rw [← map_natCast (algebraMap k[X] (RingInf k A)), ← map_natCast (Polynomial.C : k →+* k[X])]
    exact (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hk)).map _
  exact hP.ne_top (P.eq_top_of_isUnit_mem hcard hunit)

end FieldAtInf

end Tame

section Main

universe u

/-- XIII.2.12 for `g = 0`, `n = 1`, for Galois coverings: let `k` be algebraically closed and `A`
a finite étale `k[T]`-algebra which is a domain, with at least `[A : k[T]]` automorphisms (a
connected Galois covering of `𝔸¹_k`), of degree prime to the characteristic. Then `A = k[T]`.

The automorphisms form a Galois group of `Frac A / k(T)` (Artin), hence of `Frac A / k(T⁻¹)`
(`FieldAtInf.isGaloisGroup`); the integral closure `B∞` of `k[T⁻¹]` in `Frac A` is then tamely
ramified over `∞` (`FieldAtInf.tame_ringInf`), and `A` has a rational point over `0`
(`exists_ringHom_eval_zero`), so `finrank_eq_one_of_tame` applies. -/
theorem finrank_eq_one_of_le_card {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A]
    [IsDomain A] [Algebra k[X] A] [Algebra.Etale k[X] A] [Module.Finite k[X] A]
    [Finite (A ≃ₐ[k[X]] A)] (hG : finrank k[X] A ≤ Nat.card (A ≃ₐ[k[X]] A))
    (hp : (finrank k[X] A : k) ≠ 0) :
    finrank k[X] A = 1 := by
  have : IsIntegrallyClosed A := ExposeI.isIntegrallyClosed_of_etale (A := k[X])
  have hcard : Nat.card (A ≃ₐ[k[X]] A) = finrank k[X] A := by
    let := IsFractionRing.mulSemiringAction (A ≃ₐ[k[X]] A) A (FractionRing A)
    have := FieldAtInf.isGaloisGroup_fractionRing hG
    rw [IsGaloisGroup.card_eq_finrank (A ≃ₐ[k[X]] A) (FractionRing k[X]) (FractionRing A)]
    exact IsFractionRing.finrank_eq k[X] _ A _
  have := FieldAtInf.isGaloisGroup hG
  have := FieldAtInf.isDedekindDomain_ringInf (k := k) (A := A)
  have := FieldAtInf.finite_ringInf (k := k) (A := A)
  have := FieldAtInf.isSeparable_ringInf (k := k) (A := A)
  obtain ⟨χ, hχ⟩ := exists_ringHom_eval_zero (k := k) A
  exact finrank_eq_one_of_tame (B₁ := FieldAtInf.RingInf k A) (W := FieldAtInf.RingGm k A)
    FieldAtInf.algebraMap_A_ringGm FieldAtInf.algebraMap_ringInf_ringGm
    FieldAtInf.isLocalization_A_ringGm FieldAtInf.isLocalization_ringInf_ringGm
    (fun _ ↦ inferInstance) χ hχ (FieldAtInf.tame_ringInf (hcard ▸ hp))

end Main

end SGA.SGA1.ExposeXI
