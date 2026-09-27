/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Trace.Quotient
import SGA.SGA1.ExposeXI.LatticeIndex

/-!
# The discriminant of a tamely ramified extension (for XIII.2.12)

Let `B` be a Dedekind domain, finite and torsion free over a Dedekind domain `A`, with separable
fraction field extension, and `p = (π)` a nonzero principal prime of `A`. Suppose `B` is unramified
over `A` outside `p` and *tamely ramified* over `p`, in the form: for each prime `P` over `p`,
writing `πB = Pⁿ Q` with `P ∤ Q`, some `x ∈ Q` has trace `Tr_{B/A}(x) ∉ p` (for `B/Pⁿ` of
dimension prime to the characteristic, take `x ≡ 1 mod Pⁿ`). Then:

* the different ideal `𝔇` divides `πB` (`differentIdeal_dvd_of_tame`): `v_P(𝔇) ≤ n - 1` for
  each `P` over `p`, by mathlib's `not_dvd_differentIdeal_of_intTrace_not_mem`;
* hence `π B^∨ ⊆ B` (`exists_algebraMap_eq_mul_of_mem_dual`), `B^∨` the trace dual of `B`;
* the trace condition holds when `dim_{A/p} B/Pⁿ` is nonzero in `A/p`
  (`exists_mem_intTrace_notMem_of_finrank`), e.g. for `A/p = k` algebraically closed and `n`
  prime to the characteristic; and the discriminant of a basis lies in `𝔇`
  (`algebraMap_discr_mem_differentIdeal`), so a monomial discriminant forces unramifiedness
  outside `p`.

For `A = k[X]` and `π = X` this bounds the discriminant of a basis of `B`: its degree is less
than the rank of `B` (`natDegree_discr_lt_of_tame`), since the Gram matrix `(Tr(eᵢ eⱼ))` has
`X k[X]ⁿ ⊊ im ⊆ k[X]ⁿ`. This is the bound `δ ≤ d - 1` on the ramification at `∞` of a tamely
ramified covering of `ℙ¹` used in XIII.2.12 (the case `g = 0`, `n = 1`).
-/

open Module Polynomial

namespace SGA.SGA1.ExposeXI

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
  Ideal.Quotient.field

section Different

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- For a nonzero principal prime `p = (π)` of `A` such that `B/A` is unramified outside `p` and
tamely ramified over `p` (each prime `P` over `p` admits, writing `πB = Pⁿ Q` with `P ⊔ Q = ⊤`, an
element `x ∈ Q` with `Tr(x) ∉ p`), the different ideal of `B/A` divides `πB`. -/
theorem differentIdeal_dvd_of_tame (π : A) (hπ : π ≠ 0)
    (hunr : ∀ P : Ideal B, P.IsPrime → P ∣ differentIdeal A B → algebraMap A B π ∈ P)
    (htame : ∀ P : Ideal B, P.IsMaximal → algebraMap A B π ∈ P → ∀ Q : Ideal B, P ⊔ Q = ⊤ →
      ∀ n : ℕ, (Ideal.span {π}).map (algebraMap A B) = P ^ n * Q →
        ∃ x ∈ Q, Algebra.intTrace A B x ∉ Ideal.span {π}) :
    differentIdeal A B ∣ (Ideal.span {π}).map (algebraMap A B) := by
  classical
  have hD : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  have hI : (Ideal.span {π}).map (algebraMap A B) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, ne_eq, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr hπ
  rw [UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hD]
  intro P hP
  have hP0 : P ≠ ⊥ := hP.ne_zero
  have : P.IsPrime := Ideal.isPrime_of_prime hP
  have hPm : P.IsMaximal := this.isMaximal hP0
  by_cases hπP : algebraMap A B π ∈ P
  · obtain ⟨Q, hPQ, hIPQ⟩ := Ideal.eq_prime_pow_mul_coprime hI P
    set n := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors
      ((Ideal.span {π}).map (algebraMap A B)))
    obtain ⟨x, hxQ, hx⟩ := htame P hPm hπP Q hPQ n hIPQ
    have h1 : ¬ P ^ n ∣ differentIdeal A B :=
      not_dvd_differentIdeal_of_intTrace_not_mem A (P ^ n) Q hIPQ.symm x hxQ hx
    have h2 : emultiplicity P (differentIdeal A B) < n := by
      rw [← not_le, ← pow_dvd_iff_le_emultiplicity]
      exact h1
    have h3 : (n : ℕ∞) ≤ emultiplicity P ((Ideal.span {π}).map (algebraMap A B)) :=
      pow_dvd_iff_le_emultiplicity.mp ⟨Q, hIPQ⟩
    exact h2.le.trans h3
  · have : ¬ P ∣ differentIdeal A B := fun h ↦ hπP (hunr P ‹_› h)
    rw [emultiplicity_eq_zero.mpr this]
    exact zero_le

/-- The discriminant of a basis of `B` over `A` lies in the different ideal. -/
theorem algebraMap_discr_mem_differentIdeal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Basis ι A B) : algebraMap A B (Algebra.discr A e) ∈ differentIdeal A B := by
  let K := FractionRing A
  let L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization A K L B
  have : FiniteDimensional K L := .of_isLocalization A B (nonZeroDivisors A)
  let b : Basis ι K L := e.localizationLocalization K (nonZeroDivisors A) L
  have hb : ∀ i, IsIntegral A (b i) := fun i ↦ by
    rw [show b i = algebraMap B L (e i) from
      e.localizationLocalization_apply K (nonZeroDivisors A) L i]
    exact (Algebra.IsIntegral.isIntegral (e i)).map (IsScalarTower.toAlgHom A B L)
  have hdisc : Algebra.discr K b = algebraMap A K (Algebra.discr A e) :=
    Algebra.discr_localizationLocalization A (nonZeroDivisors A) L e
  have hD := coeIdeal_differentIdeal A K L B
  have hdual0 : FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L) ≠ 0 :=
    FractionalIdeal.dual_ne_zero A K one_ne_zero
  have hmem : algebraMap B L (algebraMap A B (Algebra.discr A e)) ∈
      (differentIdeal A B : FractionalIdeal (nonZeroDivisors B) L) := by
    rw [hD, FractionalIdeal.mem_inv_iff hdual0]
    intro y hy
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one] at hy
    have := isIntegral_discr_mul_of_mem_traceDual (A := A) (K := K) (L := L) (B := B) 1 hb
      (Submodule.mem_one.mpr ⟨1, map_one _⟩) hy
    rw [hdisc, smul_mul_assoc, one_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A B L] at this
    obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp this
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨z, hz⟩
  obtain ⟨z, hz, hz'⟩ := (FractionalIdeal.mem_coeIdeal _).mp hmem
  rwa [← (IsFractionRing.injective B L) hz']

omit [Algebra.IsSeparable (FractionRing A) (FractionRing B)] in
/-- Tame ramification in terms of dimensions: if `pB = P Q` with `P`, `Q` coprime and
`dim_{A/p} B/P` nonzero in `A/p`, then some `x ∈ Q` (namely `x ≡ 1 mod P`) has `Tr(x) ∉ p`. -/
theorem exists_mem_intTrace_notMem_of_finrank {p : Ideal A} [p.IsMaximal] (P Q : Ideal B)
    (hPQ : IsCoprime P Q) (hP : P * Q = p.map (algebraMap A B))
    (hdim : letI : Algebra (A ⧸ p) (B ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap (by
        rw [← Ideal.map_le_iff_le_comap, ← hP]
        exact Ideal.mul_le_left)
      ((finrank (A ⧸ p) (B ⧸ P) : ℕ) : A ⧸ p) ≠ 0) :
    ∃ x ∈ Q, Algebra.intTrace A B x ∉ p := by
  let : Algebra (A ⧸ p) (B ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_left)
  let : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_right)
  have : IsScalarTower A (A ⧸ p) (B ⧸ P) := .of_algebraMap_eq' rfl
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ P) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P)
  have : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  let e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hP.symm).trans (Ideal.quotientMulEquivQuotientProd P Q hPQ),
      commutes' := Quotient.ind fun _ ↦ rfl }
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e.symm (1, 0))
  refine ⟨y, ?_, ?_⟩
  · have := congr((e $hy).2)
    simp at this
    simpa [e, Ideal.Quotient.eq_zero_iff_mem] using this
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
      hy, Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply, map_zero, add_zero,
      ← map_one (algebraMap (A ⧸ p) (B ⧸ P)), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
    exact hdim

/-- If the different ideal divides `πB`, then `π B^∨ ⊆ B`, where `B^∨` is the trace dual of `B`
(the elements `y` of `L = Frac B` with `Tr(y B) ⊆ A`). -/
theorem exists_algebraMap_eq_mul_of_mem_dual (π : A)
    (hdvd : differentIdeal A B ∣ (Ideal.span {π}).map (algebraMap A B)) {y : FractionRing B}
    (hy : y ∈ FractionalIdeal.dual A (FractionRing A) (1 : FractionalIdeal (nonZeroDivisors B)
      (FractionRing B))) :
    ∃ b : B, algebraMap B (FractionRing B) b = algebraMap A (FractionRing B) π * y := by
  obtain ⟨C, hC⟩ := hdvd
  have hD := coeIdeal_differentIdeal A (FractionRing A) (FractionRing B) B
  have hD0 : (differentIdeal A B : FractionalIdeal (nonZeroDivisors B) (FractionRing B)) ≠ 0 := by
    rw [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have hdual : FractionalIdeal.dual A (FractionRing A) (1 : FractionalIdeal (nonZeroDivisors B)
      (FractionRing B)) = (differentIdeal A B : FractionalIdeal (nonZeroDivisors B)
        (FractionRing B))⁻¹ := by
    rw [hD, inv_inv]
  have hπI : algebraMap A (FractionRing B) π ∈
      (((Ideal.span {π}).map (algebraMap A B) : Ideal B) :
        FractionalIdeal (nonZeroDivisors B) (FractionRing B)) := by
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨algebraMap A B π, Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self π),
      (IsScalarTower.algebraMap_apply A B _ π).symm⟩
  have hmem := FractionalIdeal.mul_mem_mul hπI hy
  rw [hC, FractionalIdeal.coeIdeal_mul, hdual, mul_right_comm, mul_inv_cancel₀ hD0,
    one_mul] at hmem
  obtain ⟨b, -, hb⟩ := (FractionalIdeal.mem_coeIdeal _).mp hmem
  exact ⟨b, hb⟩

end Different

section Polynomial

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k[X] B] [IsDedekindDomain B]
  [Module.IsTorsionFree k[X] B] [Module.Finite k[X] B]
  [Algebra.IsSeparable (FractionRing k[X]) (FractionRing B)]

/-- The discriminant bound for a tamely ramified extension of `k[X]`: if `B` is unramified over
`k[X]` outside `(X)` and tamely ramified over `(X)` (in the sense of `differentIdeal_dvd_of_tame`),
then the discriminant of any basis of `B` has degree less than the rank of `B`. -/
theorem natDegree_discr_lt_of_tame {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι k[X] B)
    (hunr : ∀ P : Ideal B, P.IsPrime → P ∣ differentIdeal k[X] B → algebraMap k[X] B X ∈ P)
    (htame : ∀ P : Ideal B, P.IsMaximal → algebraMap k[X] B X ∈ P → ∀ Q : Ideal B, P ⊔ Q = ⊤ →
      ∀ n : ℕ, (Ideal.span {X}).map (algebraMap k[X] B) = P ^ n * Q →
        ∃ x ∈ Q, Algebra.intTrace k[X] B x ∉ Ideal.span {(X : k[X])}) :
    (Algebra.discr k[X] e).natDegree < Fintype.card ι := by
  classical
  let K := FractionRing k[X]
  let L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors k[X])) L :=
    IsIntegralClosure.isLocalization k[X] K L B
  have : FiniteDimensional K L := .of_isLocalization k[X] B (nonZeroDivisors k[X])
  have hdvd := differentIdeal_dvd_of_tame k[X] X X_ne_zero hunr htame
  have htr : Algebra.intTrace k[X] B = Algebra.trace k[X] B := Algebra.intTrace_eq_trace _ _
  let Tm := Algebra.traceMatrix k[X] e
  -- (a) `X k[X]ⁿ ⊆ Tm k[X]ⁿ`, from `X B^∨ ⊆ B`.
  have ha : ∀ c : ι → k[X], (X : k[X]) • c ∈ LinearMap.range Tm.mulVecLin := by
    intro c
    obtain ⟨b, hb⟩ : ∃ b : Basis ι K L, ∀ j, b j = algebraMap B L (e j) :=
      ⟨_, e.localizationLocalization_apply K (nonZeroDivisors k[X]) L⟩
    have hdb := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate K L) b
    obtain ⟨y, hy⟩ : ∃ y : L, ∀ j,
        Algebra.traceForm K L y (algebraMap B L (e j)) = algebraMap k[X] K (c j) := by
      refine ⟨∑ i, algebraMap k[X] K (c i) •
        (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b i, fun j ↦ ?_⟩
      rw [← hb j]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hdb,
        smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp
    have hydual : y ∈ FractionalIdeal.dual k[X] K (1 : FractionalIdeal (nonZeroDivisors B) L) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors B) L) ≠ 0)]
      intro a ha
      obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
      have : Algebra.traceForm K L y (algebraMap B L a') =
          algebraMap k[X] K (∑ j, e.repr a' j * c j) := by
        conv_lhs => rw [← e.sum_repr a']
        rw [map_sum, map_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply k[X] B L,
          IsScalarTower.algebraMap_apply k[X] K L, ← Algebra.smul_def, map_smul, hy, smul_eq_mul,
          map_mul]
      rw [this]
      exact ⟨_, rfl⟩
    obtain ⟨b₀, hb₀⟩ := exists_algebraMap_eq_mul_of_mem_dual k[X] X hdvd hydual
    refine ⟨e.equivFun b₀, ?_⟩
    change Tm.mulVec (e.equivFun b₀) = (X : k[X]) • c
    rw [Algebra.traceMatrix_of_basis_mulVec]
    funext i
    apply IsFractionRing.injective k[X] K
    rw [← htr, Algebra.algebraMap_intTrace (L := L), map_mul (algebraMap B L), hb₀,
      Pi.smul_apply, smul_eq_mul, map_mul (algebraMap k[X] K), ← hy i, Algebra.traceForm_apply,
      IsScalarTower.algebraMap_apply k[X] K L, mul_assoc, ← Algebra.smul_def, map_smul,
      smul_eq_mul]
  -- (b) some vector of `Tm k[X]ⁿ` is not divisible by `X`: a tame element has trace `∉ (X)`.
  have hXp : (Ideal.span {(X : k[X])}).IsPrime :=
    (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  obtain ⟨P, -, hP, hPX⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
    (Ideal.span {(X : k[X])}) ⊥ (by
      rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective k[X] B)]
      exact bot_le)
  have hXP : algebraMap k[X] B X ∈ P := by
    rw [← Ideal.mem_comap, hPX]
    exact Ideal.mem_span_singleton_self _
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective k[X] B)] at hXP
    exact X_ne_zero hXP
  have hPm : P.IsMaximal := hP.isMaximal hP0
  have hI : (Ideal.span {(X : k[X])}).map (algebraMap k[X] B) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, ne_eq, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective k[X] B)).mpr X_ne_zero
  obtain ⟨Q, hPQ, hIPQ⟩ := Ideal.eq_prime_pow_mul_coprime hI P
  obtain ⟨x, -, hx⟩ := htame P hPm hXP Q hPQ _ hIPQ
  have hb : ∃ i, ¬ (X : k[X]) ∣ Algebra.trace k[X] B (x * e i) := by
    by_contra! h
    apply hx
    rw [Ideal.mem_span_singleton, htr, ← mul_one x, ← e.sum_repr 1, Finset.mul_sum, map_sum]
    refine Finset.dvd_sum fun i _ ↦ ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul]
    exact Dvd.dvd.mul_left (h i) _
  -- The dimension count.
  let R₁ := LinearMap.range ((X : k[X]) • (1 : Matrix ι ι k[X])).mulVecLin
  let R₂ := LinearMap.range Tm.mulVecLin
  have hR : R₁ ≤ R₂ := by
    rintro _ ⟨c, rfl⟩
    have : ((X : k[X]) • (1 : Matrix ι ι k[X])).mulVecLin c = (X : k[X]) • c := by
      simp
    rw [this]
    exact ha c
  obtain ⟨i₀, hi₀⟩ := hb
  let v : ι → k[X] := Tm.mulVec (e.equivFun x)
  have hv₂ : v ∈ R₂ := ⟨e.equivFun x, rfl⟩
  have hv₁ : v ∉ R₁ := by
    rintro ⟨c, hc⟩
    apply hi₀
    have := congrFun hc i₀
    simp only [Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
      smul_eq_mul] at this
    rw [show Algebra.trace k[X] B (x * e i₀) = v i₀ by
      change _ = Tm.mulVec (e.equivFun x) i₀
      rw [Algebra.traceMatrix_of_basis_mulVec], ← this]
    exact dvd_mul_right _ _
  have hdet₁ : ((X : k[X]) • (1 : Matrix ι ι k[X])).det = X ^ Fintype.card ι := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
  have hdet₂ : Tm.det ≠ 0 := by
    rw [← Algebra.discr_def]
    intro h0
    have := Algebra.discr_localizationLocalization k[X] (nonZeroDivisors k[X]) L e (Rₘ := K)
    rw [h0, map_zero] at this
    exact Algebra.discr_not_zero_of_basis K _ this
  obtain ⟨hfin₁, hdim₁⟩ := finrank_quotient_range_eq_natDegree_det _
    (hdet₁ ▸ pow_ne_zero _ X_ne_zero)
  obtain ⟨-, hdim₂⟩ := finrank_quotient_range_eq_natDegree_det Tm hdet₂
  rw [hdet₁, natDegree_X_pow] at hdim₁
  let f := (R₁.mapQ R₂ LinearMap.id hR).restrictScalars k
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective R₂ z
    exact ⟨Submodule.Quotient.mk w, rfl⟩
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro h
    have hz : f (Submodule.Quotient.mk v) = 0 :=
      (Submodule.Quotient.mk_eq_zero R₂).mpr hv₂
    rw [← LinearMap.mem_ker, h, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hz
    exact hv₁ hz
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, hdim₂, hdim₁] at hrn
  have hpos : 0 < Module.finrank k (LinearMap.ker f) := by
    rw [Nat.pos_iff_ne_zero, ne_eq, Submodule.finrank_eq_zero]
    exact hker
  rw [Algebra.discr_def]
  change Tm.det.natDegree < _
  omega

end Polynomial

end SGA.SGA1.ExposeXI
