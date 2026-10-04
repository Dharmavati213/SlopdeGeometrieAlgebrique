/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import SGA.SGA1.ExposeII.Generalities

/-!
# Valuation subrings of a rational function field (XI.1.4, step 1)

Let `A = k[x_i : i ∈ σ]` and `F = Frac A`. For Serre's vanishing of regular forms on unirational
varieties we use two families of valuation subrings of `F`:

* `RegularForms.primeValuationSubring π = A_(π)` for a prime element `π` of `A`;
* `RegularForms.infinityValuationSubring`, the elements `a / b` with `deg a ≤ deg b` (the valuation
  ring of the hyperplane at infinity of `ℙ^σ`), and the elements of positive valuation there,
  `RegularForms.IsSmallAtInfinity j x :⇔ x · x_j ∈ infinityValuationSubring`.

Main facts: an element of `F` in every `A_(π)` lies in `A`
(`RegularForms.mem_range_of_forall_mem_primeValuationSubring`), and an element of `A` of positive
valuation at infinity is `0` (`RegularForms.eq_zero_of_isSmallAtInfinity`).
-/

universe u

open MvPolynomial

namespace SGA.SGA1.ExposeXI.RegularForms

variable {k : Type u} [Field k] {σ : Type u}

section Degree

/-- `deg (x_j · ∂a/∂x_i) ≤ deg a`. -/
theorem totalDegree_X_mul_pderiv_le (i j : σ) (a : MvPolynomial σ k) :
    (X j * pderiv i a).totalDegree ≤ a.totalDegree := by
  classical
  conv_lhs => rw [a.as_sum, map_sum, Finset.mul_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs ↦ ?_)
  rw [pderiv_monomial, X, monomial_mul_monomial, one_mul]
  by_cases hsi : s i = 0
  · simp [hsi]
  refine (totalDegree_monomial_le _ _).trans ?_
  have hle : Finsupp.single i 1 ≤ s := by
    rw [Finsupp.single_le_iff]
    omega
  have hs' : s = (s - Finsupp.single i 1) + Finsupp.single i 1 := (tsub_add_cancel_of_le hle).symm
  have h1 := le_totalDegree hs
  rw [hs', Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
    Finsupp.sum_single_index rfl] at h1
  rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl), Finsupp.sum_single_index rfl]
  simp only [Function.id_def] at h1 ⊢
  omega

end Degree

local notation "Pol" => MvPolynomial σ k
local notation "Fr" => FractionRing (MvPolynomial σ k)

section Infinity

/-- The valuation subring at infinity of `F = k(x_i : i ∈ σ)`: the fractions `a / b` with
`deg a ≤ deg b`. -/
noncomputable def infinityValuationSubring : ValuationSubring Fr where
  carrier := {x | ∃ a b : Pol, b ≠ 0 ∧ x * algebraMap Pol Fr b = algebraMap Pol Fr a ∧
    a.totalDegree ≤ b.totalDegree}
  mul_mem' := by
    rintro x y ⟨a, b, hb, hx, hab⟩ ⟨c, d, hd, hy, hcd⟩
    refine ⟨a * c, b * d, mul_ne_zero hb hd, ?_, ?_⟩
    · rw [map_mul, map_mul, ← hx, ← hy]
      ring
    · rw [totalDegree_mul_of_isDomain hb hd]
      exact (totalDegree_mul a c).trans (add_le_add hab hcd)
  one_mem' := ⟨1, 1, one_ne_zero, by simp, le_rfl⟩
  add_mem' := by
    rintro x y ⟨a, b, hb, hx, hab⟩ ⟨c, d, hd, hy, hcd⟩
    refine ⟨a * d + c * b, b * d, mul_ne_zero hb hd, ?_, ?_⟩
    · rw [map_add, map_mul, map_mul, map_mul, ← hx, ← hy]
      ring
    · rw [totalDegree_mul_of_isDomain hb hd]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · exact (totalDegree_mul a d).trans (by omega)
      · exact (totalDegree_mul c b).trans (by omega)
  zero_mem' := ⟨0, 1, one_ne_zero, by simp, by simp⟩
  neg_mem' := by
    rintro x ⟨a, b, hb, hx, hab⟩
    exact ⟨-a, b, hb, by rw [map_neg, ← hx, neg_mul], by rwa [totalDegree_neg]⟩
  mem_or_inv_mem' := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ k) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb' : algebraMap Pol Fr b ≠ 0 :=
      (IsFractionRing.injective Pol Fr).ne_iff' (map_zero _) |>.mpr hb0
    rcases le_or_gt a.totalDegree b.totalDegree with h | h
    · exact Or.inl ⟨a, b, hb0, by rw [div_mul_cancel₀ _ hb'], h⟩
    · have ha0 : a ≠ 0 := by
        rintro rfl
        simp at h
      have ha' : algebraMap Pol Fr a ≠ 0 :=
        (IsFractionRing.injective Pol Fr).ne_iff' (map_zero _) |>.mpr ha0
      exact Or.inr ⟨b, a, ha0, by rw [inv_div, div_mul_cancel₀ _ ha'], h.le⟩

/-- `x ∈ F` has positive valuation at infinity: `x · x_j` lies in the valuation subring at
infinity (as `v_∞(x_j) = -1`). -/
def IsSmallAtInfinity (j : σ) (x : Fr) : Prop :=
  x * algebraMap Pol Fr (X j) ∈ infinityValuationSubring (k := k)

lemma mem_infinityValuationSubring_of_isSmallAtInfinity {j : σ} {x : Fr}
    (h : IsSmallAtInfinity j x) : x ∈ infinityValuationSubring (k := k) := by
  have hX : (algebraMap Pol Fr (X j))⁻¹ ∈ infinityValuationSubring (k := k) := by
    have hX0 : algebraMap Pol Fr (X j) ≠ 0 :=
      (IsFractionRing.injective Pol Fr).ne_iff' (map_zero _) |>.mpr (X_ne_zero j)
    exact ⟨1, X j, X_ne_zero j, by rw [inv_mul_cancel₀ hX0, map_one], by simp⟩
  have hX0 : algebraMap Pol Fr (X j) ≠ 0 :=
    (IsFractionRing.injective Pol Fr).ne_iff' (map_zero _) |>.mpr (X_ne_zero j)
  have := mul_mem h hX
  rwa [mul_assoc, mul_inv_cancel₀ hX0, mul_one] at this

lemma IsSmallAtInfinity.mul {j : σ} {x y : Fr} (hx : x ∈ infinityValuationSubring (k := k))
    (hy : IsSmallAtInfinity j y) : IsSmallAtInfinity j (x * y) := by
  unfold IsSmallAtInfinity at hy ⊢
  rw [mul_assoc]
  exact mul_mem hx hy

lemma IsSmallAtInfinity.add {j : σ} {x y : Fr} (hx : IsSmallAtInfinity (k := k) j x)
    (hy : IsSmallAtInfinity (k := k) j y) : IsSmallAtInfinity j (x + y) := by
  unfold IsSmallAtInfinity at hx hy ⊢
  rw [add_mul]
  exact add_mem hx hy

lemma IsSmallAtInfinity.neg {j : σ} {x : Fr} (hx : IsSmallAtInfinity (k := k) j x) :
    IsSmallAtInfinity j (-x) := by
  unfold IsSmallAtInfinity at hx ⊢
  rw [neg_mul]
  exact neg_mem hx

lemma isSmallAtInfinity_zero (j : σ) : IsSmallAtInfinity (k := k) j 0 := by
  unfold IsSmallAtInfinity
  rw [zero_mul]
  exact zero_mem _

/-- A polynomial of positive valuation at infinity is `0`. -/
lemma eq_zero_of_isSmallAtInfinity {j : σ} (q : Pol)
    (h : IsSmallAtInfinity j (algebraMap Pol Fr q)) : q = 0 := by
  obtain ⟨a, b, hb, he, hab⟩ := h
  rw [← map_mul, ← map_mul] at he
  have he' := IsFractionRing.injective Pol Fr he
  by_contra hq
  have h1 : (q * X j * b).totalDegree = q.totalDegree + 1 + b.totalDegree := by
    rw [totalDegree_mul_of_isDomain (mul_ne_zero hq (X_ne_zero j)) hb,
      totalDegree_mul_of_isDomain hq (X_ne_zero j), totalDegree_X]
  rw [he'] at h1
  omega

end Infinity

section Prime

/-- The valuation subring `A_(π)` of `F` for a prime element `π` of `A = k[x_i : i ∈ σ]`: the
fractions `a / b` with `π ∤ b`. -/
noncomputable def primeValuationSubring (π : Pol) (hπ : Prime π) : ValuationSubring Fr where
  carrier := {x | ∃ a b : Pol, ¬ π ∣ b ∧ x * algebraMap Pol Fr b = algebraMap Pol Fr a}
  mul_mem' := by
    rintro x y ⟨a, b, hb, hx⟩ ⟨c, d, hd, hy⟩
    refine ⟨a * c, b * d, fun h ↦ (hπ.dvd_or_dvd h).elim hb hd, ?_⟩
    rw [map_mul, map_mul, ← hx, ← hy]
    ring
  one_mem' := ⟨1, 1, hπ.not_dvd_one, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, hb, hx⟩ ⟨c, d, hd, hy⟩
    refine ⟨a * d + c * b, b * d, fun h ↦ (hπ.dvd_or_dvd h).elim hb hd, ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, ← hx, ← hy]
    ring
  zero_mem' := ⟨0, 1, hπ.not_dvd_one, by simp⟩
  neg_mem' := by
    rintro x ⟨a, b, hb, hx⟩
    exact ⟨-a, b, hb, by rw [map_neg, ← hx, neg_mul]⟩
  mem_or_inv_mem' := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ k) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hinj := IsFractionRing.injective Pol Fr
    by_cases ha0 : a = 0
    · left
      exact ⟨0, 1, hπ.not_dvd_one, by simp [ha0]⟩
    obtain ⟨m, a', ha', rfl⟩ := WfDvdMonoid.max_power_factor ha0 hπ.irreducible
    obtain ⟨n, b', hb', rfl⟩ := WfDvdMonoid.max_power_factor hb0 hπ.irreducible
    have hπ0 : algebraMap Pol Fr π ≠ 0 := hinj.ne_iff' (map_zero _) |>.mpr hπ.ne_zero
    have hb'0 : algebraMap Pol Fr b' ≠ 0 := hinj.ne_iff' (map_zero _) |>.mpr (by
      rintro rfl; exact hb' (dvd_zero π))
    have ha'0 : algebraMap Pol Fr a' ≠ 0 := hinj.ne_iff' (map_zero _) |>.mpr (by
      rintro rfl; exact ha' (dvd_zero π))
    rcases le_total n m with h | h
    · left
      refine ⟨π ^ (m - n) * a', b', hb', ?_⟩
      simp only [map_mul, map_pow]
      rw [← Nat.sub_add_cancel h, pow_add]
      field_simp
      simp
    · right
      refine ⟨π ^ (n - m) * b', a', ha', ?_⟩
      simp only [map_mul, map_pow]
      rw [← Nat.sub_add_cancel h, pow_add]
      field_simp
      simp

/-- An element of `F = Frac A` which lies in `A_(π)` for every prime element `π` of the factorial
ring `A` lies in `A`. -/
theorem mem_range_of_forall_mem_primeValuationSubring (c : Fr)
    (h : ∀ (π : Pol) (hπ : Prime π), c ∈ primeValuationSubring π hπ) :
    c ∈ (algebraMap Pol Fr).range := by
  have hinj := IsFractionRing.injective Pol Fr
  obtain ⟨a, b, hb, he⟩ : ∃ a b : Pol, b ≠ 0 ∧ c * algebraMap Pol Fr b = algebraMap Pol Fr a := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ k) c
    have hb' : algebraMap Pol Fr b ≠ 0 :=
      hinj.ne_iff' (map_zero _) |>.mpr (nonZeroDivisors.ne_zero hb)
    exact ⟨a, b, nonZeroDivisors.ne_zero hb, by rw [div_mul_cancel₀ _ hb']⟩
  induction b using WfDvdMonoid.induction_on_irreducible generalizing a with
  | zero => exact absurd rfl hb
  | unit u hu =>
    refine ⟨a * ↑hu.unit⁻¹, ?_⟩
    rw [map_mul, ← he, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
  | mul b π hb0 hirr ih =>
    have hπ : Prime π := hirr.prime
    obtain ⟨e, d, hd, hc⟩ := h π hπ
    -- `π ∣ a`: `a d = c π b d = e π b`
    have hcross : a * d = e * (π * b) := by
      apply hinj
      rw [map_mul, map_mul, ← he, ← hc]
      ring
    have hπa : π ∣ a := by
      have : π ∣ a * d := ⟨e * b, by rw [hcross]; ring⟩
      exact (hπ.dvd_or_dvd this).resolve_right hd
    obtain ⟨a₁, rfl⟩ := hπa
    refine ih a₁ hb0 ?_
    have hπ0 : algebraMap Pol Fr π ≠ 0 := hinj.ne_iff' (map_zero _) |>.mpr hπ.ne_zero
    apply mul_left_cancel₀ hπ0
    rw [← map_mul, ← he, map_mul]
    ring

end Prime

section Derivations

open KaehlerDifferential

variable (k σ)

/-- The basis `(dx_i)` of `Ω_{F/k}`, `F = k(x_i : i ∈ σ)`: II.1.5 (affine version,
`ExposeII.basisKaehlerOfFormallyEtale`), `F` being a localization of `k[x]`, hence formally étale
over it. -/
noncomputable abbrev kaehlerBasis : Module.Basis σ Fr Ω[Fr⁄k] :=
  ExposeII.basisKaehlerOfFormallyEtale σ

/-- `kaehlerBasis` is the base change of the basis `(dx_i)` of `Ω_{k[x]/k}`. -/
lemma kaehlerBasis_eq_isBaseChange_basis :
    kaehlerBasis k σ =
      IsBaseChange.basis (mvPolynomialBasis k σ) (isBaseChange_of_formallyEtale k Pol Fr) :=
  Module.Basis.eq_of_apply_eq fun i ↦ by
    rw [ExposeII.basisKaehlerOfFormallyEtale_apply, IsBaseChange.basis_apply,
      mvPolynomialBasis_apply]
    exact (map_D k k Pol Fr (X i)).symm

/-- The partial derivative `∂/∂x_t` on `F = k(x_i : i ∈ σ)`. -/
noncomputable def pderivF (t : σ) : Derivation k Fr Fr :=
  ((kaehlerBasis k σ).coord t).compDer (D k Fr)

variable {k σ}

lemma pderivF_apply (t : σ) (x : Fr) : pderivF k σ t x = (kaehlerBasis k σ).repr (D k Fr x) t :=
  rfl

lemma pderivF_algebraMap (t : σ) (a : Pol) :
    pderivF k σ t (algebraMap Pol Fr a) = algebraMap Pol Fr (pderiv t a) := by
  rw [pderivF_apply, ← map_D k k Pol Fr, kaehlerBasis_eq_isBaseChange_basis,
    IsBaseChange.basis_repr_comp_apply, mvPolynomialBasis_repr_apply]

/-- The quotient rule: if `x b = a` then `∂x · b² = b ∂a - a ∂b`. -/
lemma pderivF_mul_sq (t : σ) {x : Fr} {a b : Pol}
    (h : x * algebraMap Pol Fr b = algebraMap Pol Fr a) :
    pderivF k σ t x * algebraMap Pol Fr (b * b) =
      algebraMap Pol Fr (b * pderiv t a - a * pderiv t b) := by
  have h1 := congrArg (pderivF k σ t) h
  rw [Derivation.leibniz, pderivF_algebraMap, pderivF_algebraMap, smul_eq_mul, smul_eq_mul] at h1
  simp only [map_sub, map_mul]
  linear_combination (algebraMap Pol Fr b) * h1 - (algebraMap Pol Fr (pderiv t b)) * h

lemma pderivF_mem_primeValuationSubring (t : σ) (π : Pol) (hπ : Prime π) {x : Fr}
    (hx : x ∈ primeValuationSubring π hπ) : pderivF k σ t x ∈ primeValuationSubring π hπ := by
  obtain ⟨a, b, hb, hx⟩ := hx
  exact ⟨_, b * b, fun h ↦ (hπ.dvd_or_dvd h).elim hb hb, pderivF_mul_sq t hx⟩

lemma isSmallAtInfinity_pderivF (t j : σ) {x : Fr} (hx : x ∈ infinityValuationSubring (k := k)) :
    IsSmallAtInfinity j (pderivF k σ t x) := by
  obtain ⟨a, b, hb, hx, hab⟩ := hx
  refine ⟨(b * pderiv t a - a * pderiv t b) * X j, b * b, mul_ne_zero hb hb, ?_, ?_⟩
  · have e := pderivF_mul_sq t hx
    simp only [map_mul] at e ⊢
    rw [← e]
    ring
  · rw [totalDegree_mul_of_isDomain hb hb, sub_mul, mul_assoc, mul_assoc]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · rw [← mul_comm (X j)]
      exact (totalDegree_mul _ _).trans (by have := totalDegree_X_mul_pderiv_le t j a; omega)
    · rw [← mul_comm (X j)]
      exact (totalDegree_mul _ _).trans (by have := totalDegree_X_mul_pderiv_le t j b; omega)

end Derivations

section Coefficients

open KaehlerDifferential exteriorPower Set.powersetCard

variable {K : Type u} [Field K] [Algebra k K] [Algebra K (FractionRing (MvPolynomial σ k))]
  [IsScalarTower k K (FractionRing (MvPolynomial σ k))] [Finite σ]

/-- The map `Ω_{K/k} → F^σ`, `da ↦ (∂a/∂x_t)_t`, for a field `K ⊆ F = k(x_i : i ∈ σ)`. -/
noncomputable def jacobian : Ω[K⁄k] →ₗ[K] (σ → Fr) :=
  ((kaehlerBasis k σ).equivFun.toLinearMap.restrictScalars K) ∘ₗ map k k K Fr

lemma jacobian_D (a : K) (t : σ) :
    jacobian (σ := σ) (D k K a) t = pderivF k σ t (algebraMap K Fr a) := by
  simp [jacobian, pderivF_apply]

variable [LinearOrder σ] (p : ℕ)

/-- The coefficient of `dx_I` (`I` a `p`-subset of `σ`) of the image of a `p`-form of `K` in
`Ω^p_{F/k}`, as a `K`-linear form: on `a₀ da₁ ∧ ⋯ ∧ daₚ` it is `a₀ det (∂aᵢ/∂x_{I_j})`. -/
noncomputable def coeff (I : Set.powersetCard σ p) : ⋀[K]^p Ω[K⁄k] →ₗ[K] Fr :=
  alternatingMapLinearEquiv
    { (((ιMultiDual Fr p (Pi.basisFun Fr σ) I).compAlternatingMap
        (ιMulti Fr p)).toMultilinearMap.restrictScalars K).compLinearMap
          (fun _ ↦ jacobian (k := k) (σ := σ) (K := K)) with
      map_eq_zero_of_eq' := fun v i j h hij ↦
        ((ιMultiDual Fr p (Pi.basisFun Fr σ) I).compAlternatingMap (ιMulti Fr p)).map_eq_zero_of_eq
          _ (by simp [h]) hij }

lemma coeff_ιMulti (I : Set.powersetCard σ p) (v : Fin p → Ω[K⁄k]) :
    coeff (k := k) p I (ιMulti K p v) =
      ιMultiDual Fr p (Pi.basisFun Fr σ) I (ιMulti Fr p (jacobian ∘ v)) := by
  rw [coeff, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

lemma coeff_ιMulti_D (I : Set.powersetCard σ p) (a : Fin p → K) :
    coeff (k := k) p I (ιMulti K p (fun i ↦ D k K (a i))) =
      (Matrix.of fun i j ↦ pderivF k σ (ofFinEmbEquiv.symm I j) (algebraMap K Fr (a i))).det := by
  rw [coeff_ιMulti, ιMultiDual_apply_ιMulti]
  congr 1
  ext i j
  simp [jacobian_D]

lemma coeff_smul_ιMulti_D (I : Set.powersetCard σ p) (a : Fin (p + 1) → K) :
    coeff (k := k) p I (a 0 • ιMulti K p (fun i ↦ D k K (a i.succ))) =
      algebraMap K Fr (a 0) * (Matrix.of fun i j ↦
        pderivF k σ (ofFinEmbEquiv.symm I j) (algebraMap K Fr (a i.succ))).det := by
  rw [map_smul, coeff_ιMulti_D, Algebra.smul_def]

lemma coeff_smul_field (I : Set.powersetCard σ p) (c : k) (ω : ⋀[K]^p Ω[K⁄k]) :
    coeff (k := k) p I (c • ω) = algebraMap k Fr c * coeff p I ω := by
  rw [← algebraMap_smul K c ω, map_smul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]

/-- **Injectivity**: for `F` finite over `K` in characteristic `0`, a `p`-form of `K` all of whose
coefficients in `Ω^p_{F/k}` vanish is `0`: `F/K` is separable, so `Ω_{F/k} = F ⊗_K Ω_{K/k}`
(`KaehlerDifferential.isBaseChange_of_formallyEtale`), and `⋀^p` of an injective map of vector
spaces is injective. -/
theorem eq_zero_of_forall_coeff_eq_zero [CharZero k] [FiniteDimensional K Fr]
    (ω : ⋀[K]^p Ω[K⁄k]) (h : ∀ I, coeff (k := k) (σ := σ) p I ω = 0) : ω = 0 := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have : Algebra.FormallyEtale K Fr := Algebra.FormallyEtale.of_isSeparable K Fr
  have hbc := isBaseChange_of_formallyEtale k K Fr
  let b := Module.Basis.ofVectorSpace K Ω[K⁄k]
  let ι := Module.Basis.ofVectorSpaceIndex K Ω[K⁄k]
  let _ : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  -- `jacobian ∘ b` is linearly independent over `F`.
  have hu : LinearIndependent Fr (jacobian (k := k) (σ := σ) (K := K) ∘ b) := by
    have h1 : jacobian (k := k) (σ := σ) (K := K) ∘ b =
        (kaehlerBasis k σ).equivFun ∘ (IsBaseChange.basis b hbc) := by
      ext i t
      simp [jacobian, IsBaseChange.basis_apply]
    rw [h1]
    exact (IsBaseChange.basis b hbc).linearIndependent.map' _
      (kaehlerBasis k σ).equivFun.ker
  let BF := (Pi.basisFun Fr σ).exteriorPower p
  -- The coefficient map sends the basis of `⋀^p Ω_K` to a linearly independent family.
  let Γ : ⋀[K]^p Ω[K⁄k] →ₗ[K] (Set.powersetCard σ p → Fr) :=
    LinearMap.pi fun I ↦ coeff (k := k) p I
  have hΓ : Γ ∘ (b.exteriorPower p) =
      BF.equivFun ∘ ιMulti_family Fr p (jacobian (k := k) (σ := σ) (K := K) ∘ b) := by
    ext J I
    simp only [Function.comp_apply, Γ, LinearMap.pi_apply, Module.Basis.equivFun_apply, BF,
      basis_repr_apply, basis_apply, ιMulti_family, coeff_ιMulti]
    rfl
  have hli : LinearIndependent K (Γ ∘ (b.exteriorPower p)) := by
    rw [hΓ]
    exact ((ιMulti_family_linearIndependent_field p hu).map' _ BF.equivFun.ker).restrict_scalars'
      K
  have hΓω : Γ ω = 0 := funext h
  rw [← (b.exteriorPower p).linearCombination_repr ω, Finsupp.apply_linearCombination] at hΓω
  have := linearIndependent_iff.mp hli _ hΓω
  rw [← (b.exteriorPower p).linearCombination_repr ω, this, map_zero]

omit [Finite σ] [LinearOrder σ] in
/-- A valuation subring contains the determinant of a matrix with entries in it. -/
lemma det_mem_valuationSubring {V : ValuationSubring Fr} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) Fr) (hM : ∀ i j, M i j ∈ V) : M.det ∈ V := by
  have e := RingHom.map_det V.subtype (Matrix.of fun i j ↦ (⟨M i j, hM i j⟩ : V))
  have hM' : V.subtype.mapMatrix (Matrix.of fun i j ↦ (⟨M i j, hM i j⟩ : V)) = M := by
    ext i j
    rfl
  rw [hM'] at e
  rw [← e]
  exact Subtype.property _

omit [Finite σ] [LinearOrder σ] in
lemma isSmallAtInfinity_det {j : σ} {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Fr)
    (hM : ∀ i i', IsSmallAtInfinity j (M i i')) : IsSmallAtInfinity j M.det := by
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_induction _ (IsSmallAtInfinity (k := k) j) (fun x y hx hy ↦ hx.add hy)
    (isSmallAtInfinity_zero j) fun i' _ ↦ ?_
  have hsub : (M.submatrix Fin.succ i'.succAbove).det ∈ infinityValuationSubring (k := k) :=
    det_mem_valuationSubring _ fun _ _ ↦ mem_infinityValuationSubring_of_isSmallAtInfinity (hM _ _)
  have hsign : ((-1 : Fr) ^ (i' : ℕ)) ∈ infinityValuationSubring (k := k) :=
    pow_mem (neg_mem (one_mem _)) _
  rw [show (-1 : Fr) ^ (i' : ℕ) * M 0 i' * (M.submatrix Fin.succ i'.succAbove).det =
    ((-1) ^ (i' : ℕ) * (M.submatrix Fin.succ i'.succAbove).det) * M 0 i' by ring]
  exact IsSmallAtInfinity.mul (mul_mem hsign hsub) (hM 0 i')

/-- The `k`-span of the forms `a₀ da₁ ∧ ⋯ ∧ daₚ` with all `aᵢ` in `V` (through `K → F`). -/
noncomputable def spanOver (V : ValuationSubring Fr) : Submodule k (⋀[K]^p Ω[K⁄k]) :=
  Submodule.span k {ω | ∃ a : Fin (p + 1) → K, (∀ i, algebraMap K Fr (a i) ∈ V) ∧
    ω = a 0 • ιMulti K p (fun i ↦ D k K (a i.succ))}

lemma coeff_mem_of_mem_spanOver (I : Set.powersetCard σ p) (V : ValuationSubring Fr)
    (P : Fr → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : k) x, P x → P (algebraMap k Fr c * x))
    (hgen : ∀ a : Fin (p + 1) → K, (∀ i, algebraMap K Fr (a i) ∈ V) →
      P (coeff (k := k) p I (a 0 • ιMulti K p (fun i ↦ D k K (a i.succ)))))
    {ω : ⋀[K]^p Ω[K⁄k]} (hω : ω ∈ spanOver (σ := σ) p V) : P (coeff (k := k) p I ω) := by
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact hgen a ha
  | zero => rw [map_zero]; exact h0
  | add x y _ _ hx hy => rw [map_add]; exact hadd _ _ hx hy
  | smul c x _ hx => rw [coeff_smul_field]; exact hsmul c _ hx

/-- **Regular forms on a unirational field vanish**, algebraic form (XI.1.4, step 1): let `K` be a
field over `k` (characteristic `0`) with `F = k(x_i : i ∈ σ)` finite over `K`, and `ω` a `p`-form
of `K`, `p > 0`, which for every valuation subring `V ⊇ k` of `F` is a `k`-linear combination of
forms `a₀ da₁ ∧ ⋯ ∧ daₚ` with all `aᵢ ∈ V`. Then `ω = 0`. The coefficients of `ω` in `Ω^p_{F/k}`
lie in every `k[x]_(π)` (`π` prime), hence in `k[x]`, and have positive valuation at infinity, so
they vanish. -/
theorem eq_zero_of_forall_mem_spanOver [CharZero k] [FiniteDimensional K Fr] (hp : 0 < p)
    (ω : ⋀[K]^p Ω[K⁄k])
    (h : ∀ V : ValuationSubring Fr, (∀ c : k, algebraMap k Fr c ∈ V) → ω ∈ spanOver (σ := σ) p V) :
    ω = 0 := by
  refine eq_zero_of_forall_coeff_eq_zero (σ := σ) p ω fun I ↦ ?_
  have hC : ∀ c : k, algebraMap k Fr c = algebraMap Pol Fr (C c) := fun c ↦
    (IsScalarTower.algebraMap_apply k Pol Fr c)
  -- The coefficient lies in every `A_(π)`, hence in `A`.
  have hprime : ∀ (π : Pol) (hπ : Prime π), coeff (k := k) p I ω ∈ primeValuationSubring π hπ := by
    intro π hπ
    have hk : ∀ c : k, algebraMap k Fr c ∈ primeValuationSubring π hπ := fun c ↦
      ⟨C c, 1, hπ.not_dvd_one, by rw [hC, map_one, mul_one]⟩
    refine coeff_mem_of_mem_spanOver p I _ (· ∈ primeValuationSubring π hπ) (zero_mem _)
      (fun _ _ ↦ add_mem) (fun c _ hx ↦ mul_mem (hk c) hx) (fun a ha ↦ ?_) (h _ hk)
    rw [coeff_smul_ιMulti_D]
    exact mul_mem (ha 0) (det_mem_valuationSubring _ fun i j ↦
      pderivF_mem_primeValuationSubring _ π hπ (ha i.succ))
  obtain ⟨q, hq⟩ := mem_range_of_forall_mem_primeValuationSubring _ hprime
  -- The coefficient has positive valuation at infinity.
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  let j := ofFinEmbEquiv.symm I 0
  have hk : ∀ c : k, algebraMap k Fr c ∈ infinityValuationSubring (k := k) := fun c ↦
    ⟨C c, 1, one_ne_zero, by rw [hC, map_one, mul_one], by simp⟩
  have hsmall : IsSmallAtInfinity j (coeff (k := k) (n + 1) I ω) := by
    refine coeff_mem_of_mem_spanOver (n + 1) I _ (IsSmallAtInfinity j) (isSmallAtInfinity_zero j)
      (fun _ _ hx hy ↦ hx.add hy) (fun c _ hx ↦ IsSmallAtInfinity.mul (hk c) hx) (fun a ha ↦ ?_)
      (h _ hk)
    rw [coeff_smul_ιMulti_D]
    exact IsSmallAtInfinity.mul (ha 0) (isSmallAtInfinity_det _ fun i i' ↦
      isSmallAtInfinity_pderivF _ j (ha i.succ))
  rw [← hq] at hsmall ⊢
  rw [eq_zero_of_isSmallAtInfinity q hsmall, map_zero]

end Coefficients

end SGA.SGA1.ExposeXI.RegularForms
