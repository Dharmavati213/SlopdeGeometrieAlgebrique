/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import SGA.Foundations.Blowup.AffineAlgebra
import SGA.Foundations.CommAlg.RegularLocalRing
import SGA.SGA2.ExposeV.HomologicalRegularityCriterion

/-!
# Quadratic transformations: blowing up a regular local ring of dimension two

Let `(A, 𝔪, κ)` be a regular local ring of dimension `2`, `𝔪 = (x, y)`. The blow-up of `Spec A`
at the closed point is covered by the charts `Spec A[𝔪/x]` and `Spec A[𝔪/y]`. We prove (Stacks,
Tags 0AGQ and 0AGR, on the chart `Spec A[𝔪/x]`):

* `Ideal.QuadraticTransform.coeff_mem_of_aeval_mem`: with `t = y/x ∈ A[𝔪/x]`
  (`Ideal.QuadraticTransform.ratio`), a polynomial
  `f ∈ A[T]` with `f(t) ∈ 𝔪 A[𝔪/x]` has all its coefficients in `𝔪`; hence the fibre of the chart
  over the closed point is the affine line, `A[𝔪/x]/𝔪 A[𝔪/x] ≅ κ[T]`
  (`Ideal.QuadraticTransform.quotientEquiv`);
* `Ideal.QuadraticTransform.isRegularRing`: `A[𝔪/x]` is a regular ring. At a point of the
  exceptional divisor this uses Stacks, Tag 00NU (`R/(r)` regular with `r` a nonzerodivisor of the
  maximal ideal implies `R` regular), which is
  `SGA.SGA2.ExposeV.isRegularLocalRing_of_regular_principal_quotient` in this repository.

This covers only the chart part of Tag 0AGQ (1) (the exceptional fibre meets `D₊(x t)` in
`𝔸¹_κ`; the statement `E ≅ ℙ¹_κ` and items (2), (3) of 0AGQ are not proved here), and the
regularity half of Tag 0AGR (irreducibility of the blow-up is not proved).

The input on `A` is that `(x, y)` is a *quasi-regular* sequence: a homogeneous polynomial `F` of
degree `d` with `F(x, y) ∈ 𝔪^{d+1}` has all its coefficients in `𝔪` (the injectivity of
`κ[X, Y] → gr_𝔪(A)`). This holds for any regular local ring and any regular system of parameters
(Matsumura, Thm 14.4 and 16.2); in this repository it is
`SGA.SGA1.ExposeII.isRegularSystemOfGenerators_of_isWeaklyRegular` together with
`IsRegularLocalRing.isRegular_of_span_eq_maximalIdeal`, which Foundations cannot import, so it is
a hypothesis here.

## References

* [Stacks Project, Section 54.3 (Quadratic transformations), Tags 0AGQ, 0AGR](https://stacks.math.columbia.edu/tag/0AGP)
* [Stacks Project, Tag 00NU](https://stacks.math.columbia.edu/tag/00NU), proved as
  `SGA.SGA2.ExposeV.isRegularLocalRing_of_regular_principal_quotient`
-/

universe u

open IsLocalRing

section Localization

/-- A localization of a regular ring at a prime is a regular local ring (mathlib's
`IsRegularRing.isRegularLocalRing_localization` for any `IsLocalization.AtPrime`). -/
theorem IsRegularRing.isRegularLocalRing_of_isLocalization {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [IsRegularRing R] (p : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime S p] : IsRegularLocalRing S :=
  IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) S).toRingEquiv

end Localization

namespace Ideal.QuadraticTransform

open Polynomial

variable {A : Type u} [CommRing A] [IsLocalRing A] {x y : A}

/-- The unit `1/x` of `A_x`. -/
private noncomputable abbrev invX (x : A) : Localization.Away x :=
  ↑(IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x).unit⁻¹

omit [IsLocalRing A] in
private lemma algebraMap_mul_invX (x : A) :
    algebraMap A (Localization.Away x) x * invX x = 1 :=
  IsUnit.mul_val_inv _

variable (hxy : maximalIdeal A = Ideal.span {x, y})
include hxy

lemma mem_maximalIdeal_left : x ∈ maximalIdeal A :=
  hxy ▸ Ideal.subset_span (Set.mem_insert x _)

lemma mem_maximalIdeal_right : y ∈ maximalIdeal A :=
  hxy ▸ Ideal.subset_span (Set.mem_insert_of_mem x rfl)

/-- The element `t = y/x` of the chart `A[𝔪/x]`. -/
noncomputable def ratio : (maximalIdeal A).affineBlowup x :=
  ⟨algebraMap A _ y * invX x,
    algebraMap_mul_inv_mem_affineBlowupAlgebra (mem_maximalIdeal_right hxy)⟩

/-- The key computation behind Stacks, Tag 0AGQ: with `t = y/x ∈ A[𝔪/x]`, if `f(t) ∈ 𝔪 A[𝔪/x]`
then all the coefficients of `f` lie in `𝔪`. The hypothesis `hqr` says that `(x, y)` is a
quasi-regular sequence (true in a regular local ring of dimension `2`). -/
theorem coeff_mem_of_aeval_mem [IsDomain A] (hx0 : x ≠ 0)
    (hqr : ∀ (d : ℕ) (F : MvPolynomial (Fin 2) A), F.IsHomogeneous d →
      MvPolynomial.eval ![x, y] F ∈ maximalIdeal A ^ (d + 1) → ∀ m, F.coeff m ∈ maximalIdeal A)
    (f : A[X])
    (hf : aeval (ratio hxy) f ∈
      (maximalIdeal A).map (algebraMap A ((maximalIdeal A).affineBlowup x)))
    (i : ℕ) : f.coeff i ∈ maximalIdeal A := by
  classical
  set S := Localization.Away x
  set B := (maximalIdeal A).affineBlowup x
  have hxm := mem_maximalIdeal_left hxy
  have hux : algebraMap A S x * invX x = 1 := algebraMap_mul_invX x
  rw [map_affineBlowupAlgebra_eq_span hxm, Ideal.mem_span_singleton'] at hf
  obtain ⟨b, hb⟩ := hf
  obtain ⟨n, z, hz, hbz⟩ := (mem_affineBlowupAlgebra_iff hxm).mp b.2
  set d := f.natDegree
  set D := d + n
  -- the relation in `S = A_x`
  have hS : ∑ j ∈ Finset.range (d + 1), algebraMap A S (f.coeff j) * (algebraMap A S y * invX x) ^ j
      = algebraMap A S z * invX x ^ n * algebraMap A S x := by
    have := congrArg Subtype.val hb
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, hbz, Polynomial.aeval_subalgebra_coe,
      aeval_eq_sum_range] at this
    simp only [Algebra.smul_def, Units.val_pow_eq_pow_val] at this
    exact this.symm
  -- clearing denominators: the relation in `A`
  have hpow : ∀ k : ℕ, (algebraMap A S x * invX x) ^ k = 1 := fun k ↦ by rw [hux, one_pow]
  have hA : ∑ j ∈ Finset.range (d + 1), f.coeff j * x ^ (D - j) * y ^ j = z * x ^ (d + 1) := by
    refine IsLocalization.injective S (M := Submonoid.powers x)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx0) ?_
    have h : (∑ j ∈ Finset.range (d + 1),
        algebraMap A S (f.coeff j) * (algebraMap A S y * invX x) ^ j) * algebraMap A S x ^ D =
        algebraMap A S z * invX x ^ n * algebraMap A S x * algebraMap A S x ^ D := by
      rw [hS]
    rw [Finset.sum_mul] at h
    rw [map_sum, map_mul, map_pow]
    convert h using 1
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hjD : j ≤ D := by
        have := Finset.mem_range.mp hj
        omega
      rw [show D = (D - j) + j by omega, pow_add, Nat.add_sub_cancel]
      simp only [map_mul, map_pow]
      linear_combination (-(algebraMap A S (f.coeff j) * algebraMap A S x ^ (D - j) *
        algebraMap A S y ^ j)) * hpow j
    · rw [show D = d + n from rfl, pow_add]
      linear_combination (-(algebraMap A S z * algebraMap A S x ^ (d + 1))) * hpow n
  have hmem : ∑ j ∈ Finset.range (d + 1), f.coeff j * x ^ (D - j) * y ^ j ∈
      maximalIdeal A ^ (D + 1) := by
    rw [hA, show D + 1 = n + (d + 1) by omega, pow_add]
    exact Submodule.mul_mem_mul hz (Ideal.pow_mem_pow hxm _)
  -- the homogeneous polynomial `G = ∑ aⱼ X^{D-j} Y^j`
  let m : ℕ → (Fin 2 →₀ ℕ) := fun j ↦ Finsupp.single 0 (D - j) + Finsupp.single 1 j
  let G : MvPolynomial (Fin 2) A :=
    ∑ j ∈ Finset.range (d + 1), MvPolynomial.monomial (m j) (f.coeff j)
  have hG : G.IsHomogeneous D := by
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j hj ↦ ?_
    refine MvPolynomial.isHomogeneous_monomial _ ?_
    have := Finset.mem_range.mp hj
    simp only [m, map_add, Finsupp.degree_single]
    omega
  have heval : MvPolynomial.eval ![x, y] G =
      ∑ j ∈ Finset.range (d + 1), f.coeff j * x ^ (D - j) * y ^ j := by
    simp only [G, m, map_sum, MvPolynomial.eval_monomial]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]),
      Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
    simp [mul_assoc]
  have hm_inj : ∀ j k, m j = m k → j = k := fun j k h ↦ by
    have := congrArg (fun e ↦ e 1) h
    simpa [m] using this
  rcases lt_or_ge d i with hi | hi
  · rw [coeff_eq_zero_of_natDegree_lt hi]
    exact zero_mem _
  have hcoeff : G.coeff (m i) = f.coeff i := by
    simp only [G, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      exact ite_eq_right_iff.mpr fun h ↦ absurd (hm_inj j i h) hji
    · intro hi'
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)) hi'
  rw [← hcoeff]
  exact hqr D G hG (heval ▸ hmem) (m i)

/-- The chart `A[𝔪/x]` is generated over `A` by `t = y/x`. -/
theorem adjoin_ratio_eq_top :
    Algebra.adjoin A {ratio hxy} = ⊤ := by
  have hxm := mem_maximalIdeal_left hxy
  have hgen := affineBlowupAlgebra_eq_adjoin
    (ha := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x) hxy.symm
  rw [eq_top_iff]
  rintro ⟨b, hb⟩ -
  have hb' : b ∈ (maximalIdeal A).affineBlowupAlgebra
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x) := hb
  rw [hgen, Set.image_insert_eq, Set.image_singleton] at hb'
  -- `x / x = 1`
  have h1 : algebraMap A (Localization.Away x) x * invX x = 1 := algebraMap_mul_invX x
  rw [h1] at hb'
  -- transport along the inclusion `A[𝔪/x] ⊆ A_x`
  have key : Algebra.adjoin A {(1 : Localization.Away x), algebraMap A _ y * invX x} ≤
      (Algebra.adjoin A {ratio hxy}).map ((maximalIdeal A).affineBlowup x).val := by
    rw [Algebra.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Subalgebra.one_mem _, ⟨ratio hxy, Algebra.subset_adjoin rfl, rfl⟩⟩
  obtain ⟨c, hc, hcb⟩ := key hb'
  have hc' : c = ⟨b, hb⟩ := Subtype.ext hcb
  rwa [← hc']

variable (A) in
/-- The maximal ideal `𝔪` extended to the chart `A[𝔪/x]`. -/
noncomputable abbrev extendedIdeal (x : A) : Ideal ((maximalIdeal A).affineBlowup x) :=
  (maximalIdeal A).map (algebraMap A ((maximalIdeal A).affineBlowup x))

/-- The map `κ[T] → A[𝔪/x] / 𝔪 A[𝔪/x]`, `T ↦ t`. -/
noncomputable def toQuotient :
    (A ⧸ maximalIdeal A)[X] →+* (maximalIdeal A).affineBlowup x ⧸ extendedIdeal A x :=
  eval₂RingHom (Ideal.quotientMap _ (algebraMap A _) Ideal.le_comap_map)
    (Ideal.Quotient.mk _ (ratio hxy))

lemma toQuotient_map (f : A[X]) :
    toQuotient hxy (f.map (Ideal.Quotient.mk _)) = Ideal.Quotient.mk _ (aeval (ratio hxy) f) := by
  rw [toQuotient, coe_eval₂RingHom, eval₂_map, Ideal.quotientMap_comp_mk, aeval_def,
    hom_eval₂]

/-- The chart part of Stacks, Tag 0AGQ (1), on `A[𝔪/x]`: the fibre of the blow-up over the closed
point meets the chart in the affine line over the residue field, `A[𝔪/x] / 𝔪 A[𝔪/x] ≅ κ[T]` with
`T ↦ y/x`, when `(x, y)` is a quasi-regular sequence generating `𝔪` (e.g. a regular system of
parameters of a regular local ring of dimension `2`). -/
noncomputable def quotientEquiv [IsDomain A] (hx0 : x ≠ 0)
    (hqr : ∀ (d : ℕ) (F : MvPolynomial (Fin 2) A), F.IsHomogeneous d →
      MvPolynomial.eval ![x, y] F ∈ maximalIdeal A ^ (d + 1) → ∀ m, F.coeff m ∈ maximalIdeal A) :
    (A ⧸ maximalIdeal A)[X] ≃+* (maximalIdeal A).affineBlowup x ⧸ extendedIdeal A x :=
  RingEquiv.ofBijective (toQuotient hxy) <| by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun g hg ↦ ?_, fun w ↦ ?_⟩
    · obtain ⟨f, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective g
      rw [toQuotient_map, Ideal.Quotient.eq_zero_iff_mem] at hg
      ext i
      rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact coeff_mem_of_aeval_mem hxy hx0 hqr f hg i
    · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
      have hb : b ∈ Algebra.adjoin A {ratio hxy} := (adjoin_ratio_eq_top hxy).symm ▸ Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
      obtain ⟨f, rfl⟩ := hb
      exact ⟨f.map (Ideal.Quotient.mk _), toQuotient_map hxy f⟩

omit hxy in
/-- `A → A[𝔪/x]` is injective (`A` is a domain and `x ≠ 0`). -/
lemma algebraMap_injective [IsDomain A] (hx0 : x ≠ 0) :
    Function.Injective (algebraMap A ((maximalIdeal A).affineBlowup x)) := by
  intro a a' h
  have h' := congrArg Subtype.val h
  simp only [Subalgebra.coe_algebraMap] at h'
  exact IsLocalization.injective (Localization.Away x) (M := Submonoid.powers x)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx0) h'

omit hxy in
/-- Away from the exceptional divisor the chart is `A`: the local ring of `A[𝔪/x]` at a prime not
containing `x` is the localization of `A` at the inverse image of that prime. -/
theorem isLocalization_atPrime_of_notMem [IsDomain A] (hxm : x ∈ maximalIdeal A) (hx0 : x ≠ 0)
    (𝔮 : Ideal ((maximalIdeal A).affineBlowup x)) [𝔮.IsPrime]
    (hx𝔮 : algebraMap A ((maximalIdeal A).affineBlowup x) x ∉ 𝔮) :
    IsLocalization.AtPrime (Localization.AtPrime 𝔮)
      (𝔮.comap (algebraMap A ((maximalIdeal A).affineBlowup x))) := by
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime 𝔮)) := by
    rw [IsScalarTower.algebraMap_eq A ((maximalIdeal A).affineBlowup x)]
    exact (IsLocalization.injective _ 𝔮.primeCompl_le_nonZeroDivisors).comp
      (algebraMap_injective hx0)
  -- `b xⁿ ∈ A` for some `n`, for every `b` of the chart
  have hden : ∀ b : (maximalIdeal A).affineBlowup x, ∃ (n : ℕ) (z : A),
      b * algebraMap A _ x ^ n = algebraMap A _ z := by
    intro b
    obtain ⟨n, z, -, hbz⟩ := (mem_affineBlowupAlgebra_iff hxm).mp b.2
    refine ⟨n, z, Subtype.ext ?_⟩
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, hbz,
      Units.val_pow_eq_pow_val, mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, mul_one]
  have hxpow : ∀ k : ℕ, algebraMap A ((maximalIdeal A).affineBlowup x) x ^ k ∉ 𝔮 :=
    fun k h ↦ hx𝔮 (Ideal.IsPrime.mem_of_pow_mem ‹_› _ h)
  refine ⟨fun c ↦ ?_, fun q ↦ ?_, fun {a a'} h ↦ ⟨1, by rw [hinj h]⟩⟩
  · rw [IsScalarTower.algebraMap_apply A ((maximalIdeal A).affineBlowup x)]
    exact IsLocalization.map_units _ (⟨_, c.2⟩ : 𝔮.primeCompl)
  · obtain ⟨⟨b, s'⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl q
    obtain ⟨n, z, hz⟩ := hden b
    obtain ⟨m, w, hw⟩ := hden s'
    have hs : algebraMap A ((maximalIdeal A).affineBlowup x) (w * x ^ n) ∉ 𝔮 := by
      rw [map_mul, ← hw, map_pow]
      exact Ideal.IsPrime.mul_notMem ‹_› (Ideal.IsPrime.mul_notMem ‹_› s'.2 (hxpow m))
        (hxpow n)
    refine ⟨⟨z * x ^ m, ⟨w * x ^ n, hs⟩⟩, ?_⟩
    simp only [IsScalarTower.algebraMap_apply A ((maximalIdeal A).affineBlowup x)
      (Localization.AtPrime 𝔮)]
    have key : IsLocalization.mk' (Localization.AtPrime 𝔮) b s' *
        algebraMap _ (Localization.AtPrime 𝔮) (s' : (maximalIdeal A).affineBlowup x) =
        algebraMap _ (Localization.AtPrime 𝔮) b := IsLocalization.mk'_spec _ _ _
    rw [map_mul, ← hw, show algebraMap A ((maximalIdeal A).affineBlowup x) (z * x ^ m) =
      b * algebraMap A _ x ^ n * algebraMap A _ x ^ m by rw [map_mul, ← hz, map_pow]]
    simp only [map_mul, map_pow]
    linear_combination (algebraMap _ (Localization.AtPrime 𝔮)
      (algebraMap A ((maximalIdeal A).affineBlowup x) x) ^ m * algebraMap _
      (Localization.AtPrime 𝔮) (algebraMap A ((maximalIdeal A).affineBlowup x) x) ^ n) * key

/-- The regularity half of Stacks, Tag 0AGR, on the chart `A[𝔪/x]`: blowing up the closed point
of a regular local ring of dimension two gives a regular scheme (irreducibility is not proved
here). Here `A` is a regular local ring, `𝔪 = (x, y)` with
`(x, y)` quasi-regular (`hqr`; true for every regular system of parameters), and the conclusion
is that `A[𝔪/x]` is a regular ring. -/
theorem isRegularRing (hA : IsRegularLocalRing A) (hx0 : x ≠ 0)
    (hqr : ∀ (d : ℕ) (F : MvPolynomial (Fin 2) A), F.IsHomogeneous d →
      MvPolynomial.eval ![x, y] F ∈ maximalIdeal A ^ (d + 1) → ∀ m, F.coeff m ∈ maximalIdeal A) :
    IsRegularRing ((maximalIdeal A).affineBlowup x) := by
  have hxm := mem_maximalIdeal_left hxy
  have : IsNoetherianRing A := by have := hA; infer_instance
  have : IsDomain A := by have := hA; infer_instance
  have : IsNoetherianRing ((maximalIdeal A).affineBlowup x) :=
    isNoetherianRing_affineBlowupAlgebra
  have : IsDomain (Localization.Away x) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  rw [isRegularRing_iff]
  intro 𝔮 _
  by_cases hx𝔮 : algebraMap A ((maximalIdeal A).affineBlowup x) x ∈ 𝔮
  · -- a point of the exceptional divisor: divide by the equation `x` of the divisor
    set xQ := algebraMap _ (Localization.AtPrime 𝔮)
      (algebraMap A ((maximalIdeal A).affineBlowup x) x) with hxQ
    have hxQm : xQ ∈ maximalIdeal (Localization.AtPrime 𝔮) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔮 _).mpr hx𝔮
    have hxQ0 : xQ ∈ nonZeroDivisors (Localization.AtPrime 𝔮) := by
      refine mem_nonZeroDivisors_of_ne_zero fun h ↦ hx0 ?_
      have h' := (IsLocalization.injective _ 𝔮.primeCompl_le_nonZeroDivisors)
        (h.trans (map_zero _).symm)
      exact algebraMap_injective hx0 (h'.trans (map_zero _).symm)
    -- the quotient of the chart by `x` is `κ[T]`, a regular ring
    let J := extendedIdeal A x
    have hJ : J = Ideal.span {algebraMap A ((maximalIdeal A).affineBlowup x) x} :=
      map_affineBlowupAlgebra_eq_span hxm
    have hJ𝔮 : J ≤ 𝔮 := by
      rw [hJ, Ideal.span_le, Set.singleton_subset_iff]
      exact hx𝔮
    have : IsRegularRing (A ⧸ maximalIdeal A) := by
      let := Ideal.Quotient.field (maximalIdeal A)
      infer_instance
    have : IsRegularRing ((maximalIdeal A).affineBlowup x ⧸ J) :=
      IsRegularRing.of_ringEquiv (quotientEquiv hxy hx0 hqr)
    let 𝔮' : Ideal ((maximalIdeal A).affineBlowup x ⧸ J) := 𝔮.map (Ideal.Quotient.mk J)
    have h𝔮' : 𝔮'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
    have hsub : Algebra.algebraMapSubmonoid ((maximalIdeal A).affineBlowup x ⧸ J) 𝔮.primeCompl =
        𝔮'.primeCompl := by
      ext w
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact fun h ↦ hb ((Ideal.mem_quotient_iff_mem hJ𝔮).mp h)
      · intro hw
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
        exact ⟨b, fun h ↦ hw (Ideal.mem_map_of_mem _ h), rfl⟩
    have hloc : IsLocalization.AtPrime
        (Localization.AtPrime 𝔮 ⧸ J.map (algebraMap _ (Localization.AtPrime 𝔮))) 𝔮' := by
      have := (inferInstance : IsLocalization
        (Algebra.algebraMapSubmonoid ((maximalIdeal A).affineBlowup x ⧸ J) 𝔮.primeCompl)
        (Localization.AtPrime 𝔮 ⧸ J.map (algebraMap _ (Localization.AtPrime 𝔮))))
      rw [hsub] at this
      exact this
    have hreg := IsRegularRing.isRegularLocalRing_of_isLocalization
      (S := Localization.AtPrime 𝔮 ⧸ J.map (algebraMap _ (Localization.AtPrime 𝔮))) 𝔮'
    have hJQ : J.map (algebraMap _ (Localization.AtPrime 𝔮)) = Ideal.span {xQ} := by
      rw [hJ, Ideal.map_span, Set.image_singleton]
    have : IsRegularLocalRing (Localization.AtPrime 𝔮 ⧸ Ideal.span {xQ}) :=
      IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq hJQ)
    exact SGA.SGA2.ExposeV.isRegularLocalRing_of_regular_principal_quotient xQ hxQm
      (Module.Flat.isSMulRegular_of_nonZeroDivisors hxQ0)
  · -- away from the exceptional divisor the chart is a localization of `A`
    have := isLocalization_atPrime_of_notMem hxm hx0 𝔮 hx𝔮
    exact IsRegularLocalRing.of_isLocalization_atPrime
      (𝔮.comap (algebraMap A ((maximalIdeal A).affineBlowup x))) _

end Ideal.QuadraticTransform
