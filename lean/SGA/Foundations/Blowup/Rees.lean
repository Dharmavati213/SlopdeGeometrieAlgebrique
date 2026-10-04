/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.ReesAlgebra
import SGA.Foundations.Blowup.AffineAlgebra
import SGA.Foundations.Projective.SectionRing

/-!
# The Rees algebra as a graded algebra, and the affine charts of the blow-up

Let `A` be a commutative ring and `I ⊆ A` an ideal. The Rees algebra `⊕ₙ Iⁿ` is graded by `n`, and
the blow-up of `Spec A` along `V(I)` is `Proj (⊕ₙ Iⁿ)` (Stacks, Tag 0804; EGA II 8.1.3). We realize
the Rees algebra as the external direct sum of the powers `Iⁿ ⊆ A` (`Ideal.ReesAlgebra I`), graded
by the images of the summands (`Ideal.reesGrading I`, an instance of `DirectSum.lofGrading`). It is
isomorphic to mathlib's `reesAlgebra I ⊆ A[t]`, which has no grading (`Ideal.reesAlgebraEquiv`).

## Main results

* `Ideal.reesZeroEquiv`: the degree-zero part of `⊕ₙ Iⁿ` is `A`;
* `Ideal.reesSum`: the `A`-algebra map `⊕ₙ Iⁿ → A`, `x tⁿ ↦ x` ("`t = 1`"), injective on every
  graded piece;
* `Ideal.reesAlgebraEquiv : ⊕ₙ Iⁿ ≃ₐ[A] reesAlgebra I`, `x tⁿ ↦ x Xⁿ`: agreement with mathlib's
  ungraded Rees algebra;
* `Ideal.reesAwayEquiv`: for `a ∈ I` with image `a t` in degree `1`, the degree-zero part of the
  localization `(⊕ₙ Iⁿ)_{a t}` is the affine blowup algebra `A[I/a]` (Stacks, Tag 0804; the charts
  of the blow-up).

## References

* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [A. Grothendieck, *EGA* II, 8.1]
-/

universe u

open DirectSum

namespace Ideal

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The Rees algebra `⊕ₙ Iⁿ` of an ideal `I`, as the external direct sum of the powers `Iⁿ ⊆ A`
(a graded `A`-algebra through `Submodule.nat_power_gradedMonoid`). It is isomorphic to mathlib's
`reesAlgebra I ⊆ A[t]` (`Ideal.reesAlgebraEquiv`); this model carries the grading
`Ideal.reesGrading I`. -/
abbrev ReesAlgebra : Type u := ⨁ n : ℕ, (I ^ n : Submodule A A)

/-- The grading of the Rees algebra: `Iⁿ tⁿ` in degree `n`. -/
abbrev reesGrading : ℕ → Submodule A I.ReesAlgebra :=
  DirectSum.lofGrading fun n ↦ (I ^ n : Submodule A A)

variable {I}

/-- The element `x tⁿ` of the Rees algebra, for `x ∈ Iⁿ`. -/
noncomputable abbrev reesMonomial (n : ℕ) (x : A) (hx : x ∈ I ^ n) : I.ReesAlgebra :=
  DirectSum.of (fun n ↦ (I ^ n : Submodule A A)) n ⟨x, hx⟩

lemma reesMonomial_mem (n : ℕ) (x : A) (hx : x ∈ I ^ n) :
    reesMonomial n x hx ∈ I.reesGrading n :=
  DirectSum.of_mem_lofGrading _ n _

lemma mem_reesGrading_iff {n : ℕ} {z : I.ReesAlgebra} :
    z ∈ I.reesGrading n ↔ ∃ x hx, reesMonomial n x hx = z := by
  rw [DirectSum.mem_lofGrading_iff]
  exact ⟨fun ⟨⟨x, hx⟩, h⟩ ↦ ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ ↦ ⟨⟨x, hx⟩, h⟩⟩

lemma reesMonomial_mul {m n : ℕ} {x y : A} (hx : x ∈ I ^ m) (hy : y ∈ I ^ n) :
    reesMonomial m x hx * reesMonomial n y hy =
      reesMonomial (m + n) (x * y) (by rw [pow_add]; exact Submodule.mul_mem_mul hx hy) := by
  rw [DirectSum.of_mul_of]
  rfl

lemma reesMonomial_pow {n : ℕ} {x : A} (hx : x ∈ I ^ n) (k : ℕ) :
    reesMonomial n x hx ^ k =
      reesMonomial (k * n) (x ^ k) (by rw [mul_comm, pow_mul]; exact Ideal.pow_mem_pow hx k) := by
  induction k with
  | zero => simp; rfl
  | succ k ih =>
    rw [pow_succ, ih, reesMonomial_mul]
    congr 1 <;> ring

variable (I)

/-- The `A`-algebra map `⊕ₙ Iⁿ → A`, `x tⁿ ↦ x` (setting `t = 1`). -/
noncomputable def reesSum : I.ReesAlgebra →ₐ[A] A :=
  DirectSum.coeAlgHom fun n ↦ (I ^ n : Submodule A A)

variable {I}

@[simp]
lemma reesSum_reesMonomial (n : ℕ) (x : A) (hx : x ∈ I ^ n) :
    I.reesSum (reesMonomial n x hx) = x :=
  DirectSum.coeAlgHom_of _ _ _

/-- `x tⁿ ↦ x` is injective on each graded piece. -/
lemma eq_zero_of_reesSum_eq_zero {n : ℕ} {z : I.ReesAlgebra} (hz : z ∈ I.reesGrading n)
    (h : I.reesSum z = 0) : z = 0 := by
  obtain ⟨x, hx, rfl⟩ := mem_reesGrading_iff.mp hz
  rw [reesSum_reesMonomial] at h
  subst h
  exact map_zero (DirectSum.of (fun n ↦ (I ^ n : Submodule A A)) n)

lemma algebraMap_reesAlgebra (x : A) :
    algebraMap A I.ReesAlgebra x = reesMonomial 0 x (by simp) := by
  rw [DirectSum.algebraMap_apply]
  rfl

lemma reesMonomial_add {n : ℕ} {x y : A} (hx : x ∈ I ^ n) (hy : y ∈ I ^ n) :
    reesMonomial n (x + y) (add_mem hx hy) = reesMonomial n x hx + reesMonomial n y hy := by
  rw [← map_add]
  rfl

lemma reesMonomial_mul_left {n : ℕ} (r : A) {x : A} (hx : x ∈ I ^ n) :
    reesMonomial n (r * x) (Ideal.mul_mem_left _ r hx) =
      algebraMap A I.ReesAlgebra r * reesMonomial n x hx := by
  rw [algebraMap_reesAlgebra, reesMonomial_mul]
  congr 1
  exact (zero_add n).symm

variable (I) in
/-- The degree-zero part of the Rees algebra is `A`. -/
noncomputable def reesZeroEquiv : A ≃+* I.reesGrading 0 :=
  RingEquiv.ofBijective (algebraMap A (I.reesGrading 0)) <| by
    refine ⟨fun x y h ↦ ?_, fun z ↦ ?_⟩
    · have h' := congrArg (fun z : I.reesGrading 0 ↦ I.reesSum (z : I.ReesAlgebra)) h
      simpa [SetLike.GradeZero.coe_algebraMap, AlgHom.commutes] using h'
    · obtain ⟨x, hx, hz⟩ := mem_reesGrading_iff.mp z.2
      refine ⟨x, Subtype.ext ?_⟩
      rw [SetLike.GradeZero.coe_algebraMap, algebraMap_reesAlgebra, hz]

@[simp]
lemma coe_reesZeroEquiv (x : A) :
    (I.reesZeroEquiv x : I.ReesAlgebra) = algebraMap A I.ReesAlgebra x := rfl

/-- The element `a t` of degree `1` of the Rees algebra, for `a ∈ I`. -/
noncomputable abbrev reesT {a : A} (ha : a ∈ I) : I.ReesAlgebra :=
  reesMonomial 1 a (by simpa using ha)

lemma reesT_mem {a : A} (ha : a ∈ I) : reesT ha ∈ I.reesGrading 1 := reesMonomial_mem _ _ _

lemma reesSum_reesT {a : A} (ha : a ∈ I) : I.reesSum (reesT ha) = a :=
  reesSum_reesMonomial _ _ _

lemma mem_of_span_eq {s : Set A} (hs : Ideal.span s = I) (a : s) : (a : A) ∈ I :=
  hs ▸ Ideal.subset_span a.2

/-- The Rees algebra is generated over its degree-zero part by the elements `a t`, `a ∈ s`, for any
set `s` of generators of `I`. -/
theorem adjoin_reesT_eq_top {s : Set A} (hs : Ideal.span s = I) :
    Algebra.adjoin (I.reesGrading 0) (Set.range fun a : s ↦ reesT (mem_of_span_eq hs a)) = ⊤ := by
  set T := Algebra.adjoin (I.reesGrading 0) (Set.range fun a : s ↦ reesT (mem_of_span_eq hs a))
  have hA : ∀ r : A, algebraMap A I.ReesAlgebra r ∈ T := fun r ↦
    Subalgebra.algebraMap_mem T (algebraMap A (I.reesGrading 0) r)
  have hI1 : ∀ {y : A}, y ∈ Submodule.span A s → y ∈ I ^ 1 := fun hy ↦ by
    rw [pow_one, ← hs]; exact hy
  -- degree one
  have h1 : ∀ x (hx : x ∈ I ^ 1), reesMonomial 1 x hx ∈ T := by
    intro x hx
    have hx' : x ∈ Submodule.span A s := by rw [pow_one, ← hs] at hx; exact hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Algebra.subset_adjoin ⟨⟨y, hy⟩, rfl⟩
    | zero =>
      change DirectSum.of (fun n ↦ (I ^ n : Submodule A A)) 1 0 ∈ T
      rw [map_zero]
      exact T.zero_mem
    | add y z hy hz ihy ihz =>
      rw [reesMonomial_add (hI1 hy) (hI1 hz)]
      exact add_mem (ihy _) (ihz _)
    | smul r y hy ihy =>
      change reesMonomial 1 (r * y) hx ∈ T
      rw [reesMonomial_mul_left r (hI1 hy)]
      exact mul_mem (hA r) (ihy _)
  -- all degrees
  have hn : ∀ n x (hx : x ∈ I ^ n), reesMonomial n x hx ∈ T := by
    intro n
    induction n with
    | zero =>
      intro x hx
      rw [← algebraMap_reesAlgebra]
      exact hA x
    | succ n ih =>
      suffices ∀ x (hx : x ∈ I ^ n * I) (h : x ∈ I ^ (n + 1)), reesMonomial (n + 1) x h ∈ T from
        fun x hx ↦ this x (by rwa [← pow_succ]) hx
      intro x hx
      induction hx using Submodule.mul_induction_on' with
      | mem_mul_mem y hy z hz =>
        intro h
        have hz' : z ∈ I ^ 1 := by rwa [pow_one]
        rw [← reesMonomial_mul hy hz']
        exact mul_mem (ih _ _) (h1 _ _)
      | add y hy z hz ihy ihz =>
        intro h
        rw [reesMonomial_add (by rw [pow_succ]; exact hy) (by rw [pow_succ]; exact hz)]
        exact add_mem (ihy _) (ihz _)
  rw [eq_top_iff]
  rintro z -
  induction z using DirectSum.induction_on with
  | zero => exact T.zero_mem
  | of n x => exact hn n x.1 x.2
  | add x y hx hy => exact add_mem hx hy

/-- The Rees algebra of a finitely generated ideal is of finite type over its degree-zero part. -/
theorem finiteType_reesAlgebra (hI : I.FG) :
    Algebra.FiniteType (I.reesGrading 0) I.ReesAlgebra := by
  classical
  obtain ⟨s, hs⟩ := hI
  refine ⟨⟨(Set.finite_range fun a : (s : Set A) ↦ reesT (mem_of_span_eq hs a)).toFinset, ?_⟩⟩
  rw [Set.Finite.coe_toFinset]
  exact adjoin_reesT_eq_top hs

section Chart

variable {a : A} (ha : a ∈ I)

private lemma isUnit_reesSum_reesT :
    IsUnit (((algebraMap A (Localization.Away a)).comp I.reesSum.toRingHom) (reesT ha)) := by
  simpa [reesSum_reesT] using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a

/-- The ring map `(⊕ₙ Iⁿ)_{(a t)} → A_a`, `x tⁿ / (a t)ⁿ ↦ x / aⁿ`, from the degree-zero part of the
homogeneous localization at `a t` (an auxiliary map for `Ideal.reesAwayEquiv`). -/
noncomputable def reesAwayToAway :
    HomogeneousLocalization.Away I.reesGrading (reesT ha) →+* Localization.Away a :=
  (IsLocalization.Away.lift (S := Localization.Away (reesT ha)) (reesT ha)
    (isUnit_reesSum_reesT ha)).comp
    (algebraMap (HomogeneousLocalization.Away I.reesGrading (reesT ha))
      (Localization.Away (reesT ha)))

lemma reesAwayToAway_mk_mul (n : ℕ) (z : I.ReesAlgebra) (hz : z ∈ I.reesGrading (n • 1)) :
    reesAwayToAway ha (HomogeneousLocalization.Away.mk _ (reesT_mem ha) n z hz) *
      algebraMap A (Localization.Away a) a ^ n =
        algebraMap A (Localization.Away a) (I.reesSum z) := by
  set g := (algebraMap A (Localization.Away a)).comp I.reesSum.toRingHom
  have hg : g (reesT ha) = algebraMap A (Localization.Away a) a := by
    simp [g]
  have key : (HomogeneousLocalization.Away.mk _ (reesT_mem ha) n z hz).val *
      algebraMap I.ReesAlgebra (Localization.Away (reesT ha)) (reesT ha ^ n) =
      algebraMap I.ReesAlgebra (Localization.Away (reesT ha)) z := by
    rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ _ _
  have := congrArg (IsLocalization.Away.lift (S := Localization.Away (reesT ha)) (reesT ha)
    (isUnit_reesSum_reesT ha)) key
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, map_pow, hg] at this
  exact this

private lemma algebraMap_away_unit_inv_pow_mul (n : ℕ) :
    (↑((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).unit⁻¹ ^ n) :
      Localization.Away a) * algebraMap A (Localization.Away a) a ^ n = 1 := by
  rw [Units.val_pow_eq_pow_val, ← mul_pow, IsUnit.val_inv_mul, one_pow]

lemma reesAwayToAway_mk (n : ℕ) (z : I.ReesAlgebra) (hz : z ∈ I.reesGrading (n • 1)) :
    reesAwayToAway ha (HomogeneousLocalization.Away.mk _ (reesT_mem ha) n z hz) =
      algebraMap A (Localization.Away a) (I.reesSum z) *
        ↑((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).unit⁻¹ ^ n) := by
  rw [← reesAwayToAway_mk_mul, mul_assoc, mul_comm (_ ^ n), algebraMap_away_unit_inv_pow_mul,
    mul_one]

lemma reesAwayToAway_mem (z : HomogeneousLocalization.Away I.reesGrading (reesT ha)) :
    reesAwayToAway ha z ∈ I.affineBlowup a := by
  obtain ⟨n, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (reesT_mem ha) z
  rw [reesAwayToAway_mk]
  obtain ⟨x, hx, rfl⟩ := mem_reesGrading_iff.mp hy
  rw [reesSum_reesMonomial]
  exact algebraMap_mul_inv_pow_mem_affineBlowupAlgebra (by simpa using hx)

lemma reesAwayToAway_injective : Function.Injective (reesAwayToAway ha) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
  obtain ⟨n, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (reesT_mem ha) z
  have h0 := reesAwayToAway_mk_mul ha n y hy
  rw [hz, zero_mul, eq_comm, IsLocalization.map_eq_zero_iff (Submonoid.powers a)] at h0
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := h0
  have hdeg : reesT ha ^ m * y ∈ I.reesGrading (m • 1 + n • 1) :=
    SetLike.mul_mem_graded (SetLike.pow_mem_graded m (reesT_mem ha)) hy
  have hzero : reesT ha ^ m * y = 0 := by
    refine eq_zero_of_reesSum_eq_zero hdeg ?_
    rw [map_mul, map_pow, reesSum_reesT]
    exact hm
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨_, m, rfl⟩, hzero⟩

lemma reesAwayToAway_surjective (y : I.affineBlowup a) :
    ∃ z, reesAwayToAway ha z = y := by
  obtain ⟨n, x, hx, hy⟩ := (mem_affineBlowupAlgebra_iff ha).mp y.2
  have hz : reesMonomial n x hx ∈ I.reesGrading (n • 1) := by
    simpa using reesMonomial_mem n x hx
  refine ⟨HomogeneousLocalization.Away.mk _ (reesT_mem ha) n _ hz, ?_⟩
  rw [reesAwayToAway_mk, reesSum_reesMonomial, hy]

/-- The affine charts of the blow-up (Stacks, Tag 0804): for `a ∈ I`, the degree-zero part of the
localization of the Rees algebra `⊕ₙ Iⁿ` at `a t` is the affine blowup algebra `A[I/a]`, by
`x tⁿ / (a t)ⁿ ↦ x / aⁿ`. -/
noncomputable def reesAwayEquiv :
    HomogeneousLocalization.Away I.reesGrading (reesT ha) ≃+* I.affineBlowup a :=
  RingEquiv.ofBijective ((reesAwayToAway ha).codRestrict (I.affineBlowup a)
    (reesAwayToAway_mem ha)) <| by
    refine ⟨fun z w h ↦ reesAwayToAway_injective ha (congrArg Subtype.val h), fun y ↦ ?_⟩
    obtain ⟨z, hz⟩ := reesAwayToAway_surjective ha y
    exact ⟨z, Subtype.ext hz⟩

@[simp]
lemma coe_reesAwayEquiv (z : HomogeneousLocalization.Away I.reesGrading (reesT ha)) :
    (reesAwayEquiv ha z : Localization.Away a) = reesAwayToAway ha z := rfl

end Chart

section Comparison

open Polynomial

variable (I) in
/-- The `A`-linear maps `Iⁿ → A[X]`, `x ↦ x Xⁿ`. -/
private noncomputable abbrev reesToPolynomialAux (n : ℕ) :
    (I ^ n : Submodule A A) →ₗ[A] A[X] :=
  (Polynomial.monomial n).comp (I ^ n : Submodule A A).subtype

private lemma reesToPolynomialAux_one :
    reesToPolynomialAux I 0
      (@GradedMonoid.GOne.one ℕ (fun n ↦ (I ^ n : Submodule A A)) _ _) = 1 := by
  simp

private lemma reesToPolynomialAux_mul {i j : ℕ} (ai : (I ^ i : Submodule A A))
    (aj : (I ^ j : Submodule A A)) :
    reesToPolynomialAux I (i + j)
      (@GradedMonoid.GMul.mul ℕ (fun n ↦ (I ^ n : Submodule A A)) _ _ i j ai aj) =
      reesToPolynomialAux I i ai * reesToPolynomialAux I j aj := by
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, monomial_mul_monomial]
  rfl

variable (I) in
/-- The `A`-algebra map `⊕ₙ Iⁿ → A[X]`, `x tⁿ ↦ x Xⁿ`. -/
noncomputable def reesToPolynomial : I.ReesAlgebra →ₐ[A] A[X] :=
  DirectSum.toAlgebra A (fun n ↦ (I ^ n : Submodule A A)) (reesToPolynomialAux I)
    reesToPolynomialAux_one reesToPolynomialAux_mul

@[simp]
lemma reesToPolynomial_reesMonomial (n : ℕ) (x : A) (hx : x ∈ I ^ n) :
    I.reesToPolynomial (reesMonomial n x hx) = Polynomial.monomial n x :=
  DirectSum.toSemiring_of _ reesToPolynomialAux_one reesToPolynomialAux_mul _ _

lemma coeff_reesToPolynomial (z : I.ReesAlgebra) (n : ℕ) :
    (I.reesToPolynomial z).coeff n = (z n : A) := by
  classical
  induction z using DirectSum.induction_on with
  | zero => simp
  | of m x =>
    obtain ⟨x, hx⟩ := x
    change (I.reesToPolynomial (reesMonomial m x hx)).coeff n = _
    rw [reesToPolynomial_reesMonomial, coeff_monomial]
    by_cases h : m = n
    · subst h
      simp only [↓reduceIte, DirectSum.of_eq_same]
    · simp only [h, ↓reduceIte]
      rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      rfl
  | add x y hx hy => simp [hx, hy]

lemma reesToPolynomial_injective : Function.Injective I.reesToPolynomial := by
  intro z w h
  ext n
  rw [← coeff_reesToPolynomial, ← coeff_reesToPolynomial, h]

lemma range_reesToPolynomial : I.reesToPolynomial.range = reesAlgebra I := by
  classical
  refine le_antisymm ?_ fun f hf ↦ ?_
  · rintro _ ⟨z, rfl⟩ n
    change (I.reesToPolynomial z).coeff n ∈ I ^ n
    rw [coeff_reesToPolynomial]
    exact (z n).2
  · refine ⟨∑ n ∈ f.support, reesMonomial n (f.coeff n) ((mem_reesAlgebra_iff I f).mp hf n), ?_⟩
    change I.reesToPolynomial _ = f
    rw [map_sum]
    simp only [reesToPolynomial_reesMonomial]
    exact (f.as_sum_support).symm

variable (I) in
/-- The graded model `⊕ₙ Iⁿ` of the Rees algebra is isomorphic to mathlib's
`reesAlgebra I ⊆ A[X]`, by `x tⁿ ↦ x Xⁿ`. -/
noncomputable def reesAlgebraEquiv : I.ReesAlgebra ≃ₐ[A] reesAlgebra I :=
  (AlgEquiv.ofInjective _ reesToPolynomial_injective).trans
    (Subalgebra.equivOfEq _ _ range_reesToPolynomial)

@[simp]
lemma coe_reesAlgebraEquiv (z : I.ReesAlgebra) :
    (I.reesAlgebraEquiv z : A[X]) = I.reesToPolynomial z := rfl

end Comparison

end Ideal
