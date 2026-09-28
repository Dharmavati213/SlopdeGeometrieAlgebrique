/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Primitive elements for finite extensions of domains

For a finite extension of domains `R ⊆ B` with `Frac R` of characteristic `0`, there are `f ∈ B`
and `g ≠ 0` in `R` with `g • B ⊆ R[f]` (`exists_smul_mem_adjoin`, from the primitive element
theorem), and, for `R` integrally closed, the minimal polynomial `P` of any `f ∈ B` satisfies a
Bézout relation `a P + b P' = h ∈ R ∖ 0` (`exists_bezout_minpoly`). Used in the proof of XII.2.4
(`Connected.lean`), for a Noether normalization `ℂ[z₁, …, zₙ] ⊆ B`.
-/

open Polynomial IntermediateField

namespace SGA.SGA1.ExposeXII

attribute [local instance] FractionRing.liftAlgebra

variable (R B : Type*) [CommRing R] [IsDomain R] [CommRing B] [IsDomain B] [Algebra R B]
  [FaithfulSMul R B] [Module.Finite R B] [CharZero (FractionRing R)]

/-- Primitive element for a finite extension of domains `R ⊆ B` in characteristic `0`: there are
`f ∈ B` and `g ≠ 0` in `R` with `g • B ⊆ R[f]`. -/
theorem exists_smul_mem_adjoin :
    ∃ (f : B) (g : R), g ≠ 0 ∧ ∀ b : B, g • b ∈ Algebra.adjoin R {f} := by
  classical
  let K := FractionRing R
  let L := FractionRing B
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := B) α
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcint : IsIntegral R c := Algebra.IsIntegral.isIntegral c
  have hne := Ideal.comap_ne_bot_of_integral_mem hc0 (Ideal.mem_span_singleton_self c) hcint
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hr
  set f : B := b * e
  set f' : L := algebraMap B L f
  have hcL : algebraMap B L c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hc0
  have hrK : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr0
  have hf' : f' = algebraMap K L (algebraMap R K r) *
      (algebraMap B L b / algebraMap B L c) := by
    rw [← IsScalarTower.algebraMap_apply R K L r, IsScalarTower.algebraMap_apply R B L r, ← he,
      mul_div_assoc', eq_div_iff hcL]
    simp only [f', f, map_mul]
    ring
  have htop : K⟮f'⟯ = ⊤ := by
    refine top_le_iff.mp (hα ▸ IntermediateField.adjoin_simple_le_iff.mpr ?_)
    have : algebraMap B L b / algebraMap B L c =
        (algebraMap K L (algebraMap R K r))⁻¹ * f' := by
      rw [hf', ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero_iff _ (algebraMap K L).injective).mpr
        hrK), one_mul]
    rw [this, ← map_inv₀]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.mem_adjoin_simple_self K f')
  -- every element of `B` becomes an `R`-polynomial in `f` after multiplying by some `β ≠ 0`
  have key (x : B) : ∃ β ∈ nonZeroDivisors R, β • x ∈ Algebra.adjoin R {f} := by
    have hx : algebraMap B L x ∈ (K⟮f'⟯).toSubalgebra := by rw [htop]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic f'), Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨p, hp⟩ := hx
    obtain ⟨β, hβ, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
    refine ⟨β, hβ, ?_⟩
    have h1 : aeval f' (IsLocalization.integerNormalization (nonZeroDivisors R) p) =
        β • algebraMap B L x := by
      rw [← aeval_map_algebraMap K, hq, ← algebraMap_smul K β p, map_smul,
        show (aeval f') p = algebraMap B L x from hp, algebraMap_smul]
    have h2 : algebraMap B L (aeval f (IsLocalization.integerNormalization (nonZeroDivisors R) p)) =
        algebraMap B L (β • x) := by
      rw [← aeval_algebraMap_apply, h1, Algebra.smul_def, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply]
    rw [← IsFractionRing.injective B L h2]
    exact Polynomial.aeval_mem_adjoin_singleton R f
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := B)
  choose β hβ hβs using fun i ↦ key (s i)
  refine ⟨f, ∏ i, β i, Finset.prod_ne_zero_iff.mpr fun i _ ↦ nonZeroDivisors.ne_zero (hβ i),
    fun x ↦ ?_⟩
  have hx : x ∈ Submodule.span R (Set.range s) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
    exact Subalgebra.smul_mem _ (hβs i) _
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul a y _ hy => rw [smul_comm]; exact Subalgebra.smul_mem _ hy _

/-- The minimal polynomial `P` of an element `f ∈ B` over an integrally closed domain `R` of
characteristic `0` is separable: `a P + b P' = h` for some `a b ∈ R[T]` and `h ≠ 0` in `R`. -/
theorem exists_bezout_minpoly [IsIntegrallyClosed R] (f : B) :
    ∃ (a b : R[X]) (h : R), h ≠ 0 ∧ a * minpoly R f + b * derivative (minpoly R f) = C h := by
  let K := FractionRing R
  let L := FractionRing B
  have hint : IsIntegral R f := Algebra.IsIntegral.isIntegral f
  have hmin : minpoly K (algebraMap B L f) = (minpoly R f).map (algebraMap R K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  have hsep : (minpoly K (algebraMap B L f)).Separable :=
    Algebra.IsSeparable.isSeparable K (algebraMap B L f)
  obtain ⟨u, v, huv⟩ := hsep
  rw [hmin, derivative_map] at huv
  obtain ⟨βu, hβu, hu⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) u
  obtain ⟨βv, hβv, hv⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) v
  set u' := IsLocalization.integerNormalization (nonZeroDivisors R) u
  set v' := IsLocalization.integerNormalization (nonZeroDivisors R) v
  refine ⟨C βv * u', C βu * v', βu * βv, mul_ne_zero (nonZeroDivisors.ne_zero hβu)
    (nonZeroDivisors.ne_zero hβv), Polynomial.map_injective _ (IsFractionRing.injective R K) ?_⟩
  have hu' : u'.map (algebraMap R K) = C (algebraMap R K βu) * u := by
    rw [hu, Algebra.smul_def]; rfl
  have hv' : v'.map (algebraMap R K) = C (algebraMap R K βv) * v := by
    rw [hv, Algebra.smul_def]; rfl
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hu', hv', map_mul]
  linear_combination (C (algebraMap R K βu) * C (algebraMap R K βv)) * huv

end SGA.SGA1.ExposeXII
