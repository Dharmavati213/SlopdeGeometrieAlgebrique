/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Flat.TorsionFree
import SGA.SGA1.ExposeXII.RiemannExtensionAlgebra

/-!
# SGA 1, Exposé XII, 5.1 for curves: the integral closure of a curve in a covering of an open part

Let `B` be a Dedekind domain of characteristic `0`, `h ∈ B` nonzero, and `C'` a domain which is a
finite flat `B[1/h]`-algebra and is integrally closed (e.g. a connected finite étale
`B[1/h]`-algebra, `B` normal). Then the integral closure `C` of `B` in `C'` is

* the integral closure of `B` in the fraction field `L` of `C'`
  (`RiemannExtension.isIntegralClosure_fractionRing`), and `L` is a finite separable extension of
  the fraction field of `B`;
* hence finite over `B` (`RiemannExtension.finite_integralClosure`) and a Dedekind domain
  (`RiemannExtension.isDedekindDomain_integralClosure`), by mathlib's `IsIntegralClosure.finite`
  and `IsIntegralClosure.isDedekindDomain` (the trace form argument);
* flat over `B` (`RiemannExtension.flat_integralClosure`), being torsion free over a Dedekind
  domain;
* and `C[1/h] = C'` (`RiemannExtension.isLocalization_away_integralClosure`,
  `RiemannExtensionAlgebra.lean`).

Geometrically: `Spec C` is the normalization of the curve `Spec B` in the covering `Spec C'` of the
open part `{h ≠ 0}`; it is a normal curve, finite and flat over `Spec B`, which agrees with `C'`
over `{h ≠ 0}`. Whether it is étale over the points of `{h = 0}` is decided by counting points
(`Points.etale_of_forall_card_fiber`).

References: Serre, *Corps locaux*, I §4 (integral closure of a Dedekind domain in a finite separable
extension); Stacks 0AUW (flat = torsion free over a Dedekind domain).
-/

noncomputable section

open Module

namespace SGA.SGA1.ExposeXII

namespace RiemannExtension

variable {B : Type*} [CommRing B] [IsDomain B] {h : B} (hh : h ≠ 0)
  {C' : Type*} [CommRing C'] [IsDomain C'] [Algebra B C'] [Algebra (Localization.Away h) C']
  [IsScalarTower B (Localization.Away h) C']

include hh

/-- `B[1/h]` is a domain (`h ≠ 0`). -/
lemma isDomain_away : IsDomain (Localization.Away h) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hh)

/-- `B → C'` is injective when `C'` is a nonzero flat `B[1/h]`-algebra, `h ≠ 0`. -/
lemma injective_algebraMap_of_flat [Module.Flat (Localization.Away h) C'] :
    Function.Injective (algebraMap B C') := by
  have h₁ : Function.Injective (algebraMap B (Localization.Away h)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hh)
  have : IsDomain (Localization.Away h) := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hh)
  have h₂ : Function.Injective (algebraMap (Localization.Away h) C') :=
    Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance
  rw [IsScalarTower.algebraMap_eq B (Localization.Away h) C']
  exact h₂.comp h₁

omit [IsDomain B] [IsDomain C'] hh in
/-- If `C'` is integrally closed, the integral closure of `B` in `C'` is the integral closure of
`B` in the fraction field of `C'`. -/
theorem isIntegralClosure_fractionRing [IsIntegrallyClosed C'] :
    IsIntegralClosure (integralClosure B C') B (FractionRing C') := by
  refine ⟨?_, fun {x} ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · rw [IsScalarTower.algebraMap_eq (integralClosure B C') C' (FractionRing C')]
    exact (IsFractionRing.injective C' (FractionRing C')).comp Subtype.val_injective
  · obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := C'))
    have hy : IsIntegral B y :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom B C' (FractionRing C'))
        (IsFractionRing.injective C' (FractionRing C'))).mp hx
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    rw [IsScalarTower.algebraMap_apply (integralClosure B C') C' (FractionRing C')]
    exact y.2.map (IsScalarTower.toAlgHom B C' (FractionRing C'))

section FractionField

variable [Module.Finite (Localization.Away h) C'] [Module.Flat (Localization.Away h) C']

attribute [local instance] FractionRing.liftAlgebra

omit [Algebra B C'] [IsScalarTower B (Localization.Away h) C']
  [Module.Finite (Localization.Away h) C'] in
/-- `B[1/h] → Frac C'` is injective (`h ≠ 0`, `C'` a flat `B[1/h]`-domain). -/
lemma faithfulSMul_localization_fractionRing :
    FaithfulSMul (Localization.Away h) (FractionRing C') := by
  have : IsDomain (Localization.Away h) := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hh)
  rw [faithfulSMul_iff_algebraMap_injective,
    IsScalarTower.algebraMap_eq (Localization.Away h) C' (FractionRing C')]
  exact (IsFractionRing.injective C' (FractionRing C')).comp
    (Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance)

/-- The fraction field of `B[1/h]` is a fraction field of `B` (`h ≠ 0`). -/
lemma isFractionRing_fractionRing_localization :
    IsFractionRing B (FractionRing (Localization.Away h)) := by
  set K := FractionRing (Localization.Away h)
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hh
  have : IsDomain (Localization.Away h) := IsLocalization.isDomain_localization hle
  have hK : Function.Injective (algebraMap (Localization.Away h) K) :=
    IsFractionRing.injective (Localization.Away h) K
  have hinj : Function.Injective (algebraMap B K) := by
    rw [IsScalarTower.algebraMap_eq B (Localization.Away h) K]
    exact hK.comp (IsLocalization.injective (Localization.Away h) hle)
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field B K fun z ↦ ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Localization.Away h) z
  obtain ⟨n, a₀, ha⟩ := IsLocalization.Away.surj h a
  obtain ⟨m, b₀, hb'⟩ := IsLocalization.Away.surj h b
  refine ⟨a₀ * h ^ m, b₀ * h ^ n, ?_⟩
  set H := algebraMap B K h
  have hH : H ≠ 0 := (map_ne_zero_iff _ hinj).mpr hh
  have e₁ : algebraMap B K a₀ = algebraMap (Localization.Away h) K a * H ^ n := by
    rw [IsScalarTower.algebraMap_apply B (Localization.Away h) K, ← ha, map_mul, map_pow,
      ← IsScalarTower.algebraMap_apply]
  have e₂ : algebraMap B K b₀ = algebraMap (Localization.Away h) K b * H ^ m := by
    rw [IsScalarTower.algebraMap_apply B (Localization.Away h) K, ← hb', map_mul, map_pow,
      ← IsScalarTower.algebraMap_apply]
  have hb0 : algebraMap (Localization.Away h) K b ≠ 0 :=
    (map_ne_zero_iff _ hK).mpr (nonZeroDivisors.ne_zero hb)
  rw [map_mul, map_mul, map_pow, map_pow, e₁, e₂,
    div_eq_div_iff hb0 (mul_ne_zero (mul_ne_zero hb0 (pow_ne_zero _ hH)) (pow_ne_zero _ hH))]
  ring

variable [CharZero B] [IsIntegrallyClosed C']

/-- The setting of mathlib's integral closure theorems: with `K = Frac B[1/h]` (a fraction field
of `B`) and `L = Frac C'`, `L` is a finite separable extension of `K` and the integral closure of
`B` in `C'` is the integral closure of `B` in `L`. -/
lemma integralClosure_setting :
    letI := isDomain_away hh
    letI : FaithfulSMul (Localization.Away h) (FractionRing C') :=
      faithfulSMul_localization_fractionRing hh
    IsFractionRing B (FractionRing (Localization.Away h)) ∧
      IsScalarTower B (FractionRing (Localization.Away h)) (FractionRing C') ∧
      FiniteDimensional (FractionRing (Localization.Away h)) (FractionRing C') ∧
      Algebra.IsSeparable (FractionRing (Localization.Away h)) (FractionRing C') ∧
      IsIntegralClosure (integralClosure B C') B (FractionRing C') := by
  have : FaithfulSMul (Localization.Away h) (FractionRing C') :=
    faithfulSMul_localization_fractionRing hh
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hh
  have : IsDomain (Localization.Away h) := IsLocalization.isDomain_localization hle
  set K := FractionRing (Localization.Away h)
  set L := FractionRing C'
  have hfr := isFractionRing_fractionRing_localization hh
  have hst : IsScalarTower B K L := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply B (Localization.Away h) K,
      ← IsScalarTower.algebraMap_apply (Localization.Away h) K L,
      ← IsScalarTower.algebraMap_apply B (Localization.Away h) L]
  have hfd : FiniteDimensional K L := inferInstance
  have : CharZero K := charZero_of_injective_ringHom
    (f := algebraMap B K) (IsFractionRing.injective B K)
  have hsep : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨hfr, hst, hfd, hsep, isIntegralClosure_fractionRing⟩

/-- **Finiteness of the normalization** (Noether): for `B` a noetherian integrally closed domain
of characteristic `0`, `h ≠ 0`, and `C'` an integrally closed domain finite and flat over
`B[1/h]`, the integral closure of `B` in `C'` is a finite `B`-module. -/
theorem finite_integralClosure [IsIntegrallyClosed B] [IsNoetherianRing B] :
    Module.Finite B (integralClosure B C') := by
  have := isDomain_away hh
  have : FaithfulSMul (Localization.Away h) (FractionRing C') :=
    faithfulSMul_localization_fractionRing hh
  obtain ⟨_, _, _, _, _⟩ := integralClosure_setting (C' := C') hh
  exact IsIntegralClosure.finite B (FractionRing (Localization.Away h)) (FractionRing C')
    (integralClosure B C')

omit [IsDomain B] in
/-- **The normalization is a Dedekind domain**: for `B` a Dedekind domain of characteristic `0`,
`h ≠ 0`, and `C'` an integrally closed domain finite and flat over `B[1/h]`, the integral closure
of `B` in `C'` is a Dedekind domain. -/
theorem isDedekindDomain_integralClosure [IsDedekindDomain B] :
    IsDedekindDomain (integralClosure B C') := by
  have := isDomain_away hh
  have : FaithfulSMul (Localization.Away h) (FractionRing C') :=
    faithfulSMul_localization_fractionRing hh
  obtain ⟨_, _, _, _, _⟩ := integralClosure_setting (C' := C') hh
  exact IsIntegralClosure.isDedekindDomain B (FractionRing (Localization.Away h))
    (FractionRing C') (integralClosure B C')

omit [CharZero B] [IsIntegrallyClosed C'] [Module.Finite (Localization.Away h) C'] in
/-- `B` injects into the integral closure of `B` in `C'` (`h ≠ 0`, `C'` a flat `B[1/h]`-domain). -/
lemma injective_algebraMap_integralClosure :
    Function.Injective (algebraMap B (integralClosure B C')) := fun _ _ hxy ↦
  injective_algebraMap_of_flat hh (congrArg Subtype.val hxy)

omit [IsDomain B] [CharZero B] [IsIntegrallyClosed C'] [Module.Finite (Localization.Away h) C'] in
/-- **The normalization is flat**: over a Dedekind domain `B`, the integral closure of `B` in a
flat `B[1/h]`-domain `C'` (`h ≠ 0`) is torsion free, hence flat. -/
theorem flat_integralClosure [IsDedekindDomain B] : Module.Flat B (integralClosure B C') := by
  have : Module.IsTorsionFree B (integralClosure B C') :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (injective_algebraMap_integralClosure hh)
  infer_instance

end FractionField

end RiemannExtension

end SGA.SGA1.ExposeXII
