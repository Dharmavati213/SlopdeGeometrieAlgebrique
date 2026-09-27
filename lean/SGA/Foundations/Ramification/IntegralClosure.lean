/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Galois groups acting on integral closures

Let `R` be a Dedekind domain with fraction field `K`, `M/K` a finite separable extension and
`B = integralClosure R M`. Then `B` is a Dedekind domain, finite and flat over `R`, and when `M/K`
is Galois, `Gal(M/K)` is a Galois group for `B/R` in the sense of `IsGaloisGroup`, so that the
ramification theory of `Mathlib.NumberTheory.RamificationInertia.Galois` applies
(Serre, *Local fields*, I §4).

For a tower `K → E → M`, with `C = integralClosure R E`, `integralClosure.algebraOfTower` is the
inclusion `C → B`; `B` is a finite flat `C`-algebra and, when `M/K` is Galois, the subgroup of
`Gal(M/K)` fixing `E` is a Galois group for `B/C` (`integralClosure.isGaloisGroup_of_tower`).
These are not instances, as `K` and `E` cannot be inferred.

Finally, for an algebra `C` integral over `A[1/π]`, `C` is the localization at `π` of the
normalization of `A` in `C` (`integralClosure.isLocalization_powers`).
-/

namespace integralClosure

section Basic

variable (R K M : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Field M] [Algebra K M] [Algebra R M] [IsScalarTower R K M]

include K in
omit [IsDedekindDomain R] in
lemma algebraMap_injective_of_isFractionRing :
    Function.Injective (algebraMap R (integralClosure R M)) := by
  have h : Function.Injective (algebraMap R M) := by
    rw [IsScalarTower.algebraMap_eq R K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective R K)
  rw [IsScalarTower.algebraMap_eq R (integralClosure R M) M, RingHom.coe_comp] at h
  exact h.of_comp

include K in
theorem flat : Module.Flat R (integralClosure R M) := by
  have : Module.IsTorsionFree R (integralClosure R M) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap_injective_of_isFractionRing R K M)
  infer_instance

variable [FiniteDimensional K M]

include K in
theorem isFractionRing_of_finiteDimensional : IsFractionRing (integralClosure R M) M :=
  integralClosure.isFractionRing_of_finite_extension K M

include K in
theorem finite [Algebra.IsSeparable K M] : Module.Finite R (integralClosure R M) :=
  IsIntegralClosure.finite R K M _

include K in
theorem isDedekindDomain' [Algebra.IsSeparable K M] : IsDedekindDomain (integralClosure R M) :=
  integralClosure.isDedekindDomain R K M

include K in
theorem isIntegrallyClosed' : IsIntegrallyClosed (integralClosure R M) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension K

/-- `Gal(M/K)` is a Galois group for `integralClosure R M` over `R`. -/
theorem isGaloisGroup [IsGalois K M] : IsGaloisGroup Gal(M/K) R (integralClosure R M) :=
  have := isFractionRing_of_finiteDimensional R K M
  IsGaloisGroup.of_isFractionRing Gal(M/K) R (integralClosure R M) K M

end Basic

section Tower

variable (R : Type*) [CommRing R] (E M : Type*) [Field E] [Field M] [Algebra E M] [Algebra R E]
  [Algebra R M] [IsScalarTower R E M]

/-- The inclusion `integralClosure R E → integralClosure R M` induced by `E → M`. -/
noncomputable abbrev algebraOfTower : Algebra (integralClosure R E) (integralClosure R M) :=
  ((IsScalarTower.toAlgHom R E M).mapIntegralClosure).toRingHom.toAlgebra

attribute [local instance] algebraOfTower

@[simp]
lemma coe_algebraMap_algebraOfTower (x : integralClosure R E) :
    (algebraMap (integralClosure R E) (integralClosure R M) x : M) = algebraMap E M x :=
  rfl

instance : IsScalarTower R (integralClosure R E) (integralClosure R M) :=
  .of_algebraMap_eq fun r ↦ Subtype.ext (by
    simp [← IsScalarTower.algebraMap_apply])

lemma algebraMap_algebraOfTower_injective :
    Function.Injective (algebraMap (integralClosure R E) (integralClosure R M)) := by
  intro x y h
  have := congrArg (fun z : integralClosure R M ↦ (z : M)) h
  simp only [coe_algebraMap_algebraOfTower] at this
  exact Subtype.ext ((algebraMap E M).injective this)

variable [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

theorem finite_of_tower [Algebra K M] [IsScalarTower R K M] [FiniteDimensional K M]
    [Algebra.IsSeparable K M] :
    Module.Finite (integralClosure R E) (integralClosure R M) :=
  have := finite R K M
  Module.Finite.of_restrictScalars_finite R _ _

theorem flat_of_tower [Algebra K E] [IsScalarTower R K E] [FiniteDimensional K E]
    [Algebra.IsSeparable K E] :
    Module.Flat (integralClosure R E) (integralClosure R M) := by
  have := isDedekindDomain' R K E
  have : Module.IsTorsionFree (integralClosure R E) (integralClosure R M) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap_algebraOfTower_injective R E M)
  infer_instance

/-- For a tower `K → E → M` with `M/K` finite Galois, the subgroup of `Gal(M/K)` fixing `E` is a
Galois group for `integralClosure R M` over `integralClosure R E`. -/
theorem isGaloisGroup_of_tower [Algebra K E] [Algebra K M] [IsScalarTower K E M]
    [IsScalarTower R K E] [IsScalarTower R K M] [FiniteDimensional K M] [IsGalois K M] :
    IsGaloisGroup (fixingSubgroup Gal(M/K) (Set.range (algebraMap E M)))
      (integralClosure R E) (integralClosure R M) := by
  have : FiniteDimensional K E := FiniteDimensional.left K E M
  have := isFractionRing_of_finiteDimensional R K E
  have := isFractionRing_of_finiteDimensional R K M
  have := isIntegrallyClosed' R K E
  have : Algebra.IsIntegral (integralClosure R E) (integralClosure R M) :=
    Algebra.IsIntegral.tower_top R
  have := IsGaloisGroup.of_isScalarTower Gal(M/K) K M E
  have : IsScalarTower (integralClosure R E) (integralClosure R M) M :=
    .of_algebraMap_eq fun _ ↦ rfl
  exact IsGaloisGroup.of_isFractionRing _ (integralClosure R E) (integralClosure R M) E M

end Tower

section Localization

/-- For an algebra `C` integral over `A[1/π]`, `C` is the localization at `π` of the
normalization of `A` in `C`. -/
theorem isLocalization_powers {A : Type*} [CommRing A] (π : A) (Aπ : Type*) [CommRing Aπ]
    [Algebra A Aπ] [IsLocalization.Away π Aπ] (C : Type*) [CommRing C] [Algebra Aπ C]
    [Algebra A C] [IsScalarTower A Aπ C] [Algebra.IsIntegral Aπ C] :
    IsLocalization (Submonoid.powers (algebraMap A (integralClosure A C) π)) C where
  map_units := by
    rintro ⟨_, k, rfl⟩
    change IsUnit (((algebraMap A (integralClosure A C) π ^ k : integralClosure A C)) : C)
    rw [SubmonoidClass.coe_pow]
    change IsUnit (algebraMap A C π ^ k)
    rw [IsScalarTower.algebraMap_apply A Aπ C]
    exact ((IsLocalization.Away.algebraMap_isUnit π).map _).pow k
  surj z := by
    obtain ⟨⟨_, k, rfl⟩, hmz⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := Aπ)
      (Submonoid.powers π) z (Algebra.IsIntegral.isIntegral z)
    refine ⟨⟨⟨π ^ k • z, hmz⟩, ⟨_, k, rfl⟩⟩, ?_⟩
    change z * ((algebraMap A (integralClosure A C) π ^ k : integralClosure A C) : C) = π ^ k • z
    rw [SubmonoidClass.coe_pow, Algebra.smul_def, map_pow, mul_comm]
    rfl
  exists_of_eq h := ⟨1, by simpa using Subtype.ext h⟩

end Localization

end integralClosure
