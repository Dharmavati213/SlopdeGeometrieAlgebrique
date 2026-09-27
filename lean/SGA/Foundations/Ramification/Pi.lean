/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import SGA.Foundations.Ramification.Transport

/-!
# Ramification in finite products

Let `L = Π i, L i` be a finite product of `A`-algebras.

* `IsIntegral.pi`: a family of integral elements is integral;
* `integralClosure.piAlgEquiv`: the integral closure of `A` in `L` is the product of the integral
  closures of `A` in the `L i`;
* `Ideal.ramificationIdx_comap_evalAlgHom`,
  `Ideal.isSeparable_residueField_comap_evalAlgHom_iff`: for a prime `Q` of `L i`, the prime
  `Q × Π_{j ≠ i} L j` of `L` has the same ramification index and residue field extension (its local
  ring is that of `Q`). Every prime of `L` is of this form (`PrimeSpectrum.sigmaToPi_bijective`).
-/

variable {A : Type*} [CommRing A] {ι : Type*} {L : ι → Type*} [∀ i, CommRing (L i)]
  [∀ i, Algebra A (L i)]

open Polynomial

/-- A family of integral elements of a finite product is integral. -/
theorem IsIntegral.pi [Finite ι] {x : Π i, L i} (hx : ∀ i, IsIntegral A (x i)) :
    IsIntegral A x := by
  classical
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single x]
  refine IsIntegral.sum _ fun i _ ↦ ?_
  obtain ⟨p, hp, hpx⟩ := hx i
  refine ⟨X * p, monic_X.mul hp, ?_⟩
  rw [← aeval_def, map_mul, aeval_X]
  ext j
  have h := aeval_algHom_apply (Pi.evalAlgHom A L j) (Pi.single i (x i)) p
  simp only [Pi.evalAlgHom_apply] at h
  rw [Pi.mul_apply, ← h, Pi.zero_apply]
  by_cases hij : j = i
  · subst hij
    rw [Pi.single_eq_same, aeval_def, hpx, mul_zero]
  · rw [Pi.single_eq_of_ne hij, zero_mul]

variable (A L) in
/-- The integral closure of `A` in a finite product is the product of the integral closures. -/
noncomputable def integralClosure.piAlgEquiv [Finite ι] :
    integralClosure A (Π i, L i) ≃ₐ[A] Π i, integralClosure A (L i) where
  toFun x i := ⟨x.1 i, x.2.map (Pi.evalAlgHom A L i)⟩
  invFun y := ⟨fun i ↦ (y i : L i), IsIntegral.pi fun i ↦ (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

namespace Ideal

variable (i : ι) (Q : Ideal (L i)) [Q.IsPrime]

lemma bijective_localAlgHom_evalAlgHom :
    Function.Bijective (Localization.localAlgHom (Q.comap (Pi.evalAlgHom A L i)) Q
      (Pi.evalAlgHom A L i) rfl) :=
  Localization.AtPrime.mapPiEvalRingHom_bijective Q

/-- The prime `Q × Π_{j ≠ i} L j` of `Π L` has the ramification index of `Q`. -/
theorem ramificationIdx_comap_evalAlgHom :
    (Q.comap (Pi.evalAlgHom A L i)).ramificationIdx A = Q.ramificationIdx A :=
  ramificationIdx_comap_of_bijective _ Q (bijective_localAlgHom_evalAlgHom i Q)

/-- The prime `Q × Π_{j ≠ i} L j` of `Π L` has the residue field of `Q`. -/
theorem isSeparable_residueField_comap_evalAlgHom_iff (p : Ideal A) [p.IsPrime]
    [Q.LiesOver p] :
    haveI : (Q.comap (Pi.evalAlgHom A L i)).LiesOver p :=
      ⟨(under_comap_algHom _ Q).trans (over_def Q p).symm |>.symm⟩
    letI := Localization.AtPrime.algebraOfLiesOver p (Q.comap (Pi.evalAlgHom A L i))
    letI := Localization.AtPrime.algebraOfLiesOver p Q
    Algebra.IsSeparable p.ResidueField (Q.comap (Pi.evalAlgHom A L i)).ResidueField ↔
      Algebra.IsSeparable p.ResidueField Q.ResidueField :=
  isSeparable_residueField_comap_iff_of_bijective _ Q (bijective_localAlgHom_evalAlgHom i Q) p

end Ideal
