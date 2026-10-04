/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Smooth.Flat
import SGA.Foundations.Ramification.Pi

/-!
# SGA 1, Exposé X, 3.7: commutative algebra for extending coverings

In the proof of X.3.8 an étale covering of the generic fibre `X_K` of a scheme over a discrete
valuation ring is extended over a neighbourhood of the generic point of the closed fibre: over an
affine open `Spec A` (`A` a normal noetherian domain), with `X_K ∩ Spec A = Spec A[1/t]` and the
covering given by a finite étale `A[1/t]`-algebra `C`, the extension is `Spec B_s`, `B` the
integral closure of `A` in `C`. We prove:

* `finite_integralClosure_of_etale`: the integral closure of a noetherian integrally closed domain
  `A` in a finite étale algebra over its fraction field is finite over `A` (the algebra is a finite
  product of finite separable field extensions);
* `finite_integralClosure_of_etale_away`: the same for a finite étale `A[1/t]`-algebra, `t ≠ 0`;
* `exists_notMem_forall_mem_etaleLocus`: for a finite `A`-algebra `B`, `A` noetherian, étale above
  a prime `P` of `A`, there is `s ∉ P` with `B` étale above `D(s)`.
-/

universe u

open TensorProduct

namespace SGA.SGA1.ExposeX

section Finite

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]

/-- The integral closure of a noetherian integrally closed domain `A` in a finite étale algebra
`L` over its fraction field is a finite `A`-module: `L` is a finite product of finite separable
extensions of `Frac A`, in each of which the integral closure is finite. -/
theorem finite_integralClosure_of_etale (L : Type u) [CommRing L] [Algebra (FractionRing A) L]
    [Algebra A L] [IsScalarTower A (FractionRing A) L] [Module.Finite (FractionRing A) L]
    [Algebra.Etale (FractionRing A) L] : Module.Finite A (integralClosure A L) := by
  classical
  have : IsArtinianRing L := IsArtinianRing.of_finite (FractionRing A) L
  have : IsReduced L := Algebra.FormallyUnramified.isReduced_of_field (FractionRing A) L
  let Φ := ((IsArtinianRing.equivPi L).restrictScalars A).mapIntegralClosure.trans
    (integralClosure.piAlgEquiv A (fun M : MaximalSpectrum L ↦ L ⧸ M.asIdeal))
  have key (M : MaximalSpectrum L) : Module.Finite A (integralClosure A (L ⧸ M.asIdeal)) := by
    let := Ideal.Quotient.field M.asIdeal
    have : Module.Finite (FractionRing A) (L ⧸ M.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ _ M.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have : Algebra.FormallyUnramified (FractionRing A) (L ⧸ M.asIdeal) :=
      Algebra.FormallyUnramified.comp _ L _
    have : Algebra.IsSeparable (FractionRing A) (L ⧸ M.asIdeal) :=
      Algebra.FormallyUnramified.isSeparable _ _
    exact IsIntegralClosure.finite A (FractionRing A) (L ⧸ M.asIdeal)
      (integralClosure A (L ⧸ M.asIdeal))
  have : Module.Finite A (Π M : MaximalSpectrum L, integralClosure A (L ⧸ M.asIdeal)) :=
    inferInstance
  exact Module.Finite.equiv Φ.symm.toLinearEquiv

/-- The integral closure of a noetherian integrally closed domain `A` in a finite étale algebra
`C` over `A[1/t]`, `t ≠ 0`, is a finite `A`-module: it embeds into the integral closure of `A` in
the finite étale `Frac A`-algebra `C ⊗_{A[1/t]} Frac A`. -/
theorem finite_integralClosure_of_etale_away {t : A} (ht : t ≠ 0) (C : Type u) [CommRing C]
    [Algebra A C] [Algebra (Localization.Away t) C] [IsScalarTower A (Localization.Away t) C]
    [Module.Finite (Localization.Away t) C] [Algebra.Etale (Localization.Away t) C] :
    Module.Finite A (integralClosure A C) := by
  have ht' := powers_le_nonZeroDivisors_of_noZeroDivisors ht
  have : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization ht'
  let g : Localization.Away t →+* FractionRing A :=
    IsLocalization.map _ (T := nonZeroDivisors A) (RingHom.id A) ht'
  let : Algebra (Localization.Away t) (FractionRing A) := g.toAlgebra
  have : IsScalarTower A (Localization.Away t) (FractionRing A) :=
    .of_algebraMap_eq fun s ↦ by
      exact (IsLocalization.map_eq (S := Localization.Away t) (Q := FractionRing A)
        (g := RingHom.id A) (T := nonZeroDivisors A) ht' s).symm
  have : IsFractionRing (Localization.Away t) (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers t) _ _
  let L := C ⊗[Localization.Away t] FractionRing A
  let : Algebra (FractionRing A) L := Algebra.TensorProduct.rightAlgebra
  let eL : FractionRing A ⊗[Localization.Away t] C ≃ₐ[FractionRing A] L :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm _ _ _).toRingEquiv) fun _ ↦ rfl
  have : Algebra.Etale (FractionRing A) L := Algebra.Etale.of_equiv eL
  have : Module.Finite (FractionRing A) L := Module.Finite.equiv eL.toLinearEquiv
  have : IsScalarTower A (FractionRing A) L :=
    .of_algebraMap_eq fun s ↦ by
      change algebraMap A C s ⊗ₜ[Localization.Away t] (1 : FractionRing A) =
        (1 : C) ⊗ₜ[Localization.Away t] algebraMap A (FractionRing A) s
      rw [IsScalarTower.algebraMap_apply A (Localization.Away t) C,
        IsScalarTower.algebraMap_apply A (Localization.Away t) (FractionRing A),
        ← mul_one (algebraMap (Localization.Away t) C _), ← Algebra.smul_def,
        TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have hfin := finite_integralClosure_of_etale (A := A) L
  -- `C → L` is injective (`C` is flat over the domain `A[1/t]`)
  have : Module.Flat (Localization.Away t) C := Algebra.Smooth.flat _ _
  have hinj : Function.Injective (algebraMap C L) := by
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := C)
      (Algebra.linearMap (Localization.Away t) (FractionRing A))
      (IsFractionRing.injective (Localization.Away t) (FractionRing A))
    intro x y hxy
    apply (TensorProduct.rid (Localization.Away t) C).symm.injective
    apply this
    change x ⊗ₜ[Localization.Away t] (1 : FractionRing A) =
      y ⊗ₜ[Localization.Away t] (1 : FractionRing A) at hxy
    simpa using hxy
  let φ : integralClosure A C →ₐ[A] integralClosure A L :=
    (IsScalarTower.toAlgHom A C L).mapIntegralClosure
  have hφ : Function.Injective φ := fun x y hxy ↦
    Subtype.ext (hinj (congrArg Subtype.val hxy))
  exact Module.Finite.of_injective φ.toLinearMap hφ

end Finite

section Locus

variable {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B]

/-- Étaleness spreads from a prime to a basic open neighbourhood, for finite algebras over a
noetherian ring: if `B` is finite over `A` and étale at every prime above the prime `P` of `A`,
there is `s ∉ P` such that `B` is étale at every prime above `D(s)`. -/
theorem exists_notMem_forall_mem_etaleLocus (P : Ideal A) [P.IsPrime]
    (h : ∀ q : PrimeSpectrum B, q.asIdeal.comap (algebraMap A B) = P →
      q ∈ Algebra.etaleLocus A B) :
    ∃ s ∉ P, ∀ q : PrimeSpectrum B, algebraMap A B s ∉ q.asIdeal →
      q ∈ Algebra.etaleLocus A B := by
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let Z : Set (PrimeSpectrum B) := (Algebra.etaleLocus A B)ᶜ
  have hZ : IsClosed Z := (Algebra.isOpen_etaleLocus).isClosed_compl
  have hint : (algebraMap A B).IsIntegral := Algebra.IsIntegral.isIntegral
  have hW : IsClosed (PrimeSpectrum.comap (algebraMap A B) '' Z) :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hint Z hZ
  have hP : (⟨P, inferInstance⟩ : PrimeSpectrum A) ∉
      PrimeSpectrum.comap (algebraMap A B) '' Z := by
    rintro ⟨q, hqZ, hq⟩
    exact hqZ (h q (congrArg PrimeSpectrum.asIdeal hq))
  obtain ⟨_, ⟨s, rfl⟩, hPs, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_compl hP) hW.isOpen_compl
  refine ⟨s, hPs, fun q hq ↦ ?_⟩
  by_contra hqZ
  exact hsub (show PrimeSpectrum.comap (algebraMap A B) q ∈ PrimeSpectrum.basicOpen s from hq)
    ⟨q, hqZ, rfl⟩

end Locus

end SGA.SGA1.ExposeX
