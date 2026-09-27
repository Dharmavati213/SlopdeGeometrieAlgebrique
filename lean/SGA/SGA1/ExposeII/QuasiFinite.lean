/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.QuasiFinite.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# SGA 1, Exposé II, II.1.4: étale = quasi-finite + smooth

SGA says this is "trivial from the definition", since the relative dimension of II.1.1 is the
dimension of the fibre. We prove it without dimension theory: locally `S` is étale over
`R[t₁,…,tₙ]`; quasi-finiteness descends along the flat map `R[t₁,…,tₙ] → S` (through the
faithfully flat local homomorphisms of local rings), and a polynomial ring in `n ≥ 1` variables
is quasi-finite at no prime (mathlib), so `n = 0`.
-/

open Algebra TensorProduct

namespace SGA.SGA1.ExposeII

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
  [Algebra R B] [IsScalarTower R A B]

/-- An `R`-linear map `M → N` which becomes a faithfully flat base change stays injective after
tensoring. -/
private lemma rTensor_injective_of_faithfullyFlat [Module.FaithfullyFlat A B] (K : Type*)
    [AddCommGroup K] [Module R K] :
    Function.Injective ((IsScalarTower.toAlgHom R A B).toLinearMap.rTensor K) := by
  have h := Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) (A ⊗[R] K)
  let e := AlgebraTensorModule.cancelBaseChange R A B B K
  have heq : (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor K =
      ((e.restrictScalars R).toLinearMap ∘ₗ
        ((TensorProduct.mk A B (A ⊗[R] K) 1).restrictScalars R)) := by
    ext a k
    simp [e, AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def]
  rw [heq, LinearMap.coe_comp]
  exact (e.restrictScalars R).injective.comp h


/-- Quasi-finiteness at a point descends along flat homomorphisms: if `B` is flat over `A` and
quasi-finite over `R` at `Q`, then `A` is quasi-finite over `R` at `Q ∩ A`. -/
theorem quasiFiniteAt_under_of_flat [Module.Flat A B] (Q : Ideal B) [Q.IsPrime]
    [QuasiFiniteAt R Q] : QuasiFiniteAt R (Q.under A) := by
  set p := Q.under A
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom p Q (algebraMap A B) Ideal.LiesOver.over
  have : Module.Flat A (Localization.AtPrime Q) := .trans A B _
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime Q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _).mpr ‹_›
  have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime Q) :=
    .of_flat_of_isLocalHom
  refine ⟨fun P _ ↦ ?_⟩
  have : Module.Finite P.ResidueField (P.ResidueField ⊗[R] Localization.AtPrime Q) :=
    .of_quasiFinite
  let φ := Algebra.TensorProduct.map (AlgHom.id P.ResidueField P.ResidueField)
    (IsScalarTower.toAlgHom R (Localization.AtPrime p) (Localization.AtPrime Q))
  refine Module.Finite.of_injective φ.toLinearMap ?_
  have h := rTensor_injective_of_faithfullyFlat (R := R) (A := Localization.AtPrime p)
    (B := Localization.AtPrime Q) P.ResidueField
  have heq : ⇑φ.toLinearMap = (TensorProduct.comm R _ _) ∘
      (LinearMap.rTensor P.ResidueField
        (IsScalarTower.toAlgHom R (Localization.AtPrime p) (Localization.AtPrime Q)).toLinearMap) ∘
      (TensorProduct.comm R _ _) := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [φ]
    | add x y hx hy => simp_all
  rw [heq]
  exact (TensorProduct.comm R _ _).injective.comp (h.comp (TensorProduct.comm R _ _).injective)


/-- A polynomial ring in at least one variable is quasi-finite at no prime. -/
theorem not_quasiFiniteAt_mvPolynomial (R : Type*) [CommRing R] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin (n + 1)) R)) [P.IsPrime] : ¬ QuasiFiniteAt R P := by
  intro h
  let e := (MvPolynomial.finSuccEquiv R n).symm
  have : QuasiFiniteAt R (P.comap e.toRingHom) := inferInstance
  have : QuasiFiniteAt (MvPolynomial (Fin n) R) (P.comap e.toRingHom) :=
    QuasiFinite.of_restrictScalars R _ _
  exact Polynomial.not_quasiFiniteAt _ this


/-- II.1.4, affine form: an algebra is étale iff it is smooth and quasi-finite. -/
theorem etale_iff_smooth_and_quasiFinite {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Etale R S ↔ Smooth R S ∧ QuasiFinite R S := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ?_⟩
  rw [← etaleLocus_eq_univ_iff_etale]
  refine Set.eq_univ_iff_forall.mpr fun Q ↦ ?_
  have : IsSmoothAt R Q.asIdeal := by
    have := smoothLocus_eq_univ (R := R) (A := S) ▸ Set.mem_univ Q
    exact this
  obtain ⟨f, hf, n, _, _, _⟩ :=
    IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := Q.asIdeal)
  obtain rfl : n = 0 := by
    by_contra hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hdisj : Disjoint (Submonoid.powers f : Set S) Q.asIdeal :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
    have := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) (Localization.Away f)
      Q.asIdeal Q.2 hdisj
    exact not_quasiFiniteAt_mvPolynomial R m _
      (quasiFiniteAt_under_of_flat (A := MvPolynomial (Fin (m + 1)) R)
        (Q.asIdeal.map (algebraMap S (Localization.Away f))))
  have : Etale R (MvPolynomial (Fin 0) R) := .of_equiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm
  have : Etale R (Localization.Away f) := .comp R (MvPolynomial (Fin 0) R) _
  exact basicOpen_subset_etaleLocus_iff_etale.mpr this hf


section Scheme

open AlgebraicGeometry

/-- II.1.4: a morphism is étale iff it is smooth and locally quasi-finite. -/
theorem etale_iff_smooth_and_locallyQuasiFinite {X Y : Scheme} (f : X ⟶ Y) :
    Etale f ↔ AlgebraicGeometry.Smooth f ∧ LocallyQuasiFinite f := by
  have key (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) :
      (f.appLE U V e).hom.Etale ↔ (f.appLE U V e).hom.Smooth ∧ (f.appLE U V e).hom.QuasiFinite := by
    algebraize [(f.appLE U V e).hom]
    exact etale_iff_smooth_and_quasiFinite
  rw [HasRingHomProperty.iff_appLE (P := @Etale), HasRingHomProperty.iff_appLE (P := @Smooth),
    HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  simp_rw [key]
  exact ⟨fun h ↦ ⟨fun U V e ↦ (h U V e).1, fun U V e ↦ (h U V e).2⟩,
    fun h U V e ↦ ⟨h.1 U V e, h.2 U V e⟩⟩

end Scheme

end SGA.SGA1.ExposeII
