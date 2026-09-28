/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import SGA.Foundations.HenselianFiniteEtale
import SGA.Foundations.Ramification.Inertia

/-!
# Ramification over a henselian local ring

* `HenselianLocalRing.eq_of_liesOver`: a finite free algebra over a henselian local ring `A`
  which is a domain has at most one prime over the maximal ideal of `A` (Stacks 04GG (10): it is
  local). The proof lifts a nontrivial idempotent of the fibre `k ⊗_A T`.
* `Ideal.stabilizer_eq_top_of_henselian`, `Ideal.inertia_eq_top_of_isSepClosed`: if `T/A` is
  Galois with group `G`, the decomposition group of the prime over the maximal ideal is `G`, and
  if moreover the residue field of `A` is separably closed (`A` strictly henselian), so is the
  inertia group (Serre, *Local fields*, I §7; SGA 1 XIII 2.0.1).
-/

universe u

open IsLocalRing TensorProduct

namespace HenselianLocalRing

variable {A : Type u} [CommRing A] [HenselianLocalRing A] {T : Type*} [CommRing T] [Algebra A T]
  [Module.Finite A T] [Module.Free A T]

/-- The map `k ⊗_A T → T/Q` for a prime `Q` of `T` over the maximal ideal of `A`. -/
noncomputable def fibreToQuotient (Q : Ideal T) [Q.LiesOver (maximalIdeal A)] :
    ResidueField A ⊗[A] T →ₐ[A] T ⧸ Q :=
  Algebra.TensorProduct.lift
    (Ideal.quotientMapₐ Q (Algebra.ofId A T) (Ideal.over_def Q (maximalIdeal A)).le)
    (Ideal.Quotient.mkₐ A Q) fun _ _ ↦ Commute.all _ _

omit [Module.Finite A T] [Module.Free A T] in
lemma fibreToQuotient_tmul_one (Q : Ideal T) [Q.LiesOver (maximalIdeal A)] (t : T) :
    fibreToQuotient (A := A) Q (1 ⊗ₜ t) = Ideal.Quotient.mk Q t := by
  unfold fibreToQuotient
  erw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

/-- A domain finite and free over a henselian local ring has at most one prime over the maximal
ideal (Stacks 04GG (10)). -/
theorem eq_of_liesOver [IsDomain T] (Q₁ Q₂ : Ideal T) [Q₁.IsPrime] [Q₂.IsPrime]
    [Q₁.LiesOver (maximalIdeal A)] [Q₂.LiesOver (maximalIdeal A)] : Q₁ = Q₂ := by
  by_contra hne
  have : IsArtinianRing (ResidueField A ⊗[A] T) := IsArtinianRing.of_finite (ResidueField A) _
  have hmem (Q : Ideal T) [Q.IsPrime] [Q.LiesOver (maximalIdeal A)] (t : T) :
      (1 ⊗ₜ t : ResidueField A ⊗[A] T) ∈ RingHom.ker (fibreToQuotient (A := A) Q) ↔ t ∈ Q := by
    rw [RingHom.mem_ker, fibreToQuotient_tmul_one, Ideal.Quotient.eq_zero_iff_mem]
  have hK : RingHom.ker (fibreToQuotient (A := A) Q₁) ≠
      RingHom.ker (fibreToQuotient (A := A) Q₂) := by
    intro h
    apply hne
    ext t
    rw [← hmem Q₁, ← hmem Q₂, h]
  have := RingHom.ker_isPrime (fibreToQuotient (A := A) Q₁)
  have h₂ := RingHom.ker_isPrime (fibreToQuotient (A := A) Q₂)
  obtain ⟨e₀, he₀₁, he₀, he₀₂⟩ :=
    IsArtinianRing.exists_not_mem_forall_mem_of_ne (RingHom.ker (fibreToQuotient (A := A) Q₁))
  have he₀₂' := he₀₂ _ h₂ hK.symm
  obtain ⟨e, ⟨he, hee₀⟩, -⟩ := existsUnique_isIdempotentElem_lift (T := T) he₀
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp he with rfl | rfl
  · rw [TensorProduct.tmul_zero] at hee₀
    exact he₀₁ (hee₀ ▸ Ideal.zero_mem _)
  · rw [← Algebra.TensorProduct.one_def] at hee₀
    exact h₂.ne_top ((Ideal.eq_top_iff_one _).mpr (hee₀ ▸ he₀₂'))

end HenselianLocalRing

namespace Ideal

variable {A : Type u} [CommRing A] [HenselianLocalRing A] {B : Type*} [CommRing B] [IsDomain B]
  [Algebra A B] [Module.Finite A B] [Module.Free A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

open scoped Pointwise

omit [Finite G] in
/-- Over a henselian local ring, the decomposition group of the prime over the maximal ideal is
the whole Galois group. -/
theorem stabilizer_eq_top_of_henselian (P : Ideal B) [P.IsPrime] [P.LiesOver (maximalIdeal A)] :
    MulAction.stabilizer G P = ⊤ := by
  refine eq_top_iff.mpr fun g _ ↦ ?_
  have : (g • P).IsPrime := Ideal.map_isPrime_of_equiv (MulSemiringAction.toRingEquiv G B g)
  exact HenselianLocalRing.eq_of_liesOver (A := A) (g • P) P

/-- The residue field of a local ring is that of its maximal ideal. -/
noncomputable def _root_.IsLocalRing.residueFieldEquivResidueFieldMaximalIdeal (A : Type*)
    [CommRing A] [IsLocalRing A] : IsLocalRing.ResidueField A ≃+* (maximalIdeal A).ResidueField :=
  RingEquiv.ofBijective (algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField)
    (maximalIdeal A).bijective_algebraMap_quotient_residueField

/-- Over a strictly henselian local ring (henselian with separably closed residue field), the
inertia group of the prime over the maximal ideal is the whole Galois group (SGA 1 XIII 2.0.1). -/
theorem inertia_eq_top_of_isSepClosed [IsDomain A] [Module.Flat A B]
    [IsSepClosed (IsLocalRing.ResidueField A)] (P : Ideal B) [P.IsPrime]
    [P.LiesOver (maximalIdeal A)] :
    P.inertia G = ⊤ := by
  have : IsSepClosed (maximalIdeal A).ResidueField :=
    IsSepClosed.of_ringEquiv (IsLocalRing.residueFieldEquivResidueFieldMaximalIdeal A)
  let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal A) P
  have h := card_stabilizer_eq_card_inertia_mul_finSepDegree (G := G) (maximalIdeal A) P
  rw [stabilizer_eq_top_of_henselian (A := A) P, IsPurelyInseparable.finSepDegree_eq_one, mul_one,
    Subgroup.card_top] at h
  exact (Subgroup.card_eq_iff_eq_top _).mp h.symm

end Ideal
