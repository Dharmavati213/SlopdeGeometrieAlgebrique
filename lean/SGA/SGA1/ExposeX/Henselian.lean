/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.HenselianFiniteEtale
import SGA.Foundations.Formal.FiniteEtaleSpec
import SGA.SGA1.ExposeIX.CompleteLocal
import SGA.SGA1.ExposeX.EtaleCoverings

/-!
# SGA 1, Exposé X: étale coverings over a henselian local ring

Before X.2.2, SGA uses the "more elementary" isomorphism `π₁(k) ≅ π₁(Y)` for `Y` the spectrum of
a complete (more generally, henselian) local ring `A` with residue field `k`: reduction modulo
the maximal ideal is an equivalence from the finite étale `A`-algebras to the finite étale
`k`-algebras (EGA IV 18.5). The algebra is in `SGA.Foundations.HenselianLifting` and
`SGA.Foundations.HenselianFiniteEtale` (faithfulness and essential surjectivity over any local
ring, fullness over a henselian one); this file keeps the names under which it was first proved
here, as aliases, and adds:

* `isEquivalence_pullback_spec_residueField`: for `A` henselian, `Y' ↦ Y' ×_A k` is an
  equivalence from the étale coverings of `Spec A` to those of `Spec k`;
* `bijective_map_spec_residueField`, `bijective_map_spec_residueField_of_isAdicComplete`: the
  isomorphism `π₁(Spec k) ≅ π₁(Spec A)` used before X.2.2, for `A` henselian, in particular
  complete;
* `rootsEquivResidueRoots`: the points of a monogenic étale covering `A[x]/(f)` over a henselian
  `A` are those of its reduction.
-/

open Polynomial IsLocalRing TensorProduct CategoryTheory AlgebraicGeometry

universe u

namespace SGA.SGA1.ExposeX

/-- An idempotent in the Jacobson radical is zero (`IsIdempotentElem.eq_zero_of_mem_jacobson`). -/
alias eq_zero_of_isIdempotentElem_of_mem_jacobson := IsIdempotentElem.eq_zero_of_mem_jacobson

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-- Two `A`-algebra maps from an unramified `A`-algebra `B` to `C` that agree modulo an ideal
contained in the Jacobson radical of `C` are equal
(`Algebra.FormallyUnramified.algHom_ext_of_sub_mem_jacobson`). -/
theorem algHom_ext_of_sub_mem_jacobson [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]
    {J : Ideal C} (hJ : J ≤ Ideal.jacobson ⊥) (f g : B →ₐ[A] C) (h : ∀ b, f b - g b ∈ J) :
    f = g :=
  Algebra.FormallyUnramified.algHom_ext_of_sub_mem_jacobson hJ h

/-- For `C` finite over a local ring `A`, `𝔪_A C` lies in the Jacobson radical
(`IsLocalRing.map_maximalIdeal_le_jacobson`). -/
theorem map_maximalIdeal_le_jacobson [IsLocalRing A] [Module.Finite A C] :
    (maximalIdeal A).map (algebraMap A C) ≤ Ideal.jacobson ⊥ :=
  IsLocalRing.map_maximalIdeal_le_jacobson

/-- Two `A`-algebra maps from an unramified `A`-algebra to a finite `A`-algebra, `A` local, that
agree modulo the maximal ideal of `A` are equal. -/
theorem algHom_ext_of_sub_mem_map_maximalIdeal [IsLocalRing A] [Algebra.FormallyUnramified A B]
    [Algebra.EssFiniteType A B] [Module.Finite A C] (f g : B →ₐ[A] C)
    (h : ∀ b, f b - g b ∈ (maximalIdeal A).map (algebraMap A C)) : f = g :=
  algHom_ext_of_sub_mem_jacobson map_maximalIdeal_le_jacobson f g h

/-- Reduction modulo the maximal ideal is faithful on finite étale algebras over any local ring
(`IsLocalRing.faithful_baseChange_residueField`). -/
theorem faithful_baseChange_residueField (A : Type u) [CommRing A] [IsLocalRing A] :
    (CommAlgCat.FiniteEtale.baseChange.{u, u} A (ResidueField A)).Faithful :=
  inferInstance

/-- Every finite separable extension of the residue field of a local ring `A` is the reduction of
a finite étale `A`-algebra (`IsLocalRing.exists_finite_etale_lift_of_isSeparable`). -/
alias exists_etale_lift_of_isSeparable := IsLocalRing.exists_finite_etale_lift_of_isSeparable

/-- Every finite étale algebra over the residue field of a local ring `A` is the reduction of a
finite étale `A`-algebra (`IsLocalRing.exists_finite_etale_lift`). -/
alias exists_etale_lift := IsLocalRing.exists_finite_etale_lift

/-- Reduction modulo the maximal ideal is essentially surjective on finite étale algebras over any
local ring (`IsLocalRing.essSurj_baseChange_residueField`). -/
theorem essSurj_baseChange_residueField (A : Type u) [CommRing A] [IsLocalRing A] :
    (CommAlgCat.FiniteEtale.baseChange.{u, u} A (ResidueField A)).EssSurj :=
  inferInstance

/-- Over a henselian local ring `A`, reduction modulo the maximal ideal is an equivalence from
finite étale `A`-algebras to finite étale algebras over the residue field (EGA IV 18.5;
`HenselianLocalRing.isEquivalence_baseChange_residueField`). -/
theorem isEquivalence_baseChange_residueField (A : Type u) [CommRing A] [HenselianLocalRing A] :
    (CommAlgCat.FiniteEtale.baseChange.{u, u} A (ResidueField A)).IsEquivalence :=
  inferInstance

/-- Existence part of `algHomEquivResidue` (`HenselianLocalRing.exists_algHom_lift`). -/
alias exists_lift_of_etale := HenselianLocalRing.exists_algHom_lift

/-- Stacks 04GG (8): for `S` étale over a henselian local ring `A`, reduction modulo `𝔪_A` is a
bijection `(S →ₐ[A] A) ≃ (S →ₐ[A] k)` (`HenselianLocalRing.algHomEquivResidueField`). -/
noncomputable abbrev algHomEquivResidue (A S : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing S] [Algebra A S] [Algebra.Etale A S] :
    (S →ₐ[A] A) ≃ (S →ₐ[A] ResidueField A) :=
  HenselianLocalRing.algHomEquivResidueField A S A

section Scheme

/-- For a henselian local ring `A` with residue field `k`, `Y' ↦ Y' ×_{Spec A} Spec k` is an
equivalence from the étale coverings of `Spec A` to those of `Spec k` (the geometric form of
`isEquivalence_baseChange_residueField`). -/
theorem isEquivalence_pullback_spec_residueField (A : Type u) [CommRing A] [HenselianLocalRing A] :
    (FEt.pullback (Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField A))))).IsEquivalence :=
  have : (CommAlgCat.FiniteEtale.baseChange.{u, u} (CommRingCat.of A)
      (CommRingCat.of (ResidueField A))).IsEquivalence :=
    HenselianLocalRing.isEquivalence_baseChange_residueField A
  Scheme.FiniteEtale.isEquivalence_pullback_spec (CommRingCat.of A)
    (CommRingCat.of (ResidueField A))

/-- The isomorphism `π₁(Spec k) ≅ π₁(Spec A)` used before X.2.2: for `A` henselian local with
residue field `k` and every geometric point `t` of `Spec k`, `π₁(Spec k, t) → π₁(Spec A, t)` is
bijective (V.6.10). -/
theorem bijective_map_spec_residueField (A : Type u) [CommRing A] [HenselianLocalRing A]
    (Ω : Type u) [Field Ω] (t : Spec (.of Ω) ⟶ Spec (.of (ResidueField A))) :
    Function.Bijective (ExposeV.etaleFundamentalGroup.map Ω
      (Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField A)))) t) :=
  have := isEquivalence_pullback_spec_residueField A
  ExposeV.autMap_bijective _ _

/-- The isomorphism `π₁(Spec k) ≅ π₁(Y)` used before X.2.2, for `Y = Spec A` with `A` a complete
local ring (complete local rings are henselian, `ExposeIX.henselianLocalRing_of_isAdicComplete`;
the noetherian hypothesis of SGA is not needed). -/
theorem bijective_map_spec_residueField_of_isAdicComplete (A : Type u) [CommRing A]
    [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] (Ω : Type u) [Field Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of (ResidueField A))) :
    Function.Bijective (ExposeV.etaleFundamentalGroup.map Ω
      (Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField A)))) t) :=
  have := ExposeIX.henselianLocalRing_of_isAdicComplete A
  bijective_map_spec_residueField A Ω t

end Scheme

section Roots

lemma aeval_residue [IsLocalRing A] (f : A[X]) (a : A) :
    aeval (residue A a) f = residue A (f.eval a) := by
  rw [← ResidueField.algebraMap_eq, aeval_algebraMap_apply, coe_aeval_eq_eval]

lemma aeval_residue_eq_zero [IsLocalRing A] {f : A[X]} {a : A} (ha : f.IsRoot a) :
    aeval (residue A a) f = 0 := by
  rw [aeval_residue, ha.eq_zero, map_zero]

variable [HenselianLocalRing A]

/-- For a monic `f` whose derivative is invertible modulo `f` (so that `A[x]/(f)` is a finite
étale covering of `A`), every root of `f` in the residue field lifts to a unique root in `A`:
the points of `A[x]/(f)` over `A` are those of its reduction over `k`. -/
theorem existsUnique_root_residue {f : A[X]} (hf : f.Monic)
    (hu : ∃ u v : A[X], derivative f * u + f * v = 1) {a₀ : ResidueField A}
    (ha₀ : aeval a₀ f = 0) : ∃! a : A, f.IsRoot a ∧ residue A a = a₀ := by
  obtain ⟨u, v, huv⟩ := hu
  have hder (x : ResidueField A) (hx : aeval x f = 0) : aeval x (derivative f) ≠ 0 := by
    intro h0
    have := congrArg (aeval x) huv
    simp [h0, hx] at this
  have hunit (b : A) (hb : aeval (residue A b) f = 0) : IsUnit (f.derivative.eval b) := by
    have h := hder (residue A b) hb
    rwa [aeval_residue, ne_eq, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
      not_not] at h
  obtain ⟨a₀, rfl⟩ := residue_surjective a₀
  have h₁ : f.eval a₀ ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, ← aeval_residue]
    exact ha₀
  obtain ⟨a, ha, hmem⟩ := HenselianLocalRing.is_henselian f hf a₀ h₁ (hunit a₀ ha₀)
  have hres : residue A a = residue A a₀ := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hmem
  refine ⟨a, ⟨ha, hres⟩, fun b ⟨hb, hab⟩ ↦ ?_⟩
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hb ha ?_
    (hunit b (aeval_residue_eq_zero hb))
  rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, hab, hres,
    sub_self]

/-- The bijection between the roots in `A` of `f` (monic, with `f'` invertible modulo `f`) and
its roots in the residue field. -/
noncomputable def rootsEquivResidueRoots {f : A[X]} (hf : f.Monic)
    (hu : ∃ u v : A[X], derivative f * u + f * v = 1) :
    {a : A // f.IsRoot a} ≃ {a₀ : ResidueField A // aeval a₀ f = 0} :=
  Equiv.ofBijective (fun a ↦ ⟨residue A a, aeval_residue_eq_zero a.2⟩) <| by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      obtain ⟨c, -, hc⟩ := existsUnique_root_residue hf hu (aeval_residue_eq_zero ha)
      have h1 := hc a ⟨ha, rfl⟩
      have h2 := hc b ⟨hb, (congrArg Subtype.val hab).symm⟩
      exact Subtype.ext (h1.trans h2.symm)
    · rintro ⟨a₀, ha₀⟩
      obtain ⟨a, ⟨ha, rfl⟩, -⟩ := existsUnique_root_residue hf hu ha₀
      exact ⟨⟨a, ha⟩, rfl⟩

end Roots

end SGA.SGA1.ExposeX
