/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.NormalCrossings
import SGA.SGA1.ExposeIX.StrictlyLocalDescent
import SGA.Foundations.StrictHenselization

/-!
# A complete discrete valuation ring with separably closed residue field over a given one

SGA reduces X.3.8 to a complete discrete valuation ring with algebraically closed residue field.
To do so it dominates the local ring of the closure of `y₁` at `y₀` by a discrete valuation ring
(EGA II 7.1.7), then passes to a flat local extension with algebraically closed residue field
(EGA 0_III 10.3.1). The core proved here (`tameLiftingDVRStatement`) only needs a *separably*
closed residue field. For that the second step is elementary: the completion `R'` of the strict
henselization of `R` with respect to an algebraic closure of its residue field works:

* `R'` is a discrete valuation ring: it is regular local of dimension one, because the strict
  henselization is a discrete valuation ring (`isDiscreteValuationRing_strictHenselization`) and
  `R^{sh} → R'` is flat and local with `𝔪 R' = 𝔪_{R'}`
  (`ExposeI.isRegularLocalRing_iff_of_flat`).
* `R'` is complete, and its residue field, the separable closure of that of `R`, is separably
  closed.
* `R → R'` is injective and local (faithfully flat).

This is `exists_isAdicComplete_isDiscreteValuationRing` (EGA IV 18.8; Stacks 0BSK, 06LJ for the
strict henselization, Stacks 00MA for the completion). The same ring is moreover unramified over
`R`: `𝔪_R R' = 𝔪_{R'}`, and `κ(R')`, the separable closure of `κ(R)`, is separable over `κ(R)`
(`exists_isAdicComplete_isDiscreteValuationRing_unramified`).
-/

universe u

open IsLocalRing

namespace SGA.SGA1.ExposeX

attribute [local instance] isLocalHom_algebraMap_of_isScalarTower

/-- Every discrete valuation ring `R` is dominated by a complete discrete valuation ring with
separably closed residue field: there is an injective local homomorphism `R → R'` with `R'` a
complete discrete valuation ring whose residue field is separably closed. Take for `R'` the
completion of the strict henselization of `R` with respect to an algebraic closure of its
residue field (EGA IV 18.8; the separable case of EGA 0_III 10.3.1 for discrete valuation
rings). -/
theorem exists_isAdicComplete_isDiscreteValuationRing (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (_ : IsAdicComplete (maximalIdeal R') R') (_ : IsSepClosed (ResidueField R'))
      (φ : R →+* R'), Function.Injective φ ∧ IsLocalHom φ := by
  let K := AlgebraicClosure (ResidueField R)
  let S := StrictHenselization R K
  let R' := AdicCompletion (maximalIdeal S) S
  have hm : (maximalIdeal S).map (algebraMap S R') = maximalIdeal R' :=
    AdicCompletion.maximalIdeal_eq_map.symm
  have : IsRegularLocalRing R' :=
    (ExposeI.isRegularLocalRing_iff_of_flat hm).mp inferInstance
  have hdim : ringKrullDim R' = 1 := by
    rw [← ExposeI.ringKrullDim_eq_of_flat_of_map_maximalIdeal hm,
      IsDiscreteValuationRing.ringKrullDim_eq_one]
  have : IsDiscreteValuationRing R' := IsRegularLocalRing.isDiscreteValuationRing hdim
  have : IsSepClosed (ResidueField R') :=
    IsSepClosed.of_ringEquiv (ExposeIX.residueFieldCompletionEquiv S)
  have : Module.FaithfullyFlat S R' := .of_flat_of_isLocalHom
  refine ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap S R').comp (algebraMap R S), ?_, inferInstance⟩
  exact (FaithfulSMul.algebraMap_injective S R').comp (FaithfulSMul.algebraMap_injective R S)

/-- `exists_isAdicComplete_isDiscreteValuationRing` with the unramifiedness of `R → R'`: every
discrete valuation ring `R` has a complete discrete valuation ring `R'` with separably closed
residue field as an `R`-algebra, with `R → R'` injective and local, `𝔪_R R' = 𝔪_{R'}`, and
`κ(R')/κ(R)` separable. (`R'` is the completion of the strict henselization of `R`; EGA IV 18.8,
Stacks 0BSK.) -/
theorem exists_isAdicComplete_isDiscreteValuationRing_unramified (R : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (_ : IsAdicComplete (maximalIdeal R') R') (_ : IsSepClosed (ResidueField R'))
      (_ : Algebra R R') (_ : IsLocalHom (algebraMap R R')),
      Function.Injective (algebraMap R R') ∧
        (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' ∧
        Algebra.IsSeparable (ResidueField R) (ResidueField R') := by
  let K := AlgebraicClosure (ResidueField R)
  let S := StrictHenselization R K
  let R' := AdicCompletion (maximalIdeal S) S
  have hm : (maximalIdeal S).map (algebraMap S R') = maximalIdeal R' :=
    AdicCompletion.maximalIdeal_eq_map.symm
  have : IsRegularLocalRing R' :=
    (ExposeI.isRegularLocalRing_iff_of_flat hm).mp inferInstance
  have hdim : ringKrullDim R' = 1 := by
    rw [← ExposeI.ringKrullDim_eq_of_flat_of_map_maximalIdeal hm,
      IsDiscreteValuationRing.ringKrullDim_eq_one]
  have : IsDiscreteValuationRing R' := IsRegularLocalRing.isDiscreteValuationRing hdim
  have : IsSepClosed (ResidueField R') :=
    IsSepClosed.of_ringEquiv (ExposeIX.residueFieldCompletionEquiv S)
  have : Module.FaithfullyFlat S R' := .of_flat_of_isLocalHom
  have : IsScalarTower R S R' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hloc : IsLocalHom (algebraMap R R') := by
    rw [IsScalarTower.algebraMap_eq R S R']
    infer_instance
  -- `κ(S)` is the separable closure of `κ(R)` in `K`
  let φ : ResidueField S →ₐ[ResidueField R] separableClosure (ResidueField R) K :=
    { (StrictHenselization.residueFieldEquivSeparableClosure R K).toRingHom with
      commutes' := fun a ↦ by
        obtain ⟨r, rfl⟩ := residue_surjective a
        apply Subtype.ext
        change (StrictHenselization.residueFieldEquivSeparableClosure R K
          (algebraMap (ResidueField R) (ResidueField S) (residue R r)) : K) =
          algebraMap (ResidueField R) K (residue R r)
        rw [ResidueField.algebraMap_residue,
          StrictHenselization.coe_residueFieldEquivSeparableClosure_residue, AlgHom.commutes,
          IsScalarTower.algebraMap_apply R (ResidueField R) K, ResidueField.algebraMap_eq] }
  have hsepS : Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
    Algebra.IsSeparable.of_algHom _ _ φ
  -- `κ(R') = κ(S)`
  let e := ExposeIX.residueFieldCompletionEquiv S
  let ψ : ResidueField R' →ₐ[ResidueField R] ResidueField S :=
    { e.symm.toRingHom with
      commutes' := fun a ↦ by
        obtain ⟨r, rfl⟩ := residue_surjective a
        apply e.injective
        change e (e.symm _) = e _
        rw [RingEquiv.apply_symm_apply, ResidueField.algebraMap_residue,
          ResidueField.algebraMap_residue]
        change _ = ResidueField.map (algebraMap S R') (residue S (algebraMap R S r))
        rw [ResidueField.map_residue]
        rfl }
  have hsep : Algebra.IsSeparable (ResidueField R) (ResidueField R') :=
    Algebra.IsSeparable.of_algHom _ _ ψ
  refine ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hloc, ?_, ?_, hsep⟩
  · exact (FaithfulSMul.algebraMap_injective S R').comp (FaithfulSMul.algebraMap_injective R S)
  · rw [IsScalarTower.algebraMap_eq R S R', ← Ideal.map_map, StrictHenselization.map_maximalIdeal,
      hm]

end SGA.SGA1.ExposeX
