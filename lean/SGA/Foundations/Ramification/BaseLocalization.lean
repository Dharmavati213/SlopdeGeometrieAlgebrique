/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Localization.AtPrime.Extension
import SGA.Foundations.Ramification.Transport

/-!
# Ramification data under localization of the base

Let `p` be a prime of `R`, `Rₚ = R_p` and `Sₚ = S_p` the localizations of `R` and of an
`R`-algebra `S` at `R - p`. For a prime `P` of `S` over `p`, the prime `P Sₚ` of `Sₚ` lies over the
maximal ideal of `Rₚ` and has the same local ring as `P`. Mathlib shows that the ramification
indices agree (`IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx`); here:

* `IsLocalization.AtPrime.isSeparable_residueField_map_iff`: the residue field extension of `P Sₚ`
  over `Rₚ` is separable if and only if that of `P` over `R` is.
-/

open IsLocalRing Ideal

namespace IsLocalization.AtPrime

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
  (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
  (Sₚ : Type*) [CommRing Sₚ] [Algebra S Sₚ]
  [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ] [Algebra Rₚ Sₚ] [Algebra R Sₚ]
  [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] (P : Ideal S) [P.IsPrime] [P.LiesOver p]

/-- The residue field extension of `P Sₚ` over `Rₚ` is separable if and only if that of `P` over
`R` is. -/
theorem isSeparable_residueField_map_iff :
    haveI := liesOver_map_of_liesOver p Rₚ Sₚ P
    haveI := isPrime_map_of_liesOver S p Sₚ P
    letI := Localization.AtPrime.algebraOfLiesOver p P
    letI := Localization.AtPrime.algebraOfLiesOver (maximalIdeal Rₚ) (P.map (algebraMap S Sₚ))
    Algebra.IsSeparable (maximalIdeal Rₚ).ResidueField (P.map (algebraMap S Sₚ)).ResidueField ↔
      Algebra.IsSeparable p.ResidueField P.ResidueField := by
  have := liesOver_map_of_liesOver p Rₚ Sₚ P
  have := isPrime_map_of_liesOver S p Sₚ P
  let := Localization.AtPrime.algebraOfLiesOver p P
  let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal Rₚ) (P.map (algebraMap S Sₚ))
  have := IsLocalization.liesOver_map_of_isPrime_disjoint (Algebra.algebraMapSubmonoid S
    p.primeCompl) Sₚ (Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (LiesOver.over (P := P) (p := p)).ge))
  let R₁ := Localization.AtPrime (P.map (algebraMap S Sₚ))
  let R₂ := Localization.AtPrime P
  let : Algebra R₂ R₁ := Localization.AtPrime.algebraOfLiesOver P (P.map (algebraMap S Sₚ))
  have : IsLocalization.AtPrime R₁ P := by
    convert isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid S p.primeCompl) R₁ (P.map (algebraMap S Sₚ))
    rw [← Ideal.under_def, ← Ideal.over_def (P.map (algebraMap S Sₚ)) P]
  have h : Function.Bijective (algebraMap R₂ R₁) :=
    (Localization.algEquiv P.primeCompl R₁).bijective
  let φ : R₂ ≃+* R₁ := RingEquiv.ofBijective (algebraMap R₂ R₁) h
  let ψ : Localization.AtPrime p ≃+* Localization.AtPrime (maximalIdeal Rₚ) :=
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) Rₚ).toRingEquiv.trans
      (IsLocalization.atUnits Rₚ (maximalIdeal Rₚ).primeCompl
        (S := Localization.AtPrime (maximalIdeal Rₚ))
        fun x hx ↦ IsLocalRing.notMem_maximalIdeal.mp hx).toRingEquiv
  refine (Algebra.IsSeparable.iff_of_equiv_equiv (ResidueField.mapEquiv ψ)
    (ResidueField.mapEquiv φ) ?_).symm
  refine Ideal.ResidueField.ringHom_ext ?_
  ext r
  have h1 : ψ (algebraMap R (Localization.AtPrime p) r) =
      algebraMap R (Localization.AtPrime (maximalIdeal Rₚ)) r := by
    simp only [ψ, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes]
    rw [IsScalarTower.algebraMap_apply R Rₚ (Localization.AtPrime (maximalIdeal Rₚ))]
    exact AlgEquiv.commutes _ _
  have h2 : φ (algebraMap (Localization.AtPrime p) R₂ (algebraMap R (Localization.AtPrime p) r)) =
      algebraMap R R₁ r := by
    simp only [φ, RingEquiv.ofBijective_apply, ← IsScalarTower.algebraMap_apply]
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
    IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField,
    ResidueField.algebraMap_eq]
  simp only [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.algebraMap_residue]
  change residue _ (algebraMap _ _ (ψ _)) = residue _ (φ _)
  rw [h1, h2, ← IsScalarTower.algebraMap_apply]

end IsLocalization.AtPrime
