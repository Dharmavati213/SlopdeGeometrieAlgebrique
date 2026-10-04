/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.DominatingDVR
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.FiniteType

/-!
# EGA II 7.1.7 for finitely generated field extensions

Let `A` be a noetherian local domain which is not a field, `K` its fraction field and `L` a
finitely generated field extension of `K` (`Algebra.EssFiniteType K L`). There is a discrete
valuation ring of `L` dominating `A` (EGA II 7.1.7; Stacks, Tag 00PH):
`IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_of_essFiniteType`, hence
`IsLocalRing.dominatingDVRStatement : IsLocalRing.DominatingDVRStatement`.

## Proof

Reduce to the case `L = K` (`IsLocalRing.exists_valuationSubring_isDiscreteValuationRing`) for a
noetherian local domain `A'` with fraction field `L` dominating `A`. Let `V₀` be a valuation ring
of `L` dominating `A` (Chevalley) and `y₁, …, yₙ` elements generating `L` as a field over `K`
(from `EssFiniteType`). Replacing `yᵢ` by `yᵢ⁻¹` when `yᵢ ∉ V₀`, all `yᵢ` lie in `V₀`. Then
`B = A[y₁, …, yₙ]` is a noetherian domain with fraction field `L` contained in `V₀`, and
`A' = B_𝔓` for `𝔓 = 𝔪_{V₀} ∩ B` is a noetherian local domain with fraction field `L`
dominating `A`. (EGA reduces instead by a transcendence basis to `A[x]_{(𝔪, x)}` and the finite
case; choosing the generators inside `V₀` avoids transcendence bases.)
-/

open IsLocalRing

namespace IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- EGA II 7.1.7 (Stacks 00PH): let `A` be a noetherian local domain which is not a field, `K` its
fraction field and `L` a finitely generated field extension of `K`. There is a discrete
valuation ring `V` with fraction field `L` dominating `A`: `V` is a valuation subring of `L`
which is a DVR, contains (the image of) `A`, and every element of `𝔪_A` has valuation `< 1` on
`V`. -/
theorem exists_valuationSubring_isDiscreteValuationRing_of_essFiniteType (hA : ¬ IsField A)
    (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra.EssFiniteType K L] :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧ (∀ a : A, algebraMap A L a ∈ V) ∧
      ∀ a ∈ maximalIdeal A, V.valuation (algebraMap A L a) < 1 := by
  classical
  obtain ⟨σ, hσ⟩ := (‹Algebra.EssFiniteType K L›).cond
  rw [Algebra.essFiniteType_cond_iff] at hσ
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  -- A valuation ring `V₀` of `L` dominating `A`.
  obtain ⟨V₀, hV₀, hloc₀⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap A L)
  have hv₀ : ∀ a ∈ maximalIdeal A, V₀.valuation (algebraMap A L a) < 1 := by
    intro a ha
    have hnu : ¬ IsUnit ((algebraMap A L).codRestrict V₀.toSubring hV₀ a) :=
      fun h ↦ (mem_maximalIdeal a).mp ha (isUnit_of_map_unit _ a h)
    exact (V₀.valuation_lt_one_iff ⟨algebraMap A L a, hV₀ a⟩).mp hnu
  -- Generators of `L` over `K` lying in `V₀`, and `B = A[τ] ⊆ V₀`.
  let τ : Finset L := σ.image fun y ↦ if y ∈ V₀ then y else y⁻¹
  have hτ : ∀ z ∈ τ, z ∈ V₀ := by
    intro z hz
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hz
    split_ifs with hy
    · exact hy
    · exact (V₀.mem_or_inv_mem y).resolve_left hy
  let B : Subalgebra A L := Algebra.adjoin A (τ : Set L)
  have : Algebra.FiniteType A B := ⟨(Subalgebra.fg_top _).mpr ⟨τ, rfl⟩⟩
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let V₀' : Subalgebra A L := { V₀.toSubring with algebraMap_mem' := hV₀ }
  have hBV : ∀ b ∈ B, b ∈ V₀ := fun b hb ↦
    (Algebra.adjoin_le (S := V₀') fun z hz ↦ hτ z hz) hb
  -- `L` is the fraction field of `B`.
  have hfrac : ∀ z : L, ∃ x y : B, z = algebraMap B L x / algebraMap B L y := by
    let F := Subfield.closure (B : Set L)
    have hBF : ∀ b ∈ B, b ∈ F := fun b hb ↦ Subfield.subset_closure hb
    have hKF : ∀ k : K, algebraMap K L k ∈ F := by
      intro k
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) k
      rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      exact F.div_mem (hBF _ (B.algebraMap_mem a)) (hBF _ (B.algebraMap_mem b))
    let FK : Subalgebra K L := { F.toSubring with algebraMap_mem' := hKF }
    have hσF : Algebra.adjoin K (σ : Set L) ≤ FK := by
      refine Algebra.adjoin_le fun y hy ↦ ?_
      by_cases hyV : y ∈ V₀
      · exact hBF _ (Algebra.subset_adjoin (Finset.mem_image.mpr ⟨y, hy, by simp [hyV]⟩))
      · have : y⁻¹ ∈ F :=
          hBF _ (Algebra.subset_adjoin (Finset.mem_image.mpr ⟨y, hy, by simp [hyV]⟩))
        have h2 : y ∈ F := by simpa using F.inv_mem this
        exact h2
    have hF : ∀ z : L, z ∈ F := by
      intro z
      obtain ⟨t, ht, htu, hzt⟩ := hσ z
      have : z = (z * t) / t := by rw [mul_div_assoc, div_self htu.ne_zero, mul_one]
      rw [this]
      exact F.div_mem (hσF hzt) (hσF ht)
    intro z
    obtain ⟨x, hx, y, hy, rfl⟩ := Subfield.mem_closure_iff.mp (hF z)
    have hcl : Subring.closure (B : Set L) = B.toSubring := Subring.closure_eq B.toSubring
    rw [hcl] at hx hy
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, rfl⟩
  -- The prime `𝔓 = 𝔪_{V₀} ∩ B` and the local ring `A' = B_𝔓 ⊆ L`.
  let R' : Subring L := B.toSubring
  let ι : R' →+* V₀ := Subring.inclusion (S := R') (T := V₀.toSubring) fun b hb ↦ hBV b hb
  let 𝔓 : Ideal R' := (maximalIdeal V₀).comap ι
  have : 𝔓.IsPrime := Ideal.comap_isPrime _ _
  let A' : LocalSubring L := LocalSubring.ofPrime R' 𝔓
  have : IsNoetherianRing A'.toSubring :=
    IsLocalization.isNoetherianRing 𝔓.primeCompl A'.toSubring inferInstance
  have hBA' : ∀ b ∈ B, b ∈ A'.toSubring := fun b hb ↦ LocalSubring.le_ofPrime R' 𝔓 hb
  have hAA' : ∀ a : A, algebraMap A L a ∈ A'.toSubring := fun a ↦ hBA' _ (B.algebraMap_mem a)
  have : IsFractionRing A'.toSubring L := by
    refine IsFractionRing.of_field A'.toSubring L fun z ↦ ?_
    obtain ⟨x, y, rfl⟩ := hfrac z
    exact ⟨⟨_, hBA' _ x.2⟩, ⟨_, hBA' _ y.2⟩, rfl⟩
  -- `A'` dominates `A`.
  have hmA' : ∀ a ∈ maximalIdeal A,
      (⟨algebraMap A L a, hAA' a⟩ : A'.toSubring) ∈ maximalIdeal A'.toSubring := by
    intro a ha
    let r : R' := ⟨algebraMap A L a, B.algebraMap_mem a⟩
    have hr : r ∈ 𝔓 := by
      change ι r ∈ maximalIdeal V₀
      exact (V₀.valuation_lt_one_iff _).mpr (hv₀ a ha)
    have hnu : ¬ IsUnit (algebraMap R' A'.toSubring r) := fun h ↦
      ((IsLocalization.AtPrime.isUnit_to_map_iff A'.toSubring 𝔓 r).mp h) hr
    exact (mem_maximalIdeal _).mpr hnu
  have hA' : ¬ IsField A'.toSubring := by
    intro hF
    have hm : maximalIdeal A ≠ ⊥ := fun h ↦ hA (isField_iff_maximalIdeal_eq.mpr h)
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    have hne : (⟨algebraMap A L a, hAA' a⟩ : A'.toSubring) ≠ 0 := fun h ↦
      ha0 (hAL ((congrArg Subtype.val h).trans (map_zero _).symm))
    have := (isField_iff_maximalIdeal_eq.mp hF).symm ▸ hmA' a ha
    exact hne this
  -- A discrete valuation ring of `L` dominating `A'`.
  obtain ⟨V, hV, hA'V, hmV⟩ :=
    exists_valuationSubring_isDiscreteValuationRing (A := A'.toSubring) (K := L) hA'
  exact ⟨V, hV, fun a ↦ hA'V ⟨_, hAA' a⟩, fun a ha ↦ hmV _ (hmA' a ha)⟩

/-- EGA II 7.1.7 (`IsLocalRing.DominatingDVRStatement`) holds. -/
theorem dominatingDVRStatement : DominatingDVRStatement.{u} := by
  intro A _ _ _ _ hA K L _ _ _ _ _ _ _ _
  exact exists_valuationSubring_isDiscreteValuationRing_of_essFiniteType (K := K) hA L

end IsLocalRing
