/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.OkaFactorization

/-!
# Simultaneous Weierstrass preparation of a finite family

One linear shear makes every nonzero member of a finite family of convergent power
series regular in the last variable. Each then becomes a monic polynomial after
multiplication by a unit; zero members remain zero. The same coordinates therefore work
for the entire relation problem in Oka's coherence induction (Demailly, *Complex Analytic
and Differential Geometry*, II.3.19).
-/

noncomputable section

open Finset
open scoped Polynomial

namespace MvPowerSeries

variable {τ : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- A series whose restriction to the last coordinate axis is nonzero is regular
of a finite order in that variable. -/
lemma exists_isRegularOfOrder_of_restrictY_ne_zero {f : MvPowerSeries (Option τ) 𝕜}
    (hf : restrictY f ≠ 0) : ∃ b, IsRegularOfOrder b f := by
  classical
  have hex : ∃ b, coeff (Finsupp.single none b) f ≠ 0 := by
    by_contra! h
    exact hf (restrictY_eq_zero_iff.mpr h)
  refine ⟨Nat.find hex, fun j hj ↦ not_not.mp (Nat.find_min hex hj), Nat.find_spec hex⟩

variable [Finite τ] [CompleteSpace 𝕜]

local instance : Fintype τ := Fintype.ofFinite τ

/-- One linear change of coordinates makes all nonzero members of a finite family
regular in the same last variable. -/
theorem exists_simultaneously_regular_shear {ι : Type*} [Finite ι]
    (f : ι → convergent (Option τ) 𝕜) :
    ∃ (v : Option τ → 𝕜) (hv : v none ≠ 0),
      ∀ i, f i ≠ 0 → ∃ b, IsRegularOfOrder b (shearEquiv hv (f i)).1 := by
  classical
  let := Fintype.ofFinite ι
  let f' : ι → convergent (Option τ) 𝕜 := fun i ↦ if f i = 0 then 1 else f i
  have hf' (i : ι) : f' i ≠ 0 := by
    dsimp only [f']
    split_ifs with hi
    · exact one_ne_zero
    · exact hi
  let g := ∏ i, f' i
  have hg : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hf' i
  obtain ⟨v, hv, b, hreg⟩ := exists_isRegularOfOrder_shearEquiv hg
  let ρ : convergent (Option τ) 𝕜 →+* MvPowerSeries Unit 𝕜 :=
    restrictY.toRingHom.comp ((convergent (Option τ) 𝕜).val.toRingHom.comp
      (shearEquiv hv).toRingHom)
  have hρg : ρ g ≠ 0 := by
    intro h
    apply hreg.2
    have h' := congrArg (coeff (Finsupp.single () b)) h
    change coeff (Finsupp.single () b) (restrictY (shearEquiv hv g).1) =
      coeff (Finsupp.single () b) 0 at h'
    simpa only [coeff_restrictY, map_zero] using h'
  have hprod : (∏ i, ρ (f' i)) ≠ 0 := by
    rw [← map_prod]
    exact hρg
  refine ⟨v, hv, fun i hi ↦ ?_⟩
  apply exists_isRegularOfOrder_of_restrictY_ne_zero
  have h := Finset.prod_ne_zero_iff.mp hprod i (mem_univ i)
  change ρ (f i) ≠ 0
  simpa only [f', ite_eq_right hi] using h

/-- Preparation in polynomial form, with the multiplier recorded as an actual unit. -/
theorem exists_unit_mul_eq_polyY {b : ℕ} (f : convergent (Option τ) 𝕜)
    (hf : IsRegularOfOrder b f.1) :
    ∃ (u : (convergent (Option τ) 𝕜)ˣ) (P : (convergent τ 𝕜)[X]),
      P.Monic ∧ P.natDegree = b ∧ f * u = polyY P ∧
      P.map convergentConstantCoeff = Polynomial.X ^ b := by
  classical
  obtain ⟨u, hu, hu0, r, hr, hrlow, hr0, hprep⟩ := exists_weierstrassPreparation f.2 hf
  obtain ⟨R, hRdeg, hR⟩ := exists_polyY_of_isLow (f := ⟨r, hr⟩) hrlow
  let P : (convergent τ 𝕜)[X] := Polynomial.X ^ b - R
  have hP : P.Monic := Polynomial.monic_X_pow_sub hRdeg
  have hPdeg : P.natDegree = b := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    change (Polynomial.X ^ b - R).degree = (b : WithBot ℕ)
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (by simpa using hRdeg), Polynomial.degree_X_pow]
  have hunit : IsUnit (⟨u, hu⟩ : convergent (Option τ) 𝕜) :=
    isUnit_convergent_iff.mpr hu0
  obtain ⟨v, hv⟩ := hunit
  refine ⟨v, P, hP, hPdeg, ?_, ?_⟩
  · rw [hv]
    change f * ⟨u, hu⟩ = polyY (Polynomial.X ^ b - R)
    rw [polyY_sub, polyY_X_pow, hR]
    exact Subtype.ext hprep
  · ext j
    rw [Polynomial.coeff_map]
    change constantCoeff (P.coeff j).1 = _
    have hRzero : constantCoeff (R.coeff j).1 = 0 := by
      rw [← coeff_single_none_polyY, hR]
      exact hr0 j
    simp only [P, Polynomial.coeff_sub, AddSubgroupClass.coe_sub, map_sub, hRzero, sub_zero]
    by_cases hj : j = b <;> simp [Polynomial.coeff_X_pow, hj]

/-- Simultaneous preparation of a finite family, allowing zero members. After one
common shear and multiplication by analytic units, all coefficients are polynomial. -/
theorem exists_simultaneous_weierstrass_preparation {ι : Type*} [Finite ι]
    (f : ι → convergent (Option τ) 𝕜) :
    ∃ (v : Option τ → 𝕜) (hv : v none ≠ 0)
      (u : ι → (convergent (Option τ) 𝕜)ˣ) (P : ι → (convergent τ 𝕜)[X]),
      (∀ i, shearEquiv hv (f i) * u i = polyY (P i)) ∧
      (∀ i, f i = 0 → P i = 0) ∧ (∀ i, f i ≠ 0 → (P i).Monic) := by
  classical
  obtain ⟨v, hv, hreg⟩ := exists_simultaneously_regular_shear f
  have hex (i : ι) : ∃ (u : (convergent (Option τ) 𝕜)ˣ) (P : (convergent τ 𝕜)[X]),
      shearEquiv hv (f i) * u = polyY P ∧ (f i = 0 → P = 0) ∧
        (f i ≠ 0 → P.Monic) := by
    by_cases hi : f i = 0
    · exact ⟨1, 0, by simp [hi, polyY], fun _ ↦ rfl, fun h ↦ (h hi).elim⟩
    · obtain ⟨b, hb⟩ := hreg i hi
      obtain ⟨u, P, hP, -, hmul, -⟩ := exists_unit_mul_eq_polyY (shearEquiv hv (f i)) hb
      exact ⟨u, P, hmul, fun h ↦ (hi h).elim, fun _ ↦ hP⟩
  choose u P hmul hzero hmonic using hex
  exact ⟨v, hv, u, P, hmul, hzero, hmonic⟩

end MvPowerSeries
