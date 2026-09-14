/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.GlobalProjectiveDimension
import SGA.SGA2.ExposeIII.RegularLocalParameterChoice

/-!
# A regular parameter from finite residue-field projective dimension

A projective residue field forces a local ring to be a field. More generally,
if the maximal ideal is associated, its actual residue-field embedding into
the ring lowers any finite projective-dimension bound repeatedly to zero.
For a nonfield, finite prime avoidance therefore supplies a genuine regular
element outside the square of the maximal ideal. No regular-local hypothesis
is assumed in this homological construction of a first parameter.
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing
open SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] in
/-- A projective residue field is free and faithful, so its annihilator,
the maximal ideal, is zero. -/
theorem isField_of_projective_residueField
    [Projective (ModuleCat.of R (ResidueField R))] : IsField R := by
  have : Module.Projective R (ResidueField R) :=
    (ModuleCat.of R (ResidueField R)).projective_of_module_projective
  have : Module.Free R (ResidueField R) := Module.free_of_flat_of_isLocalRing
  have hfaith : FaithfulSMul R (ResidueField R) := inferInstance
  apply isField_iff_maximalIdeal_eq.mpr
  rw [← Ideal.annihilator_quotient (I := maximalIdeal R)]
  exact Module.annihilator_eq_bot.mpr hfaith

/-- An associated maximal ideal and any finite residue-field bound force
the ring to be a field. The original embedding `k → R` and its cokernel
lower the bound at every induction step. -/
theorem isField_of_associated_maximalIdeal_of_residueField_bound
    (hassoc : maximalIdeal R ∈ associatedPrimes R R) (n : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n → IsField R := by
  obtain ⟨_, f, hf⟩ := (isAssociatedPrime_iff_exists_injective_linearMap
    (maximalIdeal R) R).mp hassoc
  let g : ModuleCat.of R (ResidueField R) ⟶ ModuleCat.of R R := ModuleCat.ofHom f
  have : Mono g := (ModuleCat.mono_iff_injective g).mpr hf
  let S := ShortComplex.mk _ _ (cokernel.condition g)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel g }
  induction n with
  | zero =>
    intro hpd
    have := hpd
    exact isField_of_projective_residueField
  | succ n ih =>
    intro hpd
    have := hpd
    have hC := hasProjectiveDimensionLE_of_residueField (n + 1) S.X₃
    have hfree : Projective S.X₂ := inferInstanceAs (Projective (ModuleCat.of R R))
    exact ih ((hS.hasProjectiveDimensionLT_X₃_iff n hfree).mp hC)

/-- Finite prime avoidance chooses a regular element with nonzero
cotangent class whenever the maximal ideal is not associated. -/
theorem local_exists_regular_parameter_of_not_associated (hfield : ¬ IsField R)
    (hassoc : maximalIdeal R ∉ associatedPrimes R R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ IsSMulRegular R x := by
  have hmnot : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2 := by
    intro h
    apply hfield
    apply isField_iff_maximalIdeal_eq.mpr
    exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
      (maximalIdeal R).fg_of_isNoetherianRing
      (by simpa only [Ideal.smul_eq_mul, ← pow_two] using h)
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
  have hpnot : ∀ p ∈ associatedPrimes R R, ¬ maximalIdeal R ≤ p := by
    intro p hp hle
    have heq : p = maximalIdeal R := (le_maximalIdeal hp.isPrime.ne_top).antisymm hle
    exact hassoc (heq ▸ hp)
  let T : Set (Ideal R) := insert (maximalIdeal R ^ 2) (associatedPrimes R R)
  have hT : T.Finite := (associatedPrimes.finite R R).insert _
  have hnsub : ¬ (maximalIdeal R : Set R) ⊆ ⋃ p ∈ T, (p : Set R) := by
    intro hsub
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime_finite hT
      (f := id) (maximalIdeal R ^ 2) (maximalIdeal R ^ 2)
      (fun p hp hne _ ↦ ((Set.mem_insert_iff.mp hp).resolve_left hne).isPrime)).mp hsub
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact hmnot hmp
    · exact hpnot p hp hmp
  obtain ⟨x, hx, havoid⟩ := Set.not_subset.mp hnsub
  refine ⟨x, hx, ?_, IsSMulRegular.of_right_eq_zero_of_smul ?_⟩
  · intro hx2
    exact havoid (Set.mem_iUnion₂_of_mem (Set.mem_insert _ _) hx2)
  · intro y hy
    by_contra hy0
    obtain ⟨p, hp, hxp⟩ := (exists_nonzero_smul_eq_zero_iff R x).mp ⟨y, hy0, hy⟩
    exact havoid (Set.mem_iUnion₂_of_mem (Set.mem_insert_of_mem _ hp) hxp)

/-- Finite projective dimension of the residue field produces an actual
regular first parameter in every nonfield noetherian local ring. -/
theorem local_exists_regular_parameter_of_residueField_bound (n : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n]
    (hfield : ¬ IsField R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ IsSMulRegular R x :=
  local_exists_regular_parameter_of_not_associated hfield (fun hassoc ↦ hfield
    (isField_of_associated_maximalIdeal_of_residueField_bound hassoc n inferInstance))

end SGA.SGA2.ExposeV
