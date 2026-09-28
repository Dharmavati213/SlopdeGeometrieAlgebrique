/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.MatlisCategories
import SGA.SGA2.ExposeIV.CompleteScalarAction
import SGA.SGA2.ExposeIV.NoetherianCompletion
import SGA.SGA2.ExposeIV.CompletionSubmodules

/-!
# Original complete modules under completed scalar change

Actual ideal-power quotients commute with restriction from the completed
ring. Consequently restriction preserves the literal `DA` condition.
Completing an original `DA` module gives a finite completed-ring module,
by topological Nakayama applied to its actual first quotient. All assertions
retain the given scalar actions and the original module completion.
-/

noncomputable section
universe u
open CategoryTheory ModuleCat

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (J : Ideal R)

/-- The quotient map induced by an actual linear equivalence preserves the
original ideal-power filtration. -/
def idealPowerQuotientEquiv {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N) (n : ℕ) :
    (M ⧸ (J ^ n • (⊤ : Submodule R M))) ≃ₗ[R]
      N ⧸ (J ^ n • (⊤ : Submodule R N)) :=
  Submodule.Quotient.equiv _ _ e (by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])

section Restriction

variable (X : ModuleCat.{u} (AdicCompletion J R))

local instance : Module R X := Module.compHom X (algebraMap R (AdicCompletion J R))
local instance : IsScalarTower R (AdicCompletion J R) X :=
  IsScalarTower.of_compHom R (AdicCompletion J R) X

/-- Restricting the actual completed ideal-power quotient gives the original
ideal-power quotient, by an identity-on-representatives equivalence. -/
def completionPowerQuotientRestrictionEquiv (n : ℕ) :
    (((restrictScalars (algebraMap R (AdicCompletion J R))).obj X) ⧸
      (J ^ n • (⊤ : Submodule R
        ((restrictScalars (algebraMap R (AdicCompletion J R))).obj X)))) ≃ₗ[R]
    (restrictScalars (algebraMap R (AdicCompletion J R))).obj
      (ModuleCat.of (AdicCompletion J R)
        (X ⧸ ((J.map (algebraMap R (AdicCompletion J R))) ^ n •
          (⊤ : Submodule (AdicCompletion J R) X)))) := by
  let N : Submodule (AdicCompletion J R) X :=
    (J.map (algebraMap R (AdicCompletion J R))) ^ n • ⊤
  have hN : N.restrictScalars R = J ^ n • (⊤ : Submodule R X) := by
    dsimp only [N]
    rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
      Submodule.restrictScalars_top]
  exact Submodule.Quotient.equiv _ (N.restrictScalars R) (LinearEquiv.refl R X)
    (by simpa only [LinearEquiv.refl_toLinearMap, Submodule.map_id] using hN.symm)

/-- Adic completeness itself is unchanged by actual restriction. -/
theorem completion_restrict_isAdicComplete_iff :
    IsAdicComplete (J.map (algebraMap R (AdicCompletion J R))) X ↔
      IsAdicComplete J ((restrictScalars (algebraMap R (AdicCompletion J R))).obj X) :=
  IsAdicComplete.map_algebraMap_iff J X

variable [IsNoetherianRing R]

/-- A finite completed module has finite original-ring power quotients;
the whole restricted module need not be finite. -/
theorem completion_restrict_powerQuotient_finite [Module.Finite (AdicCompletion J R) X]
    (n : ℕ) : Module.Finite R
      (((restrictScalars (algebraMap R (AdicCompletion J R))).obj X) ⧸
        (J ^ n • (⊤ : Submodule R
          ((restrictScalars (algebraMap R (AdicCompletion J R))).obj X)))) := by
  let Q := ModuleCat.of (AdicCompletion J R)
    (X ⧸ ((J.map (algebraMap R (AdicCompletion J R))) ^ n •
      (⊤ : Submodule (AdicCompletion J R) X)))
  have hQ := finiteSource_powerQuotient_supported
    (J.map (algebraMap R (AdicCompletion J R))) X n
  have := completion_restrictScalars_finite J Q hQ
  exact Module.Finite.of_surjective
    (completionPowerQuotientRestrictionEquiv J X n).symm.toLinearMap
    (completionPowerQuotientRestrictionEquiv J X n).symm.surjective

end Restriction

section Local

variable [IsLocalRing R] [IsNoetherianRing R]

/-- Restriction of the existing completed action preserves the literal `DA`
property, not a substituted finite-module definition. -/
theorem matlisComplete_completion_restrict
    (X : ModuleCat.{u} (AdicCompletion (IsLocalRing.maximalIdeal R) R))
    (hX : matlisCompleteModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R) X) :
    matlisCompleteModuleProperty R
      ((restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj X) := by
  let m := IsLocalRing.maximalIdeal R
  have : Module.Finite (AdicCompletion m R) X :=
    (matlisCompleteModuleProperty_iff_finite X).mp hX
  refine ⟨fun n ↦ ?_, ?_⟩
  · have := completion_restrict_powerQuotient_finite m X (n + 1)
    exact isFiniteLength_of_maximalIdeal_pow_annihilator_of_fg m.fg_of_isNoetherianRing _
      (n + 1) (by
        intro r hr
        apply Module.mem_annihilator.mpr
        intro x
        obtain ⟨y, rfl⟩ := (m ^ (n + 1) •
          (⊤ : Submodule R
            ((restrictScalars (algebraMap R (AdicCompletion m R))).obj X))).mkQ_surjective x
        exact (Submodule.Quotient.mk_eq_zero _).mpr
          (Submodule.smul_mem_smul hr Submodule.mem_top))
  · apply (completion_restrict_isAdicComplete_iff m X).mp
    have h := hX.2
    rw [AdicCompletion.maximalIdeal_eq_map] at h
    exact h

/-- The actual completion of an original `DA` module is finite for its
canonical completed action. Only topological Nakayama is used here. -/
theorem matlisComplete_completion_finite (M : ModuleCat.{u} R)
    (hM : matlisCompleteModuleProperty R M) :
    Module.Finite (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      (AdicCompletion (IsLocalRing.maximalIdeal R) M) := by
  let m := IsLocalRing.maximalIdeal R
  let A := AdicCompletion m R
  let C := ModuleCat.of A (AdicCompletion m M)
  have : IsAdicComplete m M := hM.2
  have : IsAdicComplete m (AdicCompletion m M) :=
    AdicCompletion.isAdicComplete (M := M) m.fg_of_isNoetherianRing
  have : IsAdicComplete (IsLocalRing.maximalIdeal A) C := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact (IsAdicComplete.map_algebraMap_iff m (AdicCompletion m M)).mpr inferInstance
  have hlen := hM.1 0
  have : IsNoetherian R (M ⧸ (m ^ 1 • (⊤ : Submodule R M))) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).1
  have : Module.Finite R (M ⧸ (m ^ 1 • (⊤ : Submodule R M))) := inferInstance
  let e := (idealPowerQuotientEquiv m (AdicCompletion.ofLinearEquiv m M) 1).trans
    (completionPowerQuotientRestrictionEquiv m C 1)
  let Q := ModuleCat.of A
    (C ⧸ ((m.map (algebraMap R A)) ^ 1 • (⊤ : Submodule A C)))
  have : Module.Finite R ((restrictScalars (algebraMap R A)).obj Q) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  let g : ((restrictScalars (algebraMap R A)).obj Q) →ₛₗ[algebraMap R A] Q :=
    { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have hQ : Module.Finite A Q := Module.Finite.of_surjective g Function.surjective_id
  have : Module.Finite A (C ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A C))) := by
    change Module.Finite A (C ⧸ ((m.map (algebraMap R A)) ^ 1 •
      (⊤ : Submodule A C))) at hQ
    rw [pow_one] at hQ
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact hQ
  exact finite_of_isHausdorff_of_finite_reduction (IsLocalRing.maximalIdeal A) C

/-- The actual module completion, with its canonical completed action,
preserves the literal `DA` property. -/
theorem matlisComplete_completion_obj (M : ModuleCat.{u} R)
    (hM : matlisCompleteModuleProperty R M) :
    matlisCompleteModuleProperty (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      (ModuleCat.of (AdicCompletion (IsLocalRing.maximalIdeal R) R)
        (AdicCompletion (IsLocalRing.maximalIdeal R) M)) :=
  (matlisCompleteModuleProperty_iff_finite _).mpr (matlisComplete_completion_finite M hM)

end Local

end SGA.SGA2.ExposeIV
