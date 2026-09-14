/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.CoinductionHomDuality
import SGA.SGA2.ExposeIV.FiniteCoinductionDuality
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Coefficient-field duality without a finite-algebra assumption

The vector-space bidual comparison is the actual canonical evaluation.
Only the residue field, not the local algebra, is required to be finite
over the coefficient field.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite ModuleCat IsLocalRing

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K]

/-- Every actual vector space is injective in the category of vector spaces. -/
theorem fieldModule_injective (I : ModuleCat.{u} K) : Injective I where
  factors g f hf := by
    obtain ⟨l, hl⟩ := f.hom.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective f).mp hf))
    refine ⟨ModuleCat.ofHom (g.hom.comp l), ?_⟩
    apply ModuleCat.hom_ext
    change g.hom.comp (l.comp f.hom) = g.hom
    rw [hl, LinearMap.comp_id]

/-- The original categorical Hom bidual is the ordinary vector-space bidual. -/
def fieldHomBidualIso (M : ModuleCat.{u} K) :
    (moduleHomBidual (ModuleCat.of K K)).obj M ≅
      ModuleCat.of K (Module.Dual K (Module.Dual K M)) :=
  LinearEquiv.toModuleIso
    (X₁ := (moduleHomBidual (ModuleCat.of K K)).obj M)
    (X₂ := ModuleCat.of K (Module.Dual K (Module.Dual K M)))
    ((ModuleCat.homLinearEquiv (R := K) (S := K)).trans
      (ModuleCat.homLinearEquiv (R := K) (S := K)
        (M := M) (N := ModuleCat.of K K)).symm.dualMap)

/-- Finite-dimensional vector-space duality identifies the canonical map,
not merely the two underlying objects. -/
theorem field_moduleBidualEvaluation_isIso (M : ModuleCat.{u} K) [Module.Finite K M] :
    IsIso (moduleBidualEvaluation (ModuleCat.of K K) M) := by
  have he : moduleBidualEvaluation (ModuleCat.of K K) M ≫ (fieldHomBidualIso M).hom =
      (Module.evalEquiv K M).toModuleIso.hom := by
    apply ModuleCat.hom_ext
    ext x g
    rfl
  have : IsIso (moduleBidualEvaluation (ModuleCat.of K K) M ≫
      (fieldHomBidualIso M).hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_right _ (fieldHomBidualIso M).hom

/-- The original field-valued Hom of a finite-dimensional space is finite. -/
theorem field_moduleHomDual_finite (M : ModuleCat.{u} K) [Module.Finite K M] :
    Module.Finite K ((moduleHomDual (ModuleCat.of K K)).obj (op M)) :=
  Module.Finite.equiv
    (ModuleCat.homLinearEquiv (R := K) (S := K) (M := M) (N := ModuleCat.of K K)).symm

variable {A : Type u} [CommRing A] [Algebra K A]

/-- Actual restriction of a module with a compatible coefficient-field action. -/
def restrictCoefficientFieldIso (M : Type u) [AddCommGroup M]
    [Module A M] [Module K M] [IsScalarTower K A M] :
    (restrictScalars (algebraMap K A)).obj (ModuleCat.of A M) ≅ ModuleCat.of K M :=
  LinearEquiv.toModuleIso
    (X₁ := (restrictScalars (algebraMap K A)).obj (ModuleCat.of A M))
    (X₂ := ModuleCat.of K M)
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' r x := by
        change algebraMap K A r • (show M from x) = r • (show M from x)
        exact IsScalarTower.algebraMap_smul A r (show M from x) }

variable [IsLocalRing A] [Module.Finite K (ResidueField A)]

/-- Finite-length modules are genuinely finite dimensional over the
coefficient field, even when the local algebra itself is not finite. -/
theorem coefficientField_finite_of_finiteLength (M : ModuleCat.{u} A)
    (hM : IsFiniteLength A M) :
    Module.Finite K ((restrictScalars (algebraMap K A)).obj M) := by
  apply moduleFiniteLength_induction
    (fun N ↦ Module.Finite K ((restrictScalars (algebraMap K A)).obj N)) ?_ ?_ ?_ M hM
  · intro N hN
    have := ModuleCat.isZero_iff_subsingleton.mp
      ((restrictScalars (algebraMap K A)).map_isZero hN)
    infer_instance
  · intro N hN
    obtain ⟨m, hm, ⟨e⟩⟩ :=
      (isSimpleModule_iff_quot_maximal (R := A) (M := N)).mp hN
    have hmk : m = maximalIdeal A := eq_maximalIdeal hm
    subst m
    let e' : (restrictScalars (algebraMap K A)).obj N ≅ ModuleCat.of K (ResidueField A) :=
      (restrictScalars (algebraMap K A)).mapIso e.toModuleIso ≪≫
        restrictCoefficientFieldIso (A := A) (K := K) (ResidueField A)
    exact Module.Finite.equiv e'.symm.toLinearEquiv
  · intro S hS h₁ h₃
    have := h₁
    have := h₃
    let D := S.map (restrictScalars (algebraMap K A))
    have hD : D.ShortExact := hS.map_of_exact _
    have : Module.Finite K D.X₁ := h₁
    have : Module.Finite K D.X₃ := h₃
    exact Module.Finite.of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact D).mp hD.exact)
      ((ModuleCat.epi_iff_surjective D.g).mp hD.epi_g)

/-- The numerical relation in IV.5.2: coefficient-field dimension is the
residue-field degree times the original module length. -/
theorem coefficientField_finrank_eq_residueDegree_mul_length (M : ModuleCat.{u} A)
    (hM : IsFiniteLength A M) :
    (Module.finrank K ((restrictScalars (algebraMap K A)).obj M) : ℕ∞) =
      (Module.finrank K (ResidueField A) : ℕ∞) * Module.length A M := by
  have hlen : Module.length K ((restrictScalars (algebraMap K A)).obj M) =
      (Module.finrank K (ResidueField A) : ℕ∞) * Module.length A M := by
    apply moduleFiniteLength_induction
      (fun N ↦ Module.length K ((restrictScalars (algebraMap K A)).obj N) =
        (Module.finrank K (ResidueField A) : ℕ∞) * Module.length A N) ?_ ?_ ?_ M hM
    · intro N hN
      have := ModuleCat.isZero_iff_subsingleton.mp hN
      have := ModuleCat.isZero_iff_subsingleton.mp
        ((restrictScalars (algebraMap K A)).map_isZero hN)
      simp only [Module.length_eq_zero, mul_zero]
    · intro N hN
      have := hN
      obtain ⟨m, hm, ⟨e⟩⟩ :=
        (isSimpleModule_iff_quot_maximal (R := A) (M := N)).mp hN
      have hmk : m = maximalIdeal A := eq_maximalIdeal hm
      subst m
      let e' : (restrictScalars (algebraMap K A)).obj N ≅
          ModuleCat.of K (ResidueField A) :=
        (restrictScalars (algebraMap K A)).mapIso e.toModuleIso ≪≫
          restrictCoefficientFieldIso (A := A) (K := K) (ResidueField A)
      rw [e'.toLinearEquiv.length_eq, Module.length_eq_one A N, mul_one]
      exact Module.length_eq_finrank K (ResidueField A)
    · intro S hS h₁ h₃
      let D := S.map (restrictScalars (algebraMap K A))
      have hD : D.ShortExact := hS.map_of_exact _
      have hlenD := Module.length_eq_add_of_exact D.f.hom D.g.hom
        ((ModuleCat.mono_iff_injective _).mp hD.mono_f)
        ((ModuleCat.epi_iff_surjective _).mp hD.epi_g)
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hD.exact)
      change Module.length K ((restrictScalars (algebraMap K A)).obj S.X₂) =
        Module.length K ((restrictScalars (algebraMap K A)).obj S.X₁) +
          Module.length K ((restrictScalars (algebraMap K A)).obj S.X₃) at hlenD
      rw [hlenD, h₁, h₃, Module.length_eq_add_of_exact S.f.hom S.g.hom
        ((ModuleCat.mono_iff_injective _).mp hS.mono_f)
        ((ModuleCat.epi_iff_surjective _).mp hS.epi_g)
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact), mul_add]
  have := coefficientField_finite_of_finiteLength (K := K) M hM
  rwa [Module.length_eq_finrank] at hlen

/-- The actual full coinduced coefficient for the field dual. It need not
itself be supported; its supported representing module is constructed separately. -/
abbrev coefficientFieldCoinduced : ModuleCat.{u} A :=
  (coextendScalars (algebraMap K A)).obj (ModuleCat.of K K)

/-- The actual canonical biduality holds on every finite-length module. -/
theorem coefficientFieldCoinduced_bidual_finiteLength (M : ModuleCat.{u} A)
    (hM : IsFiniteLength A M) :
    IsIso (moduleBidualEvaluation (coefficientFieldCoinduced (K := K) (A := A)) M) := by
  have := coefficientField_finite_of_finiteLength (K := K) M hM
  have := field_moduleBidualEvaluation_isIso ((restrictScalars (algebraMap K A)).obj M)
  exact coinduced_moduleBidualEvaluation_isIso (algebraMap K A) (ModuleCat.of K K) M

/-- Actual Hom into the coinduced coefficient is finite on finite-length modules. -/
theorem coefficientFieldCoinduced_hom_finiteLength (M : ModuleCat.{u} A)
    (hM : IsFiniteLength A M) :
    Module.Finite A ((moduleHomDual (coefficientFieldCoinduced (K := K) (A := A))).obj
      (op M)) := by
  have := coefficientField_finite_of_finiteLength (K := K) M hM
  have := field_moduleHomDual_finite ((restrictScalars (algebraMap K A)).obj M)
  exact coinduced_moduleHomDual_finite (algebraMap K A) (ModuleCat.of K K) M

end SGA.SGA2.ExposeIV
