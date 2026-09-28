/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.ModuleExtYonedaExactness
import SGA.SGA2.ExposeV.LocalDualityTargetExactness

/-!
# The target Yoneda sequence in local duality

Hom into the actual injective coefficient dualizes the original-object
contravariant Ext sequence. Its boundary is literal precomposition by the
transported Yoneda boundary, with no finiteness condition on the Ext value.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable (J : Ideal R) (P : ModuleCat.{u} R)
  (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (j n : ℕ)

/-- The target boundary is actual precomposition by the Ext boundary. -/
def localDualityTargetYonedaBoundary :
    localDualityTargetValue J S.X₃ P (j + 1) n ⟶ localDualityTargetValue J S.X₁ P j n :=
  ModuleCat.ofHom
    { toFun := fun φ => φ.comp (moduleExtYonedaContravariantBoundary P S hS j).hom
      map_add' := by intro φ ψ; rfl
      map_smul' := by intro r φ; rfl }

@[simp]
theorem localDualityTargetYonedaBoundary_apply
    (φ : localDualityTargetValue J S.X₃ P (j + 1) n) (x : moduleExtValue S.X₁ P j) :
    localDualityTargetYonedaBoundary J P S hS j n φ x =
      φ (moduleExtYonedaContravariantBoundary P S hS j x) := rfl

@[reassoc (attr := simp)]
theorem localDualityTargetYonedaBoundary_comp :
    localDualityTargetYonedaBoundary J P S hS j n ≫
      (localDualityTargetFunctor J P j n).map S.f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  change φ ((moduleExtYonedaContravariantBoundary P S hS j)
    (((_root_.Ext R (ModuleCat.{u} R) j).map S.f.op).app P x)) = 0
  have h := ConcreteCategory.congr_hom (comp_moduleExtYonedaContravariantBoundary P S hS j) x
  change (moduleExtYonedaContravariantBoundary P S hS j)
    (((_root_.Ext R (ModuleCat.{u} R) j).map S.f.op).app P x) = 0 at h
  rw [h, map_zero]

/-- Injective Hom gives exactness after the target boundary. -/
theorem localDualityTargetYoneda_exact
    [Injective ((_root_.localCohomology J n).obj P)] :
    (ShortComplex.mk _ _ (localDualityTargetYonedaBoundary_comp J P S hS j n)).Exact := by
  let D := (linearYoneda R (ModuleCat.{u} R)).obj ((_root_.localCohomology J n).obj P)
  let T := ShortComplex.mk _ _ (comp_moduleExtYonedaContravariantBoundary P S hS j)
  have hT : (T.op.map D).Exact :=
    (moduleExtYoneda_contravariant_exact₁ P S hS j).op.map D
  apply ShortComplex.exact_of_iso _ hT
  exact (ShortComplex.isoMk
    ((localDualityTargetIsoHom J P (j + 1) n).app S.X₃)
    ((localDualityTargetIsoHom J P j n).app S.X₁)
    ((localDualityTargetIsoHom J P j n).app S.X₂) (by rfl) (by rfl)).symm

/-- Vanishing of positive Ext on the free middle term makes the target
boundary monic. -/
theorem localDualityTargetYonedaBoundary_mono
    (hz : IsZero (moduleExtValue S.X₂ P (j + 1))) :
    Mono (localDualityTargetYonedaBoundary J P S hS j n) := by
  have : Epi (moduleExtYonedaContravariantBoundary P S hS j) :=
    (moduleExtYoneda_contravariant_exact₃ P S hS j).epi_f (hz.eq_zero_of_tgt _)
  apply (ModuleCat.mono_iff_injective _).mpr
  intro φ ψ h
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective
    (moduleExtYonedaContravariantBoundary P S hS j)).mp inferInstance x
  exact congrArg (fun z : localDualityTargetValue J S.X₁ P j n => z y) h

end SGA.SGA2.ExposeV
