/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.ModuleExtYonedaBoundary
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exactness of Yoneda sequences on original module Ext

Exactness is transported through the proved canonical linear comparison.
All degree-preserving arrows are the original module-valued Ext maps.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
  (hS : S.ShortExact) (i : ℕ)

@[reassoc (attr := simp)]
theorem moduleExtYonedaCovariantBoundary_comp :
    moduleExtYonedaCovariantBoundary N S hS i ≫
      ((_root_.Ext R (ModuleCat.{u} R) (i + 1)).obj (op N)).map S.f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (moduleExtLinearEquivAbelianExt N S.X₂ (i + 1)).injective
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero, moduleExtLinearEquivAbelianExt_naturality_coefficient,
    moduleExtYonedaCovariantBoundary_compare, Abelian.Ext.comp_assoc_of_third_deg_zero,
    hS.extClass_comp, Abelian.Ext.comp_zero]

@[reassoc (attr := simp)]
theorem comp_moduleExtYonedaCovariantBoundary :
    ((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).map S.g ≫
      moduleExtYonedaCovariantBoundary N S hS i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (moduleExtLinearEquivAbelianExt N S.X₁ (i + 1)).injective
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero, moduleExtYonedaCovariantBoundary_compare,
    moduleExtLinearEquivAbelianExt_naturality_coefficient,
    Abelian.Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Abelian.Ext.comp_zero]

/-- Exactness immediately after the original-object Yoneda boundary. -/
theorem moduleExtYoneda_covariant_exact₁ :
    (ShortComplex.mk _ _ (moduleExtYonedaCovariantBoundary_comp N S hS i)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' := congrArg (moduleExtLinearEquivAbelianExt N S.X₂ (i + 1)) hx
  simp only [moduleExtLinearEquivAbelianExt_naturality_coefficient, map_zero] at hx'
  obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ N hS
    (moduleExtLinearEquivAbelianExt N S.X₁ (i + 1) x) hx' rfl
  refine ⟨(moduleExtLinearEquivAbelianExt N S.X₃ i).symm y, ?_⟩
  apply (moduleExtLinearEquivAbelianExt N S.X₁ (i + 1)).injective
  simpa only [moduleExtYonedaCovariantBoundary_compare, LinearEquiv.apply_symm_apply] using hy

/-- Exactness immediately before the original-object Yoneda boundary. -/
theorem moduleExtYoneda_covariant_exact₃ :
    (ShortComplex.mk _ _ (comp_moduleExtYonedaCovariantBoundary N S hS i)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' := congrArg (moduleExtLinearEquivAbelianExt N S.X₁ (i + 1)) hx
  simp only [moduleExtYonedaCovariantBoundary_compare, map_zero] at hx'
  obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₃ N hS
    (moduleExtLinearEquivAbelianExt N S.X₃ i x) rfl hx'
  refine ⟨(moduleExtLinearEquivAbelianExt N S.X₂ i).symm y, ?_⟩
  apply (moduleExtLinearEquivAbelianExt N S.X₃ i).injective
  simpa only [moduleExtLinearEquivAbelianExt_naturality_coefficient,
    LinearEquiv.apply_symm_apply] using hy

@[reassoc (attr := simp)]
theorem comp_moduleExtYonedaContravariantBoundary :
    ((_root_.Ext R (ModuleCat.{u} R) i).map S.f.op).app N ≫
      moduleExtYonedaContravariantBoundary N S hS i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (moduleExtLinearEquivAbelianExt S.X₃ N (i + 1)).injective
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero, moduleExtYonedaContravariantBoundary_compare,
    moduleExtLinearEquivAbelianExt_naturality_first, hS.extClass_comp_assoc]

@[reassoc (attr := simp)]
theorem moduleExtYonedaContravariantBoundary_comp :
    moduleExtYonedaContravariantBoundary N S hS i ≫
      ((_root_.Ext R (ModuleCat.{u} R) (i + 1)).map S.g.op).app N = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (moduleExtLinearEquivAbelianExt S.X₂ N (i + 1)).injective
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero, moduleExtLinearEquivAbelianExt_naturality_first,
    moduleExtYonedaContravariantBoundary_compare, hS.comp_extClass_assoc]

/-- Exactness before the contravariant boundary. -/
theorem moduleExtYoneda_contravariant_exact₁ :
    (ShortComplex.mk _ _ (comp_moduleExtYonedaContravariantBoundary N S hS i)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' := congrArg (moduleExtLinearEquivAbelianExt S.X₃ N (i + 1)) hx
  simp only [moduleExtYonedaContravariantBoundary_compare, map_zero] at hx'
  obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS N
    (moduleExtLinearEquivAbelianExt S.X₁ N i x) (Nat.add_comm 1 i) hx'
  refine ⟨(moduleExtLinearEquivAbelianExt S.X₂ N i).symm y, ?_⟩
  apply (moduleExtLinearEquivAbelianExt S.X₁ N i).injective
  simpa only [moduleExtLinearEquivAbelianExt_naturality_first,
    LinearEquiv.apply_symm_apply] using hy

/-- Exactness after the contravariant boundary. -/
theorem moduleExtYoneda_contravariant_exact₃ :
    (ShortComplex.mk _ _ (moduleExtYonedaContravariantBoundary_comp N S hS i)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' := congrArg (moduleExtLinearEquivAbelianExt S.X₂ N (i + 1)) hx
  simp only [moduleExtLinearEquivAbelianExt_naturality_first, map_zero] at hx'
  obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS N
    (moduleExtLinearEquivAbelianExt S.X₃ N (i + 1) x) hx' (Nat.add_comm 1 i)
  refine ⟨(moduleExtLinearEquivAbelianExt S.X₁ N i).symm y, ?_⟩
  apply (moduleExtLinearEquivAbelianExt S.X₃ N (i + 1)).injective
  simpa only [moduleExtYonedaContravariantBoundary_compare, LinearEquiv.apply_symm_apply] using hy

end SGA.SGA2.ExposeV
