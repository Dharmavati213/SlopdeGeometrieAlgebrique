/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.RestrictionRedundancy
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Coefficient dimension shifting for actual cohomology restriction

The relative restriction is an actual Ext precomposition, followed by the
proved open-support comparison. Its coefficient long exact sequences
therefore commute by Ext associativity. The five lemma propagates ordinary
restriction bijectivity from a short exact sequence to its cokernel.
-/

noncomputable section

universe u v w

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian
open SGA.SGA2.ExposeI

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

section Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {A B : C} (f : A ⟶ B)

/-- Actual Ext precomposition commutes with every coefficient Ext class,
in particular with the connecting class of a short exact sequence. -/
theorem extPrecomp_postcomp_comm {M N : C} {i j k : ℕ}
    (β : Ext M N j) (h : i + j = k) :
    AddCommGrpCat.ofHom (β.postcomp B h) ≫
        AddCommGrpCat.ofHom ((Ext.mk₀ f).precomp N (zero_add k)) =
      AddCommGrpCat.ofHom ((Ext.mk₀ f).precomp M (zero_add i)) ≫
        AddCommGrpCat.ofHom (β.postcomp A h) := by
  ext x
  exact (Ext.comp_assoc (Ext.mk₀ f) x β (zero_add i) h (by omega)).symm

/-- The actual map between five consecutive terms of the coefficient
Ext sequences, induced by a fixed map in the first variable. -/
def extPrecompCoefficientSequenceMap {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (Ext.covariantSequence B hS n (n + 1) rfl).δlast ⟶
      (Ext.covariantSequence A hS n (n + 1) rfl).δlast :=
  ComposableArrows.homMk₄
    (AddCommGrpCat.ofHom ((Ext.mk₀ f).precomp S.X₁ (zero_add n)))
    (AddCommGrpCat.ofHom ((Ext.mk₀ f).precomp S.X₂ (zero_add n)))
    (AddCommGrpCat.ofHom ((Ext.mk₀ f).precomp S.X₃ (zero_add n)))
    (AddCommGrpCat.ofHom ((Ext.mk₀ f).precomp S.X₁ (zero_add (n + 1))))
    (AddCommGrpCat.ofHom ((Ext.mk₀ f).precomp S.X₂ (zero_add (n + 1))))
    (extPrecomp_postcomp_comm f (Ext.mk₀ S.f) (add_zero n))
    (extPrecomp_postcomp_comm f (Ext.mk₀ S.g) (add_zero n))
    (extPrecomp_postcomp_comm f hS.extClass rfl)
    (extPrecomp_postcomp_comm f (Ext.mk₀ S.f) (add_zero (n + 1)))

/-- Bijectivity of actual Ext precomposition passes to the cokernel
coefficient by the five lemma for the genuine coefficient sequence. -/
theorem extPrecomp_bijective_cokernel {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    (h₁ : Function.Bijective ((Ext.mk₀ f).precomp S.X₁ (zero_add n)))
    (h₂ : Function.Bijective ((Ext.mk₀ f).precomp S.X₂ (zero_add n)))
    (h₃ : Function.Bijective ((Ext.mk₀ f).precomp S.X₁ (zero_add (n + 1))))
    (h₄ : Function.Bijective ((Ext.mk₀ f).precomp S.X₂ (zero_add (n + 1)))) :
    Function.Bijective ((Ext.mk₀ f).precomp S.X₃ (zero_add n)) := by
  let φ := extPrecompCoefficientSequenceMap f hS n
  have hsource := ((Ext.covariantSequence B hS n (n + 1) rfl).exact_iff_δlast.mp
    (Ext.covariantSequence_exact B hS n (n + 1) rfl)).1
  have htarget := ((Ext.covariantSequence A hS n (n + 1) rfl).exact_iff_δlast.mp
    (Ext.covariantSequence_exact A hS n (n + 1) rfl)).1
  have h₀ : Epi (ComposableArrows.app' φ 0) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr h₁.surjective
  have hi₁ : IsIso (ComposableArrows.app' φ 1) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h₂
  have hi₃ : IsIso (ComposableArrows.app' φ 3) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h₃
  have hi₄ : Mono (ComposableArrows.app' φ 4) :=
    (AddCommGrpCat.mono_iff_injective _).mpr h₄.injective
  have hmid := Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    hsource htarget φ h₀ hi₁ hi₃ hi₄
  exact (ConcreteCategory.isIso_iff_bijective (ComposableArrows.app' φ 2)).mp hmid

end Ext

section Sheaves

variable {X : TopCat.{u}}

/-- The original relative map is bijective exactly when its actual Ext
precomposition is; the open-support comparison is an already proved iso. -/
theorem relativeRestriction_bijective_iff_extPrecomp (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Function.Bijective (relativeRestriction Z F n) ↔
      Function.Bijective ((Ext.mk₀ (zZX_openToConstant Z.compl)).precomp F (zero_add n)) :=
  (openSupportExtEquiv Z.compl F n).bijective.of_comp_iff' _

/-- The coefficient five lemma for the original relative restriction.
Its identification with ordinary restriction holds in every degree. -/
theorem relativeRestriction_bijective_cokernel (Z : Closeds X)
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) (n : ℕ)
    (h₁ : Function.Bijective (relativeRestriction Z S.X₁ n))
    (h₂ : Function.Bijective (relativeRestriction Z S.X₂ n))
    (h₃ : Function.Bijective (relativeRestriction Z S.X₁ (n + 1)))
    (h₄ : Function.Bijective (relativeRestriction Z S.X₂ (n + 1))) :
    Function.Bijective (relativeRestriction Z S.X₃ n) :=
  (relativeRestriction_bijective_iff_extPrecomp Z S.X₃ n).mpr
    (extPrecomp_bijective_cokernel (zZX_openToConstant Z.compl) hS n
      ((relativeRestriction_bijective_iff_extPrecomp Z S.X₁ n).mp h₁)
      ((relativeRestriction_bijective_iff_extPrecomp Z S.X₂ n).mp h₂)
      ((relativeRestriction_bijective_iff_extPrecomp Z S.X₁ (n + 1)).mp h₃)
      ((relativeRestriction_bijective_iff_extPrecomp Z S.X₂ (n + 1)).mp h₄))

end Sheaves

end SGA.SGA2.ExposeIII
