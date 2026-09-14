/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Ext adjunction for exact restriction

The Hom adjunction extends to actual derived-category Ext whenever the
right adjoint is exact and preserves injectives. The map is constructed
by applying the exact right adjoint and precomposing with the unit.
-/

noncomputable section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory Limits Abelian

namespace SGA.SGA2.ExposeI

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D]
  {F : C ⥤ D} {G : D ⥤ C} [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

set_option backward.isDefEq.respectTransparency false

/-- The actual Ext adjunction map: exact functoriality followed by the unit. -/
def adjunctionExtMap (adj : F ⊣ G) (A : C) (B : D) (n : ℕ) :
    Ext.{w₂} (F.obj A) B n →+ Ext.{w₁} A (G.obj B) n :=
  ((Ext.mk₀ (adj.unit.app A)).precomp (G.obj B) (zero_add n)).comp
    (G.mapExtAddHom (F.obj A) B n)

theorem adjunctionExtMap_apply (adj : F ⊣ G) (A : C) (B : D) (n : ℕ)
    (x : Ext.{w₂} (F.obj A) B n) :
    adjunctionExtMap adj A B n x =
      (Ext.mk₀ (adj.unit.app A)).comp (x.mapExactFunctor G) (zero_add n) := rfl

/-- The Ext adjunction map agrees with the Hom adjunction in degree zero. -/
theorem adjunctionExtMap_mk₀ (adj : F ⊣ G) (A : C) (B : D) (f : F.obj A ⟶ B) :
    adjunctionExtMap adj A B 0 (Ext.mk₀ f) = Ext.mk₀ (adj.homEquiv A B f) := by
  simp only [adjunctionExtMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀,
    Adjunction.homEquiv_apply]

/-- Naturality in the coefficient object. -/
theorem adjunctionExtMap_naturality (adj : F ⊣ G) (A : C) {B B' : D}
    (f : B ⟶ B') (n : ℕ) (x : Ext.{w₂} (F.obj A) B n) :
    adjunctionExtMap adj A B' n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (adjunctionExtMap adj A B n x).comp (Ext.mk₀ (G.map f)) (add_zero n) := by
  simp only [adjunctionExtMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- The Ext adjunction map respects the genuine coefficient boundaries. -/
theorem adjunctionExtMap_boundary (adj : F ⊣ G) (A : C)
    {S : ShortComplex D} (hS : S.ShortExact) (n : ℕ)
    (x : Ext.{w₂} (F.obj A) S.X₃ n) :
    adjunctionExtMap adj A S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (adjunctionExtMap adj A S.X₃ n x).comp (hS.map_of_exact G).extClass rfl := by
  simp only [adjunctionExtMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

/-- Degree-zero bijectivity comes from the actual Hom adjunction. -/
theorem adjunctionExtMap_zero_bijective (adj : F ⊣ G) (A : C) (B : D) :
    Function.Bijective (adjunctionExtMap adj A B 0) := by
  have h : (adjunctionExtMap adj A B 0 : _ → _) =
      Ext.addEquiv₀.symm ∘ adj.homEquiv A B ∘ Ext.addEquiv₀ := by
    funext x
    obtain ⟨f, rfl⟩ := Ext.mk₀_bijective (F.obj A) B |>.surjective x
    simp only [adjunctionExtMap_mk₀, Function.comp_apply]
    change Ext.addEquiv₀.symm _ = Ext.addEquiv₀.symm _
    rw [show Ext.addEquiv₀ (Ext.mk₀ f) = f from Ext.addEquiv₀.apply_symm_apply f]
  rw [h]
  exact Ext.addEquiv₀.symm.bijective.comp
    ((adj.homEquiv A B).bijective.comp Ext.addEquiv₀.bijective)

attribute [local instance] Ext.subsingleton_of_injective in
/-- An exact right adjoint preserving injectives induces the Ext adjunction
in every degree, by dimension shifting along injective presentations. -/
theorem adjunctionExtMap_bijective [EnoughInjectives D] [G.PreservesInjectiveObjects]
    (adj : F ⊣ G) (A : C) (B : D) (n : ℕ) :
    Function.Bijective (adjunctionExtMap adj A B n) := by
  induction n generalizing B with
  | zero => exact adjunctionExtMap_zero_bijective adj A B
  | succ n hn =>
    let I : InjectivePresentation B := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map G).X₂ :=
      Functor.PreservesInjectiveObjects.injective_obj I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (adjunctionExtMap adj A S.X₂ n) (adjunctionExtMap adj A S.X₃ n)
      (adjunctionExtMap adj A S.X₁ (n + 1))
      (by ext x; exact (adjunctionExtMap_naturality adj A S.g n x).symm)
      (by ext x; exact (adjunctionExtMap_boundary adj A hS n x).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (F.obj A) hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A (hS.map_of_exact G) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map_of_exact G) y₁
        (by subsingleton) rfl)

/-- The additive Ext adjunction, for an exact right adjoint preserving injectives. -/
def adjunctionExtEquiv [EnoughInjectives D] [G.PreservesInjectiveObjects]
    (adj : F ⊣ G) (A : C) (B : D) (n : ℕ) :
    Ext.{w₂} (F.obj A) B n ≃+ Ext.{w₁} A (G.obj B) n :=
  AddEquiv.ofBijective _ (adjunctionExtMap_bijective adj A B n)

theorem adjunctionExtEquiv_apply [EnoughInjectives D] [G.PreservesInjectiveObjects]
    (adj : F ⊣ G) (A : C) (B : D) (n : ℕ)
    (x : Ext.{w₂} (F.obj A) B n) :
    adjunctionExtEquiv adj A B n x = adjunctionExtMap adj A B n x := rfl

end SGA.SGA2.ExposeI
