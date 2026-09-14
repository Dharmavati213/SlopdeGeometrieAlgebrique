/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The Yoneda pairing and the two actual Ext boundaries

This file constructs the linear pairing of Exposé V, §1 from the original
derived-category `Abelian.Ext.comp`.  It is natural in the two outer variables,
balanced in the middle variable, and compatible with the actual covariant and
contravariant Ext connecting maps.  The latter maps are identified with the
third arrows of mathlib's original Ext long exact sequences, so the boundary
identity does not assume an unspecified connecting-map comparison.

The result addresses the Yoneda-pairing content of V.1.5. The companion file
`InjectiveHomComplexProduct.lean` identifies original Hom-complex composition
with this Yoneda product and tracks the displayed source convention through
its explicit sign correction. `ModuleExtCoefficientBoundaryComparison.lean`
identifies the separately constructed module-valued coefficient boundary with
the signed Yoneda boundary in every degree. `HomComplexContravariantBoundary.lean`
and `SourceHomContravariantBoundary.lean` compare actual contravariant Hom
boundaries with the derived connecting arrow into K-injective targets.
`InjectiveHomModuleExtBoundary.lean` now specializes both boundaries through
the original augmentation and module-valued Ext comparisons for a supplied
augmented short exact resolution sequence. Construction of such sequences
and their coherent resolution-comparison maps remains open.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R]

/-- The original Yoneda composition, linear in both entries, with an explicit
total-degree equality. -/
def extPairing (N M P : ModuleCat.{u} R) (i j k : ℕ) (h : i + j = k) :
    Abelian.Ext N M i →ₗ[R] (Abelian.Ext M P j →ₗ[R] Abelian.Ext N P k) :=
  Abelian.Ext.bilinearCompOfLinear R N M P i j k h

@[simp]
theorem extPairing_apply (N M P : ModuleCat.{u} R) (i j k : ℕ)
    (h : i + j = k) (α : Abelian.Ext N M i) (β : Abelian.Ext M P j) :
    extPairing N M P i j k h α β = α.comp β h := rfl

/-- Naturality in the contravariant outer variable, using the original
degree-zero class of the module map. -/
theorem extPairing_naturality_first {N N' M P : ModuleCat.{u} R}
    (f : N' ⟶ N) {i j k : ℕ} (h : i + j = k)
    (α : Abelian.Ext N M i) (β : Abelian.Ext M P j) :
    extPairing N' M P i j k h ((Abelian.Ext.mk₀ f).comp α (zero_add i)) β =
      (Abelian.Ext.mk₀ f).comp (extPairing N M P i j k h α β) (zero_add k) := by
  exact Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ f) α β (zero_add i) h (by omega)

/-- Middle-variable naturality: postcomposition in the first Ext factor and
precomposition in the second Ext factor give the same pairing. -/
theorem extPairing_naturality_middle {N M M' P : ModuleCat.{u} R}
    (f : M ⟶ M') {i j k : ℕ} (h : i + j = k)
    (α : Abelian.Ext N M i) (β : Abelian.Ext M' P j) :
    extPairing N M' P i j k h (α.comp (Abelian.Ext.mk₀ f) (add_zero i)) β =
      extPairing N M P i j k h α ((Abelian.Ext.mk₀ f).comp β (zero_add j)) :=
  Abelian.Ext.comp_assoc_of_second_deg_zero α (Abelian.Ext.mk₀ f) β h

/-- Naturality in the covariant outer variable. -/
theorem extPairing_naturality_last {N M P P' : ModuleCat.{u} R}
    (f : P ⟶ P') {i j k : ℕ} (h : i + j = k)
    (α : Abelian.Ext N M i) (β : Abelian.Ext M P j) :
    (extPairing N M P i j k h α β).comp (Abelian.Ext.mk₀ f) (add_zero k) =
      extPairing N M P' i j k h α (β.comp (Abelian.Ext.mk₀ f) (add_zero j)) :=
  Abelian.Ext.comp_assoc_of_third_deg_zero α β (Abelian.Ext.mk₀ f) h

/-- The first-variable identity for the literal original Ext functor maps. -/
theorem extPairing_extFunctor_naturality_first {N N' M P : ModuleCat.{u} R}
    (f : N' ⟶ N) {i j k : ℕ} (h : i + j = k)
    (α : Abelian.Ext N M i) (β : Abelian.Ext M P j) :
    extPairing N' M P i j k h (((Abelian.extFunctor i).map f.op).app M α) β =
      ((Abelian.extFunctor k).map f.op).app P (extPairing N M P i j k h α β) :=
  extPairing_naturality_first f h α β

/-- The middle-variable identity for the literal original Ext functor maps. -/
theorem extPairing_extFunctor_naturality_middle {N M M' P : ModuleCat.{u} R}
    (f : M ⟶ M') {i j k : ℕ} (h : i + j = k)
    (α : Abelian.Ext N M i) (β : Abelian.Ext M' P j) :
    extPairing N M' P i j k h ((Abelian.extFunctorObj N i).map f α) β =
      extPairing N M P i j k h α (((Abelian.extFunctor j).map f.op).app P β) :=
  extPairing_naturality_middle f h α β

/-- The final-variable identity for the literal original Ext functor maps. -/
theorem extPairing_extFunctor_naturality_last {N M P P' : ModuleCat.{u} R}
    (f : P ⟶ P') {i j k : ℕ} (h : i + j = k)
    (α : Abelian.Ext N M i) (β : Abelian.Ext M P j) :
    (Abelian.extFunctorObj N k).map f (extPairing N M P i j k h α β) =
      extPairing N M P' i j k h α ((Abelian.extFunctorObj M j).map f β) :=
  extPairing_naturality_last f h α β

/-- The covariant Ext boundary, with its actual linear structure. -/
def extCovariantBoundary (N : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (i i' : ℕ) (hi : i + 1 = i') :
    Abelian.Ext N S.X₃ i →ₗ[R] Abelian.Ext N S.X₁ i' :=
  hS.extClass.postcompOfLinear R N hi

/-- The contravariant Ext boundary, with its actual linear structure. -/
def extContravariantBoundary (P : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (j j' : ℕ) (hj : 1 + j = j') :
    Abelian.Ext S.X₁ P j →ₗ[R] Abelian.Ext S.X₃ P j' :=
  hS.extClass.precompOfLinear R P hj

@[simp]
theorem extCovariantBoundary_apply (N : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (i i' : ℕ) (hi : i + 1 = i') (α : Abelian.Ext N S.X₃ i) :
    extCovariantBoundary N S hS i i' hi α = α.comp hS.extClass hi := rfl

@[simp]
theorem extContravariantBoundary_apply (P : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (j j' : ℕ) (hj : 1 + j = j') (β : Abelian.Ext S.X₁ P j) :
    extContravariantBoundary P S hS j j' hj β = hS.extClass.comp β hj := rfl

/-- After forgetting scalars, the covariant boundary is literally the third
arrow of the original covariant Ext long exact sequence. -/
theorem extCovariantBoundary_eq_sequence_map (N : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (i i' : ℕ) (hi : i + 1 = i') :
    AddCommGrpCat.ofHom (extCovariantBoundary N S hS i i' hi).toAddMonoidHom =
      (Abelian.Ext.covariantSequence N hS i i' hi).map' 2 3 := rfl

/-- After forgetting scalars, the contravariant boundary is literally the third
arrow of the original contravariant Ext long exact sequence. -/
theorem extContravariantBoundary_eq_sequence_map (P : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (j j' : ℕ) (hj : 1 + j = j') :
    AddCommGrpCat.ofHom (extContravariantBoundary P S hS j j' hj).toAddMonoidHom =
      (Abelian.Ext.contravariantSequence hS P j j' hj).map' 2 3 := rfl

/-- V.1.5: pairing with the covariant connecting class agrees with pairing
with the contravariant connecting class.  Both boundaries are the actual
Ext long exact sequence maps, with no additional sign. -/
theorem extPairing_connecting (N P : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    {i i' j j' k : ℕ} (hi : i + 1 = i') (hj : 1 + j = j')
    (hleft : i' + j = k) (hright : i + j' = k)
    (α : Abelian.Ext N S.X₃ i) (β : Abelian.Ext S.X₁ P j) :
    extPairing N S.X₁ P i' j k hleft
        (extCovariantBoundary N S hS i i' hi α) β =
      extPairing N S.X₃ P i j' k hright α
        (extContravariantBoundary P S hS j j' hj β) := by
  exact Abelian.Ext.comp_assoc α hS.extClass β hi hj (by omega)

/-- The boundary compatibility with the two literal long exact sequence
arrows in the statement, rather than separately named boundary maps. -/
theorem extPairing_sequence_connecting (N P : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    {i i' j j' k : ℕ} (hi : i + 1 = i') (hj : 1 + j = j')
    (hleft : i' + j = k) (hright : i + j' = k)
    (α : Abelian.Ext N S.X₃ i) (β : Abelian.Ext S.X₁ P j) :
    extPairing N S.X₁ P i' j k hleft
        (((Abelian.Ext.covariantSequence N hS i i' hi).map' 2 3) α) β =
      extPairing N S.X₃ P i j' k hright α
        (((Abelian.Ext.contravariantSequence hS P j j' hj).map' 2 3) β) :=
  extPairing_connecting N P S hS hi hj hleft hright α β

/-- In degree zero the pairing is the actual composition of module maps. -/
@[simp]
theorem extPairing_mk₀ (N M P : ModuleCat.{u} R) (f : N ⟶ M) (g : M ⟶ P) :
    extPairing N M P 0 0 0 rfl (Abelian.Ext.mk₀ f) (Abelian.Ext.mk₀ g) =
      Abelian.Ext.mk₀ (f ≫ g) := Abelian.Ext.mk₀_comp_mk₀ f g

end SGA.SGA2.ExposeV
