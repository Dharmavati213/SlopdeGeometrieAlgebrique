/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Sections of `𝒪_X`-modules

Small lemmas about sections of `𝒪_X`-modules used in this directory: restriction along an
equality of opens is injective, sections are determined locally, and a module is zero if and only
if all its modules of sections are.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}

lemma presheaf_map_injective_of_eq (M : X.Modules) {W W' : X.Opens} (i : W ⟶ W') (h : W = W') :
    Function.Injective (M.presheaf.map i.op) := by
  subst h
  rw [Subsingleton.elim i (𝟙 W), op_id, M.presheaf.map_id]
  exact Function.injective_id

/-- Two composites of restriction maps with the same source and target agree. -/
lemma presheaf_map_map (M : X.Modules) {A B C D : X.Opens} (f : A ⟶ B) (g : B ⟶ C) (f' : A ⟶ D)
    (g' : D ⟶ C) (x : Γ(M, C)) :
    M.presheaf.map f.op (M.presheaf.map g.op x) =
      M.presheaf.map f'.op (M.presheaf.map g'.op x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, ← op_comp, ← op_comp, Subsingleton.elim (f ≫ g) (f' ≫ g')]

/-- A section of an `𝒪_X`-module is zero if it is zero on a neighbourhood of every point. -/
lemma eq_zero_of_locally {U : X.Opens} (s : Γ(M, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ M.presheaf.map (homOfLE hV).op s = 0) :
    s = 0 :=
  M.isSheaf.section_ext (U := op U) fun x hx ↦ by
    obtain ⟨V, hV, hxV, h⟩ := h x hx
    exact ⟨V, hV, hxV, by rw [h, map_zero]⟩

/-- An `𝒪_X`-module is zero if and only if all its modules of sections are. -/
lemma isZero_iff_forall_subsingleton : IsZero M ↔ ∀ U : X.Opens, Subsingleton Γ(M, U) := by
  rw [IsZero.iff_id_eq_zero]
  refine ⟨fun h U ↦ ⟨fun x y ↦ ?_⟩, fun h ↦ hom_ext _ _ fun U ↦ ?_⟩
  · have h' (z : Γ(M, U)) : z = 0 := by
      simpa using congr($(congr(Hom.app $h U)) z)
    rw [h' x, h' y]
  · ext x
    exact Subsingleton.elim _ _

end AlgebraicGeometry.Scheme.Modules
