/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Exact.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# SGA 2, Exposé II, Lemmas 9 and 11: essentially zero systems

An inverse system is essentially zero if every term receives a zero transition
map from some later term. We prove the elementary system arguments used in
II.9(c) ⇒ (b) and in the last paragraph of the proof of II.11: contravariant
functors preserving zero maps send such systems to diagrams with zero colimit,
and essentially zero systems of modules are closed under subobjects, quotients,
and extensions. No Koszul or local-cohomology comparison is assumed here.
-/

universe u v w

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeII

section Categories

variable {J : Type u} [Category J] {C : Type v} [Category C] [HasZeroMorphisms C]

/-- II.9(c), for a general indexing category: every object receives a
transition mapped to zero. For inverse sequences, this is equivalent to
requiring a strictly later index. -/
def IsEssentiallyZero (F : J ⥤ C) : Prop :=
  ∀ j : J, ∃ (k : J) (f : k ⟶ j), F.map f = 0

/-- The colimit of a diagram in which each object has an outgoing zero
transition is zero. This uses only the colimit universal property. -/
theorem isZero_colimit_of_zero_transitions (F : J ⥤ C) [HasColimit F]
    (h : ∀ j : J, ∃ (k : J) (f : j ⟶ k), F.map f = 0) :
    IsZero (colimit F) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro j
  obtain ⟨k, f, hf⟩ := h j
  have hι : colimit.ι F j = 0 := by
    rw [← colimit.w F f, hf, zero_comp]
  simp [hι]

/-- II.9(c) ⇒ (b), the diagram argument: a contravariant functor preserving
zero maps sends an essentially zero system to a diagram with zero colimit.
In SGA the functor is `Hom(-, M)` after identifying cohomology for injective `M`. -/
theorem IsEssentiallyZero.isZero_colimit
    {D : Type w} [Category D] [HasZeroMorphisms D]
    {F : J ⥤ C} (hF : IsEssentiallyZero F) (G : Cᵒᵖ ⥤ D)
    [G.PreservesZeroMorphisms] [HasColimit (F.op ⋙ G)] :
    IsZero (colimit (F.op ⋙ G)) := by
  apply isZero_colimit_of_zero_transitions
  intro j
  obtain ⟨k, f, hf⟩ := hF j.unop
  refine ⟨op k, f.op, ?_⟩
  simp [hf]

/-- Essentially zero systems are preserved by functors preserving zero maps. -/
theorem IsEssentiallyZero.comp
    {D : Type w} [Category D] [HasZeroMorphisms D]
    {F : J ⥤ C} (hF : IsEssentiallyZero F) (G : C ⥤ D)
    [G.PreservesZeroMorphisms] : IsEssentiallyZero (F ⋙ G) := by
  intro j
  obtain ⟨k, f, hf⟩ := hF j
  exact ⟨k, f, by simp [hf]⟩

/-- An objectwise subobject of an essentially zero inverse system is
essentially zero. -/
theorem IsEssentiallyZero.of_mono {F G : J ⥤ C} (α : F ⟶ G)
    [∀ j, Mono (α.app j)] (hG : IsEssentiallyZero G) : IsEssentiallyZero F := by
  intro j
  obtain ⟨k, f, hf⟩ := hG j
  refine ⟨k, f, (cancel_mono (α.app j)).mp ?_⟩
  rw [α.naturality, hf, comp_zero, zero_comp]

/-- An objectwise quotient of an essentially zero inverse system is
essentially zero, as used for the left terms in the induction in II.11. -/
theorem IsEssentiallyZero.of_epi {F G : J ⥤ C} (α : F ⟶ G)
    [∀ j, Epi (α.app j)] (hF : IsEssentiallyZero F) : IsEssentiallyZero G := by
  intro j
  obtain ⟨k, f, hf⟩ := hF j
  refine ⟨k, f, (cancel_epi (α.app k)).mp ?_⟩
  rw [← α.naturality, hf, zero_comp, comp_zero]

end Categories

section Sequences

variable {C : Type v} [Category C] [HasZeroMorphisms C]

/-- II.9(c): for sequences the definition can require a strictly later index,
as in the English text. -/
theorem isEssentiallyZero_iff_strict (F : ℕᵒᵖ ⥤ C) :
    IsEssentiallyZero F ↔
      ∀ n : ℕ, ∃ (m : ℕ) (h : n < m), F.map (homOfLE h.le).op = 0 := by
  constructor
  · intro hF n
    obtain ⟨k, f, hf⟩ := hF (op n)
    have hnk : n ≤ k.unop := leOfHom f.unop
    refine ⟨k.unop + 1, by omega, ?_⟩
    have heq : (homOfLE (show n ≤ k.unop + 1 by omega)).op =
        (homOfLE (Nat.le_succ k.unop)).op ≫ f := Subsingleton.elim _ _
    rw [heq, F.map_comp, hf, comp_zero]
  · intro hF n
    obtain ⟨m, h, hm⟩ := hF n.unop
    exact ⟨op m, (homOfLE h.le).op, hm⟩

end Sequences

section Modules

variable {J : Type u} [Category J] {R : Type v} [Ring R]
  {A B C : J ⥤ ModuleCat.{w} R}

/-- II.11, final step: in an objectwise exact sequence of inverse systems,
if the outer systems are essentially zero, the middle system is too.
The maps need not be injective or surjective. -/
theorem IsEssentiallyZero.of_exact (α : A ⟶ B) (β : B ⟶ C)
    (hexact : ∀ j, Function.Exact (α.app j) (β.app j))
    (hA : IsEssentiallyZero A) (hC : IsEssentiallyZero C) :
    IsEssentiallyZero B := by
  intro j
  obtain ⟨k, f, hf⟩ := hA j
  obtain ⟨l, g, hg⟩ := hC k
  refine ⟨l, g ≫ f, ?_⟩
  ext x
  change B.map (g ≫ f) x = 0
  have hx : β.app k (B.map g x) = 0 := by
    change (B.map g ≫ β.app k) x = 0
    rw [β.naturality, hg, comp_zero]
    rfl
  obtain ⟨y, hy⟩ := (hexact k (B.map g x)).mp hx
  have hy' : B.map f (α.app k y) = 0 := by
    have h := congrArg (fun t : A.obj k ⟶ B.obj j ↦ t y) (α.naturality f)
    simpa [hf] using h.symm
  simpa only [Functor.map_comp, ModuleCat.comp_apply, hy] using hy'

end Modules

section HomColimits

variable {R : Type v} [CommRing R] {F : ℕᵒᵖ ⥤ ModuleCat.{v} R}

/-- II.9(c) ⇒ (b), specialized to the actual module-valued Hom functor:
the direct limit of `Hom(F_n, M)` is zero for an essentially zero system `F`.
Injectivity of `M` is needed elsewhere in SGA to identify these Hom modules
with Koszul cohomology; this colimit statement holds for every `M`. -/
theorem IsEssentiallyZero.isZero_hom_colimit (hF : IsEssentiallyZero F)
    (M : ModuleCat.{v} R) :
    IsZero (colimit (F.op ⋙ (linearYoneda R (ModuleCat.{v} R)).obj M)) :=
  hF.isZero_colimit _

end HomColimits

end SGA.SGA2.ExposeII
