/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.DerivedFunctors
import SGA.SGA2.ExposeI.Flasque
import SGA.SGA2.ExposeI.InjectiveFlasque

/-!
# Flasque sheaves and actual sheaf cohomology

Section-exactness for a flasque kernel is transported through the canonical
degree-zero comparison to the Ext-defined sheaf cohomology groups. Injective
embeddings and dimension shifting then prove vanishing in every positive
degree. The same result holds on every open subspace.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- A short exact sequence with flasque kernel is surjective on actual
degree-zero sheaf cohomology. -/
theorem surjective_H_zero_map_of_shortExact
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [IsFlasque S.X₁] : Function.Surjective (CategoryTheory.Sheaf.H.map.{u} S.g 0) := by
  have hepi : Epi (S.g.hom.app (op (⊤ : Opens X))) :=
    Sheaf.IsFlasque.epi_of_shortExact hS
  intro x
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hepi
    (CategoryTheory.Sheaf.H.equiv₀.{u} S.X₃ isTerminalTop x)
  refine ⟨(CategoryTheory.Sheaf.H.equiv₀.{u} S.X₂ isTerminalTop).symm s, ?_⟩
  apply (CategoryTheory.Sheaf.H.equiv₀.{u} S.X₃ isTerminalTop).injective
  rw [← CategoryTheory.Sheaf.H.equiv₀_naturality]
  simpa using hs

set_option backward.isDefEq.respectTransparency false in
/-- Degree-one cohomology of a flasque kernel vanishes whenever it embeds
in an injective middle term of a short exact sequence. -/
theorem H_one_subsingleton_of_shortExact
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [IsFlasque S.X₁] [Injective S.X₂] : Subsingleton (H S.X₁ 1) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x
    (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
  obtain ⟨z, rfl⟩ := surjective_H_zero_map_of_shortExact hS y
  rw [← hy]
  simp only [CategoryTheory.Sheaf.H.map_apply,
    Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
    Ext.comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- A flasque sheaf has zero first sheaf cohomology, for the actual Ext
definition of sheaf cohomology. -/
theorem H_one_subsingleton_of_isFlasque
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] : Subsingleton (H F 1) := by
  let S := ShortComplex.cokernelSequence (Injective.ι F)
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := by change Mono (Injective.ι F); infer_instance
      epi_g := by change Epi (cokernel.π (Injective.ι F)); infer_instance }
  have : IsFlasque S.X₁ := ‹IsFlasque F›
  have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
  exact H_one_subsingleton_of_shortExact hS

set_option backward.isDefEq.respectTransparency false in
/-- A flasque sheaf has zero cohomology in every positive degree. This is
acyclicity for ordinary sheaf cohomology, with its actual Ext definition. -/
theorem H_pos_subsingleton_of_isFlasque
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (n : ℕ) :
    Subsingleton (H F (n + 1)) := by
  induction n generalizing F with
  | zero => exact H_one_subsingleton_of_isFlasque F
  | succ n ih =>
    let S := ShortComplex.cokernelSequence (Injective.ι F)
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := by change Mono (Injective.ι F); infer_instance
        epi_g := by change Epi (cokernel.π (Injective.ι F)); infer_instance }
    have : IsFlasque S.X₁ := ‹IsFlasque F›
    have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
    have : IsFlasque S.X₂ := isFlasque_of_injective S.X₂
    have : IsFlasque S.X₃ := Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    have : Subsingleton (H S.X₃ (n + 1)) := ih S.X₃
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x
      (Ext.eq_zero_of_injective _) (n₀ := n + 1) rfl
    have hyzero : y = 0 := Subsingleton.elim _ _
    rw [← hy, hyzero, Ext.zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Flasqueness is preserved by isomorphisms of abelian sheaves. -/
theorem isFlasque_of_iso {F G : Sheaf AddCommGrpCat.{u} X}
    (e : F ≅ G) [IsFlasque G] : IsFlasque F where
  epi {U V} i := by
    let e' : F.obj ≅ G.obj :=
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso e
    have he : F.obj.map i = e'.hom.app U ≫ G.obj.map i ≫ e'.inv.app V := by
      rw [← e'.hom.naturality_assoc, e'.hom_inv_id_app, Category.comp_id]
    rw [he]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along an open embedding preserves flasque abelian sheaves. -/
theorem isFlasque_pullback_of_isOpenEmbedding {Y : TopCat.{u}} {f : Y ⟶ X}
    (hf : Topology.IsOpenEmbedding f) (F : Sheaf AddCommGrpCat.{u} X)
    [IsFlasque F] : IsFlasque ((Sheaf.pullback AddCommGrpCat f).obj F) := by
  have : IsFlasque ((hf.sheafPullback AddCommGrpCat).obj F) :=
    { epi := fun i ↦ inferInstanceAs (Epi (F.obj.map (hf.functor.op.map i))) }
  exact isFlasque_of_iso ((hf.sheafPullbackIso AddCommGrpCat).app F)

/-- A flasque sheaf has zero positive ordinary cohomology on every open
subspace, using the existing actual restriction functor. -/
theorem H_pos_restrict_subsingleton_of_isFlasque
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (U : Opens X) (n : ℕ) :
    Subsingleton (H (restrictToOpen F U) (n + 1)) := by
  have : IsFlasque (restrictToOpen F U) :=
    isFlasque_pullback_of_isOpenEmbedding U.isOpenEmbedding F
  exact H_pos_subsingleton_of_isFlasque _ n

end SGA.SGA2.ExposeI
