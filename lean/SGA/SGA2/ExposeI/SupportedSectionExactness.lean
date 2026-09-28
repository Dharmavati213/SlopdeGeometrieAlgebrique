/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.Flasque

/-!
# Exactness of supported sections with flasque kernel

For a short exact sequence of abelian sheaves with flasque kernel,
every supported section of the quotient lifts to a supported section of
the middle sheaf. This is the section-level input to supported acyclicity;
it does not assume a comparison between supported sections and Ext.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- The actual coefficient map on sections with closed support. -/
def gammaZSectionsMap {F G : Sheaf AddCommGrpCat.{u} X} (φ : F ⟶ G)
    (Z : Closeds X) (U : Opens X) : gammaZSections F Z U →+ gammaZSections G Z U where
  toFun s := ⟨φ.hom.app (op U) s.val, map_mem_gammaZSections F φ s.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _s _t := Subtype.ext (map_add _ _ _)

@[simp]
theorem gammaZSectionsMap_apply {F G : Sheaf AddCommGrpCat.{u} X} (φ : F ⟶ G)
    (Z : Closeds X) (U : Opens X) (s : gammaZSections F Z U) :
    (gammaZSectionsMap φ Z U s).val = φ.hom.app (op U) s.val := rfl

/-- Supported sections on an open, as a coefficient functor to abelian groups. -/
def gammaZSectionsFunctor (Z : Closeds X) (U : Opens X) :
    Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} where
  obj F := AddCommGrpCat.of (gammaZSections F Z U)
  map φ := AddCommGrpCat.ofHom (gammaZSectionsMap φ Z U)
  map_id _ := by ext s; rfl
  map_comp _ _ := by ext s; rfl

instance (Z : Closeds X) (U : Opens X) : (gammaZSectionsFunctor Z U).Additive where
  map_add := by intros; ext s; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The supported-section coefficient map of a monomorphism is injective. -/
theorem injective_gammaZSectionsMap_of_mono
    {F G : Sheaf AddCommGrpCat.{u} X} (φ : F ⟶ G) [Mono φ]
    (Z : Closeds X) (U : Opens X) : Function.Injective (gammaZSectionsMap φ Z U) := by
  have hmono : Mono (φ.hom.app (op U)) := inferInstance
  intro s t hst
  apply Subtype.ext
  exact (AddCommGrpCat.mono_iff_injective _).mp hmono (congrArg Subtype.val hst)

set_option backward.isDefEq.respectTransparency false in
/-- Supported sections are left exact in coefficients. -/
theorem exact_gammaZSectionsMap_of_shortExact
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (Z : Closeds X) (U : Opens X) :
    Function.Exact (gammaZSectionsMap S.f Z U) (gammaZSectionsMap S.g Z U) := by
  have : Mono S.f := hS.mono_f
  intro t
  constructor
  · intro ht
    have htzero : S.g.hom.app (op U) t.val = 0 := congrArg Subtype.val ht
    obtain ⟨s, hs⟩ := Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f t.val htzero
    refine ⟨⟨s, ?_⟩, Subtype.ext hs⟩
    let i : op U ⟶ op (U ⊓ Z.compl) := (homOfLE inf_le_left).op
    change S.X₁.obj.map i s = 0
    apply (AddCommGrpCat.mono_iff_injective (S.f.hom.app (op (U ⊓ Z.compl)))).mp
      inferInstance
    rw [map_zero, ← CategoryTheory.comp_apply, S.f.hom.naturality,
      CategoryTheory.comp_apply, hs]
    exact t.property
  · rintro ⟨s, rfl⟩
    apply Subtype.ext
    change S.g.hom.app (op U) (S.f.hom.app (op U) s.val) = 0
    have hfg : S.f.hom.app (op U) ≫ S.g.hom.app (op U) = 0 := by
      rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, S.zero]
      rfl
    rw [← CategoryTheory.comp_apply, hfg]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- In a short exact sequence with flasque kernel, supported sections of
the quotient lift without increasing their support. -/
theorem surjective_gammaZSectionsMap_of_shortExact
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [IsFlasque S.X₁] (Z : Closeds X) (U : Opens X) :
    Function.Surjective (gammaZSectionsMap S.g Z U) := by
  have hepi : Epi (S.g.hom.app (op U)) := Sheaf.IsFlasque.epi_of_shortExact hS
  intro t
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hepi t.val
  let i : op U ⟶ op (U ⊓ Z.compl) := (homOfLE inf_le_left).op
  have hzero : S.g.hom.app (op (U ⊓ Z.compl)) (S.X₂.obj.map i s) = 0 := by
    rw [← CategoryTheory.comp_apply, S.g.hom.naturality, CategoryTheory.comp_apply, hs]
    exact t.property
  obtain ⟨a, ha⟩ := Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f
    (S.X₂.obj.map i s) hzero
  obtain ⟨b, hb⟩ := (AddCommGrpCat.epi_iff_surjective (S.X₁.obj.map i)).mp inferInstance a
  refine ⟨⟨s - S.f.hom.app (op U) b, ?_⟩, ?_⟩
  · change S.X₂.obj.map i (s - S.f.hom.app (op U) b) = 0
    rw [map_sub, ← CategoryTheory.comp_apply, ← S.f.hom.naturality,
      CategoryTheory.comp_apply, hb, ha, sub_self]
  · apply Subtype.ext
    change S.g.hom.app (op U) (s - S.f.hom.app (op U) b) = t.val
    have hfg : S.f.hom.app (op U) ≫ S.g.hom.app (op U) = 0 := by
      rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, S.zero]
      rfl
    rw [map_sub, ← CategoryTheory.comp_apply, hfg]
    simpa using hs

set_option backward.isDefEq.respectTransparency false in
/-- The actual supported-section functor sends a short exact sequence with
flasque kernel to a short exact sequence of abelian groups. -/
theorem gammaZSectionsFunctor_map_shortExact
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [IsFlasque S.X₁] (Z : Closeds X) (U : Opens X) :
    (S.map (gammaZSectionsFunctor Z U)).ShortExact := by
  have : Mono S.f := hS.mono_f
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.ab_exact_iff_function_exact]
    exact exact_gammaZSectionsMap_of_shortExact hS Z U
  · exact (AddCommGrpCat.mono_iff_injective _).mpr
      (injective_gammaZSectionsMap_of_mono S.f Z U)
  · exact (AddCommGrpCat.epi_iff_surjective _).mpr
      (surjective_gammaZSectionsMap_of_shortExact hS Z U)

end SGA.SGA2.ExposeI
