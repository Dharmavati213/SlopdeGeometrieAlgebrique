/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedSheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Actual module support commutes with scheme open restriction

The comparisons act as the identity on the original coefficient sections.
The support conditions agree by the literal equality between the image of
an open intersected with the preimage complement and its image intersected
with the ambient complement. Local scalar actions are retained.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The actual inverse image closed subset under a scheme morphism. -/
def schemeClosedSupportPreimage (Z : Closeds X) : Closeds Y :=
  ⟨f ⁻¹' (Z : Set X), Z.isClosed.preimage f.continuous⟩

variable [IsOpenImmersion f] (Z : Closeds X)

/-- The existing closed-supported module sheaf, regarded as an actual scheme module. -/
abbrev schemeModuleGammaZ {T : Scheme.{u}} (A : Closeds T) (M : T.Modules) : T.Modules :=
  moduleGammaZSheaf T.ringCatSheaf A M

/-- The support-complement opens in the two actual restriction calculations agree. -/
theorem schemeSupport_image_inf_compl (U : Y.Opens) :
    f ''ᵁ (U ⊓ (schemeClosedSupportPreimage f Z).compl) = (f ''ᵁ U) ⊓ Z.compl := by
  ext x
  change x ∈ f '' ((U : Set Y) ∩ (f ⁻¹' (Z : Set X))ᶜ) ↔
    x ∈ f '' (U : Set Y) ∩ (Z : Set X)ᶜ
  constructor
  · rintro ⟨y, ⟨hy, hz⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hz⟩
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    exact ⟨y, ⟨hy, hz⟩, rfl⟩

/-- Actual restriction sends supported sections to supported sections on the open subscheme. -/
def schemeModuleGammaZRestrictionMap (M : X.Modules) :
    (schemeModuleGammaZ Z M).restrict f ⟶
      moduleGammaZSheaf Y.ringCatSheaf (schemeClosedSupportPreimage f Z) (M.restrict f) :=
  ⟨
    { app U := ModuleCat.ofHom
        (X := ((schemeModuleGammaZ Z M).restrict f).val.obj U)
        (Y := (moduleGammaZSheaf Y.ringCatSheaf
          (schemeClosedSupportPreimage f Z) (M.restrict f)).val.obj U)
        { toFun s := ⟨s.val, by
            let e := schemeSupport_image_inf_compl f Z U.unop
            have hs : M.val.map
                (homOfLE (inf_le_left : (f ''ᵁ U.unop) ⊓ Z.compl ≤ f ''ᵁ U.unop)).op s.val = 0 :=
              s.property
            change M.val.map (f.opensFunctor.map
              (homOfLE (inf_le_left : U.unop ⊓ (schemeClosedSupportPreimage f Z).compl ≤
                U.unop))).op s.val = 0
            calc
              _ = M.val.map (eqToHom e).op (M.val.map
                (homOfLE (inf_le_left : (f ''ᵁ U.unop) ⊓ Z.compl ≤ f ''ᵁ U.unop)).op s.val) := by
                  rw [← M.val.map_comp_apply]
                  rfl
              _ = 0 := by rw [hs, map_zero]⟩
          map_add' _ _ := Subtype.ext rfl
          map_smul' _ _ := Subtype.ext rfl }
      naturality := by intros; ext s; rfl }⟩

/-- The inverse comparison retains the same actual coefficient section. -/
def schemeModuleGammaZRestrictionInv (M : X.Modules) :
    moduleGammaZSheaf Y.ringCatSheaf (schemeClosedSupportPreimage f Z) (M.restrict f) ⟶
      (schemeModuleGammaZ Z M).restrict f :=
  ⟨
    { app U := ModuleCat.ofHom
        (X := (moduleGammaZSheaf Y.ringCatSheaf
          (schemeClosedSupportPreimage f Z) (M.restrict f)).val.obj U)
        (Y := ((schemeModuleGammaZ Z M).restrict f).val.obj U)
        { toFun s := ⟨s.val, by
            let e := schemeSupport_image_inf_compl f Z U.unop
            have hs : M.val.map (f.opensFunctor.map
                (homOfLE (inf_le_left : U.unop ⊓ (schemeClosedSupportPreimage f Z).compl ≤
                  U.unop))).op s.val = 0 := s.property
            change M.val.map
              (homOfLE (inf_le_left : (f ''ᵁ U.unop) ⊓ Z.compl ≤ f ''ᵁ U.unop)).op s.val = 0
            calc
              _ = M.val.map (eqToHom e.symm).op (M.val.map (f.opensFunctor.map
                (homOfLE (inf_le_left : U.unop ⊓ (schemeClosedSupportPreimage f Z).compl ≤
                  U.unop))).op s.val) := by
                    rw [← M.val.map_comp_apply]
                    rfl
              _ = 0 := by rw [hs, map_zero]⟩
          map_add' _ _ := Subtype.ext rfl
          map_smul' _ _ := Subtype.ext rfl }
      naturality := by intros; ext s; rfl }⟩

/-- Actual module sheaves of closed-supported sections commute with open restriction. -/
def schemeModuleGammaZRestrictionIso (M : X.Modules) :
    (schemeModuleGammaZ Z M).restrict f ≅
      moduleGammaZSheaf Y.ringCatSheaf (schemeClosedSupportPreimage f Z) (M.restrict f) where
  hom := schemeModuleGammaZRestrictionMap f Z M
  inv := schemeModuleGammaZRestrictionInv f Z M
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

/-- The restriction comparison preserves the original coefficient-module maps. -/
def schemeModuleGammaZRestrictionFunctorIso :
    moduleGammaZSheafFunctor X.ringCatSheaf Z ⋙ Scheme.Modules.restrictFunctor f ≅
      Scheme.Modules.restrictFunctor f ⋙
        moduleGammaZSheafFunctor Y.ringCatSheaf (schemeClosedSupportPreimage f Z) :=
  NatIso.ofComponents (fun M ↦ schemeModuleGammaZRestrictionIso f Z M)
    (fun a ↦ by ext U s; rfl)

end SGA.SGA2.ExposeVI
