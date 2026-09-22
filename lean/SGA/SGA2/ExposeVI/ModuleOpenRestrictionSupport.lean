/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleOpenRestrictionExt
import SGA.SGA2.ExposeI.SupportedExcision

/-!
# Supported module Hom on an open

For module sheaves on the actual open slice site, supported Hom is the
subgroup of morphisms that vanish on every open disjoint from the support.
For restrictions of ambient modules this agrees naturally with the concrete
kernel of restriction of the Hom sheaf.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (U : Opens X) (Z : Closeds X)

/-- Supported morphisms of actual module sheaves on the open slice site:
all component maps off the support are zero. -/
def moduleSupportedHomOnOpen
    (F G : SheafOfModules.{u} (R.over U)) : AddSubgroup (F ⟶ G) where
  carrier := {f | ∀ V : Over U, V.left ≤ Z.compl → f.val.app (op V) = 0}
  zero_mem' := by intro V hV; rfl
  add_mem' {f g} hf hg := by
    intro V hV
    change f.val.app (op V) + g.val.app (op V) = 0
    rw [hf V hV, hg V hV, add_zero]
  neg_mem' {f} hf := by
    intro V hV
    change -f.val.app (op V) = 0
    rw [hf V hV, neg_zero]

/-- Supported Hom on the open site, with its actual postcomposition maps. -/
def moduleSupportedHomOnOpenFunctor (F : SheafOfModules.{u} (R.over U)) :
    SheafOfModules.{u} (R.over U) ⥤ AddCommGrpCat.{u} where
  obj G := AddCommGrpCat.of (moduleSupportedHomOnOpen R U Z F G)
  map {G H} a := AddCommGrpCat.ofHom
    { toFun f := ⟨f.val ≫ a, by
        intro V hV
        change f.val.val.app (op V) ≫ a.val.app (op V) = 0
        rw [f.property V hV, zero_comp]⟩
      map_zero' := Subtype.ext zero_comp
      map_add' f g := Subtype.ext (Preadditive.add_comp _ _ _ f.val g.val a) }
  map_id G := by ext f V x; rfl
  map_comp f g := by ext h V x; rfl

instance moduleSupportedHomOnOpenFunctor_additive
    (F : SheafOfModules.{u} (R.over U)) : (moduleSupportedHomOnOpenFunctor R U Z F).Additive where
  map_add := by
    intro G H a b
    ext f
    exact Subtype.ext (Preadditive.comp_add _ _ _ f.val a b)

/-- Changing the source by an actual module isomorphism preserves supported Hom. -/
def moduleSupportedHomOnOpenSourceEquiv
    {F F' : SheafOfModules.{u} (R.over U)} (e : F ≅ F')
    (G : SheafOfModules.{u} (R.over U)) :
    moduleSupportedHomOnOpen R U Z F G ≃+ moduleSupportedHomOnOpen R U Z F' G where
  toFun f := ⟨e.inv ≫ f.val, by
    intro V hV
    change e.inv.val.app (op V) ≫ f.val.val.app (op V) = 0
    rw [f.property V hV, comp_zero]⟩
  invFun f := ⟨e.hom ≫ f.val, by
    intro V hV
    change e.hom.val.app (op V) ≫ f.val.val.app (op V) = 0
    rw [f.property V hV, comp_zero]⟩
  left_inv f := Subtype.ext (by simp)
  right_inv f := Subtype.ext (by simp)
  map_add' f g := Subtype.ext (Preadditive.comp_add _ _ _ e.inv f.val g.val)

/-- Supported Hom is naturally invariant under an isomorphism of its source. -/
def moduleSupportedHomOnOpenSourceIso
    {F F' : SheafOfModules.{u} (R.over U)} (e : F ≅ F') :
    moduleSupportedHomOnOpenFunctor R U Z F ≅ moduleSupportedHomOnOpenFunctor R U Z F' :=
  NatIso.ofComponents (fun G => (moduleSupportedHomOnOpenSourceEquiv R U Z e G).toAddCommGrpIso)
    (fun f => by ext φ; rfl)

/-- A supported section of ambient local Hom is exactly a supported
morphism between the actual restricted module sheaves. -/
def moduleSupportedHomOnOpenEquiv (F G : SheafOfModules.{u} R) :
    ExposeI.gammaZSections (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z U ≃+
      moduleSupportedHomOnOpen R U Z (F.over U) (G.over U) where
  toFun φ := ⟨moduleLocalHomSheafOverAddEquiv R F G U φ.val, by
    intro V hV
    obtain ⟨V, iV, rfl⟩ := V.mk_surjective
    ext x
    let j : V ⟶ U ⊓ Z.compl := homOfLE (le_inf (leOfHom iV) hV)
    have h := congrArg
      (fun ψ : moduleLocalHom F.val G.val (U ⊓ Z.compl) => ψ.val.app (op (Over.mk j)) x)
      φ.property
    exact h⟩
  invFun φ := ⟨(moduleLocalHomSheafOverAddEquiv R F G U).symm φ.val, by
    apply moduleLocalHom_ext
    intro V x
    let j : U ⊓ Z.compl ⟶ U := homOfLE inf_le_left
    have h := φ.property ((Over.map j).obj V) ((leOfHom V.hom).trans inf_le_right)
    exact ConcreteCategory.congr_hom h x⟩
  left_inv φ := Subtype.ext ((moduleLocalHomSheafOverAddEquiv R F G U).symm_apply_apply φ.val)
  right_inv φ := Subtype.ext ((moduleLocalHomSheafOverAddEquiv R F G U).apply_symm_apply φ.val)
  map_add' φ ψ := Subtype.ext ((moduleLocalHomSheafOverAddEquiv R F G U).map_add φ.val ψ.val)

/-- The supported-Hom comparison is natural for actual coefficient maps. -/
def moduleSupportedHomSectionsRestrictionIso (F : SheafOfModules.{u} R) :
    moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        ExposeI.gammaZSectionsFunctor Z U ≅
      moduleOpenRestriction R U ⋙ moduleSupportedHomOnOpenFunctor R U Z (F.over U) :=
  NatIso.ofComponents (fun G => (moduleSupportedHomOnOpenEquiv R U Z F G).toAddCommGrpIso)
    (fun f => by ext φ; rfl)

/-- Supported Ext derived in the actual module category of the open. -/
def moduleSupportedExtOnOpenFunctor (F : SheafOfModules.{u} (R.over U)) (n : ℕ) :
    SheafOfModules.{u} (R.over U) ⥤ AddCommGrpCat.{u} :=
  (moduleSupportedHomOnOpenFunctor R U Z F).rightDerived n

/-- Excision of actual supported linear Hom when the closed support lies
inside the designated open. -/
def moduleSupportedHomExcisionIso (hZU : (Z : Set X) ⊆ (U : Set X))
    (F : SheafOfModules.{u} R) :
    moduleSupportedHomFunctor R F Z ≅
      moduleOpenRestriction R U ⋙ moduleSupportedHomOnOpenFunctor R U Z (F.over U) :=
  NatIso.ofComponents
    (fun G => ((ExposeI.gammaZ_restrict_addEquiv
      (moduleSheafHomAb (Opens.grothendieckTopology X) F G) hZU).trans
        (moduleSupportedHomOnOpenEquiv R U Z F G)).toAddCommGrpIso)
    (fun f => by
      ext φ
      apply Subtype.ext
      ext V x
      rfl)

/-- **VI.1.3, closed support:** true supported module Ext is unchanged on
an open neighborhood of the support. The right side is derived in the
category of module sheaves on that open. -/
def moduleSupportedExtExcisionIso (hZU : (Z : Set X) ⊆ (U : Set X))
    (F : SheafOfModules.{u} R) (n : ℕ) :
    moduleSupportedExtFunctor R F Z n ≅
      moduleOpenRestriction R U ⋙ moduleSupportedExtOnOpenFunctor R U Z (F.over U) n :=
  ExposeI.rightDerivedFunctorIso (moduleSupportedHomExcisionIso R U Z hZU F) n ≪≫
    ExposeI.rightDerivedPrecomposeIso (moduleOpenRestriction R U)
      (moduleSupportedHomOnOpenFunctor R U Z (F.over U)) n

end SGA.SGA2.ExposeVI
