/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.AffineInternalHomSections

/-!
# Actual module-valued internal Hom commutes with open restriction

An open immersion identifies the smaller opens of `U` with the smaller
opens of its image. Reindexing the original local-linear maps along this
equivalence gives the restriction comparison, including the local scalar
actions through the structure-sheaf isomorphisms.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Functor

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

local instance (G : X.Modules) (U : X.Opens) (V : Over U) :
    Module (X.ringCatSheaf.obj.obj (op V.left))
      (((Over.forget U).op ⋙ G.val.presheaf).obj (op V)) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj (op V.left)) (G.val.obj (op V.left)))

/-- Every open inside the image of an open immersion is the image of its actual preimage. -/
theorem schemeOpensOverPost_surjective (U : Y.Opens) :
    Function.Surjective (Over.post (X := U) f.opensFunctor).obj := by
  intro W
  let h : f ⁻¹ᵁ W.left ≤ U := by
    exact (f.preimage_mono (leOfHom W.hom)).trans_eq (f.preimage_image_eq U)
  refine ⟨Over.mk (homOfLE h), ?_⟩
  refine CostructuredArrow.obj_ext _ _ ?_ (Subsingleton.elim _ _)
  · change f ''ᵁ f ⁻¹ᵁ W.left = W.left
    rw [f.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.mpr ((leOfHom W.hom).trans (f.image_le_opensRange U))

/-- The actual functor on smaller opens induced by an open immersion is an equivalence. -/
instance schemeOpensOverPost_isEquivalence (U : Y.Opens) :
    (Over.post (X := U) f.opensFunctor).IsEquivalence := by
  let : f.opensFunctor.Full :=
    { map_surjective := fun {V W} i ↦
        ⟨homOfLE ((f.image_le_image_iff V W).mp (leOfHom i)), Subsingleton.elim _ _⟩ }
  let : (Over.post (X := U) f.opensFunctor).EssSurj :=
    ⟨fun W ↦ by
      obtain ⟨V, hV⟩ := schemeOpensOverPost_surjective f U W
      exact ⟨V, ⟨eqToIso hV⟩⟩⟩
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- Restriction of an actual local-linear map along the image functor on smaller opens. -/
def schemeLocalHomRestrict (F G : X.Modules) (U : Y.Opens)
    (φ : moduleLocalHom F.val G.val (f ''ᵁ U)) :
    moduleLocalHom (F.restrict f).val (G.restrict f).val U :=
  ⟨Functor.whiskerLeft (Over.post (X := U) f.opensFunctor).op φ.val,
    fun V r x ↦ φ.property ((Over.post (X := U) f.opensFunctor).obj V)
      ((f.appIso V.left).inv r) x⟩

/-- Restriction on actual local-linear maps is bijective. -/
theorem schemeLocalHomRestrict_bijective (F G : X.Modules) (U : Y.Opens) :
    Function.Bijective (schemeLocalHomRestrict f F G U) := by
  let K := (Over.post (X := U) f.opensFunctor).op
  let T := (whiskeringLeft _ _ AddCommGrpCat.{u}).obj K
  constructor
  · intro φ ψ h
    apply Subtype.ext
    apply T.map_injective
    exact congrArg Subtype.val h
  · intro ψ
    let ψ' : T.obj ((Over.forget (f ''ᵁ U)).op ⋙ F.val.presheaf) ⟶
        T.obj ((Over.forget (f ''ᵁ U)).op ⋙ G.val.presheaf) := ψ.val
    let χ : (Over.forget (f ''ᵁ U)).op ⋙ F.val.presheaf ⟶
        (Over.forget (f ''ᵁ U)).op ⋙ G.val.presheaf := T.preimage ψ'
    have hχ : T.map χ = ψ' := T.map_preimage ψ'
    have hlin : ∀ (W : Over (f ''ᵁ U)) (r : X.ringCatSheaf.obj.obj (op W.left))
        (x : F.val.obj (op W.left)), χ.app (op W) (r • x) = r • χ.app (op W) x := by
      intro W r x
      obtain ⟨V, rfl⟩ := schemeOpensOverPost_surjective f U W
      obtain ⟨s, hs⟩ := (ConcreteCategory.bijective_of_isIso (f.appIso V.left).inv).surjective r
      subst r
      have he := congrArg (fun a ↦ a.app (op V)) hχ
      change χ.app (op ((Over.post (X := U) f.opensFunctor).obj V)) = ψ.val.app (op V) at he
      rw [he]
      exact ψ.property V s x
    refine ⟨⟨χ, hlin⟩, ?_⟩
    apply Subtype.ext
    exact hχ

/-- The canonical comparison between restriction of module Hom and Hom of restricted modules. -/
def schemeModuleInternalHomRestrictMap (F G : X.Modules) :
    (schemeModuleInternalHom F G).restrict f ⟶
      schemeModuleInternalHom (F.restrict f) (G.restrict f) :=
  ⟨
    { app U := ModuleCat.ofHom
        (X := ((schemeModuleInternalHom F G).restrict f).val.obj U)
        (Y := (schemeModuleInternalHom (F.restrict f) (G.restrict f)).val.obj U)
        { toFun := schemeLocalHomRestrict f F G U.unop
          map_add' φ ψ := rfl
          map_smul' r φ := by
            apply moduleLocalHom_ext
            intro V x
            let y : G.val.obj (op (f ''ᵁ V.left)) :=
              φ.val.app (op ((Over.post (X := U.unop) f.opensFunctor).obj V)) x
            change X.presheaf.map (f.opensFunctor.map V.hom).op ((f.appIso U.unop).inv r) • y =
              (f.appIso V.left).inv (Y.presheaf.map V.hom.op r) • y
            exact congrArg (fun a : Γ(X, f ''ᵁ V.left) ↦ a • y)
              (ConcreteCategory.congr_hom (f.appIso_inv_naturality V.hom.op) r).symm }
      naturality {U V} i := by
        ext φ
        apply moduleLocalHom_ext
        intro W x
        rfl }⟩

/-- Module-valued internal Hom commutes with genuine restriction along every open immersion. -/
def schemeModuleInternalHomRestrictIso (F G : X.Modules) :
    (schemeModuleInternalHom F G).restrict f ≅
      schemeModuleInternalHom (F.restrict f) (G.restrict f) := by
  let a := schemeModuleInternalHomRestrictMap f F G
  let (U : (Opens Y)ᵒᵖ) : IsIso (a.val.app U) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (schemeLocalHomRestrict_bijective f F G U.unop)
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ asIso (a.val.app U))
      (fun {U V} i ↦ a.val.naturality i))

end SGA.SGA2.ExposeVI
