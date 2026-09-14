/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.OpenExtensionByZero
import SGA.SGA2.ExposeI.TopologicalInternalHom

/-! # The original open extension-by-zero counit is monic -/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI
variable {X : TopCat.{u}}

private theorem openLan_zero_off (U V : Opens X) (h : ¬ V ≤ U)
    (F : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsZero ((U.isOpenEmbedding.functor.op.lan.obj F).obj (op V)) := by
  let L := U.isOpenEmbedding.functor.op
  have : IsEmpty (CostructuredArrow L (op V)) := ⟨fun A => h
    (A.hom.unop.le.trans (by rintro x ⟨y, hy, rfl⟩; exact y.property))⟩
  have hF : IsZero (CostructuredArrow.proj L (op V) ⋙ F) :=
    Functor.isZero _ (fun A => isEmptyElim A)
  exact ((colimit.isColimit _).isZero_pt hF).of_iso
    (L.leftKanExtensionObjIsoColimit F (op V))

/-- Before sheafification, the open extension/restriction counit is mono:
on opens contained in `U` it is an isomorphism, elsewhere its source is zero. -/
theorem openLanCounit_mono (U : Opens X) (F : X.Presheaf AddCommGrpCat.{u}) :
    Mono ((U.isOpenEmbedding.functor.op.lanAdjunction AddCommGrpCat.{u}).counit.app F) := by
  have : Mono U.inclusion' := (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  let L := U.isOpenEmbedding.functor.op
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro V
  by_cases hV : V.unop ≤ U
  · let W := (Opens.map U.inclusion').obj V.unop
    have he : U.isOpenEmbedding.functor.obj W = V.unop := by
      exact (Opens.functor_map_eq_inf U V.unop).trans (inf_eq_left.mpr hV)
    have hc := L.lanUnit_app_app_lanAdjunction_counit_app_app F (op W)
    have : IsIso (((L.lanAdjunction AddCommGrpCat.{u}).counit.app F).app (L.obj (op W))) :=
      isIso_of_hom_comp_eq_id _ hc
    have hm : Mono (((L.lanAdjunction AddCommGrpCat.{u}).counit.app F).app
        (L.obj (op W))) := inferInstance
    change Mono (((L.lanAdjunction AddCommGrpCat.{u}).counit.app F).app (op V.unop))
    rw [← he]
    exact hm
  · exact mono_of_source_iso_zero _ (openLan_zero_off U V.unop hV (L ⋙ F)).isoZero

/-- The same existing extension-by-zero functor, adjoint to naive open
restriction. This only changes the restriction model by its established iso. -/
def openExtensionNaiveAdjunction (U : Opens X) : iBang_open U ⊣ U.sheafRestrict := by
  letI := U.isOpenEmbedding.functor_isContinuous
  exact Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    U.isOpenEmbedding.functor AddCommGrpCat.{u}
    (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) (Opens.grothendieckTopology X)

theorem openExtensionNaiveAdjunction_counit (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (openExtensionNaiveAdjunction U).counit.app F =
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        ((U.isOpenEmbedding.functor.op.lanAdjunction AddCommGrpCat.{u}).counit.app F.obj) ≫
      (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit.app F := by
  let := U.isOpenEmbedding.functor_isContinuous
  have h := Adjunction.map_restrictFullyFaithful_counit_app
    (L := iBang_open U) (R := U.sheafRestrict)
    ((U.isOpenEmbedding.functor.op.lanAdjunction AddCommGrpCat.{u}).comp
      (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (fullyFaithfulSheafToPresheaf
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u})
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _) F
  dsimp only [Functor.FullyFaithful.id,
    Functor.id_map, Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp,
    Adjunction.comp_counit_app, NatTrans.id_app, Functor.id_obj] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp] at h
  exact h

theorem openExtensionNaiveAdjunction_counit_mono (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Mono ((openExtensionNaiveAdjunction U).counit.app F) := by
  rw [openExtensionNaiveAdjunction_counit]
  have := openLanCounit_mono U F.obj
  have : Mono ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      ((U.isOpenEmbedding.functor.op.lanAdjunction AddCommGrpCat.{u}).counit.app F.obj)) :=
    inferInstance
  have : IsIso ((sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).counit.app F) := inferInstance
  infer_instance

/-- The canonical map `j_! j^* F → F` is monic for every abelian sheaf. -/
theorem openExtensionByZero_counit_mono (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Mono ((openExtensionByZeroAdjunction U).counit.app F) := by
  have h : (openExtensionByZeroAdjunction U).counit.app F =
      (iBang_open U).map (((openPullbackSheafRestrictIso U).app F).hom) ≫
        (openExtensionNaiveAdjunction U).counit.app F := rfl
  rw [h]
  have := openExtensionNaiveAdjunction_counit_mono U F
  infer_instance

end SGA.SGA2.ExposeI
