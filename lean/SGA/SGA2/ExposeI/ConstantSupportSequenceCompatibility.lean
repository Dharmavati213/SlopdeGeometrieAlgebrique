/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.ConstantSupportSequence

/-! # Compatibility of the constant support sequence with restriction -/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

private theorem homEquiv_leftAdjointUniq_comp
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R)
    (P : C) (Q : D) (f : L'.obj P ⟶ Q) :
    adj.homEquiv P Q ((adj.leftAdjointUniq adj').hom.app P ≫ f) =
      adj'.homEquiv P Q f := by
  rw [adj.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_unit]

private theorem homEquiv_counit_eq_id
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (Q : D) :
    adj.homEquiv _ Q (adj.counit.app Q) = 𝟙 _ := by
  rw [← adj.homEquiv_symm_id]
  exact (adj.homEquiv _ _).apply_symm_apply _

private theorem homEquiv_ofNatIsoRight_comp
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (e : R' ≅ R)
    (P : C) (Q : D) (f : L.obj P ⟶ Q) :
    (adj.ofNatIsoRight e.symm).homEquiv P Q f ≫ e.hom.app Q = adj.homEquiv P Q f := by
  simp only [Adjunction.homEquiv_ofNatIsoRight_apply, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The open constant inclusion corresponds, under the actual open adjunction,
to the restriction of the universal integer-presheaf section. -/
theorem zZX_openToConstant_adjunction (U : Opens X) :
    toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        (integerPresheaf ((Opens.toTopCat X).obj U)) ≫
      (((openExtensionByZeroAdjunction U).homEquiv _ _ (zZX_openToConstant U)) ≫
        (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).hom.app (constantZ X)).hom =
      Functor.whiskerLeft U.isOpenEmbedding.functor.op
        (toSheafify (Opens.grothendieckTopology X) (integerPresheaf X)) := by
  have := U.isOpenEmbedding.functor_isContinuous
  let adjU := sheafificationAdjunction
    (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u}
  let adjX := sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let SX := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let adjO := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    U.isOpenEmbedding.functor AddCommGrpCat.{u}
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) (Opens.grothendieckTopology X)
  let adjL := U.isOpenEmbedding.functor.op.lanAdjunction AddCommGrpCat.{u}
  have h := homEquiv_leftAdjointUniq_comp (adjU.comp adjO) (adjL.comp adjX)
    (integerPresheaf ((Opens.toTopCat X).obj U)) (constantZ X)
    (SX.map (openIntegerPresheafι U))
  change (adjU.comp adjO).homEquiv _ _ (zZX_openToConstant U) = _ at h
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv] at h
  change adjU.homEquiv _ _ (adjO.homEquiv _ _ (zZX_openToConstant U)) =
    adjL.homEquiv _ _ (toSheafify (Opens.grothendieckTopology X) (openIntegerPresheaf U) ≫
      (SX.map (openIntegerPresheafι U)).hom) at h
  have hn : toSheafify (Opens.grothendieckTopology X) (openIntegerPresheaf U) ≫
      (SX.map (openIntegerPresheafι U)).hom = openIntegerPresheafι U ≫
        toSheafify (Opens.grothendieckTopology X) (integerPresheaf X) :=
    (adjX.unit.naturality (openIntegerPresheafι U)).symm
  rw [hn, adjL.homEquiv_naturality_right] at h
  have hc : adjL.homEquiv _ _ (openIntegerPresheafι U) = 𝟙 _ :=
    homEquiv_counit_eq_id adjL (integerPresheaf X)
  rw [hc, Category.id_comp] at h
  change toSheafify _ _ ≫ (adjO.homEquiv _ _ (zZX_openToConstant U)).hom = _ at h
  have he := homEquiv_ofNatIsoRight_comp adjO
    (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u})
    (constantZ ((Opens.toTopCat X).obj U)) (constantZ X) (zZX_openToConstant U)
  change ((openExtensionByZeroAdjunction U).homEquiv _ _ (zZX_openToConstant U)) ≫
    (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).hom.app (constantZ X) = _ at he
  rw [he]
  exact h

end SGA.SGA2.ExposeI
