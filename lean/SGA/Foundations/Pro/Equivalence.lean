/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Pro.Representable

/-!
# Pro-objects and equivalences of categories

An equivalence `e : C ≌ D` between categories with morphisms in the same universe induces an
equivalence `Pro.congr e : Pro C ≌ Pro D`. On the functors pro-represented by pro-objects it is
given by precomposition with `e.inverse` (`Pro.coyonedaObjCongrFunctorObjIso`), and it extends
`e` (`Pro.congrFunctorObjOfIso`).
-/

universe v u₁ u₂

namespace CategoryTheory

open Limits Opposite

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

namespace Functor.ProRepresentation

variable {G : C ⥤ Type v} (R : G.ProRepresentation) (e : C ≌ D)

/-- `Hom(e X, Y) = Hom(X, e⁻¹ Y)`, functorially. -/
@[simps!]
def coyonedaCongrIso :
    e.functor.op ⋙ coyoneda ≅ coyoneda ⋙ (Functor.whiskeringLeft D C (Type v)).obj e.inverse :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ (e.toAdjunction.homEquiv _ _).toIso)
    fun f ↦ by
      ext u
      exact e.toAdjunction.homEquiv_naturality_right u f)
    fun g ↦ by
      ext Y u
      exact e.toAdjunction.homEquiv_naturality_left g.unop u

/-- Transport of a pro-representation along an equivalence of categories. -/
@[simps I F]
noncomputable def congr : (e.inverse ⋙ G).ProRepresentation where
  I := R.I
  F := R.F ⋙ e.functor
  ι := ((Cocone.precompose (Functor.isoWhiskerLeft R.F.op (coyonedaCongrIso e)).hom).obj
    (((Functor.whiskeringLeft D C (Type v)).obj e.inverse).mapCocone R.cocone)).ι
  isColimit := by
    have : ((Functor.whiskeringLeft D C (Type v)).obj e.inverse).IsEquivalence :=
      e.congrLeft.isEquivalence_functor
    exact (IsColimit.precomposeHomEquiv _ _).symm
      (isColimitOfPreserves ((Functor.whiskeringLeft D C (Type v)).obj e.inverse) R.isColimit)

lemma congr_isStrict (hR : R.IsStrict) : (R.congr e).IsStrict :=
  fun _ _ f ↦ by
    have := hR f
    exact inferInstanceAs (Epi (e.functor.map (R.F.map f)))

end Functor.ProRepresentation

namespace Pro

variable (e : C ≌ D)

lemma isProRepresentable_comp_inverse {G : C ⥤ Type v} (hG : G.IsProRepresentable) :
    (e.inverse ⋙ G).IsProRepresentable :=
  ⟨hG.some.congr e⟩

/-- Precomposition with `e.inverse` on functors pro-represented by pro-objects. -/
noncomputable def congrEssImage :
    (coyoneda C).EssImageSubcategory ⥤ (coyoneda D).EssImageSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ e.congrLeft.functor) fun G ↦
    Functor.isProRepresentable_iff_mem_essImage.1
      (isProRepresentable_comp_inverse e (Functor.isProRepresentable_iff_mem_essImage.2 G.2))

instance : (congrEssImage e).Full :=
  Functor.Full.of_comp_faithful_iso (ObjectProperty.liftCompιIso _ _ _)

instance : (congrEssImage e).Faithful :=
  Functor.Faithful.of_comp_iso (ObjectProperty.liftCompιIso _ _ _)

instance : (congrEssImage e).EssSurj where
  mem_essImage G := by
    have h := Functor.isProRepresentable_iff_mem_essImage.1
      (isProRepresentable_comp_inverse e.symm (Functor.isProRepresentable_iff_mem_essImage.2 G.2))
    exact ⟨⟨_, h⟩, ⟨ObjectProperty.isoMk _ (e.congrLeft.counitIso.app G.obj)⟩⟩

instance : (congrEssImage e).IsEquivalence where

/-- An equivalence of categories induces an equivalence of their categories of pro-objects. -/
noncomputable def congr : Pro C ≌ Pro D :=
  ((coyoneda C).toEssImage.asEquivalence.trans
    ((congrEssImage e).asEquivalence.trans (coyoneda D).toEssImage.asEquivalence.symm)).unop

/-- The functor pro-represented by `Pro.congr e P` is `Hom(P, e⁻¹ -)`. -/
noncomputable def coyonedaObjCongrFunctorObjIso (P : Pro C) :
    (coyoneda D).obj (op ((congr e).functor.obj P)) ≅ e.inverse ⋙ (coyoneda C).obj (op P) :=
  (coyoneda D).essImage.ι.mapIso ((coyoneda D).toEssImage.asEquivalence.counitIso.app
    ((congrEssImage e).obj ((coyoneda C).toEssImage.obj (op P))))

/-- The functor pro-represented by `(Pro.congr e).inverse.obj Q` is `Hom(Q, e -)`. -/
noncomputable def coyonedaObjCongrInverseObjIso (Q : Pro D) :
    (coyoneda C).obj (op ((congr e).inverse.obj Q)) ≅ e.functor ⋙ (coyoneda D).obj (op Q) :=
  (e.funInvIdAssoc _).symm ≪≫ Functor.isoWhiskerLeft e.functor
    ((coyonedaObjCongrFunctorObjIso e _).symm ≪≫
      ((coyoneda D).mapIso ((congr e).counitIso.app Q).op).symm)

/-- `coyonedaObjCongrFunctorObjIso` is natural in `P`. -/
lemma coyonedaObjCongrFunctorObjIso_hom_naturality {P P' : Pro C} (g : P ⟶ P') :
    (coyoneda D).map ((congr e).functor.map g).op ≫ (coyonedaObjCongrFunctorObjIso e P).hom =
      (coyonedaObjCongrFunctorObjIso e P').hom ≫
        Functor.whiskerLeft e.inverse ((coyoneda C).map g.op) :=
  congrArg (coyoneda D).essImage.ι.map
    ((coyoneda D).toEssImage.asEquivalence.counitIso.hom.naturality
      ((congrEssImage e).map ((coyoneda C).toEssImage.map g.op)))

/-- `coyonedaObjCongrInverseObjIso` is natural in `Q`. -/
lemma coyonedaObjCongrInverseObjIso_hom_naturality {Q Q' : Pro D} (h : Q ⟶ Q') :
    (coyoneda C).map ((congr e).inverse.map h).op ≫ (coyonedaObjCongrInverseObjIso e Q).hom =
      (coyonedaObjCongrInverseObjIso e Q').hom ≫
        Functor.whiskerLeft e.functor ((coyoneda D).map h.op) := by
  have h1 := coyonedaObjCongrFunctorObjIso_hom_naturality e ((congr e).inverse.map h)
  have s1 : (coyoneda C).map ((congr e).inverse.map h).op ≫
      (e.funInvIdAssoc ((coyoneda C).obj (op ((congr e).inverse.obj Q)))).inv =
      (e.funInvIdAssoc ((coyoneda C).obj (op ((congr e).inverse.obj Q')))).inv ≫
        Functor.whiskerLeft e.functor
          (Functor.whiskerLeft e.inverse ((coyoneda C).map ((congr e).inverse.map h).op)) := by
    ext X u
    exact Category.assoc _ _ _
  have s2 : Functor.whiskerLeft e.inverse ((coyoneda C).map ((congr e).inverse.map h).op) ≫
      (coyonedaObjCongrFunctorObjIso e ((congr e).inverse.obj Q)).inv =
      (coyonedaObjCongrFunctorObjIso e ((congr e).inverse.obj Q')).inv ≫
        (coyoneda D).map ((congr e).functor.map ((congr e).inverse.map h)).op := by
    rw [Iso.comp_inv_eq, Category.assoc, h1, Iso.inv_hom_id_assoc]
  have s3 : (coyoneda D).map ((congr e).functor.map ((congr e).inverse.map h)).op ≫
      (coyoneda D).map ((congr e).counitIso.app Q).inv.op =
      (coyoneda D).map ((congr e).counitIso.app Q').inv.op ≫ (coyoneda D).map h.op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
    congr 2
    rw [Iso.eq_comp_inv, Category.assoc, Iso.inv_comp_eq]
    exact (congr e).counitIso.hom.naturality h
  simp only [coyonedaObjCongrInverseObjIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.mapIso_inv, Iso.op_inv, Category.assoc]
  rw [reassoc_of% s1, ← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp]
  refine congrArg (_ ≫ ·) (congrArg (Functor.whiskerLeft e.functor) ?_)
  rw [reassoc_of% s2, s3, Category.assoc]

/-- `Pro.congr e` extends `e`. -/
noncomputable def congrFunctorObjOfIso (X : C) :
    (congr e).functor.obj (of.obj X) ≅ of.obj (e.functor.obj X) :=
  ((coyonedaFullyFaithful D).preimageIso
    (coyonedaObjCongrFunctorObjIso e (of.obj X) ≪≫
      Functor.isoWhiskerLeft e.inverse (ofOpCompCoyonedaIso.app (op X)) ≪≫
      ((Functor.ProRepresentation.coyonedaCongrIso e).app (op X)).symm ≪≫
      (ofOpCompCoyonedaIso.app (op (e.functor.obj X))).symm)).unop.symm

end Pro

end CategoryTheory
