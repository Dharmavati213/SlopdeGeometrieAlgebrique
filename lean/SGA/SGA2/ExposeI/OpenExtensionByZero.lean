/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.ExtensionByZero
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Extension by zero for an open immersion

The left adjoint to ordinary restriction is constructed by left Kan extension
along the open-image functor, followed by sheafification. In particular this
is not the ordinary pushforward functor.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Genuine open extension by zero: extend the presheaf along the inclusion
of opens contained in `U`, then sheafify. -/
noncomputable def iBang_open (U : Opens X) :
    Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) ⥤
      Sheaf AddCommGrpCat.{u} X :=
  sheafToPresheaf _ _ ⋙ U.isOpenEmbedding.functor.op.lan ⋙ presheafToSheaf _ _

/-- **I.1.3, open case:** extension by zero is left adjoint to ordinary
restriction (the already defined `iShriek_open`). -/
noncomputable def openExtensionByZeroAdjunction (U : Opens X) :
    iBang_open U ⊣ iShriek_open U := by
  letI := U.isOpenEmbedding.functor_isContinuous
  exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    U.isOpenEmbedding.functor AddCommGrpCat.{u}
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      (Opens.grothendieckTopology X)).ofNatIsoRight
    (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).symm

/-- The Hom adjunction of **I.1.3** for an open immersion. -/
noncomputable def openExtensionByZeroHomEquiv (U : Opens X)
    (G : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U))
    (F : Sheaf AddCommGrpCat.{u} X) :
    ((iBang_open U).obj G ⟶ F) ≃ (G ⟶ restrictToOpen F U) :=
  (openExtensionByZeroAdjunction U).homEquiv G F

noncomputable instance (U : Opens X) : (iBang_open U).IsLeftAdjoint :=
  (openExtensionByZeroAdjunction U).isLeftAdjoint

noncomputable instance (U : Opens X) : (iBang_open U).Additive :=
  (openExtensionByZeroAdjunction U).left_adjoint_additive

private theorem openImageLan_mono_app_image (U : Opens X)
    {F G : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (φ : F ⟶ G) [Mono φ] (W : Opens ((Opens.toTopCat X).obj U)) :
    Mono ((U.isOpenEmbedding.functor.op.lan.map φ).app
      (op (U.isOpenEmbedding.functor.obj W))) := by
  have : Mono (Opens.inclusion' U) :=
    (TopCat.mono_iff_injective _).2 Subtype.val_injective
  let L := U.isOpenEmbedding.functor.op
  have h := congr_app (L.lanUnit.naturality φ) (op W)
  change φ.app (op W) ≫ (L.lanUnit.app G).app (op W) =
    (L.lanUnit.app F).app (op W) ≫ (L.lan.map φ).app (L.obj (op W)) at h
  have he : (L.lan.map φ).app (L.obj (op W)) =
      inv ((L.lanUnit.app F).app (op W)) ≫
        φ.app (op W) ≫ (L.lanUnit.app G).app (op W) := by
    rw [h, IsIso.inv_hom_id_assoc]
  change Mono ((L.lan.map φ).app (L.obj (op W)))
  rw [he]
  infer_instance

private theorem openImageLan_isZero_of_not_le (U V : Opens X) (hV : ¬ V ≤ U)
    (F : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsZero ((U.isOpenEmbedding.functor.op.lan.obj F).obj (op V)) := by
  let L := U.isOpenEmbedding.functor.op
  have : IsEmpty (CostructuredArrow L (op V)) := ⟨fun A => by
    apply hV
    have h := leOfHom A.hom.unop
    exact h.trans (by
      rintro x ⟨y, hy, rfl⟩
      exact y.property)⟩
  have hF : IsZero (CostructuredArrow.proj L (op V) ⋙ F) :=
    Functor.isZero _ (fun A => isEmptyElim A)
  exact ((colimit.isColimit _).isZero_pt hF).of_iso
    (L.leftKanExtensionObjIsoColimit F (op V))

/-- Before sheafification, extension by zero preserves monomorphisms:
inside the open its components are the original components, and every
component indexed by an open not contained in `U` has zero source. -/
instance openImageLan_preservesMonomorphisms (U : Opens X) :
    (U.isOpenEmbedding.functor.op.lan :
      (_ ⥤ AddCommGrpCat.{u}) ⥤ (_ ⥤ AddCommGrpCat.{u})).PreservesMonomorphisms where
  preserves {F G} φ hφ := by
    apply (NatTrans.mono_iff_mono_app _).2
    intro V
    by_cases hV : V.unop ≤ U
    · have h : U.isOpenEmbedding.functor.obj
          ((Opens.map (Opens.inclusion' U)).obj V.unop) = V.unop := by
        rw [Opens.functor_obj_map_obj, Opens.isOpenEmbedding_obj_top, inf_eq_right.mpr hV]
      have hm := openImageLan_mono_app_image U φ
        ((Opens.map (Opens.inclusion' U)).obj V.unop)
      change Mono ((U.isOpenEmbedding.functor.op.lan.map φ).app (op V.unop))
      rw [← h]
      exact hm
    · exact mono_of_source_iso_zero _
        (openImageLan_isZero_of_not_le U V.unop hV F).isoZero

set_option backward.isDefEq.respectTransparency false in
/-- Open extension by zero preserves monomorphisms. -/
instance iBang_open_preservesMonomorphisms (U : Opens X) :
    (iBang_open U).PreservesMonomorphisms where
  preserves {F G} φ hφ := by
    have hforget : (sheafToPresheaf
        (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        AddCommGrpCat.{u}).PreservesMonomorphisms := inferInstance
    have : Mono φ.hom := hforget.preserves φ
    have : Mono (U.isOpenEmbedding.functor.op.lan.map φ.hom) :=
      (openImageLan_preservesMonomorphisms U).preserves φ.hom
    change Mono ((presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).map (U.isOpenEmbedding.functor.op.lan.map φ.hom))
    infer_instance

/-- Open extension by zero is exact. -/
noncomputable instance iBang_open_preservesHomology (U : Opens X) :
    (iBang_open U).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels (iBang_open U)

/-- Extension by zero takes short exact sequences to short exact sequences. -/
theorem iBang_open_shortExact (U : Opens X)
    (S : ShortComplex (Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)))
    (hS : S.ShortExact) : (S.map (iBang_open U)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map (iBang_open U)

/-- **I.1.4, open case:** ordinary restriction preserves injective objects,
because its left adjoint is exact. -/
instance iShriek_open_preservesInjectiveObjects (U : Opens X) :
    (iShriek_open U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (openExtensionByZeroAdjunction U)

/-- Restricting an injective abelian sheaf to an open gives an injective sheaf. -/
theorem restrictToOpen_injective (U : Opens X) (F : Sheaf AddCommGrpCat.{u} X)
    [Injective F] : Injective (restrictToOpen F U) :=
  (openExtensionByZeroAdjunction U).map_injective F inferInstance

/-- Open extension by zero of an abelian sheaf. -/
noncomputable abbrev extendByZero_open (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)) :
    Sheaf AddCommGrpCat.{u} X :=
  (iBang_open U).obj F

/-- The actual `ℤ_{U,X}` for an open subset. -/
noncomputable def zZX_open (U : Opens X) : Sheaf AddCommGrpCat.{u} X :=
  extendByZero_open U (constantZ ((Opens.toTopCat X).obj U))

end SGA.SGA2.ExposeI
