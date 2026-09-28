/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.RelativeCohomologySections
import SGA.SGA2.ExposeI.SupportedSheafInjective

/-!
# Ordinary restriction on sheaf cohomology in every degree

The map is constructed independently of supported cohomology: apply the
actual exact inverse-image functor to Ext and use the canonical restriction
of the constant integer sheaf, obtained by sheafifying restriction of integer
presheaves. It is then proved equal, in every degree, to the map in the
existing relative cohomology sequence.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian Functor
open SGA.SGA2.ExposeI

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- Restriction of universal integer sections, extended to the actual
constant sheaf by the universal property of sheafification. -/
def constantZToNaiveOpenRestriction (U : Opens X) :
    constantZ ((Opens.toTopCat X).obj U) ⟶
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj (constantZ X) :=
  ⟨sheafifyLift (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
    (whiskerLeft U.isOpenEmbedding.functor.op
      (toSheafify (Opens.grothendieckTopology X) (integerPresheaf X)))
    ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj (constantZ X)).property⟩

/-- The canonical constant-integer map for ordinary open inverse image.
It is defined from integer sections, not from a support sequence. -/
def constantZOpenRestriction (U : Opens X) :
    constantZ ((Opens.toTopCat X).obj U) ⟶ restrictToOpen (constantZ X) U :=
  constantZToNaiveOpenRestriction U ≫
    ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).app (constantZ X)).inv

/-- The canonical integer restriction is precisely the adjoint of the
independently constructed open constant inclusion. -/
theorem constantZOpenRestriction_eq_adjunction (U : Opens X) :
    constantZOpenRestriction U =
      (openExtensionByZeroAdjunction U).homEquiv _ _ (zZX_openToConstant U) := by
  rw [← cancel_mono
    ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).app (constantZ X)).hom]
  simp only [constantZOpenRestriction, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply CategoryTheory.Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj (constantZ X)).property
  exact (toSheafify_sheafifyLift _ _ _).trans
    (zZX_openToConstant_adjunction U).symm

/-- The ordinary restriction-induced map on actual sheaf cohomology:
exact inverse image on Ext, followed by the canonical integer restriction. -/
def ordinaryCohomologyRestriction (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H F n →+ H (restrictToOpen F U) n :=
  ((Ext.mk₀ (constantZOpenRestriction U)).precomp (restrictToOpen F U) (zero_add n)).comp
    ((iShriek_open U).mapExtAddHom (constantZ X) F n)

/-- The ordinary restriction is genuine exact-functor action on Ext. -/
theorem ordinaryCohomologyRestriction_apply (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) (x : H F n) :
    ordinaryCohomologyRestriction U F n x =
      (Ext.mk₀ (constantZOpenRestriction U)).comp
        (x.mapExactFunctor (iShriek_open U)) (zero_add n) := rfl

/-- In every degree, the original relative-sequence map is the ordinary
cohomology map induced by actual restriction of sheaves. -/
theorem relativeRestriction_eq_ordinary (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    relativeRestriction Z F n = ordinaryCohomologyRestriction Z.compl F n := by
  let := (openExtensionByZeroAdjunction Z.compl).isRightAdjoint
  ext x
  change (Ext.mk₀ ((openExtensionByZeroAdjunction Z.compl).unit.app _)).comp
      (((Ext.mk₀ (zZX_openToConstant Z.compl)).comp x (zero_add n)).mapExactFunctor
        (iShriek_open Z.compl)) (zero_add n) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ordinaryCohomologyRestriction_apply, constantZOpenRestriction_eq_adjunction,
    Adjunction.homEquiv_apply, ← Ext.mk₀_comp_mk₀]
  exact (Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (zero_add n)).symm

/-- In degree zero, this exact inverse-image cohomology map is literal
restriction of sections under the original degree-zero identifications. -/
theorem ordinaryCohomologyRestriction_zero_sections (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (x : H F 0) :
    (restrictToOpenSectionsIso U F).hom
      (CategoryTheory.Sheaf.H.equiv₀ (restrictToOpen F U) isTerminalTop
        (ordinaryCohomologyRestriction U F 0 x)) =
      F.presheaf.map (homOfLE le_top : U ⟶ ⊤).op
        (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop x) := by
  have h := relativeRestriction_zero_sections U.compl F x
  rw [relativeRestriction_eq_ordinary] at h
  have hU : U.compl.compl = U := Opens.compl_compl U
  exact hU ▸ h

end SGA.SGA2.ExposeIII
