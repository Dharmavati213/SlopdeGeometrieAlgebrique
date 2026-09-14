/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.OpenDerivedSupportedSheaves
import SGA.SGA2.ExposeI.SupportedSheafRestriction
import SGA.SGA2.ExposeI.ClosedSupportInternalHom

/-!
# SGA 2, I.2.7: local vanishing for closed supported sheaves

Actual open restriction commutes with the original derived support functor.
Empty and full support computations therefore prove vanishing outside the
closed support in every degree, and on its interior in positive degrees.
The comparisons transport these facts to genuine internal sheaf Ext and to
the unchanged kernel/cokernel/derived-pushforward model.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

/-- An exact functor has zero positive right-derived functors. -/
theorem rightDerived_isZero_of_preservesHomology
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasInjectiveResolutions C] (G : C ⥤ D) [G.Additive] [G.PreservesHomology]
    (A : C) (n : ℕ) : IsZero ((G.rightDerived (n + 1)).obj A) :=
  (G.map_isZero ((injectiveResolution A).cocomplex_exactAt_succ n).isZero_homology).of_iso
    ((injectiveResolution A).isoRightDerivedObj G (n + 1) ≪≫
      complexHomologyMapIso G (ComplexShape.up ℕ) (injectiveResolution A).cocomplex (n + 1))

variable {X : TopCat.{u}}

/-- The original kernel sheaf with empty support is zero. -/
theorem underlineGammaZ_bot_isZero (F : Sheaf AddCommGrpCat.{u} X) :
    IsZero (underlineGammaZ F (⊥ : Closeds X)) := by
  apply IsZero.of_full_of_faithful_of_isZero
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  apply Functor.isZero
  intro U
  change IsZero ((underlineGammaZ F (⊥ : Closeds X)).presheaf.obj (op U.unop))
  refine IsZero.of_iso (Y := AddCommGrpCat.of (gammaZSections F (⊥ : Closeds X) U.unop)) ?_
    (underlineGammaZSectionsEquiv F ⊥ U.unop).toAddCommGrpIso
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  rw [gammaZSections_bot]
  infer_instance

/-- Every original derived sheaf with empty support is zero, including degree zero. -/
theorem derivedUnderlineGammaZ_bot_isZero (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    IsZero ((derivedUnderlineGammaZ (⊥ : Closeds X) n).obj F) := by
  let I := injectiveResolution F
  apply IsZero.of_iso _ (I.isoRightDerivedObj (underlineGammaZFunctor ⊥) n)
  apply ShortComplex.isZero_homology_of_isZero_X₂
  exact underlineGammaZ_bot_isZero (I.cocomplex.X n)

/-- The original higher supported sheaves for full support vanish in positive degrees. -/
theorem derivedUnderlineGammaZ_top_isZero (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    IsZero ((derivedUnderlineGammaZ (⊤ : Closeds X) (n + 1)).obj F) := by
  let : (underlineGammaZFunctor (⊤ : Closeds X)).Additive := inferInstance
  exact (rightDerived_isZero_of_preservesHomology (𝟭 (Sheaf AddCommGrpCat.{u} X)) F n).of_iso
    ((rightDerivedFunctorIso (underlineGammaZTopIso (X := X)) (n + 1)).app F)

/-- **I.2.7, closed support:** original derived supported sheaves restrict to
zero on every open disjoint from the support, in every degree. -/
theorem derivedUnderlineGammaZ_restrict_isZero_of_le_compl (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) (hU : U ≤ Z.compl) (n : ℕ) :
    IsZero (restrictToOpen ((derivedUnderlineGammaZ Z n).obj F) U) := by
  have hZ : closedSupportOnOpen Z U = ⊥ := by
    ext x
    exact ⟨fun hx ↦ (hU x.property hx).elim, False.elim⟩
  have hz := derivedUnderlineGammaZ_bot_isZero (restrictToOpen F U) n
  rw [← hZ] at hz
  exact hz.of_iso ((derivedSupportedSheafRestrictionIso Z U n).app F)

/-- **I.2.7, closed support:** positive original supported sheaves restrict
to zero on every open contained in the support, in particular its interior. -/
theorem derivedUnderlineGammaZ_restrict_isZero_of_subset (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X)
    (hU : (U : Set X) ⊆ Z) (n : ℕ) :
    IsZero (restrictToOpen ((derivedUnderlineGammaZ Z (n + 1)).obj F) U) := by
  have hZ : closedSupportOnOpen Z U = ⊤ := by
    ext x
    exact ⟨fun _ ↦ trivial, fun _ ↦ hU x.property⟩
  have hz := derivedUnderlineGammaZ_top_isZero (restrictToOpen F U) n
  rw [← hZ] at hz
  exact hz.of_iso ((derivedSupportedSheafRestrictionIso Z U (n + 1)).app F)

/-- The unchanged supported-sheaf model is zero off the support. -/
theorem sheafH_Z_n_restrict_isZero_of_le_compl (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) (hU : U ≤ Z.compl) (n : ℕ) :
    IsZero (restrictToOpen (sheafH_Z_n Z F n) U) :=
  (derivedUnderlineGammaZ_restrict_isZero_of_le_compl Z F U hU n).of_iso
    ((iShriek_open U).mapIso (derivedUnderlineGammaZObjIsoModel Z F n)).symm

/-- The unchanged positive supported-sheaf model is zero on the interior. -/
theorem sheafH_Z_n_restrict_isZero_of_subset (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X)
    (hU : (U : Set X) ⊆ Z) (n : ℕ) :
    IsZero (restrictToOpen (sheafH_Z_n Z F (n + 1)) U) :=
  (derivedUnderlineGammaZ_restrict_isZero_of_subset Z F U hU n).of_iso
    ((iShriek_open U).mapIso (derivedUnderlineGammaZObjIsoModel Z F (n + 1))).symm

/-- Actual internal sheaf Ext from the closed integer support sheaf is zero
on any open disjoint from the support, in every degree. -/
theorem closedSupportInternalSheafExt_restrict_isZero_of_le_compl (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) (hU : U ≤ Z.compl) (n : ℕ) :
    IsZero (restrictToOpen
      ((internalSheafExtFunctor (Opens.grothendieckTopology X) (zZX_closed Z) n).obj F) U) :=
  (derivedUnderlineGammaZ_restrict_isZero_of_le_compl Z F U hU n).of_iso
    ((iShriek_open U).mapIso ((closedSupportInternalSheafExtIso Z n).app F))

/-- Actual positive internal sheaf Ext from the closed integer support
sheaf is zero on every open contained in the support. -/
theorem closedSupportInternalSheafExt_restrict_isZero_of_subset (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X)
    (hU : (U : Set X) ⊆ Z) (n : ℕ) :
    IsZero (restrictToOpen
      ((internalSheafExtFunctor (Opens.grothendieckTopology X)
        (zZX_closed Z) (n + 1)).obj F) U) :=
  (derivedUnderlineGammaZ_restrict_isZero_of_subset Z F U hU n).of_iso
    ((iShriek_open U).mapIso ((closedSupportInternalSheafExtIso Z (n + 1)).app F))

end SGA.SGA2.ExposeI
