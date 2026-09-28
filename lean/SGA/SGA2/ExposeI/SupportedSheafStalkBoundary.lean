/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.SupportedSheafBoundary
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Abelian

/-! # Literal stalk support of original derived supported sheaves -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

/-- Ordinary inverse image has the actual source stalk at every point.
This comparison uses presheaf inverse image and the genuine sheafification unit. -/
def abelianSheafPullbackStalkIso {X Y : TopCat.{u}} (f : X ⟶ Y)
    (F : Sheaf AddCommGrpCat.{u} Y) (x : X) :
    F.presheaf.stalk (f x) ≅ ((Sheaf.pullback AddCommGrpCat.{u} f).obj F).presheaf.stalk x := by
  let P := (Presheaf.pullback AddCommGrpCat.{u} f).obj F.presheaf
  let c := toSheafify (Opens.grothendieckTopology X) P
  have : IsIso ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map c) :=
    Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  exact Presheaf.stalkPullbackIso AddCommGrpCat.{u} f F.presheaf x ≪≫
    asIso ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map c) ≪≫
      ((Sheaf.forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
        ((Sheaf.pullbackIso AddCommGrpCat.{u} f).app F)).symm

variable {X : TopCat.{u}}

/-- If actual restriction to a neighborhood is zero, the actual stalk there is zero. -/
theorem sheafStalk_isZero_of_restrict_isZero (F : Sheaf AddCommGrpCat.{u} X)
    (U : Opens X) (hF : IsZero (restrictToOpen F U)) (x : X) (hx : x ∈ U) :
    IsZero (F.presheaf.stalk x) :=
  ((Sheaf.forget AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) ⋙
      Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨x, hx⟩ : U)).map_isZero hF).of_iso
    (abelianSheafPullbackStalkIso U.inclusion' F ⟨x, hx⟩)

/-- **I.2.7, closed support:** every literal stalk off the support is zero. -/
theorem derivedUnderlineGammaZ_stalk_isZero_of_not_mem (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) (x : X) (hx : x ∉ Z) :
    IsZero (((derivedUnderlineGammaZ Z n).obj F).presheaf.stalk x) :=
  sheafStalk_isZero_of_restrict_isZero _ Z.compl
    (derivedUnderlineGammaZ_restrict_isZero_of_le_compl Z F Z.compl le_rfl n) x hx

/-- **I.2.7, closed support:** positive literal stalks are zero on the interior. -/
theorem derivedUnderlineGammaZ_stalk_isZero_of_mem_interior (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) (x : X)
    (hx : x ∈ interior (Z : Set X)) :
    IsZero (((derivedUnderlineGammaZ Z (n + 1)).obj F).presheaf.stalk x) :=
  sheafStalk_isZero_of_restrict_isZero _ ⟨interior (Z : Set X), isOpen_interior⟩
    (derivedUnderlineGammaZ_restrict_isZero_of_subset Z F _ interior_subset n) x hx

/-- The locus of nonzero actual stalks of a supported sheaf lies in the closed support. -/
theorem derivedUnderlineGammaZ_stalkSupport_subset (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    {x : X | ¬ IsZero (((derivedUnderlineGammaZ Z n).obj F).presheaf.stalk x)} ⊆ Z := by
  classical
  intro x hx
  by_contra hxZ
  exact hx (derivedUnderlineGammaZ_stalk_isZero_of_not_mem Z F n x hxZ)

/-- Positive original supported sheaves have literal stalk support on the boundary. -/
theorem derivedUnderlineGammaZ_stalkSupport_subset_frontier (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    {x : X | ¬ IsZero (((derivedUnderlineGammaZ Z (n + 1)).obj F).presheaf.stalk x)} ⊆
      frontier (Z : Set X) := by
  intro x hx
  rw [frontier, Z.isClosed.closure_eq]
  exact ⟨derivedUnderlineGammaZ_stalkSupport_subset Z F (n + 1) hx,
    fun hi ↦ hx (derivedUnderlineGammaZ_stalk_isZero_of_mem_interior Z F n x hi)⟩

/-- The unchanged supported-sheaf model has no nonzero stalk outside the support. -/
theorem sheafH_Z_n_stalkSupport_subset (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    {x : X | ¬ IsZero ((sheafH_Z_n Z F n).presheaf.stalk x)} ⊆ Z := by
  intro x hx
  apply derivedUnderlineGammaZ_stalkSupport_subset Z F n
  intro hz
  exact hx (hz.of_iso
    ((Sheaf.forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      (derivedUnderlineGammaZObjIsoModel Z F n)).symm)

/-- Positive literal stalks of the unchanged model are supported on the boundary. -/
theorem sheafH_Z_n_stalkSupport_subset_frontier (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    {x : X | ¬ IsZero ((sheafH_Z_n Z F (n + 1)).presheaf.stalk x)} ⊆
      frontier (Z : Set X) := by
  intro x hx
  apply derivedUnderlineGammaZ_stalkSupport_subset_frontier Z F n
  intro hz
  exact hx (hz.of_iso
    ((Sheaf.forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      (derivedUnderlineGammaZObjIsoModel Z F (n + 1))).symm)

/-- Actual internal sheaf Ext has literal stalk support inside the closed set. -/
theorem closedSupportInternalSheafExt_stalkSupport_subset (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    {x : X | ¬ IsZero (Presheaf.stalk (X := X)
      ((internalSheafExtFunctor (Opens.grothendieckTopology X)
        (zZX_closed Z) n).obj F).obj x)} ⊆ Z := by
  intro x hx
  apply derivedUnderlineGammaZ_stalkSupport_subset Z F n
  intro hz
  exact hx (hz.of_iso
    ((Sheaf.forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((closedSupportInternalSheafExtIso Z n).app F)))

/-- Positive actual internal sheaf Ext is supported on the boundary of the closed set. -/
theorem closedSupportInternalSheafExt_stalkSupport_subset_frontier (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    {x : X | ¬ IsZero (Presheaf.stalk (X := X)
      ((internalSheafExtFunctor (Opens.grothendieckTopology X)
        (zZX_closed Z) (n + 1)).obj F).obj x)} ⊆ frontier (Z : Set X) := by
  intro x hx
  apply derivedUnderlineGammaZ_stalkSupport_subset_frontier Z F n
  intro hz
  exact hx (hz.of_iso
    ((Sheaf.forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((closedSupportInternalSheafExtIso Z (n + 1)).app F)))

end SGA.SGA2.ExposeI
