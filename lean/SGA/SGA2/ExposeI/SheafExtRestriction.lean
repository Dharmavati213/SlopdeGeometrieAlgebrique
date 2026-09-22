/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.SheafExtLocalComparison

/-!
# Nested-open restriction of local Ext

The evaluation equivalences identifying local Ext with Ext of ordinary
restrictions commute with the presheaf restriction maps along nested opens.
Those restriction maps are the standard Ext restriction maps of I.1.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Restriction of the local Ext presheaf along an inclusion of opens. -/
def internalExtPresheafRestrict (F G : Sheaf AddCommGrpCat.{u} X)
    {U V : Opens X} (h : U ≤ V) (n : ℕ) :
    ((internalExtPresheafFunctor F n).obj G).obj (op V) →+
      ((internalExtPresheafFunctor F n).obj G).obj (op U) :=
  (((internalExtPresheafFunctor F n).obj G).map (homOfLE h).op).hom

/-- The standard Ext restriction map along nested opens, obtained by
transporting presheaf restriction along the evaluation equivalences. -/
def localExtRestriction (F G : Sheaf AddCommGrpCat.{u} X)
    {U V : Opens X} (h : U ≤ V) (n : ℕ) :
    Ext (restrictToOpen F V) (restrictToOpen G V) n →+
      Ext (restrictToOpen F U) (restrictToOpen G U) n :=
  (internalExtPresheafSectionsEquiv F G U n).toAddMonoidHom.comp
    ((internalExtPresheafRestrict F G h n).comp
      (internalExtPresheafSectionsEquiv F G V n).symm.toAddMonoidHom)

/-- Evaluation equivalences intertwine presheaf restriction with the
standard nested-open Ext restriction maps. -/
theorem internalExtPresheafSectionsEquiv_restrict (F G : Sheaf AddCommGrpCat.{u} X)
    {U V : Opens X} (h : U ≤ V) (n : ℕ)
    (x : ((internalExtPresheafFunctor F n).obj G).obj (op V)) :
    internalExtPresheafSectionsEquiv F G U n (internalExtPresheafRestrict F G h n x) =
      localExtRestriction F G h n (internalExtPresheafSectionsEquiv F G V n x) := by
  simp [localExtRestriction, AddEquiv.symm_apply_apply]

theorem localExtRestriction_id (F G : Sheaf AddCommGrpCat.{u} X)
    (U : Opens X) (n : ℕ)
    (x : Ext (restrictToOpen F U) (restrictToOpen G U) n) :
    localExtRestriction F G (le_rfl : U ≤ U) n x = x := by
  have hmap :
      ((internalExtPresheafFunctor F n).obj G).map (homOfLE (le_rfl : U ≤ U)).op =
        𝟙 _ :=
    ((internalExtPresheafFunctor F n).obj G).map_id (op U)
  rw [localExtRestriction, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    internalExtPresheafRestrict, hmap]
  simp

theorem localExtRestriction_comp (F G : Sheaf AddCommGrpCat.{u} X)
    {U V W : Opens X} (hUV : U ≤ V) (hVW : V ≤ W) (n : ℕ)
    (x : Ext (restrictToOpen F W) (restrictToOpen G W) n) :
    localExtRestriction F G hUV n (localExtRestriction F G hVW n x) =
      localExtRestriction F G (hUV.trans hVW) n x := by
  have hmap :
      ((internalExtPresheafFunctor F n).obj G).map (homOfLE (hUV.trans hVW)).op =
        ((internalExtPresheafFunctor F n).obj G).map (homOfLE hVW).op ≫
          ((internalExtPresheafFunctor F n).obj G).map (homOfLE hUV).op := by
    rw [← Functor.map_comp]
    rfl
  simp [localExtRestriction, internalExtPresheafRestrict, hmap]



end SGA.SGA2.ExposeI
