/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.RelativeCohomologySequence
import SGA.SGA2.ExposeI.FlasqueVanishingCriterion

/-!
# Degree zero of the relative cohomology sequence

The actual Ext-defined relative restriction becomes ordinary restriction of
sections under the standard degree-zero cohomology equivalences.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- The standard degree-zero cohomology equivalence on a degree-zero Ext
class is the constant-sheaf representation of global sections. -/
theorem H_equiv₀_mk₀ (F : Sheaf AddCommGrpCat.{u} X) (g : constantZ X ⟶ F) :
    CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop (Ext.mk₀ g) = constantZHomEquiv F g := by
  change constantZHomEquiv F (Ext.addEquiv₀ (Ext.mk₀ g)) = constantZHomEquiv F g
  exact congrArg (constantZHomEquiv F) (Ext.addEquiv₀.apply_symm_apply g)

/-- **I.2.9, degree zero:** the map from ordinary cohomology to the open
complement is the original restriction of global sections. -/
theorem relativeRestriction_zero_sections (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (x : H F 0) :
    (restrictToOpenSectionsIso Z.compl F).hom
      (CategoryTheory.Sheaf.H.equiv₀ (restrictToOpen F Z.compl) isTerminalTop
        (relativeRestriction Z F 0 x)) =
      F.presheaf.map (homOfLE le_top : Z.compl ⟶ ⊤).op
        (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop x) := by
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (constantZ X) F).surjective x
  change (restrictToOpenSectionsIso Z.compl F).hom
      (CategoryTheory.Sheaf.H.equiv₀ (restrictToOpen F Z.compl) isTerminalTop
        (openSupportExtEquiv Z.compl F 0
          ((Ext.mk₀ (zZX_openToConstant Z.compl)).comp (Ext.mk₀ g) (zero_add 0)))) = _
  rw [Ext.mk₀_comp_mk₀, openSupportExtEquiv_mk₀, H_equiv₀_mk₀, H_equiv₀_mk₀]
  exact openSupportHomEquiv_zZX_openToConstant Z.compl F g

/-- The ambient-to-closed constant morphism extends the existing integer
presheaf presentation of the closed constant support object. -/
theorem toSheafify_comp_constantToClosedSupport (Z : Closeds X) :
    toSheafify (Opens.grothendieckTopology X) (integerPresheaf X) ≫
      (constantToClosedSupport Z).hom = integerPresheafToClosed Z := by
  change toSheafify (Opens.grothendieckTopology X) (integerPresheaf X) ≫
    (sheafifyMap (Opens.grothendieckTopology X) (integerPresheafToClosed Z) ≫
      ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit.app
        (zZX_closed Z)).hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    sheafificationAdjunction_counit_app_val, toSheafify_sheafifyLift, Category.comp_id]

/-- The closed support map on representing Hom groups is inclusion of
supported sections into all global sections. -/
theorem constantZHomEquiv_constantToClosedSupport (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (g : zZX_closed Z ⟶ F) :
    constantZHomEquiv F (constantToClosedSupport Z ≫ g) =
      (closedSupportHomEquiv Z F g).val := by
  have h := ConcreteCategory.congr_hom (C := AddCommGrpCat.{u})
    (congrArg (fun q => q.app (op ⊤)) (toSheafify_comp_constantToClosedSupport Z))
      (⟨1⟩ : ULift.{u} ℤ)
  exact congrArg (g.hom.app (op ⊤)) h

/-- **I.2.9, degree zero:** the supported-to-ordinary map is the actual
inclusion `Γ_Z(X,F) → Γ(X,F)`. -/
theorem relativeSupportMap_zero_sections (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (x : H_Z Z F 0) :
    CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop (relativeSupportMap Z F 0 x) =
      (H_Z_zero_gammaZ_addEquiv Z F x).val := by
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (zZX_closed Z) F).surjective x
  change CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop
      ((Ext.mk₀ (constantToClosedSupport Z)).comp (Ext.mk₀ g) (zero_add 0)) =
    (closedSupportHomEquiv Z F (Ext.addEquiv₀ (Ext.mk₀ g))).val
  rw [Ext.mk₀_comp_mk₀, H_equiv₀_mk₀]
  have h : Ext.addEquiv₀ (Ext.mk₀ g) = g := Ext.addEquiv₀.apply_symm_apply g
  rw [h]
  exact constantZHomEquiv_constantToClosedSupport Z F g

end SGA.SGA2.ExposeI
