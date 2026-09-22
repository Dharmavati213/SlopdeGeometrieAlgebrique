/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleOpenRestriction

/-!
# Restriction between nested open module sites

Restriction between two open slice sites is exact and preserves injectives.
An injective on the larger open has an injective direct image on the
ambient space, whose restriction back to the open is the original module.
The comparison uses the actual restriction and direct-image adjunction.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (U : Opens X)

/-- Morphisms of opens over `U` are exactly inclusions of their underlying opens. -/
instance overForget_opens_full : (Over.forget U).Full where
  map_surjective f := ⟨Over.homMk f (Subsingleton.elim _ _), rfl⟩

/-- The actual direct image of module sheaves from the open site. -/
def moduleOpenDirectImage : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R :=
  SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)

/-- The restriction/direct-image adjunction for module sheaves. -/
def moduleOpenRestrictionDirectImageAdjunction :
    moduleOpenRestriction R U ⊣ moduleOpenDirectImage R U :=
  SheafOfModules.overPushforwardOverAdj U

/-- Direct image from an open sends injective modules to injective modules. -/
instance moduleOpenDirectImage_preservesInjectiveObjects :
    (moduleOpenDirectImage R U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (moduleOpenRestrictionDirectImageAdjunction R U)

/-- The counit identifies restriction of the direct image with the
original module sheaf on the open site. -/
instance moduleOpenDirectImage_counit_isIso (M : SheafOfModules.{u} (R.over U)) :
    IsIso ((moduleOpenRestrictionDirectImageAdjunction R U).counit.app M) := by
  let F : SheafOfModules.{u} (R.over U) ⥤ (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    SheafOfModules.forget (R.over U) ⋙ PresheafOfModules.toPresheaf (R.over U).obj
  have (V : (Over U)ᵒᵖ) :
      IsIso ((F.map ((moduleOpenRestrictionDirectImageAdjunction R U).counit.app M)).app V) := by
    change IsIso (M.val.presheaf.map ((Over.forgetAdjStar U).unit.app V.unop).op)
    infer_instance
  have : IsIso (F.map ((moduleOpenRestrictionDirectImageAdjunction R U).counit.app M)) :=
    NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ F

/-- Restriction recovers every module sheaf after direct image from the open. -/
def moduleOpenDirectImageCounitIso (M : SheafOfModules.{u} (R.over U)) :
    (moduleOpenRestriction R U).obj ((moduleOpenDirectImage R U).obj M) ≅ M :=
  asIso ((moduleOpenRestrictionDirectImageAdjunction R U).counit.app M)

variable {U} {V : Opens X} (i : V ⟶ U)

/-- The actual restriction functor between nested open sites. -/
def moduleNestedOpenRestriction : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} (R.over V) :=
  SheafOfModules.overMap R i

instance moduleNestedOpenRestriction_additive : (moduleNestedOpenRestriction R i).Additive where
  map_add := rfl

instance moduleNestedOpenRestriction_isLeftAdjoint :
    (moduleNestedOpenRestriction R i).IsLeftAdjoint := by
  dsimp [moduleNestedOpenRestriction]
  infer_instance

instance moduleNestedOpenRestriction_isRightAdjoint :
    (moduleNestedOpenRestriction R i).IsRightAdjoint := by
  dsimp [moduleNestedOpenRestriction, SheafOfModules.overMap]
  infer_instance

instance moduleNestedOpenRestriction_preservesHomology :
    (moduleNestedOpenRestriction R i).PreservesHomology := inferInstance

/-- Restriction from an open to a smaller open preserves injectives. -/
instance moduleNestedOpenRestriction_preservesInjectiveObjects :
    (moduleNestedOpenRestriction R i).PreservesInjectiveObjects where
  injective_obj {M} hM := by
    let := hM
    let N := (moduleOpenDirectImage R U).obj M
    let : Injective N := inferInstance
    have h := (SheafOfModules.overFunctorMap R i).app N
    exact Injective.of_iso (h.symm ≪≫
      (moduleNestedOpenRestriction R i).mapIso (moduleOpenDirectImageCounitIso R U M))
      (moduleOpenRestriction_injective V R N)

/-- Local linear Hom restriction agrees with the actual functor between
nested open module sites, including the canonical source and target comparisons. -/
theorem moduleLocalHomSheafOverEquiv_restrict (F G : SheafOfModules.{u} R)
    (φ : moduleLocalHom F.val G.val U) :
    moduleLocalHomSheafOverEquiv F G V (moduleLocalHomRestrict F.val G.val i φ) =
      ((SheafOfModules.overFunctorMap R i).app F).inv ≫
        (moduleNestedOpenRestriction R i).map (moduleLocalHomSheafOverEquiv F G U φ) ≫
          ((SheafOfModules.overFunctorMap R i).app G).hom := by
  ext T x
  rfl

end SGA.SGA2.ExposeVI
