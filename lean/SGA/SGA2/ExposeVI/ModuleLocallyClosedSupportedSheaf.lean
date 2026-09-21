/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedSheaf
import SGA.SGA2.ExposeI.LocallyClosedSupportedSheaves
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Actual module sheaves of locally supported sections

For a locally closed witness `W`, sections over `U` are the actual sections
over `W.V ∩ U` supported in the closed hull. Scalars act through the original
restriction `R(U) → R(W.V ∩ U)`. The module presheaf is a sheaf because its
underlying additive presheaf is naturally the original locally supported
sheaf of Exposé I.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- The scalar map used on intersections is actual structure-sheaf restriction. -/
def moduleIntersectionRingMap (V : Opens X) :
    R.obj ⟶ (ExposeI.openIntersectionFunctor V).op ⋙ R.obj where
  app U := R.obj.map (homOfLE (inf_le_right : V ⊓ U.unop ≤ U.unop)).op
  naturality {U W} i := by
    change R.obj.map i ≫ R.obj.map _ = R.obj.map _ ≫ R.obj.map _
    rw [← R.obj.map_comp, ← R.obj.map_comp]
    congr 1

variable (W : ExposeI.LocallyClosedIn X)

/-- The concrete locally supported section modules, with the original restrictions. -/
def moduleGammaLocallyClosedPresheaf (M : SheafOfModules.{u} R) :
    PresheafOfModules.{u} R.obj :=
  (PresheafOfModules.pushforward (moduleIntersectionRingMap R W.V)).obj
    (moduleGammaZPresheaf R W.closedHull M)

/-- Forgetting the module structures gives precisely the original additive
locally supported presheaf, through its ambient section comparison. -/
def moduleGammaLocallyClosedPresheafIso (M : SheafOfModules.{u} R) :
    ((ExposeI.underlineGammaLocallyClosedFunctor W).obj
        ((SheafOfModules.toSheaf R).obj M)).presheaf ≅
      (moduleGammaLocallyClosedPresheaf R W M).presheaf :=
  (ExposeI.underlineGammaLocallyClosedPresheafFunctorIso W ≪≫
    ExposeI.locallyClosedAmbientPresheafIso W W.closedHull W.closedSupportOnOpen_closedHull).app
      ((SheafOfModules.toSheaf R).obj M)

/-- The actual module sheaf of sections with locally closed support. -/
def moduleGammaLocallyClosedSheaf (M : SheafOfModules.{u} R) : SheafOfModules.{u} R where
  val := moduleGammaLocallyClosedPresheaf R W M
  isSheaf := (Presheaf.isSheaf_of_iso_iff (moduleGammaLocallyClosedPresheafIso R W M)).mp
    ((ExposeI.underlineGammaLocallyClosedFunctor W).obj
      ((SheafOfModules.toSheaf R).obj M)).property

/-- Actual coefficient maps on locally supported module sections. -/
def moduleGammaLocallyClosedSheafMap {M N : SheafOfModules.{u} R} (a : M ⟶ N) :
    moduleGammaLocallyClosedSheaf R W M ⟶ moduleGammaLocallyClosedSheaf R W N :=
  ⟨(PresheafOfModules.pushforward (moduleIntersectionRingMap R W.V)).map
    (moduleGammaZSheafMap R W.closedHull a).val⟩

/-- The actual module-valued locally supported section functor. -/
def moduleGammaLocallyClosedSheafFunctor : SheafOfModules.{u} R ⥤ SheafOfModules.{u} R where
  obj := moduleGammaLocallyClosedSheaf R W
  map := moduleGammaLocallyClosedSheafMap R W
  map_id _ := by ext U x; rfl
  map_comp _ _ := by ext U x; rfl

instance : (moduleGammaLocallyClosedSheafFunctor R W).Additive where
  map_add := by intros; ext U x; rfl

/-- The local module structures lie over the unchanged additive support functor,
naturally in every coefficient sheaf. -/
def moduleGammaLocallyClosedSheafForgetIso :
    moduleGammaLocallyClosedSheafFunctor R W ⋙ SheafOfModules.toSheaf R ≅
      SheafOfModules.toSheaf R ⋙ ExposeI.underlineGammaLocallyClosedFunctor W :=
  ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).whiskeringRight
    (SheafOfModules.{u} R)).preimageIso
      (Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
        (ExposeI.underlineGammaLocallyClosedPresheafFunctorIso W ≪≫
          ExposeI.locallyClosedAmbientPresheafIso W W.closedHull
            W.closedSupportOnOpen_closedHull)).symm

/-- The actual locally supported module-sheaf functor is left exact. -/
instance moduleGammaLocallyClosedSheafFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (moduleGammaLocallyClosedSheafFunctor R W) := by
  have : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} R) := inferInstance
  have : PreservesFiniteLimits (ExposeI.underlineGammaLocallyClosedFunctor W) := inferInstance
  have : PreservesFiniteLimits
      (moduleGammaLocallyClosedSheafFunctor R W ⋙ SheafOfModules.toSheaf R) :=
    preservesFiniteLimits_of_natIso (moduleGammaLocallyClosedSheafForgetIso R W).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (moduleGammaLocallyClosedSheafFunctor R W) (SheafOfModules.toSheaf R)

/-- The original locally supported module sheaves, right-derived in module sheaves. -/
def derivedModuleGammaLocallyClosedSheaf (n : ℕ) :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} R :=
  (moduleGammaLocallyClosedSheafFunctor R W).rightDerived n

end SGA.SGA2.ExposeVI
