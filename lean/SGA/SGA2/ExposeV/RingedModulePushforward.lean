/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.RingedModuleSupportedSections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# SGA 2, V.3.2: pushforward of modules on general ringed spaces

A continuous map and a map of structure sheaves give the actual pushforward
of module sheaves. Forgetting module structures commutes with topological
pushforward. Hence pushforward preserves flasqueness, and in particular takes
injective module sheaves to flasque module sheaves, without a flatness condition.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat
open TopCat.Sheaf (IsFlasque)

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {R : Sheaf RingCat.{u} X} {S : Sheaf RingCat.{u} Y}
  (φ : S ⟶ (Sheaf.pushforward RingCat f).obj R)

/-- The actual pushforward of module sheaves for a morphism of ringed spaces. -/
abbrev ringedModulePushforward : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S :=
  SheafOfModules.pushforward (F := Opens.map f) φ

/-- Underlying additive sheaves commute with the module-theoretic pushforward. -/
def ringedModulePushforwardForgetIso :
    ringedModulePushforward f φ ⋙ SheafOfModules.toSheaf S ≅
      SheafOfModules.toSheaf R ⋙ Sheaf.pushforward AddCommGrpCat f :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

instance : (ringedModulePushforward f φ).Additive where
  map_add := by intros; ext U s; rfl

/-- The module-theoretic direct image is left exact. -/
instance ringedModulePushforward_preservesFiniteLimits :
    PreservesFiniteLimits (ringedModulePushforward f φ) := by
  have : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} R) := inferInstance
  have : PreservesFiniteLimits (Sheaf.pushforward AddCommGrpCat.{u} f) := inferInstance
  have : PreservesFiniteLimits
      (ringedModulePushforward f φ ⋙ SheafOfModules.toSheaf S) :=
    preservesFiniteLimits_of_natIso (ringedModulePushforwardForgetIso f φ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (ringedModulePushforward f φ) (SheafOfModules.toSheaf S)

/-- The actual higher direct images in the category of module sheaves. -/
def derivedRingedModulePushforward (q : ℕ) :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} S :=
  (ringedModulePushforward f φ).rightDerived q

/-- The zeroth higher direct image is naturally ordinary module pushforward. -/
def derivedRingedModulePushforwardZeroIso :
    derivedRingedModulePushforward f φ 0 ≅ ringedModulePushforward f φ :=
  (ringedModulePushforward f φ).rightDerivedZeroIsoSelf

/-- Direct image preserves flasqueness for arbitrary morphisms of ringed spaces. -/
theorem ringedModulePushforward_isFlasque (M : SheafOfModules.{u} R)
    [IsFlasque ((SheafOfModules.toSheaf R).obj M)] :
    IsFlasque ((SheafOfModules.toSheaf S).obj ((ringedModulePushforward f φ).obj M)) := by
  exact inferInstanceAs
    (IsFlasque ((Sheaf.pushforward AddCommGrpCat f).obj ((SheafOfModules.toSheaf R).obj M)))

/-- Direct images of injective module sheaves are flasque, whether or not the
morphism of ringed spaces is flat. -/
theorem ringedModulePushforward_injective_isFlasque
    (M : SheafOfModules.{u} R) [Injective M] :
    IsFlasque ((SheafOfModules.toSheaf S).obj ((ringedModulePushforward f φ).obj M)) := by
  have := moduleIsFlasque_of_injective R M
  exact ringedModulePushforward_isFlasque f φ M

end SGA.SGA2.ExposeV
