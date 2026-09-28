/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.ClosedSupportAdjunction

/-!
# The original supported-sheaf functor preserves injectives

Topological inverse image is left exact by the representably flat functor on
open sets. Its right adjoint, ordinary direct image, therefore preserves
injectives. Combining this with the genuine closed support adjunction proves
injective preservation for the unchanged kernel-sheaf functor.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X Y : TopCat.{u}}

/-- The actual inverse image of abelian sheaves preserves finite limits for
every continuous map. -/
instance abelianSheafPullback_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits (Sheaf.pullback AddCommGrpCat.{u} f) := by
  have : ReflectsLimits (CategoryTheory.forget AddCommGrpCat.{u}) :=
    reflectsLimits_of_reflectsIsomorphisms
  have : PreservesFiniteLimits
      ((Opens.map f).op.lan : ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    lan_preservesFiniteLimits_of_flat AddCommGrpCat.{u} (Opens.map f)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map f)
    AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The actual inverse image of abelian sheaves is exact. -/
instance abelianSheafPullback_preservesHomology (f : X ⟶ Y) :
    (Sheaf.pullback AddCommGrpCat.{u} f).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- Ordinary direct image of abelian sheaves preserves injectives for every
continuous map, as the right adjoint of exact inverse image. -/
instance abelianSheafPushforward_preservesInjectiveObjects (f : X ⟶ Y) :
    (Sheaf.pushforward AddCommGrpCat.{u} f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)

/-- The original closed-support kernel functor preserves injectives. -/
instance underlineGammaZFunctor_preservesInjectiveObjects (Z : Closeds X) :
    (underlineGammaZFunctor Z).PreservesInjectiveObjects where
  injective_obj {F} hF := by
    let := hF
    have : Injective ((iUpperShriek_closed Z ⋙ iBang_closed Z).obj F) := by
      change Injective ((Sheaf.pushforward AddCommGrpCat.{u} (closedInclusion Z)).obj
        ((iUpperShriek_closed Z).obj F))
      infer_instance
    exact Injective.of_iso ((closedSupportPushforwardIso Z).app F) this

end SGA.SGA2.ExposeI
