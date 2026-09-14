/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.ModuleRepresentation
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# The precise preorder-indexed criterion of IV.1.2

The source only asks for projective limits over preordered sets, not
necessarily filtered. Such limits include products and pullbacks (up to
the actual equivalence with their thin skeletons), hence imply preservation
of all small limits. This supplies the exact source criterion, not a stronger
limit-preservation hypothesis.
-/

noncomputable section

universe u v₁ v₂ w₁ w₂

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

/-- All limits indexed by a preordered set in the specified universe.
There is deliberately no filteredness assumption. -/
def PreservesPreorderLimits {C : Type v₁} {D : Type v₂}
    [Category.{w₁} C] [Category.{w₂} D] (F : C ⥤ D) : Prop :=
  ∀ (J : Type u) (_ : Preorder J), PreservesLimitsOfShape J F

section General

variable {C : Type v₁} {D : Type v₂} [Category.{w₁} C] [Category.{w₂} D]
    (F : C ⥤ D)

/-- Thin indexing categories really are equivalent to actual preorders. -/
theorem preservesThinLimitsOfShape (h : PreservesPreorderLimits.{u} F)
    (J : Type u) [SmallCategory J] [Quiver.IsThin J] : PreservesLimitsOfShape J F := by
  have : PreservesLimitsOfShape (ThinSkeleton J) F := h (ThinSkeleton J) inferInstance
  exact preservesLimitsOfShape_of_equiv (ThinSkeleton.equivalence J) F

/-- Universe lifting lets the same preorder hypothesis apply to small
finite thin indexing categories. -/
theorem preservesFiniteThinLimitsOfShape (h : PreservesPreorderLimits.{u} F)
    (J : Type) [SmallCategory J] [Quiver.IsThin J] : PreservesLimitsOfShape J F := by
  have : Quiver.IsThin (AsSmall.{u} J) := fun X Y => by
    change Subsingleton (ULift (ULift.down X ⟶ ULift.down Y))
    infer_instance
  have : PreservesLimitsOfShape (AsSmall.{u} J) F :=
    preservesThinLimitsOfShape F h (AsSmall.{u} J)
  exact preservesLimitsOfShape_of_equiv (AsSmall.equiv (C := J)).symm F

/-- Products, terminal objects, and pullbacks are preorder-indexed limits;
together they force preservation of all small limits. -/
theorem preservesLimits_iff_preorderLimits [HasFiniteLimits C] [HasProducts.{u} C] :
    PreservesLimitsOfSize.{u, u} F ↔ PreservesPreorderLimits.{u} F := by
  constructor
  · intro h J hJ
    infer_instance
  · intro h
    have : PreservesLimitsOfShape (Discrete.{0} PEmpty) F :=
      preservesFiniteThinLimitsOfShape F h _
    have : PreservesLimitsOfShape WalkingCospan F := preservesFiniteThinLimitsOfShape F h _
    have : PreservesFiniteLimits F := preservesFiniteLimits_of_preservesTerminal_and_pullbacks F
    have (J : Type u) : PreservesLimitsOfShape (Discrete J) F :=
      preservesThinLimitsOfShape F h _
    exact preservesLimits_of_preservesEqualizers_and_products F

end General

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (A : (ModuleCat.{u} R)ᵒᵖ ⥤ AddCommGrpCat.{u}) [A.Additive]

/-- IV.1.2 in its literal preorder-indexed form, for the original functor. -/
theorem additiveModuleEvaluation_isIso_iff_preorderLimits :
    IsIso (additiveModuleEvaluationNatTrans A) ↔ PreservesPreorderLimits.{u} A :=
  (additiveModuleEvaluation_isIso_iff A).trans (preservesLimits_iff_preorderLimits A)

/-- The original functor is representable precisely when it commutes with
arbitrary projective limits over preordered sets, not necessarily filtered. -/
theorem additiveModule_representable_iff_preorderLimits :
    (∃ H : ModuleCat.{u} R,
      Nonempty (A ≅ (linearYoneda R (ModuleCat R)).obj H ⋙
        forget₂ (ModuleCat R) AddCommGrpCat)) ↔ PreservesPreorderLimits.{u} A :=
  (additiveModule_representable_iff A).trans (preservesLimits_iff_preorderLimits A)

end SGA.SGA2.ExposeIV
