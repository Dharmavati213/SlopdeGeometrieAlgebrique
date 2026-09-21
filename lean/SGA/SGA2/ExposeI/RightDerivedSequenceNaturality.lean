/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.RightDerivedFunctorSequence

/-!
# Naturality of derived connecting maps in a short complex of functors

A morphism of the original short complexes induces commuting connecting
maps on their actual right-derived functors. Both exactness hypotheses need
only hold on injective objects.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {S T : ShortComplex (C ⥤ D)}
  [S.X₁.Additive] [S.X₂.Additive] [S.X₃.Additive]
  [T.X₁.Additive] [T.X₂.Additive] [T.X₃.Additive]

/-- A morphism of functor sequences acts on their actual resolution complexes. -/
def functorSequenceComplexNatMap (φ : S ⟶ T) (K : CochainComplex C ℕ) :
    functorSequenceComplex S K ⟶ functorSequenceComplex T K where
  τ₁ := (φ.τ₁.mapHomologicalComplex _).app K
  τ₂ := (φ.τ₂.mapHomologicalComplex _).app K
  τ₃ := (φ.τ₃.mapHomologicalComplex _).app K
  comm₁₂ := by
    ext n
    exact congrArg (fun a ↦ a.app (K.X n)) φ.comm₁₂
  comm₂₃ := by
    ext n
    exact congrArg (fun a ↦ a.app (K.X n)) φ.comm₂₃

variable (hS : ∀ (I : C) [Injective I], (S.map ((evaluation C D).obj I)).ShortExact)
  (hT : ∀ (I : C) [Injective I], (T.map ((evaluation C D).obj I)).ShortExact)

/-- The genuine resolution boundaries commute with every morphism of the
original functor short complexes. -/
@[reassoc]
theorem functorSequenceResolutionBoundary_natTrans (φ : S ⟶ T)
    {X : C} (I : InjectiveResolution X) (n : ℕ) :
    functorSequenceResolutionBoundary S hS I n ≫
        homologyMap ((φ.τ₁.mapHomologicalComplex _).app I.cocomplex) (n + 1) =
      homologyMap ((φ.τ₃.mapHomologicalComplex _).app I.cocomplex) n ≫
        functorSequenceResolutionBoundary T hT I n :=
  HomologicalComplex.HomologySequence.δ_naturality (functorSequenceComplexNatMap φ I.cocomplex)
    (functorSequenceComplex_shortExact S hS I)
    (functorSequenceComplex_shortExact T hT I) n (n + 1) (by simp)

variable [HasInjectiveResolutions C]

/-- Connecting maps of actual right-derived functors commute with maps of
the original functor short complexes. -/
@[reassoc]
theorem rightDerivedFunctorBoundary_natTrans (φ : S ⟶ T) (X : C) (n : ℕ) :
    (rightDerivedFunctorBoundary S hS n).app X ≫ (φ.τ₁.rightDerived (n + 1)).app X =
      (φ.τ₃.rightDerived n).app X ≫ (rightDerivedFunctorBoundary T hT n).app X := by
  let I := injectiveResolution X
  apply (cancel_mono (I.isoRightDerivedObj T.X₁ (n + 1)).hom).mp
  rw [Category.assoc, rightDerived_natTrans_comp_resolutionIso,
    ← Category.assoc, rightDerivedFunctorBoundary_comp_resolutionIso,
    Category.assoc, functorSequenceResolutionBoundary_natTrans hS hT,
    ← Category.assoc, ← rightDerived_natTrans_comp_resolutionIso,
    Category.assoc, ← rightDerivedFunctorBoundary_comp_resolutionIso T hT]
  simp only [Category.assoc]
  rfl

end SGA.SGA2.ExposeI
