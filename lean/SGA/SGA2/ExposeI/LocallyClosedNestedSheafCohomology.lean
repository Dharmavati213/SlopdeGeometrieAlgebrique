/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedNestedSheafSequence
import SGA.SGA2.ExposeI.RightDerivedFunctorSequence
import SGA.SGA2.ExposeI.RightDerivedZeroNaturality

/-!
# I.2.10: the original nested supported-sheaf long exact sequence

This derives the proved original supported-sheaf sequence, which is short
exact on injective coefficients because injectives are flasque. The terms
are the unchanged original ambient derived supported functors. Both ordinary
arrows are their actual derived maps, and the boundary is the genuine
connecting map of the original sequence on an injective resolution.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}
variable (W : LocallyClosedIn X) (T : Closeds (W.ZV : Set W.V))

local instance locallyClosedNestedSheafFunctorSequence_additive₁ :
    (locallyClosedNestedSheafFunctorSequence W T).X₁.Additive :=
  inferInstanceAs
    (underlineGammaLocallyClosedFunctor (nestedClosedSupportWitness W T)).Additive

local instance locallyClosedNestedSheafFunctorSequence_additive₂ :
    (locallyClosedNestedSheafFunctorSequence W T).X₂.Additive :=
  inferInstanceAs (underlineGammaLocallyClosedFunctor W).Additive

local instance locallyClosedNestedSheafFunctorSequence_additive₃ :
    (locallyClosedNestedSheafFunctorSequence W T).X₃.Additive :=
  inferInstanceAs
    (underlineGammaLocallyClosedFunctor (nestedDifferenceSupportWitness W T)).Additive

/-- The exactness hypothesis for deriving is proved on actual injective sheaves. -/
theorem locallyClosedNestedSheafFunctorSequence_injective
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] :
    ((locallyClosedNestedSheafFunctorSequence W T).map
      ((evaluation (Sheaf AddCommGrpCat.{u} X) (Sheaf AddCommGrpCat.{u} X)).obj F)).ShortExact := by
  have : IsFlasque F := isFlasque_of_injective F
  exact locallyClosedNestedSheafSequence_shortExact W T F

/-- The actual support-increasing map on original derived supported sheaves. -/
def locallyClosedNestedDerivedSheafInclusion (n : ℕ) :
    derivedUnderlineGammaLocallyClosed (nestedClosedSupportWitness W T) n ⟶
      derivedUnderlineGammaLocallyClosed W n :=
  (locallyClosedNestedSheafInclusion W T).rightDerived n

/-- Actual derived restriction to the locally closed difference. -/
def locallyClosedNestedDerivedSheafRestriction (n : ℕ) :
    derivedUnderlineGammaLocallyClosed W n ⟶
      derivedUnderlineGammaLocallyClosed (nestedDifferenceSupportWitness W T) n :=
  (locallyClosedNestedSheafRestriction W T).rightDerived n

/-- The zeroth derived inclusion is the original supported-sheaf inclusion
under the original degree-zero comparisons. -/
@[reassoc]
theorem locallyClosedNestedDerivedSheafInclusion_zero
    (F : Sheaf AddCommGrpCat.{u} X) :
    (locallyClosedNestedDerivedSheafInclusion W T 0).app F ≫
        (derivedUnderlineGammaLocallyClosedZeroIso W).hom.app F =
      (derivedUnderlineGammaLocallyClosedZeroIso
        (nestedClosedSupportWitness W T)).hom.app F ≫
          (locallyClosedNestedSheafInclusion W T).app F :=
  rightDerivedZeroIsoSelf_natTrans (locallyClosedNestedSheafInclusion W T) F

/-- The zeroth derived restriction is the original restriction to the
locally closed difference under the original degree-zero comparisons. -/
@[reassoc]
theorem locallyClosedNestedDerivedSheafRestriction_zero
    (F : Sheaf AddCommGrpCat.{u} X) :
    (locallyClosedNestedDerivedSheafRestriction W T 0).app F ≫
        (derivedUnderlineGammaLocallyClosedZeroIso
          (nestedDifferenceSupportWitness W T)).hom.app F =
      (derivedUnderlineGammaLocallyClosedZeroIso W).hom.app F ≫
        (locallyClosedNestedSheafRestriction W T).app F :=
  rightDerivedZeroIsoSelf_natTrans (locallyClosedNestedSheafRestriction W T) F

/-- **I.2.10:** the actual connecting natural transformation, with no
assumed exact sequence or chosen replacement cohomology functor. -/
def locallyClosedNestedDerivedSheafBoundary (n : ℕ) :
    derivedUnderlineGammaLocallyClosed (nestedDifferenceSupportWitness W T) n ⟶
      derivedUnderlineGammaLocallyClosed (nestedClosedSupportWitness W T) (n + 1) :=
  rightDerivedFunctorBoundary
    (C := Sheaf AddCommGrpCat.{u} X) (D := Sheaf AddCommGrpCat.{u} X)
    (locallyClosedNestedSheafFunctorSequence W T)
    (locallyClosedNestedSheafFunctorSequence_injective W T) n

/-- Six consecutive original supported sheaves in the long exact sequence. -/
def locallyClosedNestedDerivedSheafSequence (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    ComposableArrows (Sheaf AddCommGrpCat.{u} X) 5 :=
  ComposableArrows.mk₅ ((locallyClosedNestedDerivedSheafInclusion W T n).app F)
    ((locallyClosedNestedDerivedSheafRestriction W T n).app F)
    ((locallyClosedNestedDerivedSheafBoundary W T n).app F)
    ((locallyClosedNestedDerivedSheafInclusion W T (n + 1)).app F)
    ((locallyClosedNestedDerivedSheafRestriction W T (n + 1)).app F)

/-- **I.2.10:** the actual original sheaf sequence is exact in all degrees. -/
theorem locallyClosedNestedDerivedSheafSequence_exact
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (locallyClosedNestedDerivedSheafSequence W T F n).Exact :=
  rightDerivedFunctorSequence_exact
    (C := Sheaf AddCommGrpCat.{u} X) (D := Sheaf AddCommGrpCat.{u} X)
    (locallyClosedNestedSheafFunctorSequence W T)
    (locallyClosedNestedSheafFunctorSequence_injective W T) F n

/-- The original degree-zero first arrow is a monomorphism. -/
theorem locallyClosedNestedDerivedSheafInclusion_zero_mono
    (F : Sheaf AddCommGrpCat.{u} X) :
    Mono ((locallyClosedNestedDerivedSheafInclusion W T 0).app F) :=
  rightDerivedFunctorSequence_zero_mono
    (C := Sheaf AddCommGrpCat.{u} X) (D := Sheaf AddCommGrpCat.{u} X)
    (locallyClosedNestedSheafFunctorSequence W T)
    (locallyClosedNestedSheafFunctorSequence_injective W T) F

/-- The actual boundary commutes with every coefficient-sheaf morphism. -/
@[reassoc]
theorem locallyClosedNestedDerivedSheafBoundary_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ) :
    (derivedUnderlineGammaLocallyClosed (nestedDifferenceSupportWitness W T) n).map f ≫
        (locallyClosedNestedDerivedSheafBoundary W T n).app G =
      (locallyClosedNestedDerivedSheafBoundary W T n).app F ≫
        (derivedUnderlineGammaLocallyClosed (nestedClosedSupportWitness W T) (n + 1)).map f :=
  (locallyClosedNestedDerivedSheafBoundary W T n).naturality f

/-- **I.2.10**, with a closed subset of the literal locally closed subspace. -/
theorem nestedClosedSubspaceDerivedSheafSequence_exact (T : Closeds W.asSet)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (locallyClosedNestedDerivedSheafSequence W (nestedClosedSubspace W T) F n).Exact :=
  locallyClosedNestedDerivedSheafSequence_exact W (nestedClosedSubspace W T) F n

end SGA.SGA2.ExposeI
