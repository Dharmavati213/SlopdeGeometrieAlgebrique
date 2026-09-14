/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorDual

/-!
# Naturality of the original twice-iterated functor

The original canonical bidual map is natural in every actual finite
supported module map. Its comparison with genuine double Hom is the
componentwise comparison already used to define it, not a replacement.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

/-- Right opposition of an actual natural isomorphism. -/
def naturalIsoRightOp {C D : Type*} [Category* C] [Category* D]
    {L U : Cᵒᵖ ⥤ D} (e : L ≅ U) : U.rightOp ≅ L.rightOp where
  hom := e.hom.rightOp
  inv := e.inv.rightOp
  hom_inv_id := by
    ext M
    apply Quiver.Hom.unop_inj
    exact e.inv_hom_id_app (op M)
  inv_hom_id := by
    ext M
    apply Quiver.Hom.unop_inj
    exact e.hom_inv_id_app (op M)

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u})
    [T.Additive] [PreservesFiniteLimits T]

/-- The original twice-iterated functor has its actual natural double Hom comparison. -/
def supportedFunctorBidualComparison (hfin : SupportedFunctorFiniteValues J T) :
    supportedFunctorBidual J T hfin ⋙ supportedFiniteToModule J ≅
      supportedFiniteToModule J ⋙ moduleHomBidual (supportedFunctorColimit J T) :=
  isoWhiskerLeft (supportedFunctorDual J T hfin).rightOp (supportedFunctorRepresentationIso J T) ≪≫
    (isoWhiskerRight (naturalIsoRightOp (supportedFunctorRepresentationIso J T))
      (moduleHomDual (supportedFunctorColimit J T))).symm

/-- This is the existing component comparison used by the original canonical map. -/
theorem supportedFunctorBidualComparison_app (hfin : SupportedFunctorFiniteValues J T)
    (M : SupportedFGModuleCat J) :
    (supportedFunctorBidualComparison J T hfin).app M =
      supportedFunctorBidualIsoHom J T hfin M := rfl

/-- The already defined original canonical maps assemble naturally. -/
def supportedFunctorBidualEvaluationNatTrans (hfin : SupportedFunctorFiniteValues J T) :
    supportedFiniteToModule J ⟶ supportedFunctorBidual J T hfin ⋙ supportedFiniteToModule J :=
  whiskerLeft (supportedFiniteToModule J)
    (moduleBidualEvaluationNatTrans (supportedFunctorColimit J T)) ≫
      (supportedFunctorBidualComparison J T hfin).inv

theorem supportedFunctorBidualEvaluationNatTrans_app
    (hfin : SupportedFunctorFiniteValues J T) (M : SupportedFGModuleCat J) :
    (supportedFunctorBidualEvaluationNatTrans J T hfin).app M =
      supportedFunctorBidualEvaluation J T hfin M := rfl

/-- Naturality uses the actual original morphism and twice-iterated functor. -/
@[reassoc]
theorem supportedFunctorBidualEvaluation_naturality
    (hfin : SupportedFunctorFiniteValues J T) {M N : SupportedFGModuleCat J} (f : M ⟶ N) :
    f.hom.hom ≫ supportedFunctorBidualEvaluation J T hfin N =
      supportedFunctorBidualEvaluation J T hfin M ≫
        ((supportedFunctorBidual J T hfin).map f).hom.hom :=
  (supportedFunctorBidualEvaluationNatTrans J T hfin).naturality f

end SGA.SGA2.ExposeIV
