/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorDuality

/-!
# SGA 2, IV §5: the original dual functor is an anti-equivalence

The functor and inverse are the original finite-valued dual and its right
opposite. The actual canonical bidual evaluation supplies both inverse
comparisons. Standard adjointification makes the unit coherent while leaving
these two functors and the canonical inverse-evaluation counit unchanged.
No abstract equivalence or replacement dual functor is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

section LeftExact

variable [PreservesFiniteLimits T]

/-- The already defined canonical bidual map, now as an actual morphism
in the original full category of finite supported modules. -/
def supportedFunctorBidualUnit (hfin : SupportedFunctorFiniteValues J T) :
    𝟭 (SupportedFGModuleCat J) ⟶ supportedFunctorBidual J T hfin where
  app M := ObjectProperty.homMk (ObjectProperty.homMk
    (supportedFunctorBidualEvaluation J T hfin M))
  naturality {_ _} f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact supportedFunctorBidualEvaluation_naturality J T hfin f

@[simp]
theorem supportedFunctorBidualUnit_app (hfin : SupportedFunctorFiniteValues J T)
    (M : SupportedFGModuleCat J) :
    ((supportedFunctorBidualUnit J T hfin).app M).hom.hom =
      supportedFunctorBidualEvaluation J T hfin M := rfl

/-- The actual canonical bidual natural isomorphism inside the original
finite supported category. -/
def supportedFunctorBidualUnitIso (hfin : SupportedFunctorFiniteValues J T)
    (href : ∀ M : SupportedFGModuleCat J,
      IsIso (supportedFunctorBidualEvaluation J T hfin M)) :
    𝟭 (SupportedFGModuleCat J) ≅ supportedFunctorBidual J T hfin := by
  have hfull : (supportedFiniteToModule J).Full := by
    unfold supportedFiniteToModule
    infer_instance
  have (M : SupportedFGModuleCat J) : IsIso ((supportedFunctorBidualUnit J T hfin).app M) := by
    have : IsIso ((supportedFiniteToModule J).map
        ((supportedFunctorBidualUnit J T hfin).app M)) := href M
    exact isIso_of_reflects_iso _ (supportedFiniteToModule J)
  exact NatIso.ofComponents (fun M ↦ asIso ((supportedFunctorBidualUnit J T hfin).app M))
    (fun f ↦ (supportedFunctorBidualUnit J T hfin).naturality f)

/-- The anti-equivalence uses the actual original dual in both directions.
Its counit is inverse canonical evaluation; its unit is obtained from the
opposite inverse comparison by standard adjointification. -/
def supportedFunctorAntiEquivalenceOfReflexive (hfin : SupportedFunctorFiniteValues J T)
    (href : ∀ M : SupportedFGModuleCat J,
      IsIso (supportedFunctorBidualEvaluation J T hfin M)) :
    (SupportedFGModuleCat J)ᵒᵖ ≌ SupportedFGModuleCat J :=
  CategoryTheory.Equivalence.mk
    (supportedFunctorDual J T hfin) (supportedFunctorDual J T hfin).rightOp
    (NatIso.op (supportedFunctorBidualUnitIso J T hfin href)).symm
    (supportedFunctorBidualUnitIso J T hfin href).symm

@[simp]
theorem supportedFunctorAntiEquivalenceOfReflexive_functor
    (hfin : SupportedFunctorFiniteValues J T)
    (href : ∀ M : SupportedFGModuleCat J,
      IsIso (supportedFunctorBidualEvaluation J T hfin M)) :
    (supportedFunctorAntiEquivalenceOfReflexive J T hfin href).functor =
      supportedFunctorDual J T hfin := rfl

@[simp]
theorem supportedFunctorAntiEquivalenceOfReflexive_inverse
    (hfin : SupportedFunctorFiniteValues J T)
    (href : ∀ M : SupportedFGModuleCat J,
      IsIso (supportedFunctorBidualEvaluation J T hfin M)) :
    (supportedFunctorAntiEquivalenceOfReflexive J T hfin href).inverse =
      (supportedFunctorDual J T hfin).rightOp := rfl

/-- The inverse of the counit remains exactly the original canonical
evaluation; adjointification does not change it. -/
@[simp]
theorem supportedFunctorAntiEquivalenceOfReflexive_counitInv
    (hfin : SupportedFunctorFiniteValues J T)
    (href : ∀ M : SupportedFGModuleCat J,
      IsIso (supportedFunctorBidualEvaluation J T hfin M))
    (M : SupportedFGModuleCat J) :
    ((supportedFunctorAntiEquivalenceOfReflexive J T hfin href).counitInv.app M).hom.hom =
      supportedFunctorBidualEvaluation J T hfin M := rfl

end LeftExact

/-- Left exactness is extracted from the actual duality condition. -/
theorem supportedFunctorDuality_leftExact (h : SupportedFunctorDuality J T) :
    PreservesFiniteLimits T := h.choose

/-- Finiteness of the original values is extracted from duality, not imposed
as a separate parameter of the final anti-equivalence. -/
theorem supportedFunctorDuality_finiteValues (h : SupportedFunctorDuality J T) :
    SupportedFunctorFiniteValues J T := by
  obtain ⟨hleft, href⟩ := h
  let := hleft
  exact href.choose

/-- Every canonical component is invertible, for any proof of the original
finiteness condition; proof choices do not change the actual dual functor. -/
theorem supportedFunctorDuality_bidually_reflexive (h : SupportedFunctorDuality J T)
    [PreservesFiniteLimits T] (hfin : SupportedFunctorFiniteValues J T)
    (M : SupportedFGModuleCat J) : IsIso (supportedFunctorBidualEvaluation J T hfin M) := by
  obtain ⟨hleft, hfin', href⟩ := h
  exact href M

/-- **SGA 2, IV §5, opening:** the unchanged original dual functor is an
anti-equivalence of the actual category of finite supported modules. -/
def supportedFunctorAntiEquivalence (h : SupportedFunctorDuality J T) :
    (SupportedFGModuleCat J)ᵒᵖ ≌ SupportedFGModuleCat J :=
  let := supportedFunctorDuality_leftExact J T h
  supportedFunctorAntiEquivalenceOfReflexive J T
    (supportedFunctorDuality_finiteValues J T h)
    (supportedFunctorDuality_bidually_reflexive J T h _)

/-- The forward functor is the actual original finite-valued factorization. -/
@[simp]
theorem supportedFunctorAntiEquivalence_functor (h : SupportedFunctorDuality J T) :
    (supportedFunctorAntiEquivalence J T h).functor =
      supportedFunctorDual J T (supportedFunctorDuality_finiteValues J T h) := rfl

/-- The inverse is the same actual dual with its variance reversed. -/
@[simp]
theorem supportedFunctorAntiEquivalence_inverse (h : SupportedFunctorDuality J T) :
    (supportedFunctorAntiEquivalence J T h).inverse =
      (supportedFunctorDual J T (supportedFunctorDuality_finiteValues J T h)).rightOp := rfl

/-- The actual morphism action, after forgetting scalar and support structure,
is exactly the original abelian-group-valued functor action. -/
@[simp]
theorem supportedFunctorAntiEquivalence_map (h : SupportedFunctorDuality J T)
    {M N : (SupportedFGModuleCat J)ᵒᵖ} (f : M ⟶ N) :
    (forget₂ (ModuleCat R) AddCommGrpCat).map
      (((supportedFunctorAntiEquivalence J T h).functor.map f).hom.hom) = T.map f := rfl

/-- The constructed unit and counit satisfy the first triangle identity. -/
theorem supportedFunctorAntiEquivalence_unit_counit (h : SupportedFunctorDuality J T)
    (M : (SupportedFGModuleCat J)ᵒᵖ) :
    (supportedFunctorAntiEquivalence J T h).functor.map
        ((supportedFunctorAntiEquivalence J T h).unit.app M) ≫
      (supportedFunctorAntiEquivalence J T h).counit.app
        ((supportedFunctorAntiEquivalence J T h).functor.obj M) = 𝟙 _ :=
  (supportedFunctorAntiEquivalence J T h).functor_unit_comp M

/-- The second triangle identity holds on every actual finite supported module. -/
theorem supportedFunctorAntiEquivalence_counit_unit (h : SupportedFunctorDuality J T)
    (M : SupportedFGModuleCat J) :
    (supportedFunctorAntiEquivalence J T h).unit.app
        ((supportedFunctorAntiEquivalence J T h).inverse.obj M) ≫
      (supportedFunctorAntiEquivalence J T h).inverse.map
        ((supportedFunctorAntiEquivalence J T h).counit.app M) = 𝟙 _ :=
  (supportedFunctorAntiEquivalence J T h).unit_inverse_comp M

end SGA.SGA2.ExposeIV
