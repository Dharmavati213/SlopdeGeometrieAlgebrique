/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.CofiniteFunctorRepresentation
import SGA.SGA2.ExposeIV.NonlocalInjectivityCriterion

/-!
# Exactness of the original nonlocal functor and injectivity of its colimit

For an additive left-exact functor on all finite-length modules over a
noetherian ring, exactness is equivalent to injectivity of its actual
cofinite-ideal colimit among all modules. The comparison uses the original
canonical representation and the proved nonlocal Baer criterion, not an
injectivity assumption or a selected family of test sequences.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

/-- Exactness on every original finite-length short exact sequence. -/
def FiniteLengthFunctorExact (T : (FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u})
    [T.Additive] : Prop :=
  ∀ S : ShortComplex (FiniteLengthModuleCat R), S.ShortExact → (S.op.map T).ShortExact

/-- This is the standard categorical exactness predicate. -/
theorem finiteLengthFunctorExact_iff_preservesHomology
    (T : (FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive] :
    FiniteLengthFunctorExact T ↔ T.PreservesHomology := by
  have h : FiniteLengthFunctorExact T ↔
      ∀ S : ShortComplex (FiniteLengthModuleCat R)ᵒᵖ,
        S.ShortExact → (S.map T).ShortExact := by
    constructor
    · intro h S hS
      exact h S.unop hS.unop
    · intro h S hS
      exact h S.op hS.op
  exact h.trans ((Functor.exact_tfae T).out 1 3)

/-- Original natural isomorphisms preserve the exactness condition. -/
theorem finiteLengthFunctorExact_iff_of_iso
    {T U : (FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    [T.Additive] [U.Additive]
    (e : T ≅ U) : FiniteLengthFunctorExact T ↔ FiniteLengthFunctorExact U := by
  constructor
  · intro h S hS
    exact (ShortComplex.shortExact_iff_of_iso (S.op.mapNatIso e)).mp (h S hS)
  · intro h S hS
    exact (ShortComplex.shortExact_iff_of_iso (S.op.mapNatIso e)).mpr (h S hS)

/-- The original scalar-forgotten Hom is the unchanged finite-length Hom
functor used in the nonlocal injectivity criterion. -/
theorem finiteLengthHomFunctorExact_iff (H : ModuleCat.{u} R) :
    FiniteLengthFunctorExact
      (finiteLengthModuleHomFunctor H ⋙ forget₂ (ModuleCat R) AddCommGrpCat) ↔
      FiniteLengthHomExact H := Iff.rfl

variable [IsNoetherianRing R]
variable (T : (FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u})
  [T.Additive] [PreservesFiniteLimits T]

/-- The original finite-length functor is exact if and only if its actual
cofinite-ideal colimit is injective among all `R`-modules. -/
theorem cofiniteFunctorExact_iff_injective_colimit :
    FiniteLengthFunctorExact T ↔ Injective (cofiniteFunctorColimit T) :=
  (finiteLengthFunctorExact_iff_of_iso (additiveCofiniteFunctorRepresentationIso T)).trans
    ((finiteLengthHomFunctorExact_iff (cofiniteFunctorColimit T)).trans
      (finiteLengthHomExact_iff_injective (cofiniteFunctorColimit T)
        (cofiniteFunctorColimit_locallyArtinian T)))

/-- The same statement with standard categorical exactness and the
unchanged original functor. -/
theorem cofiniteFunctor_preservesHomology_iff_injective_colimit :
    T.PreservesHomology ↔ Injective (cofiniteFunctorColimit T) :=
  (finiteLengthFunctorExact_iff_preservesHomology T).symm.trans
    (cofiniteFunctorExact_iff_injective_colimit T)

end SGA.SGA2.ExposeIV
