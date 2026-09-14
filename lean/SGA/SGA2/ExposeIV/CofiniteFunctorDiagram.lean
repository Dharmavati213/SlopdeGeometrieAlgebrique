/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.CofiniteIdeals
import SGA.SGA2.ExposeIV.AdditiveFunctorModules

/-!
# Canonical module-valued stages indexed by cofinite ideals

For an original additive contravariant functor on finite-length modules,
the actual groups `T(R/I)` carry their source-induced scalar actions.  The
original quotient-induced transitions are linear for these actions, and
forgetting them recovers the original cofinite-ideal diagram.  Each stage
is annihilated by its indexing ideal.  Left exactness makes the actual
transitions monic and injective.

These statements hold over every commutative ring; neither a representation
of the functor nor finite generation of its values is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]
variable (T : (FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

set_option backward.isDefEq.respectTransparency false

/-- The actual additive functor value with its original source-induced action. -/
abbrev finiteLengthFunctorValue (M : FiniteLengthModuleCat R) : ModuleCat.{u} R :=
  (additiveFunctorModuleLift (R := R) T).obj (op M)

/-- Scalar endomorphisms annihilating the source also annihilate its actual
functor value. -/
theorem finiteLengthFunctorValue_annihilator (M : FiniteLengthModuleCat R) :
    Module.annihilator R M.obj ≤ Module.annihilator R (finiteLengthFunctorValue T M) := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  change T.map (r • 𝟙 (op M)) x = 0
  have hs : r • 𝟙 M = 0 := by
    apply ObjectProperty.hom_ext
    ext y
    exact Module.mem_annihilator.mp hr y
  have hop : r • 𝟙 (op M) = 0 := by
    apply Quiver.Hom.unop_inj
    exact hs
  rw [hop, T.map_zero]
  rfl

/-- The original group `T(R/I)` with its canonical `R`-module structure. -/
def cofiniteFunctorStage (I : CofiniteIdealIndex R) : ModuleCat.{u} R :=
  finiteLengthFunctorValue T (cofiniteRingQuotient I)

/-- The actual transition is the image of the original quotient map. -/
def cofiniteFunctorTransition {I J : CofiniteIdealIndex R} (h : I ≤ J) :
    cofiniteFunctorStage T I ⟶ cofiniteFunctorStage T J :=
  (additiveFunctorModuleLift (R := R) T).map (cofiniteRingQuotientMap h).op

@[simp]
theorem cofiniteFunctorTransition_apply {I J : CofiniteIdealIndex R} (h : I ≤ J)
    (x : cofiniteFunctorStage T I) :
    cofiniteFunctorTransition T h x = T.map (cofiniteRingQuotientMap h).op x := rfl

/-- The genuine filtered diagram with the canonical module structures. -/
def cofiniteFunctorModuleDiagram : CofiniteIdealIndex R ⥤ ModuleCat.{u} R :=
  cofiniteFunctorDiagram (additiveFunctorModuleLift (R := R) T)

@[simp]
theorem cofiniteFunctorModuleDiagram_obj (I : CofiniteIdealIndex R) :
    (cofiniteFunctorModuleDiagram T).obj I = cofiniteFunctorStage T I := rfl

@[simp]
theorem cofiniteFunctorModuleDiagram_map {I J : CofiniteIdealIndex R} (f : I ⟶ J) :
    (cofiniteFunctorModuleDiagram T).map f = cofiniteFunctorTransition T (leOfHom f) := rfl

/-- Forgetting the canonical scalar actions recovers the original cofinite
diagram, including its original quotient-induced transitions. -/
def cofiniteFunctorModuleDiagramForgetIso :
    cofiniteFunctorModuleDiagram T ⋙ forget₂ (ModuleCat R) AddCommGrpCat ≅
      cofiniteFunctorDiagram T :=
  Functor.associator (cofiniteRingQuotientDiagram R).rightOp
      (additiveFunctorModuleLift (R := R) T) (forget₂ (ModuleCat R) AddCommGrpCat) ≪≫
    Functor.isoWhiskerLeft (cofiniteRingQuotientDiagram R).rightOp
      (additiveFunctorModuleLiftForgetIso (R := R) T)

@[simp]
theorem cofiniteFunctorModuleDiagramForgetIso_hom_app_apply (I : CofiniteIdealIndex R)
    (x : cofiniteFunctorStage T I) :
    (cofiniteFunctorModuleDiagramForgetIso T).hom.app I x = x := rfl

@[simp]
theorem cofiniteFunctorModuleDiagramForgetIso_inv_app_apply (I : CofiniteIdealIndex R)
    (x : (cofiniteFunctorDiagram T).obj I) :
    (cofiniteFunctorModuleDiagramForgetIso T).inv.app I x = x := rfl

/-- Its scalar action is exactly the image of scalar multiplication on `R/I`. -/
theorem cofiniteFunctorStage_smul (I : CofiniteIdealIndex R) (r : R)
    (x : cofiniteFunctorStage T I) :
    r • x = T.map (r • 𝟙 (op (cofiniteRingQuotient I))) x := rfl

/-- Each original stage is annihilated by the literal indexing ideal. -/
theorem cofiniteFunctorStage_annihilator (I : CofiniteIdealIndex R) :
    I.val ≤ Module.annihilator R (cofiniteFunctorStage T I) := by
  have h := finiteLengthFunctorValue_annihilator T (cofiniteRingQuotient I)
  change Module.annihilator R (R ⧸ I.val) ≤
    Module.annihilator R (cofiniteFunctorStage T I) at h
  rwa [Ideal.annihilator_quotient] at h

/-- In particular, every scalar from the indexing ideal kills every stage element. -/
theorem cofiniteFunctorStage_smul_eq_zero (I : CofiniteIdealIndex R)
    {r : R} (hr : r ∈ I.val) (x : cofiniteFunctorStage T I) : r • x = 0 :=
  Module.mem_annihilator.mp (cofiniteFunctorStage_annihilator T I hr) x

/-- Left exactness makes the original linear transitions monomorphisms. -/
instance cofiniteFunctorTransition_mono [PreservesFiniteLimits T]
    {I J : CofiniteIdealIndex R} (h : I ≤ J) : Mono (cofiniteFunctorTransition T h) := by
  apply (forget₂ (ModuleCat R) AddCommGrpCat).mono_of_mono_map
  change Mono (T.map (cofiniteRingQuotientMap h).op)
  infer_instance

/-- These are literal injective functions on the original functor values. -/
theorem cofiniteFunctorTransition_injective [PreservesFiniteLimits T]
    {I J : CofiniteIdealIndex R} (h : I ≤ J) :
    Function.Injective (cofiniteFunctorTransition T h) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

instance cofiniteFunctorModuleDiagram_map_mono [PreservesFiniteLimits T]
    {I J : CofiniteIdealIndex R} (f : I ⟶ J) : Mono ((cofiniteFunctorModuleDiagram T).map f) := by
  rw [cofiniteFunctorModuleDiagram_map]
  infer_instance

end SGA.SGA2.ExposeIV
