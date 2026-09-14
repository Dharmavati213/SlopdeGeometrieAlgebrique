/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.FiniteLengthModuleCategory
import SGA.SGA2.ExposeIV.SupportedArtinianDuality

/-!
# IV.4.2: actual linear Hom duality on finite-length modules

An injective coefficient satisfying all residue-field tests gives a genuine
contravariant linear endofunctor. Its canonical natural bidual evaluation
is the literal map `x ↦ (f ↦ f x)`, not a chosen objectwise involution.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable (H : ModuleCat.{u} R) [Injective H]
variable (hres : moduleHomDualResidueTests (⊥ : Ideal R) H)

include hres

/-- Residue-field tests force the actual Hom value to have finite length. -/
theorem finiteLengthHom_length (M : FiniteLengthModuleCat R) :
    Module.length R ((moduleHomDual H).obj (op M.obj)) = Module.length R M.obj :=
  moduleHomDual_length_finiteLength_of_residueTests ⊥ H hres M.obj M.property
    (by intro p _; change (⊥ : Ideal R) ≤ p.asIdeal; exact bot_le)

/-- The actual contravariant Hom endofunctor of the original finite-length category. -/
def finiteLengthHomDual : (FiniteLengthModuleCat R)ᵒᵖ ⥤ FiniteLengthModuleCat R where
  obj M := ⟨(moduleHomDual H).obj (op M.unop.obj), by
    apply Module.length_ne_top_iff.mp
    rw [finiteLengthHom_length H hres M.unop]
    exact Module.length_ne_top_iff.mpr M.unop.property⟩
  map f := ObjectProperty.homMk ((moduleHomDual H).map f.unop.hom.op)
  map_id M := by apply ObjectProperty.hom_ext; exact (moduleHomDual H).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; ext x; rfl

instance : (finiteLengthHomDual H hres).Additive where
  map_add {X Y f g} := by
    apply ObjectProperty.hom_ext
    exact (moduleHomDual H).map_add (f := f.unop.hom.op) (g := g.unop.hom.op)

instance : (finiteLengthHomDual H hres).Linear R where
  map_smul f r := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact g.hom.map_smul r (f.unop.hom.hom x)

/-- The actual twice-iterated Hom functor. -/
def finiteLengthHomBidual : FiniteLengthModuleCat R ⥤ FiniteLengthModuleCat R :=
  (finiteLengthHomDual H hres).rightOp ⋙ finiteLengthHomDual H hres

/-- Canonical evaluation as a natural transformation in the genuine category. -/
def finiteLengthHomEvaluation : 𝟭 (FiniteLengthModuleCat R) ⟶ finiteLengthHomBidual H hres where
  app M := ObjectProperty.homMk (moduleBidualEvaluation H M.obj)
  naturality {_ _} f := by
    apply ObjectProperty.hom_ext
    exact moduleBidualEvaluation_naturality H f.hom

@[simp]
theorem finiteLengthHomEvaluation_apply (M : FiniteLengthModuleCat R)
    (x : M.obj) (f : M.obj ⟶ H) :
    ModuleCat.Hom.hom (((finiteLengthHomEvaluation H hres).app M).hom x) f = f.hom x := rfl

/-- All components of the original canonical evaluation are isomorphisms. -/
def finiteLengthHomEvaluationIso : 𝟭 (FiniteLengthModuleCat R) ≅ finiteLengthHomBidual H hres := by
  have (M : FiniteLengthModuleCat R) : IsIso ((finiteLengthHomEvaluation H hres).app M) := by
    have : IsIso ((finiteLengthInclusion R).map ((finiteLengthHomEvaluation H hres).app M)) :=
      moduleBidualEvaluation_isIso_finiteLength_of_residueTests ⊥ H hres M.obj M.property
        (by intro p _; change (⊥ : Ideal R) ≤ p.asIdeal; exact bot_le)
    exact isIso_of_reflects_iso _ (finiteLengthInclusion R)
  exact NatIso.ofComponents (fun M => asIso ((finiteLengthHomEvaluation H hres).app M))
    (fun f => (finiteLengthHomEvaluation H hres).naturality f)

/-- A genuine anti-equivalence with the original Hom functor in both directions.
Its counit is inverse canonical evaluation; standard adjointification supplies
the coherent unit without changing either functor. -/
def finiteLengthHomAntiEquivalence : (FiniteLengthModuleCat R)ᵒᵖ ≌ FiniteLengthModuleCat R :=
  CategoryTheory.Equivalence.mk (finiteLengthHomDual H hres) (finiteLengthHomDual H hres).rightOp
    (NatIso.op (finiteLengthHomEvaluationIso H hres)).symm
    (finiteLengthHomEvaluationIso H hres).symm

instance : (finiteLengthHomDual H hres).PreservesHomology := by
  change (finiteLengthHomAntiEquivalence H hres).functor.PreservesHomology
  infer_instance

instance : PreservesFiniteLimits (finiteLengthHomDual H hres) := by
  change PreservesFiniteLimits (finiteLengthHomAntiEquivalence H hres).functor
  infer_instance

instance : PreservesFiniteColimits (finiteLengthHomDual H hres) := by
  change PreservesFiniteColimits (finiteLengthHomAntiEquivalence H hres).functor
  infer_instance

/-- Every original short exact sequence remains short exact under the dual. -/
theorem finiteLengthHomDual_shortExact {S : ShortComplex (FiniteLengthModuleCat R)}
    (hS : S.ShortExact) : (S.op.map (finiteLengthHomDual H hres)).ShortExact :=
  hS.op.map_of_exact (finiteLengthHomDual H hres)

end SGA.SGA2.ExposeIV
