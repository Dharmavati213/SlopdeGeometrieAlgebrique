/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorExactness
import SGA.SGA2.ExposeIV.ModuleBidual
import SGA.SGA2.ExposeIV.AdditiveFunctorModuleNaturality

/-!
# The original functor's actual dual and bidual

Every value of the original supported additive functor has its original
support, for its canonically induced module structure. If these values
are finite, the original functor really factors through finite supported
modules. Its twice-iterated functor and canonical bidual map are then
constructed from the specified IV.1.3 evaluation, as in IV.3.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Functor
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- The original functor value, with its induced scalar action. -/
abbrev supportedFunctorValue (M : SupportedFGModuleCat J) : ModuleCat.{u} R :=
  (additiveFunctorModuleLift (R := R) T).obj (op M)

omit [IsNoetherianRing R] in
/-- Annihilators grow under the canonical additive contravariant functor. -/
theorem supportedFunctorValue_annihilator (M : SupportedFGModuleCat J) :
    Module.annihilator R M.obj ≤ Module.annihilator R (supportedFunctorValue J T M) := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  change T.map (r • 𝟙 (op M)) x = 0
  have hs : r • 𝟙 M = 0 := by
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    ext y
    exact Module.mem_annihilator.mp hr y
  have hop : r • 𝟙 (op M) = 0 := by
    apply Quiver.Hom.unop_inj
    exact hs
  rw [hop, T.map_zero]
  rfl

/-- Support is proved before imposing finite values or left exactness. -/
theorem supportedFunctorValue_support (M : SupportedFGModuleCat J) :
    supportedModuleProperty J (supportedFunctorValue J T M) := by
  apply support_subset_zeroLocus_of_powerTorsion_eq_top
  apply top_unique
  intro x _
  obtain ⟨n, hn⟩ := supportedFinite_exists_pow_annihilator J M
  exact (mem_powerTorsion_iff J _ x).mpr
    ⟨n, fun r hr => Module.mem_annihilator.mp
      (supportedFunctorValue_annihilator J T M (hn hr)) x⟩

/-- Finiteness in IV.3 means finiteness of the original, canonically
structured values, not of a replacement functor. -/
def SupportedFunctorFiniteValues : Prop :=
  ∀ M : SupportedFGModuleCat J, Module.Finite R (supportedFunctorValue J T M)

/-- The original restricted linear Hom is linear for the source scalar action. -/
instance supportedModuleHomFunctor_linear (H : ModuleCat.{u} R) :
    (supportedModuleHomFunctor J H).Linear R where
  map_smul f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact g.hom.map_smul r (f.unop.hom.hom x)

/-- The original functor genuinely takes values in finite supported modules
when its values are finite; support is a theorem, not a second hypothesis. -/
def supportedFunctorDual (hfin : SupportedFunctorFiniteValues J T) :
    (SupportedFGModuleCat J)ᵒᵖ ⥤ SupportedFGModuleCat J where
  obj M := ⟨⟨supportedFunctorValue J T M.unop, hfin M.unop⟩,
    supportedFunctorValue_support J T M.unop⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk
    ((additiveFunctorModuleLift (R := R) T).map f))
  map_id M := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (additiveFunctorModuleLift (R := R) T).map_id M
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (additiveFunctorModuleLift (R := R) T).map_comp f g

/-- Forgetting this factorization is definitionally the original scalar lift. -/
theorem supportedFunctorDual_comp_inclusion (hfin : SupportedFunctorFiniteValues J T) :
    supportedFunctorDual J T hfin ⋙ supportedFiniteToModule J =
      additiveFunctorModuleLift (R := R) T := rfl

instance (hfin : SupportedFunctorFiniteValues J T) : (supportedFunctorDual J T hfin).Additive where
  map_add {M N} f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (additiveFunctorModuleLift (R := R) T).map_add

/-- The actual twice-iterated original functor. -/
def supportedFunctorBidual (hfin : SupportedFunctorFiniteValues J T) :
    SupportedFGModuleCat J ⥤ SupportedFGModuleCat J :=
  (supportedFunctorDual J T hfin).rightOp ⋙ supportedFunctorDual J T hfin

variable [PreservesFiniteLimits T]

/-- The actual `T(T(M))` identifies with genuine double Hom via the
original canonical evaluation isomorphisms of IV.1.3. -/
def supportedFunctorBidualIsoHom (hfin : SupportedFunctorFiniteValues J T)
    (M : SupportedFGModuleCat J) :
    ((supportedFunctorBidual J T hfin).obj M).obj.obj ≅
      (moduleHomBidual (supportedFunctorColimit J T)).obj M.obj.obj :=
  (supportedFunctorRepresentationIso J T).app
      (op ((supportedFunctorDual J T hfin).obj (op M))) ≪≫
    ((moduleHomDual (supportedFunctorColimit J T)).mapIso
      ((supportedFunctorRepresentationIso J T).app (op M)).op).symm

/-- IV.3's canonical map into the twice-iterated original functor. This
is the genuine double Hom evaluation transported by the specified `φ_T`. -/
def supportedFunctorBidualEvaluation (hfin : SupportedFunctorFiniteValues J T)
    (M : SupportedFGModuleCat J) :
    M.obj.obj ⟶ ((supportedFunctorBidual J T hfin).obj M).obj.obj :=
  moduleBidualEvaluation (supportedFunctorColimit J T) M.obj.obj ≫
    (supportedFunctorBidualIsoHom J T hfin M).inv

/-- The comparison identifies the original canonical map, not an arbitrary
isomorphism with the bidual. -/
@[reassoc (attr := simp)]
theorem supportedFunctorBidualEvaluation_comp_iso
    (hfin : SupportedFunctorFiniteValues J T) (M : SupportedFGModuleCat J) :
    supportedFunctorBidualEvaluation J T hfin M ≫
      (supportedFunctorBidualIsoHom J T hfin M).hom =
      moduleBidualEvaluation (supportedFunctorColimit J T) M.obj.obj := by
  simp [supportedFunctorBidualEvaluation]

theorem supportedFunctorBidualEvaluation_isIso_iff
    (hfin : SupportedFunctorFiniteValues J T) (M : SupportedFGModuleCat J) :
    IsIso (supportedFunctorBidualEvaluation J T hfin M) ↔
      IsIso (moduleBidualEvaluation (supportedFunctorColimit J T) M.obj.obj) := by
  constructor
  · intro h
    rw [← supportedFunctorBidualEvaluation_comp_iso J T hfin M]
    infer_instance
  · intro h
    unfold supportedFunctorBidualEvaluation
    infer_instance

/-- Canonical reflexivity and finite values of the original functor. -/
def SupportedFunctorReflexive : Prop :=
  ∃ hfin : SupportedFunctorFiniteValues J T,
    ∀ M : SupportedFGModuleCat J, IsIso (supportedFunctorBidualEvaluation J T hfin M)

end SGA.SGA2.ExposeIV
