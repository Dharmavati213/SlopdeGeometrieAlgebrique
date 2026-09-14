/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorRepresentation
import SGA.SGA2.ExposeIV.SupportedRestrictedHom

/-!
# The supported-module equivalence following IV.1.3

Arbitrary modules whose actual support lies in `V(J)` are equivalent to
additive left-exact contravariant functors on actual finite supported
modules. The forward functor is the original restricted Hom. Essential
surjectivity uses the original colimit and canonical evaluation, not an
assumed representing object.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The actual full subcategory of additive left-exact supported functors. -/
def leftExactSupportedFunctorProperty (J : Ideal R) :
    ObjectProperty ((SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  fun T ↦ T.Additive ∧ PreservesFiniteLimits T

abbrev LeftExactSupportedFunctor (J : Ideal R) :=
  (leftExactSupportedFunctorProperty J).FullSubcategory

/-- Restricted Hom lands in actual additive left-exact functors. -/
def supportedModuleToLeftExactFunctor (J : Ideal R) :
    SupportedModuleCat J ⥤ LeftExactSupportedFunctor J :=
  (leftExactSupportedFunctorProperty J).lift (supportedModuleRestrictedHom J) (fun H ↦ by
    change (supportedModuleHomFunctor J H.obj ⋙ forget₂ (ModuleCat R) AddCommGrpCat).Additive ∧
      PreservesFiniteLimits
        (supportedModuleHomFunctor J H.obj ⋙ forget₂ (ModuleCat R) AddCommGrpCat)
    exact ⟨inferInstance, comp_preservesFiniteLimits _ _⟩)

/-- Recording left exactness does not change the already-proved full faithfulness. -/
def supportedModuleToLeftExactFunctorFullyFaithful (J : Ideal R) :
    (supportedModuleToLeftExactFunctor J).FullyFaithful where
  preimage α := (supportedModuleRestrictedHomFullyFaithful J).preimage α.hom
  map_preimage α := ObjectProperty.hom_ext _
    ((supportedModuleRestrictedHomFullyFaithful J).map_preimage α.hom)
  preimage_map f := (supportedModuleRestrictedHomFullyFaithful J).preimage_map f

instance (J : Ideal R) : (supportedModuleToLeftExactFunctor J).Full :=
  (supportedModuleToLeftExactFunctorFullyFaithful J).full

instance (J : Ideal R) : (supportedModuleToLeftExactFunctor J).Faithful :=
  (supportedModuleToLeftExactFunctorFullyFaithful J).faithful

instance (J : Ideal R) : (supportedModuleToLeftExactFunctor J).EssSurj where
  mem_essImage T := by
    have : T.obj.Additive := T.property.1
    have : PreservesFiniteLimits T.obj := T.property.2
    refine ⟨⟨supportedFunctorColimit J T.obj, supportedFunctorColimit_support J T.obj⟩, ?_⟩
    exact ⟨ObjectProperty.isoMk _ (additiveSupportedFunctorRepresentationIso J T.obj).symm⟩

instance (J : Ideal R) : (supportedModuleToLeftExactFunctor J).IsEquivalence where

/-- **IV.1.3, categorical equivalence:** arbitrary actual supported modules
correspond to additive left-exact functors on finite supported modules. -/
def supportedModuleFunctorEquivalence (J : Ideal R) :
    SupportedModuleCat J ≌ LeftExactSupportedFunctor J :=
  (supportedModuleToLeftExactFunctor J).asEquivalence

@[simp] theorem supportedModuleFunctorEquivalence_functor (J : Ideal R) :
    (supportedModuleFunctorEquivalence J).functor = supportedModuleToLeftExactFunctor J := rfl

end SGA.SGA2.ExposeIV
