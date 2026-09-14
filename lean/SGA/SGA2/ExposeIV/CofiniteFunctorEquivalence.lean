/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.CofiniteFunctorRepresentation
import SGA.SGA2.ExposeIV.FiniteLengthRestrictedHom

/-!
# Nonlocal locally Artinian modules and finite-length functors

Original restricted Hom is an equivalence between locally Artinian modules
and additive left-exact contravariant functors on finite-length modules over
a noetherian ring. Full faithfulness uses actual finite submodules; essential
surjectivity uses the original cofinite-ideal colimit and its canonical
evaluation, not a supplied representing object.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The original additive left-exact functors on finite-length modules. -/
def leftExactFiniteLengthFunctorProperty :
    ObjectProperty ((FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  fun T ↦ T.Additive ∧ PreservesFiniteLimits T

abbrev LeftExactFiniteLengthFunctor (R : Type u) [CommRing R] :=
  (leftExactFiniteLengthFunctorProperty (R := R)).FullSubcategory

/-- Actual Hom, retaining the proved additivity and left exactness. -/
def locallyArtinianToLeftExactFunctor :
    LocallyArtinianModuleCat R ⥤ LeftExactFiniteLengthFunctor R :=
  (leftExactFiniteLengthFunctorProperty (R := R)).lift locallyArtinianRestrictedHom (fun H ↦ by
    change (finiteLengthModuleHomFunctor H.obj ⋙ forget₂ (ModuleCat R) AddCommGrpCat).Additive ∧
      PreservesFiniteLimits
        (finiteLengthModuleHomFunctor H.obj ⋙ forget₂ (ModuleCat R) AddCommGrpCat)
    exact ⟨inferInstance, comp_preservesFiniteLimits _ _⟩)

/-- Recording these properties leaves actual restricted Hom fully faithful. -/
def locallyArtinianToLeftExactFunctorFullyFaithful :
    (locallyArtinianToLeftExactFunctor (R := R)).FullyFaithful where
  preimage α := (locallyArtinianRestrictedHomFullyFaithful (R := R)).preimage α.hom
  map_preimage α := ObjectProperty.hom_ext _
    ((locallyArtinianRestrictedHomFullyFaithful (R := R)).map_preimage α.hom)
  preimage_map f := (locallyArtinianRestrictedHomFullyFaithful (R := R)).preimage_map f

instance : (locallyArtinianToLeftExactFunctor (R := R)).Full :=
  (locallyArtinianToLeftExactFunctorFullyFaithful (R := R)).full

instance : (locallyArtinianToLeftExactFunctor (R := R)).Faithful :=
  (locallyArtinianToLeftExactFunctorFullyFaithful (R := R)).faithful

instance : (locallyArtinianToLeftExactFunctor (R := R)).EssSurj where
  mem_essImage T := by
    have : T.obj.Additive := T.property.1
    have : PreservesFiniteLimits T.obj := T.property.2
    refine ⟨⟨cofiniteFunctorColimit T.obj, cofiniteFunctorColimit_locallyArtinian T.obj⟩, ?_⟩
    exact ⟨ObjectProperty.isoMk _ (additiveCofiniteFunctorRepresentationIso T.obj).symm⟩

instance : (locallyArtinianToLeftExactFunctor (R := R)).IsEquivalence where

/-- **IV.4.2, nonlocal representation equivalence.** Actual locally Artinian
modules correspond to original additive left-exact finite-length functors. -/
def locallyArtinianFiniteLengthFunctorEquivalence :
    LocallyArtinianModuleCat R ≌ LeftExactFiniteLengthFunctor R :=
  (locallyArtinianToLeftExactFunctor (R := R)).asEquivalence

@[simp]
theorem locallyArtinianFiniteLengthFunctorEquivalence_functor :
    (locallyArtinianFiniteLengthFunctorEquivalence (R := R)).functor =
      locallyArtinianToLeftExactFunctor := rfl

end SGA.SGA2.ExposeIV
