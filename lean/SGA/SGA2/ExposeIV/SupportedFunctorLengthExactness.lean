/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorDuality
import SGA.SGA2.ExposeIV.HomDualLengthExactness

/-!
# SGA 2, IV.3.2: length preservation for the original functor

Under the standing left-exactness hypothesis of IV §3, preservation of
length alone implies exactness of the unchanged abelian-group-valued
functor. Its values are not assumed finite: this follows from equality
with the finite lengths of the original supported finite modules.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (J : Ideal R) [IsArtinianRing (R ⧸ J)]
variable (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u})
  [T.Additive] [PreservesFiniteLimits T]

/-- **IV.3.2:** length preservation forces exactness of the original
left-exact functor, with no exactness or finite-value hypothesis added. -/
theorem supportedFunctor_exact_of_length_preserving
    (hlen : SupportedFunctorLengthPreserving J T) : SupportedFunctorExact J T := by
  have : Injective (supportedFunctorColimit J T) :=
    injective_of_supported_length_preserving J (supportedFunctorColimit J T)
      ((supportedFunctor_lengthPreserving_iff_homLength J T).mp hlen)
      (supportedFunctorColimit_support J T)
  exact (supportedFunctorExact_iff_injective_colimit J T).mpr inferInstance

/-- The explicit exactness clause in IV.3.1(iv) is redundant under the
standing left-exactness hypothesis of IV §3. -/
theorem supportedFunctor_exact_and_length_iff_length :
    (SupportedFunctorExact J T ∧ SupportedFunctorLengthPreserving J T) ↔
      SupportedFunctorLengthPreserving J T :=
  ⟨And.right, fun h => ⟨supportedFunctor_exact_of_length_preserving J T h, h⟩⟩

/-- Length preservation alone gives finite values of the actual functor. -/
theorem supportedFunctor_finiteValues_of_length_preserving
    (hlen : SupportedFunctorLengthPreserving J T) : SupportedFunctorFiniteValues J T :=
  (supportedFunctor_finiteValues_iff_homFinite J T).mpr
    (finiteSupportedHomValues_of_length_preserving J (supportedFunctorColimit J T)
      ((supportedFunctor_lengthPreserving_iff_homLength J T).mp hlen))

/-- **IV.3.1 and IV.3.2:** canonical duality is equivalent to preserving
length for the original functor under the standing hypothesis of IV §3. -/
theorem supportedFunctor_duality_iff_length :
    SupportedFunctorDuality J T ↔ SupportedFunctorLengthPreserving J T := by
  constructor
  · intro h
    obtain ⟨hex, hres⟩ := supportedFunctor_exact_residue_of_duality J T h
    exact supportedFunctor_length_of_exact_residue J T hex hres
  · intro hlen
    have hex := supportedFunctor_exact_of_length_preserving J T hlen
    exact supportedFunctor_duality_of_exact_residue J T hex
      (supportedFunctor_residue_of_exact_length J T hex hlen)

end SGA.SGA2.ExposeIV
