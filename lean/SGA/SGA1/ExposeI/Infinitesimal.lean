/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeI.Fundamental
import SGA.SGA1.ExposeI.StandardEtale

/-!
# SGA 1, Exposé I, §8: infinitesimal lifting of étale schemes

Theorem I.8.3 says that reducing modulo a nilpotent ideal of definition is an
equivalence on étale schemes. Uniqueness of morphisms is I.5.5
(`FormallyUnramified.hom_ext`), proved in `Fundamental.lean`. Essential
surjectivity is the local existence statement I.8.1: a standard étale
presentation over `A₀ = A / I` lifts by lifting the coefficients of the monic
polynomial, and the resulting algebra is étale by I.7.4. Global gluing of
these local lifts, and the formal-scheme variant I.8.4, remain.
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry CategoryTheory

/-- I.8.3, uniqueness half: morphisms of étale `S`-schemes are determined by
their reductions along a nilpotent closed immersion `S₀ ↪ S`. -/
theorem etale_reduction_hom_unique {S S₀ X : Scheme.{u}} (i : S₀ ⟶ S)
    (hi : IsNilpotent i.ker) [IsClosedImmersion i] {g : X ⟶ S} [Etale g]
    {f₁ f₂ : S ⟶ X} (hf : i ≫ f₁ = i ≫ f₂) (hg : f₁ ≫ g = f₂ ≫ g) : f₁ = f₂ :=
  FormallyUnramified.hom_ext i hi g hf hg

/-- I.7.4 / I.8.1: the standard étale algebra attached to a pair is étale, so a
lifted monic presentation over `A` is étale whenever the original presentation
over `A₀` was. -/
instance standardEtalePair_etale {R : Type u} [CommRing R] (P : StandardEtalePair R) :
    Algebra.Etale R P.Ring :=
  inferInstance

end SGA.SGA1.ExposeI
