/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeI.CompleteLocal
import SGA.SGA1.ExposeI.Fundamental
import SGA.SGA1.ExposeI.StandardEtale

/-!
# SGA 1, Exposé I, §8: infinitesimal lifting of étale schemes

Theorem I.8.3 says that reducing modulo a nilpotent ideal of definition is an
equivalence on étale schemes. Uniqueness of morphisms is I.5.5
(`FormallyUnramified.hom_ext`), proved in `Fundamental.lean`. Local existence
for standard étale presentations is I.8.1 / I.7.4. Global gluing of these
local lifts to a scheme over `S` (essential surjectivity of I.8.3) is not
available: mathlib has no formal schemes and no packaged gluing of affine
étale lifts along a nilpotent closed immersion.

I.8.4 is recorded in the affine artinian form and, via I.6.1, in the affine
complete-local form for adically complete targets. Formal schemes themselves
are absent from mathlib.
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry CategoryTheory
open Algebra IsLocalRing

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

/-- I.8.3 / I.5.5 uniqueness packaged for a pair of étale `S`-schemes. -/
theorem etale_reduction_fullyFaithful_hom {S S₀ X : Scheme.{u}}
    (i : S₀ ⟶ S) (hi : IsNilpotent i.ker) [IsClosedImmersion i]
    {g : X ⟶ S} [Etale g] {f₁ f₂ : S ⟶ X}
    (hf : i ≫ f₁ = i ≫ f₂) (hg : f₁ ≫ g = f₂ ≫ g) : f₁ = f₂ :=
  etale_reduction_hom_unique i hi hf hg

/-- I.8.4, affine artinian form: maps out of a formally étale algebra over an artinian
local ring correspond bijectively to maps into the special fibre (I.6.1 / I.6.2). -/
theorem etale_covering_residue_equiv {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [FormallyEtale A B] [IsLocalRing A] [IsArtinianRing A] :
    Function.Bijective fun f : B →ₐ[A] C ↦
      (Ideal.Quotient.mkₐ A ((maximalIdeal A).map (algebraMap A C))).comp f :=
  finiteEtale_hom_equiv_residue_artinian

/-- I.8.4, affine complete-local form: same bijection when the target is
`m_A`-adically complete (I.6.1 complete-local). Formal schemes are not in mathlib. -/
theorem etale_covering_residue_equiv_complete {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [FormallyEtale A B] [IsLocalRing A]
    [IsAdicComplete ((maximalIdeal A).map (algebraMap A C)) C] :
    Function.Bijective fun f : B →ₐ[A] C ↦
      (Ideal.Quotient.mkₐ A ((maximalIdeal A).map (algebraMap A C))).comp f :=
  finiteEtale_hom_equiv_residue_complete

end SGA.SGA1.ExposeI
