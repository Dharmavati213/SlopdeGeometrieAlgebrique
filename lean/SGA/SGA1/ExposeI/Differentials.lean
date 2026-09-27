/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Unramified.Basic

/-!
# SGA 1, Exposé I, §1: notions of differential calculus

SGA defines `Ω¹_{X/Y}` as `𝓘/𝓘²`, where `𝓘` is the ideal of the diagonal. On affines
this is literally mathlib's definition of the module of Kähler differentials: `Ω[S⁄R]` is
the cotangent module `I/I²` of the kernel `I` of the multiplication `S ⊗[R] S → S`.
It is finite when `S` is of finite type, and it is compatible with base change. The
sheaves of principal parts `Pⁿ_{X/Y}` are the rings `(S ⊗[R] S)/I^(n+1)`.
-/

universe u

namespace SGA.SGA1.ExposeI

open scoped TensorProduct

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- I.1: the ideal `𝓘` of the diagonal, the kernel of `S ⊗[R] S → S`. -/
noncomputable abbrev diagonalIdeal : Ideal (S ⊗[R] S) :=
  KaehlerDifferential.ideal R S

/-- I.1: `Ω¹_{S/R}` is by definition the conormal module `𝓘/𝓘²` of the diagonal. -/
theorem kaehlerDifferential_eq_cotangent : Ω[S⁄R] = (diagonalIdeal R S).Cotangent :=
  rfl

/-- I.1: formally unramified means that `Ω¹` vanishes. -/
theorem formallyUnramified_iff_subsingleton_differentials :
    Algebra.FormallyUnramified R S ↔ Subsingleton Ω[S⁄R] :=
  Algebra.formallyUnramified_iff R S

/-- I.1: if `S` is essentially of finite type over `R`, then `Ω¹_{S/R}` is finite. -/
instance differentials_finite [Algebra.EssFiniteType R S] : Module.Finite S Ω[S⁄R] :=
  KaehlerDifferential.finite R S

/-- I.1: `Ω¹` behaves well under extension of the base: for `S' = R' ⊗_R S`,
`S' ⊗_S Ω¹_{S/R} ≅ Ω¹_{S'/R'}`. -/
noncomputable def tensorKaehlerEquiv (R' S' : Type u) [CommRing R'] [CommRing S']
    [Algebra R R'] [Algebra R S'] [Algebra R' S'] [Algebra S S'] [IsScalarTower R R' S']
    [IsScalarTower R S S'] [Algebra.IsPushout R R' S S'] :
    S' ⊗[S] Ω[S⁄R] ≃ₗ[S'] Ω[S'⁄R'] :=
  KaehlerDifferential.tensorKaehlerEquiv R R' S S'

/-- I.1: the algebra of principal parts of order `n`, i.e. the `n`th infinitesimal
neighbourhood of the diagonal. -/
abbrev principalParts (n : ℕ) : Type u :=
  (S ⊗[R] S) ⧸ diagonalIdeal R S ^ (n + 1)

end SGA.SGA1.ExposeI
