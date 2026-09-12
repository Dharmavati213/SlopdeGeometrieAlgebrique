/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Unramified.Basic

/-!
# SGA 1, Exposé I, §1: notions of differential calculus

SGA writes `Ω¹_{X/Y}` for the conormal sheaf of the diagonal. On affines this is
mathlib's module of Kähler differentials `Ω[S⁄R]`. Formally unramified means
that this module vanishes. Finite type implies that it is a finite module.
The sheaves of principal parts `Pⁿ_{X/Y}` are the infinitesimal neighbourhoods
of the diagonal; they are recorded only as the corresponding quotient of
`S ⊗[R] S`.
-/

universe u

namespace SGA.SGA1.ExposeI

open scoped TensorProduct

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- I.1: the module of relative differentials of an affine morphism. -/
abbrev differentials : Type u := Ω[S⁄R]

/-- I.1: formally unramified means that `Ω¹` vanishes. -/
theorem formallyUnramified_iff_subsingleton_differentials :
    Algebra.FormallyUnramified R S ↔ Subsingleton Ω[S⁄R] :=
  Algebra.formallyUnramified_iff R S

/-- I.1: if `S` is essentially of finite type over `R`, then `Ω¹_{S/R}` is finite. -/
instance differentials_finite [Algebra.EssFiniteType R S] : Module.Finite S Ω[S⁄R] :=
  KaehlerDifferential.finite R S

/-- I.1: the kernel of multiplication `S ⊗[R] S → S`, the ideal of the diagonal. -/
abbrev diagonalIdeal : Ideal (S ⊗[R] S) :=
  RingHom.ker (Algebra.TensorProduct.lmul' R (S := S)).toRingHom

/-- I.1: the algebra of principal parts of order `n`, i.e. the `n`th infinitesimal
neighbourhood of the diagonal. -/
abbrev principalParts (n : ℕ) : Type u :=
  (S ⊗[R] S) ⧸ diagonalIdeal R S ^ (n + 1)

end SGA.SGA1.ExposeI
