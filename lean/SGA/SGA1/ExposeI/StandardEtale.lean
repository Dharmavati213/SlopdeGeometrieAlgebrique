/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# SGA 1, Exposé I, §7: local construction of unramified and étale morphisms

A standard étale algebra is `R[X]/(f)` localised away from an element `g`
with `f` monic and `f'` invertible after inverting `g`. This is SGA's local
presentation: I.7.1–I.7.4 say that `B_q` is unramified (resp. étale) over
`A_p` when the derivative of a generating polynomial misses `q`. Mathlib's
`StandardEtalePair` packages the same data, and
`Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn` is the
Zariski-local form of I.7.6–I.7.8 (unramified morphisms are locally closed
immersions into étale schemes; étale morphisms are locally standard étale).
-/

universe u

namespace SGA.SGA1.ExposeI

open Algebra Polynomial

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- I.7.4: a standard étale pair gives an étale algebra. -/
instance (P : StandardEtalePair R) : Etale R P.Ring :=
  inferInstance

/-- I.7.4: the algebra of a standard étale pair is standard étale. -/
instance (P : StandardEtalePair R) : IsStandardEtale R P.Ring :=
  inferInstance

/-- I.7.1–I.7.4: the derivative of the monic polynomial is invertible on the
standard étale algebra. -/
theorem isUnit_derivative (P : StandardEtalePair R) :
    IsUnit (P.f.derivative.aeval P.X) :=
  P.hasMap_X.isUnit_derivative_f

/-- I.7.8: an algebra of finite type unramified at `Q` is, after inverting one
element, a quotient of a standard étale algebra. -/
theorem exists_standardEtale_surjection [FiniteType R S] (Q : Ideal S) [Q.IsPrime]
    [IsUnramifiedAt R Q] : ∃ f ∉ Q, HasStandardEtaleSurjectionOn (R := R) f :=
  IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := R) Q

/-- I.7.6, étale case: an algebra of finite presentation étale at `Q` is,
after inverting one element, itself standard étale. -/
theorem exists_isStandardEtale [FinitePresentation R S] (Q : Ideal S) [Q.IsPrime]
    [IsEtaleAt R Q] : ∃ f ∉ Q, IsStandardEtale R (Localization.Away f) :=
  IsEtaleAt.exists_isStandardEtale (R := R) Q

/-- I.7.7: unramified algebras are locally quotients of étale algebras. -/
theorem exists_standardEtale_surjection_of_unramified [FiniteType R S] (Q : Ideal S)
    [Q.IsPrime] [IsUnramifiedAt R Q] :
    ∃ f ∉ Q, HasStandardEtaleSurjectionOn R f :=
  exists_standardEtale_surjection (R := R) Q

end SGA.SGA1.ExposeI
