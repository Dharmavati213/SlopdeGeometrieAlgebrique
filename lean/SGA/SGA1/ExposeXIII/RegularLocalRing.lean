/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.CommAlg.Factorial
import SGA.Foundations.CommAlg.Normal

/-!
# Regular local rings (prerequisites for XIII.5)

The commutative algebra of regular local rings used in XIII.5 is in
`SGA.Foundations.CommAlg.RegularLocalRing` and `SGA.Foundations.CommAlg.Normal`: a regular local
ring is a domain (Stacks 00NP), is normal (Stacks 0567) and even factorial (Stacks 0AG0), its
localizations at primes are regular (Stacks 00OE), and quotients by part of a regular system of
parameters are regular (Stacks 00NR).
The names below are kept for the files of this exposé.
-/

universe u

namespace SGA.SGA1.ExposeXIII

export IsLocalRing (exists_span_insert_eq_maximalIdeal
  exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes maximalIdeal_le_ringJacobson)

/-- A regular local ring is a domain (Stacks 00NP). -/
theorem isDomain_of_isRegularLocalRing (B : Type u) [CommRing B] [IsRegularLocalRing B] :
    IsDomain B :=
  inferInstance

/-- A regular local ring is an integrally closed domain (Stacks 0567), as used in XIII.5. -/
theorem isIntegrallyClosed_of_isRegularLocalRing (B : Type u) [CommRing B]
    [IsRegularLocalRing B] : IsIntegrallyClosed B :=
  inferInstance

/-- A regular local ring is factorial (Auslander–Buchsbaum; Stacks 0AG0), as used in XIII.5. -/
theorem uniqueFactorizationMonoid_of_isRegularLocalRing (B : Type u) [CommRing B]
    [IsRegularLocalRing B] : UniqueFactorizationMonoid B :=
  inferInstance

/-- The localization of a regular local ring at a prime is regular (Stacks 00OE), as used in
XIII.5. -/
theorem isRegularLocalRing_localization {B : Type u} [CommRing B] [IsRegularLocalRing B]
    (p : Ideal B) [p.IsPrime] : IsRegularLocalRing (Localization.AtPrime p) :=
  inferInstance

end SGA.SGA1.ExposeXIII
