/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RingHom.PurelyInseparable

/-!
# SGA 1, Exposé I, §11: geometrically unibranch schemes

A local domain is geometrically unibranch when its normalisation has a unique
prime over the maximal ideal and the residue-field extension is purely
inseparable. The exposé's examples (a nodal curve and `ℝ[[s,t]]/(s²+t²)`)
show that without this hypothesis a connected étale covering of an integral
scheme need not be integral. The comparison of étale schemes along a
universal homeomorphism is deferred to IX.4.10.
-/

universe u

namespace SGA.SGA1.ExposeI

open IsLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]

/-- The integral closure of a local domain in its fraction field. -/
abbrev normalizationRing : Type u := integralClosure A (FractionRing A)

/-- I.11: `A` is unibranch when its normalisation has a unique prime over the
maximal ideal. -/
def IsUnibranch : Prop :=
  Subsingleton ((maximalIdeal A).primesOver (normalizationRing A))

/-- I.11: `A` is geometrically unibranch when it is unibranch and every residue
extension of the normalisation over `A` is purely inseparable. -/
def IsGeometricallyUnibranch : Prop :=
  IsUnibranch A ∧
    ∀ Q : (maximalIdeal A).primesOver (normalizationRing A),
      (Ideal.ResidueField.map (maximalIdeal A) Q.1 (algebraMap A (normalizationRing A))
        Q.2.2.over).IsPurelyInseparable

end SGA.SGA1.ExposeI
