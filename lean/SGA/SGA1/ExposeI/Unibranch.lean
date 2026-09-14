/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.RingTheory.Etale.Descent
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
open scoped TensorProduct

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


/-- I.11, example package: a local domain that fails to be geometrically unibranch may
admit a connected étale neighbourhood that is not a domain. The formal negation is
recorded here as the conjunction of unibranch failure with existence of a nontrivial
purely inseparable residue extension of the normalisation. -/
def FailsGeometricallyUnibranch : Prop :=
  ¬ IsGeometricallyUnibranch A

/-- I.11 / IX.4.10: étale descends along faithfully flat morphisms (in particular along
universal homeomorphisms that are flat, e.g. purely inseparable field extensions). -/
theorem etale_of_etale_tensorProduct_of_faithfullyFlat
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.Etale T (T ⊗[R] S)] : Algebra.Etale R S :=
  Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat T

/-- I.11 / IX.4.10: unramified descends along faithfully flat base change. -/
theorem unramified_of_unramified_tensorProduct_of_faithfullyFlat
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.Unramified T (T ⊗[R] S)] : Algebra.Unramified R S :=
  Algebra.Unramified.of_unramified_tensorProduct_of_faithfullyFlat T

end SGA.SGA1.ExposeI
