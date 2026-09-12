/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import SGA.SGA1.ExposeI.Etale
import SGA.SGA1.ExposeI.Permanence

/-!
# SGA 1, Exposé I, §10: étale coverings of a normal scheme

Over a normal connected base, connected étale schemes are open in the
normalisation of the base in a finite separable extension of its function
field (I.10.1). Finite étale coverings correspond to unramified extensions
of that function field (I.10.3). The counting of geometric fibre points
(I.10.7–I.10.11) uses that a quasi-finite universally open morphism has an
upper semicontinuous geometric fibre-cardinality; étale morphisms are
universally open, and constancy of that function characterises étale
coverings on a connected base (I.10.10).
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- I.10.7, standing hypothesis: étale morphisms of finite presentation are
universally open. -/
instance (priority := 100) universallyOpen_of_etale [Etale f] : UniversallyOpen f :=
  inferInstance

/-- I.10.2 / I.4.9: a finite étale morphism is an étale covering. -/
theorem isEtaleCovering_of_isFinite [IsFinite f] [Etale f] : IsEtaleCovering f :=
  ⟨inferInstance, inferInstance⟩

/-- I.10.10, one direction: a finite étale morphism has finite fibres of constant
cardinality on connected components once the geometric number of points is
read in the residue fields. Finite morphisms have finite fibres. -/
theorem finite_preimage_of_etale_covering [IsFinite f] (y : Y) :
    (f ⁻¹' {y}).Finite :=
  f.finite_preimage_singleton y

/-- I.10.1, Zariski's main theorem input: a separated quasi-finite morphism
factors through a finite morphism after restricting to the quasi-finite locus,
with the comparison map an open immersion into the relative normalisation. -/
theorem isOpenImmersion_toNormalization_on_quasiFiniteLocus
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f] :
    IsOpenImmersion (f.quasiFiniteLocus.ι ≫ f.toNormalization) :=
  inferInstance

/-- I.10.5: étale (in particular smooth) base change commutes with integral
closure, which is the affine form of the translation property for unramified
extensions of the function field. -/
theorem translation_of_integralClosure {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra.Etale A B] :
    Function.Bijective (TensorProduct.toIntegralClosure A B C) :=
  toIntegralClosure_bijective_of_etale

end SGA.SGA1.ExposeI
