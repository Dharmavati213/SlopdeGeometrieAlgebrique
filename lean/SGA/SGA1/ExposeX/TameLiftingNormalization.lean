/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Ramification.IntegralClosure
import SGA.SGA1.ExposeI.Unibranch
import SGA.SGA1.ExposeIII.LocalComponents

/-!
# SGA 1, Exposé X, before 3.7: the normalization `V'` of a complete discrete valuation ring

In the paragraph before X.3.7, SGA replaces the complete discrete valuation ring `R` by the
normalization `V'` of `R` in a finite separable extension `K'` of its fraction field `K`. We record
the facts used: `V'` is a complete discrete valuation ring
(`isDiscreteValuationRing_integralClosure`, `isAdicComplete_integralClosure`), finite and local over
`R`, with fraction field `K'` (mathlib's `integralClosure.isFractionRing_of_finite_extension`), and
its residue field is a finite extension of that of `R`, purely inseparable when the latter is
separably closed (`isPurelyInseparable_residueField_integralClosure`). (A finite algebra over a
complete local ring which is a domain is local:
`SGA.SGA1.ExposeI.isLocalRing_of_finite_of_isDomain`.)
-/

universe u

open IsLocalRing

namespace SGA.SGA1.ExposeX

variable (R K L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

include K in
/-- The normalization of a complete discrete valuation ring `R` in a finite separable extension
`L` of its fraction field is local (`R` is henselian and the normalization is a finite domain). -/
theorem isLocalRing_integralClosure : IsLocalRing (integralClosure R L) :=
  have := integralClosure.finite R K L
  ExposeI.isLocalRing_of_finite_of_isDomain (A := R) _

include K in
/-- In the paragraph before X.3.7: the normalization of a complete discrete valuation ring `R` in a
finite separable extension `L` of its fraction field is a discrete valuation ring (a local Dedekind
domain which is not a field). -/
theorem isDiscreteValuationRing_integralClosure :
    IsDiscreteValuationRing (integralClosure R L) := by
  have := integralClosure.isDedekindDomain' R K L
  have := integralClosure.finite R K L
  have := isLocalRing_integralClosure R K L
  have hnf : ¬ IsField (integralClosure R L) := by
    intro h
    have : Algebra.IsIntegral R (integralClosure R L) := Algebra.IsIntegral.of_finite R _
    exact IsDiscreteValuationRing.not_isField R
      ((Algebra.IsIntegral.isField_iff_isField
        (integralClosure.algebraMap_injective_of_isFractionRing R K L)).mpr h)
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 3 1).mp ‹IsDedekindDomain _›

include K in
/-- The normalization of a complete discrete valuation ring in a finite separable extension of its
fraction field is complete. -/
theorem isAdicComplete_integralClosure :
    letI := isLocalRing_integralClosure R K L
    IsAdicComplete (maximalIdeal (integralClosure R L)) (integralClosure R L) :=
  letI := isLocalRing_integralClosure R K L
  have := integralClosure.finite R K L
  ExposeIII.isAdicComplete_maximalIdeal_of_finite (A := R)

include K in
/-- The normalization of a complete discrete valuation ring in a finite separable extension of its
fraction field is local over it. -/
theorem isLocalHom_integralClosure :
    letI := isLocalRing_integralClosure R K L
    IsLocalHom (algebraMap R (integralClosure R L)) :=
  letI := isLocalRing_integralClosure R K L
  have := integralClosure.finite R K L
  ExposeIII.isLocalHom_of_finite

include K in
/-- The residue field of the normalization of a complete discrete valuation ring in a finite
separable extension of its fraction field is finite over that of `R`. -/
theorem finite_residueField_integralClosure :
    letI := isLocalRing_integralClosure R K L
    letI := isLocalHom_integralClosure R K L
    Module.Finite (ResidueField R) (ResidueField (integralClosure R L)) :=
  letI := isLocalRing_integralClosure R K L
  letI := isLocalHom_integralClosure R K L
  have := integralClosure.finite R K L
  inferInstance

include K in
/-- In the paragraph before X.3.7: when the residue field of the complete discrete valuation ring
`R` is separably closed, the residue field of its normalization in a finite separable extension of
its fraction field is purely inseparable over it. -/
theorem isPurelyInseparable_residueField_integralClosure [IsSepClosed (ResidueField R)] :
    letI := isLocalRing_integralClosure R K L
    letI := isLocalHom_integralClosure R K L
    IsPurelyInseparable (ResidueField R) (ResidueField (integralClosure R L)) :=
  letI := isLocalRing_integralClosure R K L
  letI := isLocalHom_integralClosure R K L
  have := finite_residueField_integralClosure R K L
  have : Algebra.IsAlgebraic (ResidueField R) (ResidueField (integralClosure R L)) :=
    Algebra.IsAlgebraic.of_finite _ _
  inferInstance

end SGA.SGA1.ExposeX
