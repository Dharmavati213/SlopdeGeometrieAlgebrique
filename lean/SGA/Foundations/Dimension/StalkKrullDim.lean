/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.Topology.KrullDimension

/-!
# Dimension of the local rings of a scheme

* `AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim`: the local rings of a scheme have
  Krull dimension at most the dimension of the scheme (`dim 𝒪_{X,x}` is the codimension of the
  closure of `x`, mathlib's `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`);
* `IsPrincipalIdealRing.of_isIntegrallyClosed_of_ringKrullDim_le_one`: a noetherian integrally
  closed local domain of Krull dimension `≤ 1` is a principal ideal ring (a field or a discrete
  valuation ring), being a Dedekind domain with a single maximal ideal.

Together they say that the local rings of a normal locally noetherian scheme of dimension `≤ 1`
are fields or discrete valuation rings.

## References

* [Stacks, Tag 02IZ] (dimension of local rings and codimension)
* [M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Proposition 9.2]
-/

namespace AlgebraicGeometry

/-- The local rings of a scheme have Krull dimension at most the dimension of the scheme. -/
theorem ringKrullDim_stalk_le_topologicalKrullDim {X : Scheme} (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [ringKrullDim_stalk_eq_coheight, topologicalKrullDim,
    Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
  exact Order.coheight_le_krullDim x

end AlgebraicGeometry

/-- A noetherian integrally closed local domain of Krull dimension `≤ 1` is a principal ideal
ring: it is a Dedekind domain with a single maximal ideal. -/
theorem IsPrincipalIdealRing.of_isIntegrallyClosed_of_ringKrullDim_le_one {R : Type*}
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (h : ringKrullDim R ≤ 1) : IsPrincipalIdealRing R := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr h
  have : Ring.DimensionLEOne R := ⟨fun hp hP ↦ hP.isMaximal_of_ne_bot hp⟩
  have : IsDedekindDomain R := { }
  refine IsPrincipalIdealRing.of_finite_maximals ?_
  exact (Set.finite_singleton (IsLocalRing.maximalIdeal R)).subset fun I hI ↦
    IsLocalRing.eq_maximalIdeal hI
