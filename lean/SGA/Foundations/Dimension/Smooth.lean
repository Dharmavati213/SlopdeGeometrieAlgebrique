/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Unramified.LocalStructure
import SGA.Foundations.Dimension.LocalDimension
import SGA.Foundations.Dimension.QuasiFinite

/-!
# Dimension of smooth algebras over a field

Let `S` be an algebra over a field `K` which is étale over a polynomial ring `K[X₁, …, Xₙ]`,
for example a standard smooth algebra of relative dimension `n`
(`Algebra.IsStandardSmoothOfRelativeDimension n K S`). Then for every prime `Q` of `S`,
`ht Q + dim S/Q = n` (`Algebra.height_add_coheight_eq_of_etale_mvPolynomial`). Consequently
`Spec S` has dimension `n` at every point, every irreducible component of `Spec S` has
dimension `n`, and `dim S_Q + trdeg_K κ(Q) = n` (EGA IV 17.10.2).

The proof: an étale algebra is flat (going down) and quasi-finite (primes in a fibre are
incomparable), so contraction of primes to `K[X₁, …, Xₙ]` preserves heights and `dim S/Q`
(`SGA.Foundations.Dimension.QuasiFinite`).
-/

open Order PrimeSpectrum

namespace Algebra

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

/-- If `S` is étale over `K[X₁, …, Xₙ]`, then `ht Q + dim S/Q = n` for every prime `Q` of `S`. -/
theorem height_add_coheight_eq_of_etale_mvPolynomial {n : ℕ}
    [Algebra (MvPolynomial (Fin n) K) S] [IsScalarTower K (MvPolynomial (Fin n) K) S]
    [Algebra.Etale (MvPolynomial (Fin n) K) S] (Q : PrimeSpectrum S) :
    height Q + coheight Q = n := by
  set P := MvPolynomial (Fin n) K
  have : Algebra.FiniteType K S := .trans (S := P) inferInstance inferInstance
  rw [← height_comap_of_quasiFinite (R := P), ← FiniteType.coheight_comap_of_quasiFinite K (R := P)]
  exact MvPolynomial.height_add_coheight_eq _

variable (K) (n : ℕ)

theorem IsStandardSmoothOfRelativeDimension.finiteType
    [IsStandardSmoothOfRelativeDimension n K S] : Algebra.FiniteType K S :=
  have := IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := K) (S := S) n
  inferInstance

/-- For a standard smooth algebra `S` of relative dimension `n` over a field, `ht Q + dim S/Q = n`
for every prime `Q`. -/
theorem IsStandardSmoothOfRelativeDimension.height_add_coheight_eq
    [IsStandardSmoothOfRelativeDimension n K S] (Q : PrimeSpectrum S) :
    height Q + coheight Q = n := by
  obtain ⟨g, hg⟩ := IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K S
  algebraize [g.toRingHom]
  have : IsScalarTower K (MvPolynomial (Fin n) K) S := .of_algebraMap_eq' g.comp_algebraMap.symm
  exact height_add_coheight_eq_of_etale_mvPolynomial (K := K) Q

/-- A standard smooth algebra of relative dimension `n` over a field has dimension `n` at every
point of its spectrum. -/
theorem IsStandardSmoothOfRelativeDimension.topologicalKrullDimAt_eq
    [IsStandardSmoothOfRelativeDimension n K S] (Q : PrimeSpectrum S) :
    topologicalKrullDimAt (PrimeSpectrum S) Q = n := by
  have := finiteType K n (S := S)
  rw [FiniteType.topologicalKrullDimAt_eq K, height_add_coheight_eq K n]
  rfl

/-- A nonzero standard smooth algebra of relative dimension `n` over a field has Krull
dimension `n`. -/
theorem IsStandardSmoothOfRelativeDimension.ringKrullDim_eq
    [IsStandardSmoothOfRelativeDimension n K S] [Nontrivial S] : ringKrullDim S = n := by
  have : Nonempty (PrimeSpectrum S) := inferInstance
  rw [ringKrullDim, krullDim_eq_iSup_height_add_coheight_of_nonempty]
  simp_rw [height_add_coheight_eq K n]
  simp

/-- Every irreducible component of the spectrum of a standard smooth algebra of relative
dimension `n` over a field has dimension `n`: `dim S/p = n` for every minimal prime `p`. -/
theorem IsStandardSmoothOfRelativeDimension.ringKrullDim_quotient_eq_of_mem_minimalPrimes
    [IsStandardSmoothOfRelativeDimension n K S] {p : Ideal S} (hp : p ∈ minimalPrimes S) :
    ringKrullDim (S ⧸ p) = n := by
  have : p.IsPrime := hp.1.1
  have h := height_add_coheight_eq K n ⟨p, this⟩
  rw [← height_eq_orderHeight, Ideal.height_eq_zero_iff.mpr hp, zero_add] at h
  have h' := coheight_eq_ringKrullDim_quotient ⟨p, this⟩
  rw [h] at h'
  exact h'.symm

/-- `dim S_Q + trdeg_K κ(Q) = n` for a prime `Q` of a standard smooth algebra of relative
dimension `n` over a field `K`. -/
theorem IsStandardSmoothOfRelativeDimension.ringKrullDim_add_trdeg_residueField
    [IsStandardSmoothOfRelativeDimension n K S] (Q : Ideal S) [Q.IsPrime] :
    ringKrullDim (Localization.AtPrime Q) + (trdeg K Q.ResidueField).toENat = n := by
  have := finiteType K n (S := S)
  rw [← FiniteType.topologicalKrullDimAt_eq_ringKrullDim_add_trdeg K,
    topologicalKrullDimAt_eq K n]

end Algebra
