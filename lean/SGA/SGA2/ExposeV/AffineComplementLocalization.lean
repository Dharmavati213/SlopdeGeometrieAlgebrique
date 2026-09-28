/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.AffineSupport
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localizing an actual closed support at a component generic point

The inverse image of the original open complement at a minimal prime of
its support ideal is exactly the punctured spectrum of the actual local
ring. Affineness follows from the genuine spectrum morphism being affine.
-/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry IsLocalRing
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

/-- The preimage of the original complement under localization at a component
generic point is the actual punctured local spectrum. -/
theorem affineSupportComplement_preimage_at_minimalPrime (J : Ideal R)
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ J.minimalPrimes) :
    let S := CommRingCat.of (Localization.AtPrime p.asIdeal)
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) ⁻¹ᵁ affineSupportComplement J =
      affineSupportComplement (maximalIdeal S) := by
  let S := CommRingCat.of (Localization.AtPrime p.asIdeal)
  ext q
  change (¬ J ≤ q.asIdeal.under R) ↔ (¬ maximalIdeal S ≤ q.asIdeal)
  apply not_congr
  constructor
  · intro hJ
    have hqp : q.asIdeal.under R ≤ p.asIdeal :=
      (IsLocalization.AtPrime.primeSpectrumOrderIso S p.asIdeal q).property
    have hpq : p.asIdeal ≤ q.asIdeal.under R := hp.2
      ⟨Ideal.comap_isPrime (algebraMap R S) q.asIdeal, hJ⟩ hqp
    have he : q.asIdeal.under R = p.asIdeal := le_antisymm hqp hpq
    have hq : q.asIdeal = maximalIdeal S := by
      apply (IsLocalization.orderEmbedding p.asIdeal.primeCompl S).injective
      exact he.trans (IsLocalization.AtPrime.under_maximalIdeal S p.asIdeal).symm
    exact hq.ge
  · intro hm
    exact hp.1.2.trans ((IsLocalization.AtPrime.under_maximalIdeal S p.asIdeal).ge.trans
      (Ideal.comap_mono hm))

/-- **V.3.4, localization step.** An actual affine complement remains
affine as the punctured spectrum at every component generic point. -/
theorem isAffineOpen_puncturedSpectrum_at_minimalPrime (J : Ideal R)
    (hJ : IsAffineOpen (affineSupportComplement J))
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ J.minimalPrimes) :
    IsAffineOpen (affineSupportComplement
      (maximalIdeal (CommRingCat.of (Localization.AtPrime p.asIdeal)))) := by
  rw [← affineSupportComplement_preimage_at_minimalPrime J p hp]
  exact hJ.preimage _

end SGA.SGA2.ExposeV
