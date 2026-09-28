/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.LocalFiniteLengthCategory

/-!
# Finite length and vanishing away from the closed point

For a finite module over a noetherian local ring, finite length is equivalent
to vanishing of its actual localizations at every nonmaximal prime. This is
the support-theoretic step of V.3.5, before any Ext base-change comparison.
-/

noncomputable section
universe u
open CategoryTheory
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A finite original module has finite length precisely when its actual
support is contained in the closed point. -/
theorem finiteLength_iff_closedPointSupport (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsFiniteLength R M ↔ supportedModuleProperty (IsLocalRing.maximalIdeal R) M := by
  constructor
  · intro hM
    exact finiteLengthModule_support R ⟨M, hM⟩
  · intro hM
    let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
    exact isFiniteLength_of_finite_of_support (IsLocalRing.maximalIdeal R) M hM

/-- **V.3.5, support step:** finite length is detected by the actual localized
modules at the points distinct from the closed point. -/
theorem finiteLength_iff_localizedModule_subsingleton (M : ModuleCat.{u} R)
    [Module.Finite R M] :
    IsFiniteLength R M ↔ ∀ p : PrimeSpectrum R,
      p.asIdeal ≠ IsLocalRing.maximalIdeal R →
        Subsingleton (LocalizedModule p.asIdeal.primeCompl M) := by
  rw [finiteLength_iff_closedPointSupport]
  constructor
  · intro hM p hp
    apply Module.notMem_support_iff.mp
    intro hpm
    exact hp ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le p.isPrime.ne_top (hM hpm)).symm
  · intro hM p hp
    change IsLocalRing.maximalIdeal R ≤ p.asIdeal
    by_cases heq : p.asIdeal = IsLocalRing.maximalIdeal R
    · exact heq.ge
    · exact False.elim ((Module.notMem_support_iff.mpr (hM p heq)) hp)

end SGA.SGA2.ExposeV
