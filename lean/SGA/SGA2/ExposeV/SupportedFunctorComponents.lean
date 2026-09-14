/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.SupportedFunctorAssociatedPrimes
import SGA.SGA2.ExposeV.ClosedComponentGenericPoint

/-!
# V.3.3 for the actual irreducible components of the closed subspace

The component test now takes the original topological irreducible components,
not a supplied list of minimal primes or generic points. Their genuine generic
points are constructed, and the already constructed representing colimit has
exactly those associated primes. The result works for any indexed family,
in particular the finite family in the source.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- **V.3.3, actual component family.** Vanishing on modules containing
none of the specified original components identifies the associated primes
of the actual representing colimit with their actual generic points. -/
theorem supportedFunctorColimit_associatedPrimes_of_irreducibleComponents
    (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u})
    [T.Additive] [PreservesFiniteLimits T]
    {ι : Type v} (C : ι → Set (PrimeSpectrum.zeroLocus (J : Set R)))
    (hC : ∀ i, C i ∈ irreducibleComponents (PrimeSpectrum.zeroLocus (J : Set R)))
    (hvan : ∀ M : SupportedFGModuleCat J,
      IsZero (T.obj (op M)) ↔ ∀ i, ¬ Subtype.val '' C i ⊆ Module.support R M.obj) :
    ∃ p : ι → PrimeSpectrum R,
      (∀ i, IsGenericPoint (p i) (Subtype.val '' C i)) ∧
        associatedPrimeSpectrum (R := R) (supportedFunctorColimit J T) = Set.range p := by
  choose p hp he using fun i => closedComponent_exists_minimalPrime J (C i) (hC i)
  refine ⟨p, fun i => ?_, ?_⟩
  · change closure ({p i} : Set (PrimeSpectrum R)) = Subtype.val '' C i
    rw [PrimeSpectrum.closure_singleton, he i]
  · apply supportedFunctorColimit_associatedPrimeSpectrum_eq_of_components J T (Set.range p)
      (by rintro q ⟨i, rfl⟩; exact hp i)
    intro M
    rw [hvan M]
    constructor
    · intro h q hq
      obtain ⟨i, rfl⟩ := hq
      rw [← he i]
      exact h i
    · intro h i
      rw [he i]
      exact h (p i) ⟨i, rfl⟩

end SGA.SGA2.ExposeV
