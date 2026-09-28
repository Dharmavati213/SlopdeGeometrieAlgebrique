/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.TopLocalCohomologyDualFunctor

/-!
# V.3.1(iii): associated primes of the original top local-cohomology dual

Apply the actual supported representation of IV to the original top dual.
The component test of V.3.3 computes the associated primes of its actual
representing colimit, and III.1.3 computes the original functor values.
No replacement of the original dual's scalar structure is made.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Associated primes of the actual top dual, on a fixed bounded closed
support, are precisely the top component generic points lying in the
coefficient module's original support. -/
theorem supportedTopLocalCohomologyDual_associatedPrimeSpectrum
    (J : Ideal R) (n : ℕ) (D : ModuleCat.{u} R) (hD : SupportedDualizingModule D)
    (hdim : Order.krullDim (PrimeSpectrum.zeroLocus (J : Set R)) ≤ n)
    (M : SupportedFGModuleCat J) :
    associatedPrimeSpectrum (R := R)
      ((supportedTopLocalCohomologyDual J n D).obj (op M)) =
        Module.support R M.obj.obj ∩ topDimensionalPrimes J n := by
  let G := supportedTopLocalCohomologyDual J n D
  let T := G ⋙ forget₂ (ModuleCat R) AddCommGrpCat
  have : PreservesFiniteLimits G :=
    supportedTopLocalCohomologyDual_preservesFiniteLimits J n D hdim
  have : PreservesFiniteLimits T := inferInstanceAs
    (PreservesFiniteLimits (G ⋙ forget₂ (ModuleCat R) AddCommGrpCat))
  let H := supportedFunctorColimit J T
  have hH : associatedPrimeSpectrum (R := R) H = topDimensionalPrimes J n := by
    apply supportedFunctorColimit_associatedPrimeSpectrum_eq J T _
      (fun _ hp => topDimensionalPrimes_minimal J n hdim hp)
    intro N
    change IsZero (AddCommGrpCat.of (G.obj (op N))) ↔ _
    rw [AddCommGrpCat.isZero_iff_subsingleton, ← ModuleCat.isZero_iff_subsingleton]
    exact supportedTopLocalCohomologyDual_isZero_iff J n D hD hdim N
  let e : G.obj (op M) ≅ (supportedModuleHomFunctor J H).obj (op M) :=
    ((additiveFunctorModuleLiftIsoOfLinear G).symm ≪≫
      supportedFunctorRepresentationIso J T).app (op M)
  let e' : G.obj (op M) ≃ₗ[R] (M.obj.obj →ₗ[R] H) :=
    e.toLinearEquiv.trans ModuleCat.homLinearEquiv
  have he : associatedPrimeSpectrum (R := R) (G.obj (op M)) =
      associatedPrimeSpectrum (R := R) (M.obj.obj →ₗ[R] H) := by
    ext p
    change p.asIdeal ∈ associatedPrimes R (G.obj (op M)) ↔ _
    rw [LinearEquiv.AssociatedPrimes.eq e']
    rfl
  rw [he, associatedPrimeSpectrum_linearMap H M.obj.obj, hH]

/-- **V.3.1(iii), associated-prime formula.** For the original finite
coefficient module of dimension `n`, the original top dual has exactly
its dimension-`n` associated primes. This statement of associated primes
holds without completeness; completeness additionally gives finiteness
of this dual, as established separately. -/
theorem localRing_topLocalCohomologyDual_associatedPrimeSpectrum
    (n : ℕ) (M D : ModuleCat.{u} R) [Module.Finite R M]
    (hD : SupportedDualizingModule D) (hdim : Module.supportDim R M = n) :
    associatedPrimeSpectrum (R := R) ((moduleHomDual D).obj
      (op ((_root_.localCohomology (maximalIdeal R) n).obj M))) =
        {p ∈ associatedPrimeSpectrum (R := R) M | ringKrullDim (R ⧸ p.asIdeal) = n} := by
  let J := Module.annihilator R M
  have hMs : Module.support R M = PrimeSpectrum.zeroLocus (J : Set R) :=
    Module.support_eq_zeroLocus
  have hdJ : Order.krullDim (PrimeSpectrum.zeroLocus (J : Set R)) ≤ n := by
    rw [← hMs]
    exact hdim.le
  let X : SupportedFGModuleCat J := ⟨FGModuleCat.of R M, hMs.le⟩
  change associatedPrimeSpectrum (R := R)
    ((supportedTopLocalCohomologyDual J n D).obj (op X)) = _
  rw [supportedTopLocalCohomologyDual_associatedPrimeSpectrum J n D hD hdJ X]
  ext p
  constructor
  · rintro ⟨_, hp⟩
    exact ⟨Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M
      (topDimensionalPrimes_minimal J n hdJ hp), hp.2⟩
  · rintro ⟨hp, hpd⟩
    have hps : p ∈ Module.support R M := associatedPrimeSpectrum_subset_support M hp
    exact ⟨hps, ⟨Module.mem_support_iff_of_finite.mp hps, hpd⟩⟩

end SGA.SGA2.ExposeV
