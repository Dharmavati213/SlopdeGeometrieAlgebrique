/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorVanishing
import SGA.SGA2.ExposeIII.AssociatedPrimes

/-!
# V.3.3: associated primes of an actual representing module

The representing module is the original supported quotient colimit
constructed in IV.1.3. Tests on the original cyclic modules `R/p`, together
with III.1.3, identify its associated primes with any specified collection
of component generic points detected by the functor's vanishing criterion.
The components are indexed by the actual minimal primes of the support ideal.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- A module support contains the whole closure of a prime exactly when
it contains that prime itself. This retains the actual spectrum and support. -/
theorem prime_zeroLocus_subset_support_iff (M : ModuleCat.{u} R) (p : PrimeSpectrum R) :
    PrimeSpectrum.zeroLocus (p.asIdeal : Set R) ⊆ Module.support R M ↔
      p ∈ Module.support R M := by
  constructor
  · intro h
    exact h (fun _ hx => hx)
  · intro h q hq
    exact Module.mem_support_mono hq h

/-- The original cyclic module attached to a prime of `V(J)`, as an
object of the actual finite supported category. -/
def primeSupportedTestModule (J : Ideal R) (p : PrimeSpectrum R) (hp : J ≤ p.asIdeal) :
    SupportedFGModuleCat J :=
  ⟨FGModuleCat.of R (R ⧸ p.asIdeal), by
    change Module.support R (R ⧸ p.asIdeal) ⊆ PrimeSpectrum.zeroLocus (J : Set R)
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    exact PrimeSpectrum.zeroLocus_anti_mono hp⟩

/-- The test has precisely the closure of the given prime as support. -/
theorem primeSupportedTestModule_support (J : Ideal R) (p : PrimeSpectrum R)
    (hp : J ≤ p.asIdeal) :
    Module.support R (primeSupportedTestModule J p hp).obj =
      PrimeSpectrum.zeroLocus (p.asIdeal : Set R) := by
  change Module.support R (R ⧸ p.asIdeal) = _
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]

variable [IsNoetherianRing R]
variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u})
variable [T.Additive] [PreservesFiniteLimits T]

/-- Vanishing of the actual functor value is exactly vanishing of the
linear Hom module into its original representing colimit. -/
theorem supportedFunctor_isZero_iff_subsingleton_linearMap (M : SupportedFGModuleCat J) :
    IsZero (T.obj (op M)) ↔ Subsingleton (M.obj.obj →ₗ[R] supportedFunctorColimit J T) := by
  rw [((additiveSupportedFunctorRepresentationIso J T).app (op M)).isZero_iff]
  change IsZero (AddCommGrpCat.of (M.obj.obj ⟶ supportedFunctorColimit J T)) ↔ _
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact ModuleCat.homEquiv.subsingleton_congr

/-- **V.3.3, component-generic-point criterion.** If an actual supported
left-exact functor vanishes precisely on modules missing the selected
component generic points, its original representing colimit has exactly
those associated primes. No representing module is postulated. -/
theorem supportedFunctorColimit_associatedPrimeSpectrum_eq
    (P : Set (PrimeSpectrum R)) (hP : ∀ p ∈ P, p.asIdeal ∈ J.minimalPrimes)
    (hvan : ∀ M : SupportedFGModuleCat J,
      IsZero (T.obj (op M)) ↔ ∀ p ∈ P, p ∉ Module.support R M.obj) :
    associatedPrimeSpectrum (R := R) (supportedFunctorColimit J T) = P := by
  let H := supportedFunctorColimit J T
  have hsub : associatedPrimeSpectrum (R := R) H ⊆ P := by
    intro q hq
    have hJq : J ≤ q.asIdeal := (supportedFunctorColimit_support J T)
      (associatedPrimeSpectrum_subset_support H hq)
    by_contra hqP
    let X := primeSupportedTestModule J q hJq
    have hz : IsZero (T.obj (op X)) := (hvan X).mpr (by
      intro p hp hpm
      have hqp : q.asIdeal ≤ p.asIdeal := by
        change p ∈ Module.support R (R ⧸ q.asIdeal) at hpm
        simpa only [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] using hpm
      have hpq : p.asIdeal ≤ q.asIdeal := (hP p hp).2 ⟨q.isPrime, hJq⟩ hqp
      have he : q = p := PrimeSpectrum.ext (le_antisymm hqp hpq)
      exact hqP (he ▸ hp))
    have : Subsingleton (X.obj.obj →ₗ[R] H) :=
      (supportedFunctor_isZero_iff_subsingleton_linearMap J T X).mp hz
    have hself : q ∈ Module.support R X.obj.obj := by
      change q ∈ Module.support R (R ⧸ q.asIdeal)
      rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
    have hqHom := (mem_associatedPrimes_linearMap_iff H X.obj.obj q).mpr ⟨hself, hq⟩
    simp only [associatedPrimes.eq_empty_of_subsingleton, Set.mem_empty_iff_false] at hqHom
  apply Set.Subset.antisymm hsub
  intro p hp
  let X := primeSupportedTestModule J p (hP p hp).1.2
  have hn : ¬ IsZero (T.obj (op X)) := by
    intro hz
    apply (hvan X).mp hz p hp
    change p ∈ Module.support R (R ⧸ p.asIdeal)
    rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
  have : Nontrivial (X.obj.obj →ₗ[R] H) := not_subsingleton_iff_nontrivial.mp
    (fun h => hn ((supportedFunctor_isZero_iff_subsingleton_linearMap J T X).mpr h))
  obtain ⟨q, hq⟩ := associatedPrimes.nonempty R (X.obj.obj →ₗ[R] H)
  let Q : PrimeSpectrum R := ⟨q, hq.isPrime⟩
  obtain ⟨hqX, hqH⟩ := (mem_associatedPrimes_linearMap_iff H X.obj.obj Q).mp hq
  have hQP : Q ∈ P := hsub hqH
  have hpq : p.asIdeal ≤ q := by
    change Q ∈ Module.support R (R ⧸ p.asIdeal) at hqX
    simpa only [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] using hqX
  have hqp : q ≤ p.asIdeal := (hP Q hQP).2 ⟨p.isPrime, (hP p hp).1.2⟩ hpq
  have he : Q = p := PrimeSpectrum.ext (le_antisymm hqp hpq)
  exact he ▸ hqH

/-- **V.3.3, component-support formulation.** The actual representation
has precisely the selected component generic points as associated primes
when vanishing means containing none of their original closed components. -/
theorem supportedFunctorColimit_associatedPrimeSpectrum_eq_of_components
    (P : Set (PrimeSpectrum R)) (hP : ∀ p ∈ P, p.asIdeal ∈ J.minimalPrimes)
    (hvan : ∀ M : SupportedFGModuleCat J,
      IsZero (T.obj (op M)) ↔ ∀ p ∈ P,
        ¬ PrimeSpectrum.zeroLocus (p.asIdeal : Set R) ⊆ Module.support R M.obj) :
    associatedPrimeSpectrum (R := R) (supportedFunctorColimit J T) = P := by
  apply supportedFunctorColimit_associatedPrimeSpectrum_eq J T P hP
  intro M
  simpa only [prime_zeroLocus_subset_support_iff] using hvan M

end SGA.SGA2.ExposeV
