/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.SupportedFunctorAssociatedPrimes
import Mathlib.RingTheory.KrullDimension.Module

/-!
# Top-dimensional components of an actual closed support

Finite chains in the original prime spectrum detect the components of
maximal dimension. Prepending a smaller prime to a maximal-length chain
shows that any such prime is a genuine minimal prime of the support ideal.
-/

noncomputable section
universe u
open CategoryTheory

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Generic points of the dimension-`n` components of the original `V(J)`.
Minimality is proved below from the dimension bound, not assumed here. -/
def topDimensionalPrimes (J : Ideal R) (n : ℕ) : Set (PrimeSpectrum R) :=
  {p | J ≤ p.asIdeal ∧ ringKrullDim (R ⧸ p.asIdeal) = n}

/-- A prime of maximal finite dimension in a closed support is a minimal
prime of its defining ideal. A smaller prime would extend a length-`n` chain. -/
theorem topDimensionalPrimes_minimal (J : Ideal R) (n : ℕ)
    (hdim : Order.krullDim (PrimeSpectrum.zeroLocus (J : Set R)) ≤ n)
    {p : PrimeSpectrum R} (hp : p ∈ topDimensionalPrimes J n) :
    p.asIdeal ∈ J.minimalPrimes := by
  refine ⟨⟨p.isPrime, hp.1⟩, ?_⟩
  intro q hq hqp
  by_contra hpq
  have hqp' : (⟨q, hq.1⟩ : PrimeSpectrum R) < p := lt_of_le_not_ge hqp hpq
  have hd : (n : WithBot ℕ∞) ≤
      Order.krullDim (PrimeSpectrum.zeroLocus (p.asIdeal : Set R)) := by
    rw [← ringKrullDim_quotient, hp.2]
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hd
  let t : LTSeries (PrimeSpectrum.zeroLocus (J : Set R)) :=
    l.map (fun x => ⟨x.val, hp.1.trans x.property⟩) (fun _ _ h => h)
  have hqt : (⟨⟨q, hq.1⟩, hq.2⟩ : PrimeSpectrum.zeroLocus (J : Set R)) < t.head :=
    hqp'.trans_le l.head.property
  have hh := (Order.LTSeries.length_le_krullDim
    (t.cons ⟨⟨q, hq.1⟩, hq.2⟩ hqt)).trans hdim
  have hn : n + 1 ≤ n := by
    exact_mod_cast (show ((n + 1 : ℕ) : WithBot ℕ∞) ≤ n by simpa [t, hl] using hh)
  omega

/-- A finite support has the maximal allowed dimension exactly when it
contains the generic point of a top-dimensional component of `V(J)`.
The statement also covers zero modules and their bottom-valued dimension. -/
theorem supportDim_eq_iff_exists_topDimensionalPrime (J : Ideal R) (n : ℕ)
    (hdim : Order.krullDim (PrimeSpectrum.zeroLocus (J : Set R)) ≤ n)
    (M : ModuleCat.{u} R)
    (hM : Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    Module.supportDim R M = n ↔
      ∃ p ∈ topDimensionalPrimes J n, p ∈ Module.support R M := by
  have hle : Module.supportDim R M ≤ n :=
    (Order.krullDim_le_of_strictMono (fun p => ⟨p.val, hM p.property⟩)
      (fun _ _ h => h)).trans hdim
  constructor
  · intro he
    obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp he.ge
    let p : PrimeSpectrum R := l.head.val
    have hJp : J ≤ p.asIdeal := hM l.head.property
    have hpdim : ringKrullDim (R ⧸ p.asIdeal) = n := by
      rw [ringKrullDim_quotient]
      apply le_antisymm
      · exact (Order.krullDim_le_of_strictMono
          (fun q => ⟨q.val, hJp.trans q.property⟩) (fun _ _ h => h)).trans hdim
      · let t : LTSeries (PrimeSpectrum.zeroLocus (p.asIdeal : Set R)) :=
          LTSeries.mk l.length (fun i => ⟨(l i).val, l.head_le i⟩)
            (fun _ _ h => l.strictMono h)
        simpa only [t, LTSeries.mk_length, hl] using Order.LTSeries.length_le_krullDim t
    exact ⟨p, ⟨hJp, hpdim⟩, l.head.property⟩
  · rintro ⟨p, hp, hps⟩
    apply le_antisymm hle
    rw [← hp.2, ringKrullDim_quotient]
    exact Order.krullDim_le_of_strictMono
      (fun q => ⟨q.val, Module.mem_support_mono q.property hps⟩) (fun _ _ h => h)

end SGA.SGA2.ExposeV
