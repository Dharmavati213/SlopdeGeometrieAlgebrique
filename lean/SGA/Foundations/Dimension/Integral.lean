/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Krull dimension and integral extensions

Let `R → S` be an integral ring map. Contraction of primes `Spec S → Spec R` is strictly
monotone (incomparability), and it lifts chains upwards (going up). Hence

* `ringKrullDim S ≤ ringKrullDim R`, with equality if `R → S` is injective
  (`ringKrullDim_eq_of_isIntegral`), by going up and incomparability;
* `dim S/P = dim R/(P ∩ R)` for every prime `P` of `S` (`ringKrullDim_quotient_eq_of_isIntegral`);
* `ht P ≤ ht (P ∩ R)`, with equality if going down also holds, e.g. if `S` is a domain and `R`
  is integrally closed (`Ideal.height_eq_height_under_of_hasGoingDown`).

We also record the order-theoretic description `dim R/p = coheight p` of the dimension of the
quotient by a prime (`ringKrullDim_quotient_eq_coheight`), and the elementary inequality
`ht p + dim R/p ≤ dim R` (`Ideal.height_add_ringKrullDim_quotient_le`).
-/

open Order

/-- `height a + coheight a ≤ dim α`: a chain ending at `a` and a chain starting at `a` can be
concatenated. -/
theorem Order.height_add_coheight_le_krullDim {α : Type*} [Preorder α] (a : α) :
    ((height a + coheight a : ℕ∞) : WithBot ℕ∞) ≤ krullDim α := by
  have : Nonempty α := ⟨a⟩
  rw [krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
  exact le_iSup (fun b : α ↦ height b + coheight b) a

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace PrimeSpectrum

/-- The coheight of a point `p` of `Spec R` is the Krull dimension of `R ⧸ p`. -/
theorem coheight_eq_ringKrullDim_quotient (p : PrimeSpectrum R) :
    (coheight p : WithBot ℕ∞) = ringKrullDim (R ⧸ p.asIdeal) := by
  rw [ringKrullDim_quotient, coheight_eq_krullDim_Ici]
  have : (zeroLocus (p.asIdeal : Set R)) = Set.Ici p := by
    ext q
    simp [mem_zeroLocus, SetLike.coe_subset_coe, ← PrimeSpectrum.asIdeal_le_asIdeal]
  rw [this]

/-- Incomparability: the contraction of primes along an integral ring map is strictly
monotone. -/
theorem comap_strictMono_of_isIntegral [Algebra.IsIntegral R S] :
    StrictMono (comap (algebraMap R S)) := fun P Q h ↦
  Ideal.IsIntegral.comap_lt_comap (R := R) (A := S) (I := P.asIdeal) (J := Q.asIdeal) h

theorem height_le_height_comap_of_isIntegral [Algebra.IsIntegral R S] (P : PrimeSpectrum S) :
    height P ≤ height (comap (algebraMap R S) P) :=
  height_le_height_apply_of_strictMono _ comap_strictMono_of_isIntegral P

theorem coheight_le_coheight_comap_of_isIntegral [Algebra.IsIntegral R S] (P : PrimeSpectrum S) :
    coheight P ≤ coheight (comap (algebraMap R S) P) :=
  coheight_le_coheight_apply_of_strictMono _ comap_strictMono_of_isIntegral P

/-- Going up lifts every chain of primes starting at `P ∩ R` to a chain starting at `P`. -/
theorem coheight_comap_le_coheight_of_hasGoingUp [Algebra.HasGoingUp R S] (P : PrimeSpectrum S) :
    coheight (comap (algebraMap R S) P) ≤ coheight P := by
  refine coheight_le fun l hl ↦ ?_
  have : P.asIdeal.LiesOver l.head.asIdeal := ⟨by rw [hl]; rfl⟩
  obtain ⟨L, hlen, hhead, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
  rw [← hlen]
  exact length_le_coheight (le_of_eq (by rw [hhead]))

/-- Going down lifts every chain of primes ending at `P ∩ R` to a chain ending at `P`. -/
theorem height_comap_le_height_of_hasGoingDown [Algebra.HasGoingDown R S] (P : PrimeSpectrum S) :
    height (comap (algebraMap R S) P) ≤ height P := by
  refine height_le fun l hl ↦ ?_
  have : P.asIdeal.LiesOver l.last.asIdeal := ⟨by rw [hl]; rfl⟩
  obtain ⟨L, hlen, hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P.asIdeal
  rw [← hlen]
  exact length_le_height (le_of_eq (by rw [hlast]))

theorem coheight_comap_of_isIntegral [Algebra.IsIntegral R S] (P : PrimeSpectrum S) :
    coheight (comap (algebraMap R S) P) = coheight P :=
  le_antisymm (coheight_comap_le_coheight_of_hasGoingUp P)
    (coheight_le_coheight_comap_of_isIntegral P)

theorem height_comap_of_isIntegral_of_hasGoingDown [Algebra.IsIntegral R S]
    [Algebra.HasGoingDown R S] (P : PrimeSpectrum S) :
    height (comap (algebraMap R S) P) = height P :=
  le_antisymm (height_comap_le_height_of_hasGoingDown P) (height_le_height_comap_of_isIntegral P)

end PrimeSpectrum

open PrimeSpectrum

/-- The Krull dimension of the quotient by a prime `p` is the coheight of `p` in `Spec R`. -/
theorem ringKrullDim_quotient_eq_coheight (p : Ideal R) [p.IsPrime] :
    ringKrullDim (R ⧸ p) = coheight (⟨p, ‹_›⟩ : PrimeSpectrum R) :=
  (coheight_eq_ringKrullDim_quotient ⟨p, ‹_›⟩).symm

/-- `ht p + dim R/p ≤ dim R` for every prime `p`: a chain ending at `p` and a chain starting at
`p` can be concatenated. -/
theorem Ideal.height_add_ringKrullDim_quotient_le (p : Ideal R) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  rw [ringKrullDim_quotient_eq_coheight,
    show p.height = Order.height (⟨p, ‹_›⟩ : PrimeSpectrum R) from
      height_eq_orderHeight ⟨p, ‹_›⟩, ← WithBot.coe_add]
  exact Order.height_add_coheight_le_krullDim _

/-- The Krull dimension does not increase along an integral ring map. -/
theorem ringKrullDim_le_of_isIntegral [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R :=
  krullDim_le_of_strictMono _ comap_strictMono_of_isIntegral

/-- The Krull dimension is invariant under integral extensions (going up and incomparability). -/
theorem ringKrullDim_eq_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R := by
  refine le_antisymm ringKrullDim_le_of_isIntegral (iSup_le fun l ↦ ?_)
  obtain ⟨Q, -, hQ, hQl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal S)
    (by simp [← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)])
  have : Q.LiesOver l.head.asIdeal := ⟨hQl.symm⟩
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
  rw [← hlen]
  exact L.length_le_krullDim

/-- For a prime `P` of an integral `R`-algebra `S`, `dim S/P = dim R/(P ∩ R)`. -/
theorem ringKrullDim_quotient_eq_of_isIntegral [Algebra.IsIntegral R S] (P : Ideal S)
    [P.IsPrime] : ringKrullDim (S ⧸ P) = ringKrullDim (R ⧸ P.under R) := by
  rw [ringKrullDim_quotient_eq_coheight, ringKrullDim_quotient_eq_coheight]
  exact congrArg _ (coheight_comap_of_isIntegral (⟨P, ‹_›⟩ : PrimeSpectrum S)).symm

/-- For a prime `P` of an integral `R`-algebra `S`, `ht P ≤ ht (P ∩ R)`. -/
theorem Ideal.height_le_height_under_of_isIntegral [Algebra.IsIntegral R S] (P : Ideal S)
    [P.IsPrime] : P.height ≤ (P.under R).height := by
  have h := height_le_height_comap_of_isIntegral (R := R) (⟨P, ‹_›⟩ : PrimeSpectrum S)
  rwa [← height_eq_orderHeight, ← height_eq_orderHeight] at h

/-- For a prime `P` of an `R`-algebra `S` with going down, `ht (P ∩ R) ≤ ht P`. -/
theorem Ideal.height_under_le_height_of_hasGoingDown [Algebra.HasGoingDown R S] (P : Ideal S)
    [P.IsPrime] : (P.under R).height ≤ P.height := by
  have h := height_comap_le_height_of_hasGoingDown (R := R) (⟨P, ‹_›⟩ : PrimeSpectrum S)
  rwa [← height_eq_orderHeight, ← height_eq_orderHeight] at h

/-- For a prime `P` of an integral `R`-algebra `S` with going down (for example `S` a domain,
integral over the integrally closed subring `R`), `ht P = ht (P ∩ R)`. -/
theorem Ideal.height_eq_height_under_of_hasGoingDown [Algebra.IsIntegral R S]
    [Algebra.HasGoingDown R S] (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height :=
  le_antisymm (P.height_le_height_under_of_isIntegral) (P.height_under_le_height_of_hasGoingDown)
