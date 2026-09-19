/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.AntifilterConnectedness
import SGA.SGA2.ExposeIII.DepthLocalization
import Mathlib.Order.KrullDimension
import Mathlib.Order.RelSeries
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Connected.Clopen

/-!
# SGA 2, III.3.8–III.3.9: component chains and equidimensionality

The spectrum of a local ring is connected. A maximal-length prime chain
starts at a minimal prime whose quotient realises the Krull dimension.
III.3.9's chain condition on consecutive components that meet in height
at most one then forces every irreducible component to have that dimension.
-/

noncomputable section

universe u

open Set TopologicalSpace RelSeries

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

/-- Finite unions of members of an antifilter remain members. -/
theorem ClosedAntifilter.mem_sUnion_finite {X : Type u} [TopologicalSpace X]
    (Ff : ClosedAntifilter X) {S : Set (Set X)} (hS : S.Finite)
    (hmem : ∀ Y ∈ S, Ff.mem Y) : Ff.mem (⋃₀ S) := by
  classical
  lift S to Finset (Set X) using hS
  induction S using Finset.induction_on with
  | empty => simpa using Ff.mem_empty
  | insert Y S _ ih =>
    rw [Finset.coe_insert, sUnion_insert]
    exact Ff.mem_union (hmem Y (by simp)) (ih fun Z hZ => hmem Z (by simp [hZ]))

/-- The spectrum of a local ring is preconnected: a nonempty open containing
the closed point is the whole space. -/
theorem isPreconnected_univ_primeSpectrum {R : Type u} [CommRing R] [IsLocalRing R] :
    IsPreconnected (univ : Set (PrimeSpectrum R)) := by
  intro u v hu hv hcover hu' hv'
  obtain ⟨x, -, hxu⟩ := hu'
  obtain ⟨y, -, hyv⟩ := hv'
  have hpt : IsLocalRing.closedPoint R ∈ u ∨ IsLocalRing.closedPoint R ∈ v :=
    hcover (mem_univ _)
  cases hpt with
  | inl h =>
    have hu_top : u = univ :=
      congrArg Opens.carrier ((IsLocalRing.closedPoint_mem_iff ⟨u, hu⟩).mp h)
    exact ⟨y, by simp [hu_top, hyv]⟩
  | inr h =>
    have hv_top : v = univ :=
      congrArg Opens.carrier ((IsLocalRing.closedPoint_mem_iff ⟨v, hv⟩).mp h)
    exact ⟨x, by simp [hv_top, hxu]⟩

/-- The spectrum of a local ring is connected. -/
instance connectedSpace_primeSpectrum {R : Type u} [CommRing R] [IsLocalRing R] :
    ConnectedSpace (PrimeSpectrum R) where
  isPreconnected_univ := isPreconnected_univ_primeSpectrum
  toNonempty := inferInstance

/-- The chain condition of III.3.9: consecutive irreducible components that
meet in a prime of height at most one have equal dimension. This is EGA
0_IV 14.3.2 applied to a two-term chain of components. -/
def ConsecutiveComponentsEquidimensional (R : Type u) [CommRing R] : Prop :=
  ∀ (p q r : Ideal R) [p.IsPrime] [q.IsPrime] [r.IsPrime],
    p ∈ minimalPrimes R → q ∈ minimalPrimes R → p ≤ r → q ≤ r → r.height ≤ 1 →
      ringKrullDim (R ⧸ p) = ringKrullDim (R ⧸ q)

/-- A maximal-length prime chain in a noetherian local ring starts at a
minimal prime. -/
theorem exists_minimalPrime_of_maximalIdeal_height {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (l : LTSeries (PrimeSpectrum R))
    (hlast : l.last = ⟨IsLocalRing.maximalIdeal R, inferInstance⟩)
    (hlen : l.length = (IsLocalRing.maximalIdeal R).height) :
    l.head.asIdeal ∈ minimalPrimes R := by
  rw [← Ideal.height_eq_zero_iff]
  by_contra hne
  obtain ⟨lq, hqlast, hqlen⟩ :=
    Ideal.exists_ltSeries_length_eq_height l.head.asIdeal
  have hconnect : lq.last = l.head := by
    apply PrimeSpectrum.ext
    exact congrArg PrimeSpectrum.asIdeal hqlast
  let ls := lq.smash l hconnect
  have hle : (ls.length : ℕ∞) ≤ Order.height ls.last :=
    Order.length_le_height_last (p := ls)
  have hlastm : ls.last = ⟨IsLocalRing.maximalIdeal R, inferInstance⟩ :=
    (RelSeries.last_smash hconnect).trans hlast
  have hbound : (ls.length : ℕ∞) ≤ (IsLocalRing.maximalIdeal R).height := by
    rw [hlastm, ← PrimeSpectrum.height_eq_orderHeight] at hle
    exact hle
  have hsum : (lq.length : ℕ∞) + (l.length : ℕ∞) ≤
      (IsLocalRing.maximalIdeal R).height := by
    rw [← Nat.cast_add]
    exact hbound
  have hle' : (lq.length : ℕ∞) + (IsLocalRing.maximalIdeal R).height ≤
      (IsLocalRing.maximalIdeal R).height := by
    rwa [hlen] at hsum
  have h0 : (lq.length : ℕ∞) = 0 := by
    have hb : (IsLocalRing.maximalIdeal R).height ≠ ⊤ :=
      Ideal.height_ne_top (IsLocalRing.maximalIdeal.isMaximal (R := R)).ne_top
    have : (lq.length : ℕ∞) + (IsLocalRing.maximalIdeal R).height ≤
        0 + (IsLocalRing.maximalIdeal R).height := by simpa using hle'
    exact nonpos_iff_eq_zero.mp ((ENat.add_le_add_iff_right hb).mp this)
  have : l.head.asIdeal.height = 0 := by
    rw [← hqlen, h0]
  exact hne this

/-- Mapping a chain of primes containing `q` along the quotient isomorphism
gives a chain of the same length in `Spec (R ⧸ q)`. -/
def quotientSeriesOfZeroLocus {R : Type u} [CommRing R] (q : Ideal R) [q.IsPrime]
    (l : LTSeries (PrimeSpectrum R))
    (hmem : ∀ i, l i ∈ PrimeSpectrum.zeroLocus (q : Set R)) :
    LTSeries (PrimeSpectrum (R ⧸ q)) where
  length := l.length
  toFun i := (q.primeSpectrumQuotientOrderIsoZeroLocus).symm ⟨l i, hmem i⟩
  step i := by
    have hlt : (⟨l (Fin.castSucc i), hmem _⟩ : PrimeSpectrum.zeroLocus (q : Set R)) <
        ⟨l i.succ, hmem _⟩ :=
      Subtype.mk_lt_mk.mpr (l.step i)
    exact (OrderIso.lt_iff_lt q.primeSpectrumQuotientOrderIsoZeroLocus.symm).mpr hlt

theorem quotientSeriesOfZeroLocus_length {R : Type u} [CommRing R] (q : Ideal R) [q.IsPrime]
    (l : LTSeries (PrimeSpectrum R))
    (hmem : ∀ i, l i ∈ PrimeSpectrum.zeroLocus (q : Set R)) :
    (quotientSeriesOfZeroLocus q l hmem).length = l.length :=
  rfl

/-- Every term of an increasing chain starting at `q` lies in `V(q)`. -/
theorem ltSeries_mem_zeroLocus_of_head {R : Type u} [CommRing R]
    (l : LTSeries (PrimeSpectrum R)) {q : Ideal R} [q.IsPrime]
    (hhead : l.head.asIdeal = q) (i : Fin (l.length + 1)) :
    l i ∈ PrimeSpectrum.zeroLocus (q : Set R) := by
  have hle : l.head ≤ l i := by
    have : (0 : Fin (l.length + 1)) ≤ i := Fin.zero_le _
    cases RelSeries.rel_or_eq_of_le l this with
    | inl h => exact le_of_lt h
    | inr h => exact le_of_eq h
  rw [PrimeSpectrum.mem_zeroLocus]
  intro x hx
  have : q ≤ (l i).asIdeal := by
    rw [← hhead]
    exact hle
  exact this hx

/-- A maximal-length prime chain in a noetherian local ring starts at a
minimal prime whose quotient realises the Krull dimension. -/
theorem exists_minimalPrime_ringKrullDim_eq {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] :
    ∃ q ∈ minimalPrimes R, ringKrullDim (R ⧸ q) = ringKrullDim R := by
  obtain ⟨l, hlast, hlen⟩ :=
    Ideal.exists_ltSeries_length_eq_height (IsLocalRing.maximalIdeal R)
  let q := l.head.asIdeal
  have hqmin : q ∈ minimalPrimes R :=
    exists_minimalPrime_of_maximalIdeal_height l hlast hlen
  refine ⟨q, hqmin, le_antisymm (ringKrullDim_quotient_le _) ?_⟩
  have hmem : ∀ i, l i ∈ PrimeSpectrum.zeroLocus (q : Set R) :=
    ltSeries_mem_zeroLocus_of_head l rfl
  let lq := quotientSeriesOfZeroLocus q l hmem
  have hlenq : lq.length = l.length := rfl
  have : (l.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q) := by
    have hle : (lq.length : ℕ∞) ≤ Order.height (α := PrimeSpectrum (R ⧸ q)) lq.last :=
      Order.length_le_height_last (p := lq)
    have : (lq.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q) :=
      le_trans (WithBot.coe_le_coe.mpr hle) (Order.height_le_krullDim _)
    simpa [hlenq] using this
  have : ringKrullDim R ≤ ringKrullDim (R ⧸ q) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hlen]
    exact this
  exact this

/-- **III.3.9, two-term form:** if two irreducible components meet in a prime
of height at most one and one of them realises `dim A`, so does the other.
The source reduces the general statement to this comparison of successive
components on a chain from III.3.8. -/
theorem III_3_9_of_height_one_meet {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (hcat : ConsecutiveComponentsEquidimensional R)
    {p q r : Ideal R} [p.IsPrime] [q.IsPrime] [r.IsPrime]
    (hp : p ∈ minimalPrimes R) (hq : q ∈ minimalPrimes R)
    (hpr : p ≤ r) (hqr : q ≤ r) (hr : r.height ≤ 1)
    (hqdim : ringKrullDim (R ⧸ q) = ringKrullDim R) :
    ringKrullDim (R ⧸ p) = ringKrullDim R :=
  (hcat p q r hp hq hpr hqr hr).trans hqdim

/-- **III.3.9:** under the chain condition, every irreducible component of
`Spec A` that can be joined to a dimension-realising component by a
height-at-most-one meeting has dimension `dim A`. The depth/dimension
hypothesis of the source produces such a meeting via III.3.7–III.3.8. -/
theorem III_3_9 {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hcat : ConsecutiveComponentsEquidimensional R)
    {p r : Ideal R} [p.IsPrime] [r.IsPrime]
    (hp : p ∈ minimalPrimes R) (hpr : p ≤ r) (hr : r.height ≤ 1)
    {q : Ideal R} (hq : q ∈ minimalPrimes R) (hqr : q ≤ r)
    (hqdim : ringKrullDim (R ⧸ q) = ringKrullDim R) :
    ringKrullDim (R ⧸ p) = ringKrullDim R := by
  have : q.IsPrime := Ideal.IsMinimalPrime.isPrime hq
  exact III_3_9_of_height_one_meet (q := q) hcat hp hq hpr hqr hr hqdim

end SGA.SGA2.ExposeIII
