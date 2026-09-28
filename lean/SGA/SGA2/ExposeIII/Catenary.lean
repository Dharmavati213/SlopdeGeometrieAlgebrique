/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.Equidimensionality

/-!
# The chain condition and adjacent components

The chain condition says that saturated prime chains with the same
endpoints have equal lengths. In a noetherian local ring it implies that
minimal primes which meet at a prime of height at most one have quotients
of the same dimension. This supplies the chain-condition step of III.3.9.
-/

noncomputable section

universe u

open Set Order TopologicalSpace RelSeries

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

/-- A chain with no elements insertable between consecutive terms. -/
abbrev SaturatedChain (α : Type*) [PartialOrder α] :=
  RelSeries {(a, b) : α × α | a ⋖ b}

/-- Catenarity: saturated chains with fixed endpoints have equal lengths. -/
def CatenaryOrder (α : Type*) [PartialOrder α] : Prop :=
  ∀ s t : SaturatedChain α, s.head = t.head → s.last = t.last → s.length = t.length

/-- The chain condition on the prime ideals of a ring. -/
def SatisfiesChainCondition (R : Type u) [CommRing R] : Prop :=
  CatenaryOrder (PrimeSpectrum R)

/-- A finite-dimensional order with a largest element admits a saturated
chain from any element to the largest one that realizes its coheight. -/
theorem exists_saturatedChain_coheight {α : Type*} [PartialOrder α]
    [OrderTop α] [FiniteDimensionalOrder α] (a : α) :
    ∃ s : SaturatedChain α, s.head = a ∧ s.last = ⊤ ∧
      (s.length : ℕ∞) = Order.coheight a := by
  let : WellFoundedLT α :=
    ⟨SetRel.IsWellFounded.of_finiteDimensional {(a, b) : α × α | a < b}⟩
  let : WellFoundedGT α :=
    ⟨SetRel.IsWellFounded.inv_of_finiteDimensional {(a, b) : α × α | a < b}⟩
  obtain ⟨n, hn'⟩ := ENat.ne_top_iff_exists.mp (Order.coheight_lt_top a).ne
  have hn : Order.coheight a = (n : ℕ∞) := hn'.symm
  obtain ⟨l, hhead, hlen⟩ := Order.exists_series_of_coheight_eq_coe a hn
  have hlast : l.last = ⊤ := by
    by_contra hne
    have hbound := Order.length_le_coheight (p := l.snoc ⊤ (lt_top_iff_ne_top.mpr hne))
      (by simpa using le_of_eq hhead.symm)
    simp only [RelSeries.snoc_length, hlen, hn, Nat.cast_add, Nat.cast_one] at hbound
    have : n + 1 ≤ n := by exact_mod_cast hbound
    omega
  obtain ⟨s, i, hsi, hihead, hilast⟩ := l.exists_relSeries_covBy
  have hshead : s.head = a := by
    exact (congrArg s hihead.symm).trans ((congrFun hsi 0).trans hhead)
  have hslast : s.last = ⊤ := by
    exact (congrArg s hilast.symm).trans ((congrFun hsi (Fin.last _)).trans hlast)
  have hle : l.length ≤ s.length := by
    have := Fintype.card_le_of_injective i i.injective
    simpa only [Fintype.card_fin, Nat.add_le_add_iff_right] using this
  refine ⟨s, hshead, hslast, le_antisymm ?_ ?_⟩
  · exact Order.length_le_coheight (p := s.ofLE fun _ h => h.lt)
      (le_of_eq hshead.symm)
  · rw [hn, ← hlen]
    exact_mod_cast hle

/-- Under the chain condition, every saturated chain ending at the largest
element realizes the coheight of its first term. -/
theorem saturatedChain_length_eq_coheight {α : Type*} [PartialOrder α]
    [OrderTop α] [FiniteDimensionalOrder α] (hcat : CatenaryOrder α)
    (s : SaturatedChain α) (hlast : s.last = ⊤) :
    (s.length : ℕ∞) = Order.coheight s.head := by
  obtain ⟨t, hthead, htlast, htlen⟩ := exists_saturatedChain_coheight s.head
  rw [hcat s t hthead.symm (hlast.trans htlast.symm)]
  exact htlen

/-- A point of height at most one covers every strictly smaller point. -/
theorem covBy_of_height_le_one {α : Type*} [PartialOrder α] {a b : α}
    (hab : a < b) (hb : Order.height b ≤ 1) : a ⋖ b := by
  refine ⟨hab, ?_⟩
  intro c hac hcb
  exact (not_lt_of_ge hb) (Order.one_lt_height_iff.mpr ⟨c, a, hac, hcb⟩)

/-- Minimal elements meeting below height two have the same coheight in a
finite-dimensional catenary order with a largest element. -/
theorem coheight_eq_of_common_height_one {α : Type*} [PartialOrder α]
    [OrderTop α] [FiniteDimensionalOrder α] (hcat : CatenaryOrder α)
    {a b c : α} (ha : IsMin a) (hb : IsMin b) (hac : a ≤ c) (hbc : b ≤ c)
    (hc : Order.height c ≤ 1) : Order.coheight a = Order.coheight b := by
  by_cases hab : a = b
  · rw [hab]
  have hac' : a < c := lt_of_le_of_ne hac fun h =>
    hab (le_antisymm (ha (h ▸ hbc)) (h ▸ hbc))
  have hbc' : b < c := lt_of_le_of_ne hbc fun h =>
    hab (le_antisymm (h ▸ hac) (hb (h ▸ hac)))
  obtain ⟨s, hshead, hslast, _⟩ := exists_saturatedChain_coheight c
  let sa := s.cons a (hshead ▸ covBy_of_height_le_one hac' hc)
  let sb := s.cons b (hshead ▸ covBy_of_height_le_one hbc' hc)
  have hla := saturatedChain_length_eq_coheight hcat sa (by simpa [sa] using hslast)
  have hlb := saturatedChain_length_eq_coheight hcat sb (by simpa [sb] using hslast)
  exact hla.symm.trans hlb

/-- The dimension of a prime quotient is the coheight of that prime. -/
theorem ringKrullDim_quotient_eq_coheight {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] :
    ringKrullDim (R ⧸ p) = (Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum R) :
      WithBot ℕ∞) := by
  change Order.krullDim (PrimeSpectrum (R ⧸ p)) = _
  rw [Order.krullDim_eq_of_orderIso p.primeSpectrumQuotientOrderIsoZeroLocus]
  exact (Order.coheight_eq_krullDim_Ici (⟨p, inferInstance⟩ : PrimeSpectrum R)).symm

/-- The genuine chain condition implies the adjacent-component comparison
used in the proof of III.3.9. -/
theorem consecutiveComponentsEquidimensional_of_chainCondition {R : Type u}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hcat : SatisfiesChainCondition R) : ConsecutiveComponentsEquidimensional R := by
  intro p q r hp' hq' hr' hp hq hpr hqr hr
  rw [ringKrullDim_quotient_eq_coheight, ringKrullDim_quotient_eq_coheight]
  congr 1
  apply coheight_eq_of_common_height_one hcat (c := (⟨r, hr'⟩ : PrimeSpectrum R))
    (PrimeSpectrum.isMin_iff.mpr hp) (PrimeSpectrum.isMin_iff.mpr hq) hpr hqr
  simpa only [← PrimeSpectrum.height_eq_orderHeight] using hr

end SGA.SGA2.ExposeIII
