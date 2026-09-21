/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RegularLocalDimensionFormula
import SGA.SGA2.ExposeV.AffineComplementCodimension

/-!
# V.3.1: dimension and codimension of Ext support

The three conditions (a), (b), and (c) following formula (22) express the
same support bound. Over a regular local ring of dimension `n = i + j`,
a module has support dimension at most `i` precisely when its localizations
vanish at primes of height less than `j`, or equivalently its support has
codimension at least `j`. Localized Ext vanishing gives this bound for
`Ext^j(M, N)` when `M` is finite; `N` may be arbitrary.
-/

noncomputable section

universe u

open CategoryTheory Limits IsLocalRing

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R]

/-- Support dimension is bounded exactly when every prime quotient in the
support has bounded dimension. This includes the empty support. -/
theorem supportDim_le_iff_quotientDim_le (M : ModuleCat.{u} R) (d : WithBot ℕ∞) :
    Module.supportDim R M ≤ d ↔
      ∀ p ∈ Module.support R M, ringKrullDim (R ⧸ p.asIdeal) ≤ d := by
  constructor
  · intro h p hp
    rw [ringKrullDim_quotient]
    exact (Order.krullDim_le_of_strictMono
      (fun q ↦ ⟨q.val, Module.mem_support_mono q.property hp⟩)
      (fun _ _ h ↦ h)).trans h
  · intro h
    apply iSup_le
    intro l
    let t : LTSeries (PrimeSpectrum.zeroLocus (l.head.val.asIdeal : Set R)) :=
      LTSeries.mk l.length (fun i ↦ ⟨(l i).val, l.head_le i⟩)
        (fun _ _ h ↦ l.strictMono h)
    exact (Order.LTSeries.length_le_krullDim t).trans
      (by simpa only [← ringKrullDim_quotient] using h l.head.val l.head.property)

variable [IsRegularLocalRing R]

/-- Conditions (a) and (b) after V, formula (22). The statement applies
to any module, including zero, without a finite-generation hypothesis. -/
theorem regularLocal_supportDim_le_iff_localized_vanishing
    (n : ℕ) (hn : ringKrullDim R = n) (i j : ℕ) (hij : i + j = n)
    (M : ModuleCat.{u} R) :
    Module.supportDim R M ≤ i ↔
      ∀ p : PrimeSpectrum R, ringKrullDim (Localization.AtPrime p.asIdeal) < j →
        Subsingleton (LocalizedModule p.asIdeal.primeCompl M) := by
  rw [supportDim_le_iff_quotientDim_le]
  constructor
  · intro h p hp
    apply Module.notMem_support_iff.mp
    intro hps
    exact hp.not_ge
      ((regularLocal_quotient_dimension_le_iff_atPrime n hn i j hij p.asIdeal).mp (h p hps))
  · intro h p hp
    apply (regularLocal_quotient_dimension_le_iff_atPrime n hn i j hij p.asIdeal).mpr
    by_contra! hj
    exact (Module.notMem_support_iff.mpr (h p hj)) hp

/-- Conditions (a) and (c) after V, formula (22), with codimension
defined using the affine scheme's structure stalks. -/
theorem regularLocal_supportDim_le_iff_codimension_ge
    (n : ℕ) (hn : ringKrullDim R = n) (i j : ℕ) (hij : i + j = n)
    (M : ModuleCat.{u} R) :
    Module.supportDim R M ≤ i ↔
      (j : WithBot ℕ∞) ≤ affineSubsetCodimension (R := CommRingCat.of R) (Module.support R M) := by
  rw [supportDim_le_iff_quotientDim_le]
  erw [affineSubsetCodimension_eq_iInf_localization]
  simp only [le_iInf_iff]
  exact forall_congr' fun p ↦ forall_congr' fun _ ↦
    regularLocal_quotient_dimension_le_iff_atPrime n hn i j hij p.asIdeal

/-- Ext vanishes after localization at any prime whose height is below
its degree. Only the first Ext argument needs to be finite. -/
theorem regularLocal_ext_localized_subsingleton_of_lt
    (M N : ModuleCat.{u} R) [Module.Finite R M] (j : ℕ) (p : PrimeSpectrum R)
    (hp : ringKrullDim (Localization.AtPrime p.asIdeal) < j) :
    Subsingleton (LocalizedModule p.asIdeal.primeCompl (moduleExtValue M N j)) := by
  have := regularLocal_atPrime_isRegularLocalRing p.asIdeal
  let s := (maximalIdeal (Localization.AtPrime p.asIdeal)).spanFinrank
  have hs : ringKrullDim (Localization.AtPrime p.asIdeal) = s :=
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  rw [hs, Nat.cast_lt] at hp
  exact (localizedModule_ext_subsingleton_iff p.asIdeal.primeCompl M N j).mpr
    (ModuleCat.subsingleton_of_isZero
      (regularLocal_moduleExt_isZero_of_gt s hs _ _ j hp))

/-- The support of `Ext^j(M, N)` has codimension at least `j`, also
above the ring dimension, when it is empty. -/
theorem regularLocal_ext_supportCodimension_ge
    (M N : ModuleCat.{u} R) [Module.Finite R M] (j : ℕ) :
    (j : WithBot ℕ∞) ≤ affineSubsetCodimension (R := CommRingCat.of R)
      (Module.support R (moduleExtValue M N j)) := by
  erw [affineSubsetCodimension_eq_iInf_localization]
  apply le_iInf₂
  intro p hp
  by_contra! hj
  exact (Module.notMem_support_iff.mpr
    (regularLocal_ext_localized_subsingleton_of_lt M N j p hj)) hp

/-- **V.3.1(ii), Ext bound.** In complementary degree `j = n - i`,
Ext has support dimension at most `i`. The second argument is arbitrary. -/
theorem regularLocal_ext_supportDim_le
    (n : ℕ) (hn : ringKrullDim R = n) (i j : ℕ) (hij : i + j = n)
    (M N : ModuleCat.{u} R) [Module.Finite R M] :
    Module.supportDim R (moduleExtValue M N j) ≤ i :=
  (regularLocal_supportDim_le_iff_codimension_ge n hn i j hij _).mpr
    (regularLocal_ext_supportCodimension_ge M N j)

end SGA.SGA2.ExposeV
