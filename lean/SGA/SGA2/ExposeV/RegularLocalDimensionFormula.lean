/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.HomologicalRegularityCriterion
import SGA.SGA2.ExposeV.TopLocalCohomologyAssociatedPrimes
import SGA.SGA2.ExposeV.LocalCohomologyFiniteLength

/-!
# The dimension formula for prime localizations of regular local rings

The already proved top-dual associated-prime formula forces complementary
Ext to be supported at each top-dimensional associated prime. Apply this to
`R/p`, then use original Ext localization and the residue-field comparison.
Since the local ring at `p` is now proved regular, its residue Ext is
concentrated in its own dimension. This identifies the complementary degree
and gives `dim R_p + dim R/p = dim R` without a catenarity assumption.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A top-dimensional associated prime of the actual coefficient module
lies in the support of complementary Ext. This uses original local duality
and the top-dual associated-prime formula, also over noncomplete rings. -/
theorem regularLocal_top_associated_mem_ext_support (n : ℕ)
    (hn : ringKrullDim R = n) (d j : ℕ) (hdj : d + j = n)
    (M : ModuleCat.{u} R) [Module.Finite R M] (hM : Module.supportDim R M = d)
    (p : PrimeSpectrum R) (hp : p ∈ associatedPrimeSpectrum (R := R) M)
    (hpd : ringKrullDim (R ⧸ p.asIdeal) = d) :
    p ∈ Module.support R (moduleExtValue M (ModuleCat.of R R) j) := by
  let H := (_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R)
  let L := (_root_.localCohomology (maximalIdeal R) d).obj M
  let E := moduleExtValue M (ModuleCat.of R R) j
  have hH : SupportedDualizingModule H := regularLocal_localCohomology_dualizing n hn
  have hpD : p ∈ associatedPrimeSpectrum (R := R) ((moduleHomDual H).obj (op L)) := by
    rw [localRing_topLocalCohomologyDual_associatedPrimeSpectrum d M H hH hM]
    exact ⟨hp, hpd⟩
  have hEL : Module.annihilator R E ≤ Module.annihilator R L := by
    rw [(regularLocal_localCohomologyHomIso n hn d j hdj M).toLinearEquiv.annihilator_eq]
    exact moduleHomDual_annihilator_le H E
  apply Module.mem_support_iff_of_finite.mpr
  exact hEL.trans ((moduleHomDual_annihilator_le H L).trans
    (Submodule.annihilator_top.symm.le.trans (IsAssociatedPrime.annihilator_le hpD)))

/-- Complementary Ext of `R/p` is nonzero at the original prime `p`. -/
theorem regularLocal_primeQuotient_ext_localization_nontrivial (n : ℕ)
    (hn : ringKrullDim R = n) (p : Ideal R) [p.IsPrime]
    (d j : ℕ) (hpd : ringKrullDim (R ⧸ p) = d) (hdj : d + j = n) :
    Nontrivial (LocalizedModule p.primeCompl
      (moduleExtValue (ModuleCat.of R (R ⧸ p)) (ModuleCat.of R R) j)) := by
  apply (Module.mem_support_iff (p := (⟨p, inferInstance⟩ : PrimeSpectrum R))).mp
  apply regularLocal_top_associated_mem_ext_support n hn d j hdj
    (ModuleCat.of R (R ⧸ p)) (by
      rw [Module.supportDim_quotient_eq_ringKrullDim]
      exact hpd) (⟨p, inferInstance⟩ : PrimeSpectrum R) _ hpd
  exact (isAssociatedPrime_iff_exists_injective_linearMap p (R ⧸ p)).mpr
    ⟨inferInstance, LinearMap.id, Function.injective_id⟩

/-- The actual local ring dimension is the degree complementary to the
dimension of the original prime quotient. -/
theorem regularLocal_atPrime_dimension_eq_complement (n : ℕ)
    (hn : ringKrullDim R = n) (p : Ideal R) [p.IsPrime]
    (d j : ℕ) (hpd : ringKrullDim (R ⧸ p) = d) (hdj : d + j = n) :
    ringKrullDim (Localization.AtPrime p) = j := by
  let Rp := Localization.AtPrime p
  have := regularLocal_atPrime_isRegularLocalRing p
  let s := (maximalIdeal Rp).spanFinrank
  have hs : ringKrullDim Rp = s := IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  suffices hjs : j = s by rw [hs, hjs]
  by_contra hjs
  let k := ModuleCat.of Rp (ResidueField Rp)
  have hk : IsFiniteLength Rp k := by
    change IsFiniteLength Rp (Rp ⧸ maximalIdeal Rp)
    exact (Ideal.quotientEquivAlgOfEq Rp (pow_one (maximalIdeal Rp))).toLinearEquiv.isFiniteLength
      (regularLocal_powerQuotient_isFiniteLength (R := Rp) 1)
  have hzero : IsZero (moduleExtValue k (ModuleCat.of Rp Rp) j) :=
    regularLocal_moduleExt_ring_isZero_of_finiteLength s hs k hk j hjs
  let e := (((_root_.Ext Rp (ModuleCat.{u} Rp) j).mapIso
    (localizedPrimeQuotientResidueFieldIso p).op).app (ModuleCat.of Rp Rp))
  have hlocalized : Subsingleton (LocalizedModule p.primeCompl
      (moduleExtValue (ModuleCat.of R (R ⧸ p)) (ModuleCat.of R R) j)) :=
    (localizedModule_ext_ring_subsingleton_iff p.primeCompl (ModuleCat.of R (R ⧸ p)) j).mpr
      (ModuleCat.isZero_iff_subsingleton.mp (hzero.of_iso e.symm))
  have := regularLocal_primeQuotient_ext_localization_nontrivial n hn p d j hpd hdj
  exact not_nontrivial_iff_subsingleton.mpr hlocalized inferInstance

/-- **V.3.5, dimension formula.** The dimensions of an actual prime
localization and the original prime quotient add to the ring dimension. -/
theorem regularLocal_atPrime_dimension_add_quotient (p : Ideal R) [p.IsPrime] :
    ringKrullDim (Localization.AtPrime p) + ringKrullDim (R ⧸ p) = ringKrullDim R := by
  let n := (maximalIdeal R).spanFinrank
  have hn : ringKrullDim R = n := IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  let : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let d := (LTSeries.longestOf (PrimeSpectrum (R ⧸ p))).length
  have hd : ringKrullDim (R ⧸ p) = d := Order.krullDim_eq_length_of_finiteDimensionalOrder
  have hdn : d ≤ n := by
    have h := ringKrullDim_quotient_le p
    rw [hd, hn] at h
    exact_mod_cast h
  rw [regularLocal_atPrime_dimension_eq_complement n hn p d (n - d) hd
    (Nat.add_sub_of_le hdn), hd, ← Nat.cast_add, Nat.sub_add_cancel hdn, hn]

/-- Natural-number dimensions of a prime localization and its quotient,
with the dimension formula ready for degree arithmetic. -/
theorem regularLocal_atPrime_dimensions (n : ℕ) (hn : ringKrullDim R = n)
    (p : Ideal R) [p.IsPrime] :
    ∃ s d : ℕ, ringKrullDim (Localization.AtPrime p) = s ∧
      ringKrullDim (R ⧸ p) = d ∧ s + d = n := by
  have := regularLocal_atPrime_isRegularLocalRing p
  let s := (maximalIdeal (Localization.AtPrime p)).spanFinrank
  have hs : ringKrullDim (Localization.AtPrime p) = s :=
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  let : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let d := (LTSeries.longestOf (PrimeSpectrum (R ⧸ p))).length
  have hd : ringKrullDim (R ⧸ p) = d :=
    Order.krullDim_eq_length_of_finiteDimensionalOrder
  refine ⟨s, d, hs, hd, ?_⟩
  have h := regularLocal_atPrime_dimension_add_quotient p
  rw [hs, hd, hn, ← Nat.cast_add] at h
  exact_mod_cast h

/-- The quotient-dimension bound and the complementary local-dimension
bound are equivalent. -/
theorem regularLocal_quotient_dimension_le_iff_atPrime
    (n : ℕ) (hn : ringKrullDim R = n) (i j : ℕ) (hij : i + j = n)
    (p : Ideal R) [p.IsPrime] :
    ringKrullDim (R ⧸ p) ≤ i ↔
      (j : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p) := by
  obtain ⟨s, d, hs, hd, hsd⟩ := regularLocal_atPrime_dimensions n hn p
  rw [hs, hd]
  norm_cast
  omega

end SGA.SGA2.ExposeV
