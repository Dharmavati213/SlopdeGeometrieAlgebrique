/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulDegreeZero
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Parameters of the actual dimension over a noetherian local ring

The converse to Krull's height theorem produces an actual finite parameter
list. Its length is the ring's Krull dimension and its ideal has radical
equal to the original maximal ideal. Regularity is not assumed.
Passing to the actual annihilator quotient and lifting its parameter list
also produces parameters of the module's support dimension.
-/

noncomputable section
universe u
open IsLocalRing
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- If the local maximal ideal is minimal over an ideal, that ideal has
maximal radical: every prime over it lies below the unique maximal ideal. -/
theorem radical_eq_maximalIdeal_of_mem_minimalPrimes (I : Ideal R)
    (hI : maximalIdeal R ∈ I.minimalPrimes) : I.radical = maximalIdeal R := by
  rw [← Ideal.sInf_minimalPrimes]
  apply le_antisymm (sInf_le hI)
  apply le_sInf
  intro p hp
  exact hI.2 hp.1 (le_maximalIdeal hp.1.1.ne_top)

variable [IsNoetherianRing R]

/-- A noetherian local ring has an actual parameter list of its Krull
dimension, including the empty list in dimension zero. -/
theorem exists_localParameters (n : ℕ) (hdim : ringKrullDim R = n) :
    ∃ fs : List R, fs.length = n ∧ (koszulIdeal fs).radical = maximalIdeal R := by
  classical
  obtain ⟨s, hs, hcard⟩ :=
    (maximalIdeal R).exists_finset_card_eq_height_of_isNoetherianRing
  refine ⟨s.toList, ?_, ?_⟩
  · rw [Finset.length_toList]
    have hc : (s.card : WithBot ℕ∞) = n := by
      rw [← hdim, ← maximalIdeal_height_eq_ringKrullDim]
      exact_mod_cast hcard
    exact_mod_cast hc
  · simpa [koszulIdeal] using
      radical_eq_maximalIdeal_of_mem_minimalPrimes (Ideal.span (s : Set R)) hs

/-- Lift parameters of an actual quotient ring, retaining their length
and the original radical identity before passing to the quotient. -/
theorem exists_localParameters_modulo (I : Ideal R) (hI : I ≠ ⊤)
    (n : ℕ) (hdim : ringKrullDim (R ⧸ I) = n) :
    ∃ fs : List R, fs.length = n ∧ (koszulIdeal fs ⊔ I).radical = maximalIdeal R := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨gs, hlen, hrad⟩ := exists_localParameters n hdim
  obtain ⟨fs, hfs⟩ := (Ideal.Quotient.mk_surjective (I := I)).list_map gs
  refine ⟨fs, ?_, ?_⟩
  · simpa only [← hfs, List.length_map] using hlen
  · have hmap : (koszulIdeal fs).map (Ideal.Quotient.mk I) = koszulIdeal gs := by
      rw [← hfs]
      simp only [koszulIdeal, Ideal.map_span]
      congr 1
      ext x
      simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map]
    have hc := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hrad
    rw [maximalIdeal_comap, Ideal.comap_radical, ← hmap,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hc
    exact hc

/-- **V.3.1(i), module-parameter input.** A finite module of actual support
dimension `n` has `n` parameters modulo its original annihilator. Neither
regularity of the base nor a preselected parameter system is assumed. -/
theorem exists_moduleParameters (M : ModuleCat.{u} R) [Module.Finite R M]
    (n : ℕ) (hdim : Module.supportDim R M = n) :
    ∃ fs : List R, fs.length = n ∧
      (koszulIdeal fs ⊔ Module.annihilator R M).radical = maximalIdeal R := by
  have hI : Module.annihilator R M ≠ ⊤ := by
    intro h
    have : Subsingleton M := Module.annihilator_eq_top_iff.mp h
    have hb := Module.supportDim_eq_bot_of_subsingleton R M
    rw [hdim] at hb
    exact WithBot.coe_ne_bot hb
  exact exists_localParameters_modulo (Module.annihilator R M) hI n
    (by rwa [← Module.supportDim_eq_ringKrullDim_quotient_annihilator])

end SGA.SGA2.ExposeV
