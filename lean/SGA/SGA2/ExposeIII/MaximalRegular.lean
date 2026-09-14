/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.DepthSupport

/-!
# SGA 2, Exposé III, Corollary 2.6: extending regular sequences

Every regular sequence extends to any finite length bounded by the depth.
Consequently, at finite depth it extends to a maximal sequence, whose length
equals the depth. At infinite depth every finite sequence can be extended.
The finite-depth qualification is necessary with SGA's regularity convention:
for example, sequences of units of arbitrary length are weakly regular.
-/

noncomputable section

universe u

open CategoryTheory RingTheory.Sequence

namespace SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A supplied regular sequence extends to every finite length allowed by depth. -/
theorem exists_regular_extension (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] (rs : List R) (hmem : ∀ r ∈ rs, r ∈ I)
    (hreg : IsWeaklyRegular M rs) (n : ℕ) (hlen : rs.length ≤ n)
    (hdepth : (n : ℕ∞) ≤ depth I M) :
    ∃ ts : List R, (rs ++ ts).length = n ∧ (∀ r ∈ ts, r ∈ I) ∧
      IsWeaklyRegular M (rs ++ ts) := by
  induction rs generalizing M n with
  | nil =>
    simpa using (le_depth_iff_exists_regular I M n).mp hdepth
  | cons f rs ih =>
    cases n with
    | zero => simp at hlen
    | succ n =>
      obtain ⟨hf, hrs⟩ := (isWeaklyRegular_cons_iff M f rs).mp hreg
      obtain ⟨ts, htslen, htsmem, htsreg⟩ :=
        ih (ModuleCat.of R (QuotSMulTop f M))
          (fun r hr ↦ hmem r (List.mem_cons_of_mem f hr)) hrs n
          (by simpa using hlen)
          ((succ_le_depth_iff I M (hmem f List.mem_cons_self) hf n).mp hdepth)
      exact ⟨ts, by simpa using htslen, htsmem, htsreg.cons hf⟩

/-- A regular sequence is maximal if no element of the ideal can be appended. -/
def IsMaximalRegularSequence (I : Ideal R) (M : ModuleCat.{u} R) (rs : List R) : Prop :=
  (∀ r ∈ rs, r ∈ I) ∧ IsWeaklyRegular M rs ∧
    ∀ r ∈ I, ¬ IsWeaklyRegular M (rs ++ [r])

/-- The length of any maximal regular sequence is the depth. -/
theorem depth_eq_length_of_maximal (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] (rs : List R) (h : IsMaximalRegularSequence I M rs) :
    depth I M = (rs.length : ℕ∞) := by
  apply le_antisymm _ (length_le_depth I M rs h.1 h.2.1)
  apply ENat.forall_natCast_le_iff_le.mp
  intro n hn
  apply ENat.natCast_le_natCast.mpr
  by_contra hlen
  have hs : (rs.length + 1 : ℕ) ≤ n := Nat.succ_le_of_lt (Nat.lt_of_not_ge hlen)
  obtain ⟨ts, htslen, htsmem, htsreg⟩ := exists_regular_extension I M rs h.1 h.2.1
    (rs.length + 1) (by omega) ((ENat.natCast_le_natCast.mpr hs).trans hn)
  have hts : ts.length = 1 := by simpa using htslen
  obtain ⟨r, rfl⟩ := List.length_eq_one_iff.mp hts
  exact h.2.2 r (htsmem r (by simp)) htsreg

omit [IsNoetherianRing R] in
/-- A regular sequence whose length is the depth cannot be extended. -/
theorem isMaximalRegularSequence_of_depth_eq_length (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsWeaklyRegular M rs)
    (hdepth : depth I M = (rs.length : ℕ∞)) : IsMaximalRegularSequence I M rs := by
  refine ⟨hmem, hreg, fun r hr hrs ↦ ?_⟩
  have hmem' : ∀ a ∈ rs ++ [r], a ∈ I := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hmem a ha
    · exact List.mem_singleton.mp ha ▸ hr
  have hle := length_le_depth I M (rs ++ [r]) hmem' hrs
  rw [hdepth] at hle
  have h := ENat.natCast_le_natCast.mp hle
  simp only [List.length_append, List.length_singleton] at h
  omega

/-- III.2.6 at finite depth: extend any supplied sequence to a maximal one. -/
theorem III_2_6 (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (n : ℕ) (hdepth : depth I M = (n : ℕ∞)) (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsWeaklyRegular M rs) :
    ∃ ts : List R, (rs ++ ts).length = n ∧ IsMaximalRegularSequence I M (rs ++ ts) := by
  have hlen : rs.length ≤ n := ENat.natCast_le_natCast.mp
    ((length_le_depth I M rs hmem hreg).trans_eq hdepth)
  obtain ⟨ts, htslen, htsmem, htsreg⟩ := exists_regular_extension I M rs hmem hreg n hlen
    hdepth.ge
  exact ⟨ts, htslen, isMaximalRegularSequence_of_depth_eq_length I M (rs ++ ts)
    (fun r hr ↦ (List.mem_append.mp hr).elim (hmem r) (htsmem r))
    htsreg (hdepth.trans (congrArg Nat.cast htslen.symm))⟩

/-- III.2.6–III.2.7: when the support meets `V(I)`, every regular sequence
extends to a maximal one, and its length is the depth. -/
theorem exists_maximalRegularSequence_of_support_nonempty (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hsupp : (Module.support R M ∩ PrimeSpectrum.zeroLocus (I : Set R)).Nonempty)
    (rs : List R) (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsWeaklyRegular M rs) :
    ∃ ts : List R, IsMaximalRegularSequence I M (rs ++ ts) ∧
      depth I M = ((rs ++ ts).length : ℕ∞) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ((III_2_7 I M).mpr hsupp).ne
  obtain ⟨ts, hlen, hmax⟩ := III_2_6 I M n hn.symm rs hmem hreg
  exact ⟨ts, hmax, depth_eq_length_of_maximal I M (rs ++ ts) hmax⟩

/-- At infinite depth, every finite regular sequence admits a further element. -/
theorem exists_regular_extension_of_depth_top (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] (hdepth : depth I M = ⊤) (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsWeaklyRegular M rs) :
    ∃ r ∈ I, IsWeaklyRegular M (rs ++ [r]) := by
  obtain ⟨ts, htslen, htsmem, htsreg⟩ := exists_regular_extension I M rs hmem hreg
    (rs.length + 1) (by omega) (by simp [hdepth])
  have hts : ts.length = 1 := by simpa using htslen
  obtain ⟨r, rfl⟩ := List.length_eq_one_iff.mp hts
  exact ⟨r, htsmem r (by simp), htsreg⟩

end SGA.SGA2.ExposeIII
