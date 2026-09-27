/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.KrullDimension.Regular
import SGA.SGA2.ExposeIII.MaximalRegular

/-!
# Depth of a module

The `I`-depth of an `R`-module `M` is the supremum of the lengths of `M`-regular sequences
(in the weak sense, `RingTheory.Sequence.IsWeaklyRegular`) with members in `I`
(Stacks 00LF, 0AUK). With this convention a module with `I • M = M`, e.g. `M = 0`, has infinite
depth.

## Main results

* `Ideal.le_depth_iff`: `n ≤ depth_I M` iff there is an `M`-regular sequence of length `n` in `I`.
* `Ideal.depth_eq_extDepth`: over a noetherian ring and for a finite module, the depth is the
  first degree in which `Ext^i(R/I, M)` does not vanish (Rees; Stacks 0AUM). This is where the
  Ext-theoretic depth of SGA 2, Exposé III is used.
* `Ideal.depth_quotSMulTop_add_one`: `depth_I (M/xM) + 1 = depth_I M` for an `M`-regular `x ∈ I`
  (Stacks 00LE).
* `IsLocalRing.depth_le_supportDim`: over a noetherian local ring, the depth of a nonzero finite
  module is at most its dimension (Stacks 0AUI), hence finite.
-/

universe u v

open IsLocalRing RingTheory.Sequence CategoryTheory

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/-- The `I`-depth of a module `M`: the supremum of the lengths of `M`-regular sequences (in the
weak sense) with members in `I` (Stacks 00LF). -/
noncomputable def depth : ℕ∞ :=
  ⨆ (rs : List R) (_ : ∀ r ∈ rs, r ∈ I) (_ : IsWeaklyRegular M rs), (rs.length : ℕ∞)

variable {I M}

theorem length_le_depth {rs : List R} (hmem : ∀ r ∈ rs, r ∈ I) (hrs : IsWeaklyRegular M rs) :
    (rs.length : ℕ∞) ≤ I.depth M :=
  le_iSup_of_le rs (le_iSup_of_le hmem (le_iSup_of_le hrs le_rfl))

variable (I M) in
theorem le_depth_iff (n : ℕ) : (n : ℕ∞) ≤ I.depth M ↔
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsWeaklyRegular M rs := by
  refine ⟨fun h ↦ ?_, fun ⟨rs, hlen, hmem, hrs⟩ ↦ hlen ▸ length_le_depth hmem hrs⟩
  obtain _ | n := n
  · exact ⟨[], rfl, by simp, IsWeaklyRegular.nil R M⟩
  obtain ⟨rs, hrs⟩ := lt_iSup_iff.mp
    (lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self n)) h)
  obtain ⟨hmem, hrs⟩ := lt_iSup_iff.mp hrs
  obtain ⟨hreg, hlt⟩ := lt_iSup_iff.mp hrs
  have hle : n + 1 ≤ rs.length := ENat.natCast_lt_natCast.mp hlt
  refine ⟨rs.take (n + 1), by simp [hle], fun r hr ↦ hmem r (List.mem_of_mem_take hr), ?_⟩
  rw [← List.take_append_drop (n + 1) rs, isWeaklyRegular_append_iff] at hreg
  exact hreg.1

theorem depth_eq_top_iff : I.depth M = ⊤ ↔
    ∀ n : ℕ, ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsWeaklyRegular M rs := by
  simp_rw [← le_depth_iff]
  exact ⟨fun h n ↦ h ▸ le_top, fun h ↦ ENat.eq_top_iff_forall_ge.mpr h⟩

theorem depth_mono {J : Ideal R} (hIJ : I ≤ J) : I.depth M ≤ J.depth M :=
  iSup_mono fun _ ↦ iSup_mono' fun hmem ↦ ⟨fun r hr ↦ hIJ (hmem r hr), le_rfl⟩

theorem depth_eq_of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    I.depth M = I.depth N := by
  simp only [depth, e.isWeaklyRegular_congr]

/-- Prepending a regular element: `depth_I (M/xM) + 1 ≤ depth_I M`. -/
theorem depth_quotSMulTop_add_one_le {x : R} (hx : x ∈ I) (hreg : IsSMulRegular M x) :
    I.depth (QuotSMulTop x M) + 1 ≤ I.depth M := by
  apply ENat.forall_natCast_le_iff_le.mp
  intro n hn
  obtain _ | n := n
  · exact zero_le
  have : (n : ℕ∞) ≤ I.depth (QuotSMulTop x M) := by
    have h1 : ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
    rw [h1] at hn
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp hn
  obtain ⟨rs, hlen, hmem, hrs⟩ := (le_depth_iff I _ n).mp this
  exact (le_depth_iff I M (n + 1)).mpr
    ⟨x :: rs, by simp [hlen], by simpa using ⟨hx, hmem⟩, hrs.cons hreg⟩

/-- `1 ≤ depth_I M` iff some element of `I` is `M`-regular. -/
theorem one_le_depth_iff : 1 ≤ I.depth M ↔ ∃ x ∈ I, IsSMulRegular M x := by
  rw [← Nat.cast_one, le_depth_iff]
  constructor
  · rintro ⟨rs, hlen, hmem, hrs⟩
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact ⟨x, hmem x (by simp), (isWeaklyRegular_singleton_iff M x).mp hrs⟩
  · rintro ⟨x, hx, hreg⟩
    exact ⟨[x], rfl, by simpa using hx, (isWeaklyRegular_singleton_iff M x).mpr hreg⟩

section Noetherian

variable {M : Type u} [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M]

/-- The depth by regular sequences agrees with the Ext-theoretic depth of SGA 2, III.2.3
(for a finite module over a noetherian ring). -/
theorem depth_eq_sga2Depth :
    I.depth M = SGA.SGA2.ExposeIII.depth I (ModuleCat.of R M) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [le_depth_iff, SGA.SGA2.ExposeIII.le_depth_iff_exists_regular]

/-- Rees: over a noetherian ring, `n ≤ depth_I M` iff `Ext^i(N, M) = 0` for `i < n`, for any
finite module `N` with support `V(I)` (Stacks 0AUM). -/
theorem le_depth_iff_ext (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) (n : ℕ) :
    (n : ℕ∞) ≤ I.depth M ↔
      ∀ i < n, Subsingleton (Abelian.Ext (ModuleCat.of R N) (ModuleCat.of R M) i) := by
  rw [depth_eq_sga2Depth]
  exact SGA.SGA2.ExposeIII.le_depth_iff_ext_vanishes I (ModuleCat.of R N) _ hsupp n

/-- Rees: with the test module `R ⧸ I`. -/
theorem le_depth_iff_ext_quotient (n : ℕ) :
    (n : ℕ∞) ≤ I.depth M ↔
      ∀ i < n, Subsingleton (Abelian.Ext (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R M) i) :=
  le_depth_iff_ext (R ⧸ I)
    (by simp [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]) n

/-- The depth drops by one modulo a regular element (Stacks 00LE). -/
theorem depth_quotSMulTop_add_one {x : R} (hx : x ∈ I) (hreg : IsSMulRegular M x) :
    I.depth (QuotSMulTop x M) + 1 = I.depth M := by
  rw [depth_eq_sga2Depth, depth_eq_sga2Depth,
    SGA.SGA2.ExposeIII.III_2_5 I (ModuleCat.of R M) hx hreg]

/-- Every regular sequence in `I` extends to one of any length at most the depth. -/
theorem exists_isWeaklyRegular_append {rs : List R} (hmem : ∀ r ∈ rs, r ∈ I)
    (hreg : IsWeaklyRegular M rs) {n : ℕ} (hlen : rs.length ≤ n) (hn : (n : ℕ∞) ≤ I.depth M) :
    ∃ ts : List R, (rs ++ ts).length = n ∧ (∀ r ∈ ts, r ∈ I) ∧ IsWeaklyRegular M (rs ++ ts) :=
  SGA.SGA2.ExposeIII.exists_regular_extension I (ModuleCat.of R M) rs hmem hreg n hlen
    (depth_eq_sga2Depth (I := I) (M := M) ▸ hn)

end Noetherian

end Ideal

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The depth of a nonzero finite module over a noetherian local ring is at most the dimension of
its support (Stacks 0AUI). -/
theorem depth_le_supportDim [Nontrivial M] :
    ((maximalIdeal R).depth M : WithBot ℕ∞) ≤ Module.supportDim R M := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (Module.supportDim_ne_bot_of_nontrivial R M)
  rw [← hd, WithBot.coe_le_coe]
  apply ENat.forall_natCast_le_iff_le.mp
  intro n hn
  obtain ⟨rs, rfl, hmem, hrs⟩ := (Ideal.le_depth_iff _ M n).mp hn
  have hreg : IsRegular M rs :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hrs
  have h := Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg
  have : Nontrivial (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) :=
    hreg.quot_ofList_smul_nontrivial ⊤
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp (Module.supportDim_ne_bot_of_nontrivial R
    (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)))
  rw [← he, ← hd] at h
  have h' : e + (rs.length : ℕ∞) = d := by exact_mod_cast h
  rw [← h']
  exact le_add_self

/-- The depth of a nonzero finite module over a noetherian local ring is at most `dim R`. -/
theorem depth_le_ringKrullDim [Nontrivial M] :
    ((maximalIdeal R).depth M : WithBot ℕ∞) ≤ ringKrullDim R :=
  depth_le_supportDim.trans (Module.supportDim_le_ringKrullDim R M)

/-- The depth of a nonzero finite module over a noetherian local ring is finite. -/
theorem depth_ne_top [Nontrivial M] : (maximalIdeal R).depth M ≠ ⊤ := by
  intro h
  have := (depth_le_ringKrullDim (M := M)).trans_lt (ringKrullDim_lt_top (R := R))
  rw [h] at this
  exact (lt_irrefl _) (this.trans_le le_top)

end IsLocalRing
