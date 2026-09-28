/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.RegularExt
import Mathlib.Data.ENat.Lattice

/-!
# SGA 2, Exposé III, 2.3–2.4: depth

Depth is defined using Ext against all finite modules annihilated by some
power of the support ideal, exactly as in III.2.3. Its finite lower bounds
are characterized by vanishing, and, over a noetherian ring for finite
coefficients, by regular sequences and by a single finite test module
having the prescribed support. Regular sequences use SGA's convention
(`IsWeaklyRegular`), so these statements also cover infinite depth.
-/

noncomputable section

universe u

open CategoryTheory Abelian Limits RingTheory.Sequence

namespace SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R]

/-- The vanishing condition in III.2.3 and III.2.4(2). -/
def ExtVanishesBelow (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) : Prop :=
  ∀ (N : ModuleCat.{u} R), Module.Finite R N →
    (∃ k : ℕ, I ^ k ≤ Module.annihilator R N) →
      ∀ i < n, Subsingleton (Abelian.Ext N M i)

/-- III.2.3: the ideal depth, valued in the extended natural numbers. -/
def depth (I : Ideal R) (M : ModuleCat.{u} R) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ExtVanishesBelow I M n), (n : ℕ∞)

theorem ExtVanishesBelow.mono {I : Ideal R} {M : ModuleCat.{u} R}
    {n m : ℕ} (h : ExtVanishesBelow I M n) (hmn : m ≤ n) :
    ExtVanishesBelow I M m :=
  fun N hfin hN i hi ↦ h N hfin hN i (hi.trans_le hmn)

@[simp]
theorem extVanishesBelow_zero (I : Ideal R) (M : ModuleCat.{u} R) :
    ExtVanishesBelow I M 0 := by
  intro N hfin hN i hi
  omega

/-- III.2.4(1) ⇔ (2): the supremum in the definition detects every finite bound. -/
theorem le_depth_iff (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔ ExtVanishesBelow I M n := by
  constructor
  · intro h
    cases n with
    | zero => exact extVanishesBelow_zero I M
    | succ n =>
      have hn : (n : ℕ∞) < depth I M :=
        lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self n)) h
      obtain ⟨k, hk⟩ := lt_iSup_iff.mp hn
      obtain ⟨hvan, hk⟩ := lt_iSup_iff.mp hk
      exact hvan.mono (Nat.succ_le_of_lt (ENat.natCast_lt_natCast.mp hk))
  · intro h
    exact le_iSup_of_le n (le_iSup_of_le h le_rfl)

/-- The existence of a regular sequence implies the depth bound over any ring. -/
theorem length_le_depth (I : Ideal R) (M : ModuleCat.{u} R) (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsWeaklyRegular M rs) :
    (rs.length : ℕ∞) ≤ depth I M :=
  (le_depth_iff I M rs.length).mpr fun N _ hN ↦ III_2_2_a I N M rs hmem hreg hN

/-- III.2.4(2) ⇒ (3), with the explicit test module `R/I`. -/
theorem ExtVanishesBelow.quotient {I : Ideal R} {M : ModuleCat.{u} R}
    {n : ℕ} (h : ExtVanishesBelow I M n) :
    ∀ i < n, Subsingleton (Abelian.Ext (ModuleCat.of R (R ⧸ I)) M i) := by
  apply h (ModuleCat.of R (R ⧸ I)) inferInstance
  exact ⟨1, by simp [Ideal.annihilator_quotient]⟩

/-- III.2.4(2) ⇒ (3) over an arbitrary commutative ring. -/
theorem ExtVanishesBelow.exists_test_module {I : Ideal R} {M : ModuleCat.{u} R}
    {n : ℕ} (h : ExtVanishesBelow I M n) :
    ∃ N : ModuleCat.{u} R, Module.Finite R N ∧
      Module.support R N = PrimeSpectrum.zeroLocus I ∧
        ∀ i < n, Subsingleton (Abelian.Ext N M i) :=
  ⟨ModuleCat.of R (R ⧸ I), inferInstance,
    by simp [Module.support_eq_zeroLocus, Ideal.annihilator_quotient], h.quotient⟩

/-- III.2.4(1) ⇔ (4) over a noetherian ring with finite coefficients. -/
theorem le_depth_iff_exists_regular [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsWeaklyRegular M rs := by
  constructor
  · intro h
    apply III_2_2_b I n (ModuleCat.of R (R ⧸ I)) M
      (by simp [Module.support_eq_zeroLocus, Ideal.annihilator_quotient])
    exact ((le_depth_iff I M n).mp h).quotient
  · rintro ⟨rs, rfl, hmem, hreg⟩
    exact length_le_depth I M rs hmem hreg

/-- III.2.4(1) ⇔ (3) over a noetherian ring with finite coefficients. -/
theorem le_depth_iff_exists_test_module [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔
      ∃ N : ModuleCat.{u} R, Module.Finite R N ∧
        Module.support R N = PrimeSpectrum.zeroLocus I ∧
          ∀ i < n, Subsingleton (Abelian.Ext N M i) := by
  constructor
  · intro h
    exact ((le_depth_iff I M n).mp h).exists_test_module
  · rintro ⟨N, hfin, hsupp, hExt⟩
    exact (le_depth_iff_exists_regular I M n).mpr (III_2_2_b I n N M hsupp hExt)

/-- Any finite module with exactly `V(I)` as support tests the depth. -/
theorem le_depth_iff_ext_vanishes [IsNoetherianRing R]
    (I : Ideal R) (N M : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Finite R M]
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔ ∀ i < n, Subsingleton (Abelian.Ext N M i) := by
  constructor
  · intro h
    obtain ⟨rs, rfl, hmem, hreg⟩ := (le_depth_iff_exists_regular I M n).mp h
    have hrad := hsupp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_eq_iff] at hrad
    exact ext_subsingleton_of_isWeaklyRegular N M rs
      (fun r hr ↦ hrad.symm ▸ Ideal.le_radical (hmem r hr)) hreg
  · intro h
    exact (le_depth_iff_exists_regular I M n).mpr (III_2_2_b I n N M hsupp h)

/-- Infinite depth means vanishing in every degree for every finite test module. -/
theorem depth_eq_top_iff (I : Ideal R) (M : ModuleCat.{u} R) :
    depth I M = ⊤ ↔ ∀ n, ExtVanishesBelow I M n := by
  constructor
  · intro h n
    exact (le_depth_iff I M n).mp (by simp [h])
  · intro h
    apply top_unique
    rw [← ENat.iSup_natCast]
    exact iSup_le fun n ↦ (le_depth_iff I M n).mpr (h n)

/-- Increasing the support ideal can only increase depth. -/
theorem depth_mono {I J : Ideal R} (hIJ : I ≤ J) (M : ModuleCat.{u} R) :
    depth I M ≤ depth J M := by
  apply ENat.forall_natCast_le_iff_le.mp
  intro n hn
  apply (le_depth_iff J M n).mpr
  intro N hfin hN
  obtain ⟨k, hk⟩ := hN
  exact (le_depth_iff I M n).mp hn N hfin
    ⟨k, (pow_le_pow_left' hIJ k).trans hk⟩

/-- III.2.5 at finite bounds: quotienting by a regular element lowers
the depth bound by one. -/
theorem succ_le_depth_iff [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    {f : R} (hf : f ∈ I) (hreg : IsSMulRegular M f) (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ depth I M ↔
      (n : ℕ∞) ≤ depth I (ModuleCat.of R (QuotSMulTop f M)) := by
  constructor
  · intro h
    apply (le_depth_iff I _ n).mpr
    intro N hfin hN i hi
    have hExt := (le_depth_iff I M (n + 1)).mp h N hfin hN
    have hzero₁ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hExt i (by omega))
    have hzero₂ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hExt (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero <|
      ShortComplex.Exact.isZero_of_both_zeros
        (Abelian.Ext.covariant_sequence_exact₃' N hreg.smulShortComplex_shortExact
          i (i + 1) rfl)
        (hzero₁.eq_zero_of_src _) (hzero₂.eq_zero_of_tgt _)
  · intro h
    obtain ⟨rs, hlen, hmem, hrs⟩ := (le_depth_iff_exists_regular I _ n).mp h
    apply (le_depth_iff_exists_regular I M (n + 1)).mpr
    exact ⟨f :: rs, by simp [hlen], by simpa using And.intro hf hmem, hrs.cons hreg⟩

/-- III.2.5, including infinite depth: `depth_I M = depth_I(M/fM) + 1`. -/
theorem III_2_5 [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    {f : R} (hf : f ∈ I) (hreg : IsSMulRegular M f) :
    depth I M = depth I (ModuleCat.of R (QuotSMulTop f M)) + 1 := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  cases n with
  | zero => simp
  | succ n =>
    rw [succ_le_depth_iff I M hf hreg n, Nat.cast_add, Nat.cast_one,
      ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)]

/-- Depth depends only on the closed support `V(I)` in the noetherian finite case. -/
theorem depth_eq_of_radical_eq [IsNoetherianRing R]
    {I J : Ideal R} (hIJ : I.radical = J.radical)
    (M : ModuleCat.{u} R) [Module.Finite R M] : depth I M = depth J M := by
  have hsupp : Module.support R (R ⧸ J) = PrimeSpectrum.zeroLocus I := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient,
      PrimeSpectrum.zeroLocus_eq_iff]
    exact hIJ.symm
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [le_depth_iff_ext_vanishes I (ModuleCat.of R (R ⧸ J)) M hsupp n,
    le_depth_iff_ext_vanishes J (ModuleCat.of R (R ⧸ J)) M
      (by simp [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]) n]

/-- The first potentially nonzero Ext degree, with value `∞` if every degree vanishes. -/
def extDepth (N M : ModuleCat.{u} R) : ℕ∞ :=
  ⨅ (i : ℕ) (_ : ¬ Subsingleton (Abelian.Ext N M i)), (i : ℕ∞)

theorem le_extDepth_iff (N M : ModuleCat.{u} R) (n : ℕ) :
    (n : ℕ∞) ≤ extDepth N M ↔ ∀ i < n, Subsingleton (Abelian.Ext N M i) := by
  classical
  simp only [extDepth, le_iInf_iff, ENat.natCast_le_natCast]
  constructor
  · intro h i hi
    by_contra hn
    exact (Nat.not_le_of_gt hi) (h i hn)
  · intro h i hi
    by_contra hni
    exact hi (h i (Nat.lt_of_not_ge hni))

/-- III.2.8's homological description, for any finite test module of full support. -/
theorem depth_eq_extDepth [IsNoetherianRing R]
    (I : Ideal R) (N M : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Finite R M]
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    depth I M = extDepth N M := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [le_depth_iff_ext_vanishes I N M hsupp n, le_extDepth_iff]

/-- In a local ring the residue module computes the depth, as in III.2.8. -/
theorem depth_maximalIdeal_eq_extDepth [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth (IsLocalRing.maximalIdeal R) M =
      extDepth (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) M :=
  depth_eq_extDepth _ _ M
    (by simp [Module.support_eq_zeroLocus, Ideal.annihilator_quotient])

/-- III.2.8: the semilocal residue ring `R / jacobson R` computes depth.
The equality itself does not require finiteness of the set of maximal ideals. -/
theorem depth_jacobson_eq_extDepth [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth (Ring.jacobson R) M = extDepth (ModuleCat.of R (R ⧸ Ring.jacobson R)) M :=
  depth_eq_extDepth _ _ M
    (by simp [Module.support_eq_zeroLocus, Ideal.annihilator_quotient])

/-- Depth is invariant under a linear equivalence of finite coefficient modules. -/
theorem depth_eq_of_linearEquiv [IsNoetherianRing R] (I : Ideal R)
    {M N : ModuleCat.{u} R} [Module.Finite R M] [Module.Finite R N]
    (e : M ≃ₗ[R] N) : depth I M = depth I N := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  simp_rw [le_depth_iff_exists_regular, e.isWeaklyRegular_congr]

end SGA.SGA2.ExposeIII
