/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Depth.Rees

/-!
# SGA 2, Exposé III, Theorem 2.2: regular sequences and Ext vanishing

SGA's regularity convention only requires successive multiplication maps to
be injective. It is mathlib's `IsWeaklyRegular`: the final quotient may be
zero. In particular, the theorem does not require `IM ≠ M`.

Part (a) holds over every commutative ring, for arbitrary modules, provided
the first Ext argument is annihilated by a power of the ideal. Part (b)
requires a noetherian ring and finite modules, as in the source.
-/

noncomputable section

universe u

open CategoryTheory Abelian Limits RingTheory.Sequence LinearMap

namespace SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R]

/-- III.2.2(a), in the stronger form where each element of the regular
sequence has some power annihilating the first Ext argument. -/
theorem ext_subsingleton_of_isWeaklyRegular
    (N M : ModuleCat.{u} R) (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ (Module.annihilator R N).radical)
    (hreg : IsWeaklyRegular M rs) :
    ∀ i < rs.length, Subsingleton (Abelian.Ext N M i) := by
  induction rs generalizing M with
  | nil => simp
  | cons a rs ih =>
    obtain ⟨ha, hrs⟩ := (isWeaklyRegular_cons_iff M a rs).mp hreg
    obtain ⟨k, hk⟩ := hmem a List.mem_cons_self
    have hmem' : ∀ r ∈ rs, r ∈ (Module.annihilator R N).radical :=
      fun r hr ↦ hmem r (List.mem_cons_of_mem a hr)
    intro i hi
    cases i with
    | zero =>
      have := (ha.pow k).linearMap_subsingleton_of_mem_annihilator hk
      exact (Abelian.Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton
    | succ i =>
      let g := AddCommGrpCat.ofHom
        ((Abelian.Ext.mk₀ (M.smulShortComplex a).f).postcomp N (add_zero (i + 1)))
      have hg : Mono g := by
        apply (Abelian.Ext.covariant_sequence_exact₁' N
          ha.smulShortComplex_shortExact i (i + 1) rfl).mono_g
          ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr ?_).eq_zero_of_src _)
        exact ih (ModuleCat.of R (QuotSMulTop a M)) hmem' hrs i (by simpa using hi)
      let gk := AddCommGrpCat.ofHom
        ((Abelian.Ext.mk₀ (M.smulShortComplex (a ^ k)).f).postcomp N
          (add_zero (i + 1)))
      have hgk : Mono gk := by
        simp only [ModuleCat.smulShortComplex_f_eq_smul_id, g, gk] at hg ⊢
        exact (Abelian.Ext.postcomp_smul_id_mono_iff (a ^ k) (i + 1)).mpr
          (((Abelian.Ext.postcomp_smul_id_mono_iff a (i + 1)).mp hg).pow k)
      have hz : gk = 0 :=
        Abelian.Ext.postcomp_smul_id_eq_zero_of_mem_annihilator hk (i + 1)
      exact AddCommGrpCat.subsingleton_of_isZero (IsZero.of_mono_eq_zero _ hz)

/-- III.2.2(a): a regular sequence of length `l` in `I` forces
`Extⁱ(N,M) = 0` for `i < l` whenever a power of `I` annihilates `N`. -/
theorem III_2_2_a (I : Ideal R) (N M : ModuleCat.{u} R) (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsWeaklyRegular M rs)
    (hN : ∃ k : ℕ, I ^ k ≤ Module.annihilator R N) :
    ∀ i < rs.length, Subsingleton (Abelian.Ext N M i) := by
  obtain ⟨k, hk⟩ := hN
  exact ext_subsingleton_of_isWeaklyRegular N M rs
    (fun r hr ↦ ⟨k, hk (Ideal.pow_mem_pow (hmem r hr) k)⟩) hreg

/-- III.2.2(b), using SGA's regularity convention, including the case `IM = M`. -/
theorem III_2_2_b [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    (N M : ModuleCat.{u} R) [Module.Finite R N] [Module.Finite R M]
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I)
    (hExt : ∀ i < n, Subsingleton (Abelian.Ext N M i)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsWeaklyRegular M rs := by
  induction n generalizing M with
  | zero => exact ⟨[], rfl, by simp, IsWeaklyRegular.nil R M⟩
  | succ n ih =>
    have hrad := hsupp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_eq_iff] at hrad
    have : Subsingleton (N ⟶ M) :=
      Abelian.Ext.addEquiv₀.subsingleton_congr.mp (hExt 0 (by omega))
    have : Subsingleton (N →ₗ[R] M) := ModuleCat.homAddEquiv.symm.subsingleton
    obtain ⟨x, hx, hreg⟩ := IsSMulRegular.subsingleton_linearMap_iff.mp this
    obtain ⟨k, hk⟩ := le_of_le_of_eq Ideal.le_radical hrad hx
    have hExt' : ∀ i < n,
        Subsingleton (Abelian.Ext N (ModuleCat.of R (QuotSMulTop (x ^ k) M)) i) := by
      intro i hi
      have hzero₁ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hExt i (by omega))
      have hzero₂ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hExt (i + 1) (by omega))
      exact AddCommGrpCat.subsingleton_of_isZero <|
        ShortComplex.Exact.isZero_of_both_zeros
          (Abelian.Ext.covariant_sequence_exact₃' N
            (hreg.pow k).smulShortComplex_shortExact i (i + 1) rfl)
          (hzero₁.eq_zero_of_src _) (hzero₂.eq_zero_of_tgt _)
    obtain ⟨rs, hlen, hmem, hrs⟩ := ih (ModuleCat.of R (QuotSMulTop (x ^ k) M)) hExt'
    exact ⟨x ^ k :: rs, by simp [hlen], by simpa using And.intro hk hmem,
      hrs.cons (hreg.pow k)⟩

end SGA.SGA2.ExposeIII
