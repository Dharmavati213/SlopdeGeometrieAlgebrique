/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.LocalArtinianSupport
import SGA.SGA2.ExposeIV.SupportedScalarChange
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Local Artinian support with only a finitely generated maximal ideal

No noetherianity of the whole local ring is assumed. A finite module
annihilated by a maximal-ideal power has finite length: the proof uses the
actual maximal-ideal filtration and finite-dimensional residue-field
quotients. Consequently every finite supported module has finite length,
and the literal locally Artinian property is equivalent to actual support
at the closed point. These results apply to scalar-change targets whose
whole-ring noetherianity has not been established.
-/

noncomputable section

universe u

open CategoryTheory IsLocalRing
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {S : Type u} [CommRing S] [IsLocalRing S]
variable (hm : (maximalIdeal S).FG)

include hm

/-- A finite module killed by a maximal-ideal power has finite length.
Finite generation of that ideal suffices; the ambient ring need not be noetherian. -/
theorem isFiniteLength_of_maximalIdeal_pow_annihilator_of_fg
    (M : Type u) [AddCommGroup M] [Module S M] [Module.Finite S M]
    (n : ℕ) (hn : maximalIdeal S ^ n ≤ Module.annihilator S M) :
    IsFiniteLength S M := by
  induction n generalizing M with
  | zero =>
    have hzero (x : M) : x = 0 := by
      have h := Module.mem_annihilator.mp
        (hn (show (1 : S) ∈ maximalIdeal S ^ 0 by simp)) x
      simpa only [one_smul] using h
    have : Subsingleton M := ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩
    exact IsFiniteLength.of_subsingleton
  | succ n ih =>
    let N : Submodule S M := maximalIdeal S • ⊤
    have : Module.Finite S N :=
      Module.Finite.of_fg (Submodule.FG.smul hm Module.Finite.fg_top)
    have hz : maximalIdeal S ^ (n + 1) • (⊤ : Submodule S M) = ⊥ := by
      apply le_antisymm _ bot_le
      apply Submodule.smul_le.mpr
      intro r hr x _
      exact Module.mem_annihilator.mp (hn hr) x
    have hnN : maximalIdeal S ^ n ≤ Module.annihilator S N := by
      intro r hr
      apply Module.mem_annihilator.mpr
      intro x
      apply Subtype.ext
      have hx : r • x.val ∈ maximalIdeal S ^ n • (maximalIdeal S • ⊤ : Submodule S M) :=
        Submodule.smul_mem_smul hr x.property
      rw [← mul_smul, ← pow_succ, hz] at hx
      exact hx
    obtain ⟨hNN, hNA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp (ih N hnN)
    have hT : Module.IsTorsionBySet S (M ⧸ N) (maximalIdeal S) :=
      Module.isTorsionBySet_quotient_ideal_smul M (maximalIdeal S)
    let : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field _
    let := hT.module
    have : Module.Finite (S ⧸ maximalIdeal S) (M ⧸ N) :=
      Module.Finite.of_surjective hT.semilinearMap Function.surjective_id
    have hQN : IsNoetherian S (M ⧸ N) :=
      (hT.semilinearMap.isNoetherian_iff_of_bijective Function.bijective_id).mpr inferInstance
    have hQA : IsArtinian S (M ⧸ N) :=
      (hT.semilinearMap.isArtinian_iff_of_bijective Function.bijective_id).mpr inferInstance
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨(isNoetherian_iff_submodule_quotient N).mpr ⟨hNN, hQN⟩,
        (isArtinian_iff_submodule_quotient N).mpr ⟨hNA, hQA⟩⟩

/-- Every actual maximal-ideal-power quotient has finite length as an
original module, even without whole-ring noetherianity. -/
theorem maximalIdealPowQuotient_isFiniteLength_of_fg (n : ℕ) :
    IsFiniteLength S (S ⧸ maximalIdeal S ^ n) :=
  isFiniteLength_of_maximalIdeal_pow_annihilator_of_fg hm _ n
    (by rw [Ideal.annihilator_quotient])

/-- The nilpotent quotient stages themselves are Artinian rings. -/
theorem maximalIdealPowQuotient_isArtinianRing_of_fg (n : ℕ) :
    IsArtinianRing (S ⧸ maximalIdeal S ^ n) := by
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp
    (maximalIdealPowQuotient_isFiniteLength_of_fg hm n)).2
  exact isArtinian_of_tower S inferInstance

/-- Finite actual supported modules have finite length under the finite
maximal-ideal hypothesis alone. -/
theorem finite_supported_isFiniteLength_of_fg
    (M : Type u) [AddCommGroup M] [Module S M] [Module.Finite S M]
    (hM : Module.support S M ⊆ PrimeSpectrum.zeroLocus (maximalIdeal S : Set S)) :
    IsFiniteLength S M := by
  obtain ⟨n, hn⟩ := finite_support_pow_annihilator_of_fg (maximalIdeal S) hm M hM
  exact isFiniteLength_of_maximalIdeal_pow_annihilator_of_fg hm M n hn

/-- A finite Artinian module is killed by a maximal-ideal power, by
stabilization and Nakayama using only the finitely generated filtration term. -/
theorem finite_artinian_exists_maximalIdeal_pow_annihilator_of_fg
    (M : Type u) [AddCommGroup M] [Module S M] [Module.Finite S M] [IsArtinian S M] :
    ∃ n : ℕ, maximalIdeal S ^ n ≤ Module.annihilator S M := by
  let m := maximalIdeal S
  let F : ℕ →o (Submodule S M)ᵒᵈ :=
    ⟨fun n ↦ OrderDual.toDual (m ^ n • (⊤ : Submodule S M)),
      fun n k h ↦ Submodule.smul_mono_left (Ideal.pow_le_pow_right h)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes F
  have heq : m ^ n • (⊤ : Submodule S M) = m • (m ^ n • ⊤) := by
    have h := congrArg OrderDual.ofDual (hn (n + 1) (Nat.le_succ n))
    change m ^ n • (⊤ : Submodule S M) = m ^ (n + 1) • ⊤ at h
    simpa only [pow_succ', mul_smul] using h
  have hz : m ^ n • (⊤ : Submodule S M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m _
      (Submodule.FG.smul hm.pow Module.Finite.fg_top) heq.le (maximalIdeal_le_jacobson ⊥)
  refine ⟨n, fun r hr ↦ Module.mem_annihilator.mpr (fun x ↦ ?_)⟩
  have hx : r • x ∈ m ^ n • (⊤ : Submodule S M) :=
    Submodule.smul_mem_smul hr Submodule.mem_top
  simpa only [hz, Submodule.mem_bot] using hx

/-- Literal local Artinianness implies actual closed-point support without
whole-ring noetherianity. -/
theorem support_maximalIdeal_of_moduleLocallyArtinian_of_fg
    (M : Type u) [AddCommGroup M] [Module S M]
    (hM : ModuleLocallyArtinian (R := S) M) :
    Module.support S M ⊆ PrimeSpectrum.zeroLocus (maximalIdeal S : Set S) := by
  apply support_subset_zeroLocus_of_powerTorsion_eq_top
  apply top_unique
  intro x _
  let N : Submodule S M := Submodule.span S {x}
  have : IsArtinian S N := hM N (Submodule.fg_span_singleton x)
  obtain ⟨n, hn⟩ := finite_artinian_exists_maximalIdeal_pow_annihilator_of_fg hm N
  apply (mem_powerTorsion_iff _ M x).mpr
  refine ⟨n, fun r hr ↦ ?_⟩
  exact congrArg Subtype.val (Module.mem_annihilator.mp (hn hr)
    (⟨x, Submodule.mem_span_singleton_self x⟩ : N))

/-- Actual closed-point support implies literal local Artinianness under
the finite maximal-ideal hypothesis alone. -/
theorem moduleLocallyArtinian_of_support_maximalIdeal_of_fg
    (M : Type u) [AddCommGroup M] [Module S M]
    (hM : Module.support S M ⊆ PrimeSpectrum.zeroLocus (maximalIdeal S : Set S)) :
    ModuleLocallyArtinian (R := S) M := by
  intro N hN
  have : Module.Finite S N := Module.Finite.of_fg hN
  have hSupp := (Module.support_subset_of_injective N.subtype N.subtype_injective).trans hM
  exact (isFiniteLength_iff_isNoetherian_isArtinian.mp
    (finite_supported_isFiniteLength_of_fg hm N hSupp)).2

/-- The literal local-Artinian/support equivalence with no whole-ring
noetherianity assumption. -/
theorem moduleLocallyArtinian_iff_support_maximalIdeal_of_fg
    (M : Type u) [AddCommGroup M] [Module S M] :
    ModuleLocallyArtinian (R := S) M ↔
      Module.support S M ⊆ PrimeSpectrum.zeroLocus (maximalIdeal S : Set S) :=
  ⟨support_maximalIdeal_of_moduleLocallyArtinian_of_fg hm M,
    moduleLocallyArtinian_of_support_maximalIdeal_of_fg hm M⟩

end SGA.SGA2.ExposeIV
