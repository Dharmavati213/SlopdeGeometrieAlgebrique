/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedLocallyArtinian
import Mathlib.RingTheory.Nakayama

/-!
# Local Artinian modules and support at the closed point

Over a noetherian local ring, the literal property that every finitely
generated submodule is Artinian is equivalent to actual support at the
closed point. The reverse support implication is proved using stabilization
of the maximal-ideal filtration and Nakayama, not added as a convention.
-/

noncomputable section

universe u

open CategoryTheory
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A finite Artinian module is actually killed by a power of the maximal
ideal, by stabilization and Nakayama. -/
theorem finite_artinian_exists_maximalIdeal_pow_annihilator
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [IsArtinian R M] :
    ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ Module.annihilator R M := by
  let m := IsLocalRing.maximalIdeal R
  let F : ℕ →o (Submodule R M)ᵒᵈ :=
    ⟨fun n => OrderDual.toDual (m ^ n • (⊤ : Submodule R M)),
      fun n k h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes F
  have heq : m ^ n • (⊤ : Submodule R M) = m • (m ^ n • ⊤) := by
    have h := congrArg OrderDual.ofDual (hn (n + 1) (Nat.le_succ n))
    change m ^ n • (⊤ : Submodule R M) = m ^ (n + 1) • ⊤ at h
    simpa only [pow_succ', mul_smul] using h
  have hz : m ^ n • (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m _
      (IsNoetherian.noetherian _) heq.le (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  refine ⟨n, fun r hr => Module.mem_annihilator.mpr (fun x => ?_)⟩
  have hx : r • x ∈ m ^ n • (⊤ : Submodule R M) :=
    Submodule.smul_mem_smul hr (Submodule.mem_top)
  simpa only [hz, Submodule.mem_bot] using hx

/-- The literal local Artinian condition implies support at the closed point,
without assuming the whole module finite. -/
theorem support_maximalIdeal_of_moduleLocallyArtinian
    (H : Type u) [AddCommGroup H] [Module R H]
    (hH : ModuleLocallyArtinian (R := R) H) :
    Module.support R H ⊆ PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R : Set R) := by
  apply support_subset_zeroLocus_of_powerTorsion_eq_top
  apply top_unique
  intro x _
  let N : Submodule R H := Submodule.span R {x}
  have : IsArtinian R N := hH N (Submodule.fg_span_singleton x)
  obtain ⟨n, hn⟩ := finite_artinian_exists_maximalIdeal_pow_annihilator (R := R) N
  apply (mem_powerTorsion_iff _ H x).mpr
  refine ⟨n, fun r hr => ?_⟩
  exact congrArg Subtype.val (Module.mem_annihilator.mp (hn hr)
    (⟨x, Submodule.mem_span_singleton_self x⟩ : N))

/-- The source's locally Artinian condition is exactly the actual support
condition over a noetherian local ring. -/
theorem moduleLocallyArtinian_iff_support_maximalIdeal
    (H : Type u) [AddCommGroup H] [Module R H] :
    ModuleLocallyArtinian (R := R) H ↔
      Module.support R H ⊆ PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R : Set R) := by
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  exact ⟨support_maximalIdeal_of_moduleLocallyArtinian H,
    moduleLocallyArtinian_of_support _ (ModuleCat.of R H)⟩

end SGA.SGA2.ExposeIV
