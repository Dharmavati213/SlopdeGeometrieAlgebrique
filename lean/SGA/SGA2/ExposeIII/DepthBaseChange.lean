/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.Depth
import SGA.SGA2.ExposeIII.AssociatedPrimes
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# SGA 2, Exposé III, Proposition 2.11: depth and flat base change

Flat base change transports regular sequences and cannot decrease depth.
For faithfully flat base change, vanishing of the ideal annihilator descends.
Selecting regular elements and passing to their quotients then proves descent
of every finite depth bound, including equality when the depth is infinite.
-/

noncomputable section

universe u

open CategoryTheory RingTheory.Sequence
open scoped TensorProduct

namespace SGA.SGA2.ExposeIII

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The positive-depth criterion in the ideal-annihilator form of III.2.1. -/
theorem one_le_depth_iff_idealRegular [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    1 ≤ depth I M ↔ IdealRegular M I := by
  rw [idealRegular_iff_exists_regular M I]
  constructor
  · intro h
    obtain ⟨rs, hlen, hmem, hreg⟩ := (le_depth_iff_exists_regular I M 1).mp h
    obtain ⟨f, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact ⟨f, hmem f (by simp), (isWeaklyRegular_singleton_iff M f).mp hreg⟩
  · rintro ⟨f, hf, hreg⟩
    exact (le_depth_iff_exists_regular I M 1).mpr
      ⟨[f], rfl, by simpa using hf, (isWeaklyRegular_singleton_iff M f).mpr hreg⟩

/-- III.2.11, the inequality for flat base change. The target ring need
not be noetherian for this direction. -/
theorem III_2_11_flat [IsNoetherianRing R] [Module.Flat R S]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth I M ≤ depth (I.map (algebraMap R S)) (ModuleCat.of S (S ⊗[R] M)) := by
  apply ENat.forall_natCast_le_iff_le.mp
  intro n hn
  obtain ⟨rs, rfl, hmem, hreg⟩ := (le_depth_iff_exists_regular I M n).mp hn
  have hregS := hreg.of_flat_of_isBaseChange (TensorProduct.isBaseChange R M S)
  simpa only [List.length_map] using
    length_le_depth (I.map (algebraMap R S)) (ModuleCat.of S (S ⊗[R] M))
      (rs.map (algebraMap R S)) (by
        intro x hx
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
        exact Ideal.mem_map_of_mem _ (hmem r hr)) hregS

/-- Faithful flatness descends the vanishing of elements annihilated by
the whole support ideal. No noetherian or finiteness hypothesis is needed. -/
theorem idealRegular_of_faithfullyFlat [Module.FaithfullyFlat R S]
    (I : Ideal R) (M : ModuleCat.{u} R)
    (h : IdealRegular (S ⊗[R] M) (I.map (algebraMap R S))) :
    IdealRegular M I := by
  intro m hm
  have hI : I.map (algebraMap R S) ≤
      (⊥ : Submodule S (S ⊗[R] M)).colon {1 ⊗ₜ[R] m} := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change algebraMap R S r ∈ (⊥ : Submodule S (S ⊗[R] M)).colon {1 ⊗ₜ[R] m}
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    rw [IsScalarTower.algebraMap_smul S r ((1 : S) ⊗ₜ[R] m),
      ← TensorProduct.tmul_smul, hm r hr, TensorProduct.tmul_zero]
  have hzero : 1 ⊗ₜ[R] m = (0 : S ⊗[R] M) := by
    apply h
    intro s hs
    simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot] using hI hs
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) M
  simpa using hzero

/-- Every finite depth bound descends under faithfully flat base change
between noetherian rings. -/
theorem le_depth_of_faithfullyFlat [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.FaithfullyFlat R S] (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ depth (I.map (algebraMap R S)) (ModuleCat.of S (S ⊗[R] M)) →
      (n : ℕ∞) ≤ depth I M := by
  induction n generalizing M with
  | zero => exact fun _ ↦ zero_le
  | succ n ih =>
    intro hn
    have hpos : 1 ≤ depth (I.map (algebraMap R S)) (ModuleCat.of S (S ⊗[R] M)) :=
      (show (1 : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) by exact_mod_cast Nat.succ_pos n).trans hn
    have hIR := idealRegular_of_faithfullyFlat (S := S) I M
      ((one_le_depth_iff_idealRegular _ _).mp hpos)
    obtain ⟨f, hf, hreg⟩ := (idealRegular_iff_exists_regular M I).mp hIR
    apply (succ_le_depth_iff I M hf hreg n).mpr
    apply ih (ModuleCat.of R (QuotSMulTop f M))
    have hregS := hreg.of_flat_of_isBaseChange (TensorProduct.isBaseChange R M S)
    have hquot := (succ_le_depth_iff (I.map (algebraMap R S))
      (ModuleCat.of S (S ⊗[R] M)) (Ideal.mem_map_of_mem _ hf) hregS n).mp hn
    rwa [depth_eq_of_linearEquiv (I.map (algebraMap R S))
      (N := ModuleCat.of S (S ⊗[R] QuotSMulTop f M))
      (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop f M S)] at hquot

/-- III.2.11: faithfully flat base change preserves depth, including
infinite depth, for finite modules over noetherian rings. -/
theorem III_2_11_faithfullyFlat [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.FaithfullyFlat R S] (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] :
    depth (I.map (algebraMap R S)) (ModuleCat.of S (S ⊗[R] M)) = depth I M := by
  apply le_antisymm
  · exact ENat.forall_natCast_le_iff_le.mp (le_depth_of_faithfullyFlat I M)
  · exact III_2_11_flat I M

end SGA.SGA2.ExposeIII
