/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.LocalCohomologyDualDimension

/-!
# Positive support dimension and closed-point errors

For local modules, an inclusion of supports with only a closed-point error
is equality as soon as the larger support has positive dimension. This
applies to the original maximal-ideal torsion quotient and to exact
sequences whose first or last term is supported at the closed point.
-/

noncomputable section
universe u
open CategoryTheory IsLocalRing
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A closed-point error can be removed from an upper bound on a
positive-dimensional module support. -/
theorem support_subset_of_subset_union_closedPoint
    (M N : ModuleCat.{u} R)
    (hMN : Module.support R M ⊆ Module.support R N ∪
      PrimeSpectrum.zeroLocus (maximalIdeal R : Set R))
    (hpos : 0 < Module.supportDim R M) :
    Module.support R M ⊆ Module.support R N := by
  have : Nontrivial N := by
    by_contra! hN
    have : Subsingleton N := hN
    have hs : supportedModuleProperty (maximalIdeal R) M := by
      simpa only [supportedModuleProperty, Module.support_eq_empty, Set.empty_union] using hMN
    exact (not_le_of_gt hpos) (supportDim_le_zero_of_supported_maximalIdeal M hs)
  intro p hp
  rcases hMN hp with hp | hp
  · exact hp
  · rw [PrimeSpectrum.zeroLocus_eq_singleton] at hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact IsLocalRing.closedPoint_mem_support R N

/-- A closed-point error cannot change a positive-dimensional module support. -/
theorem support_eq_of_subset_union_closedPoint
    (M N : ModuleCat.{u} R)
    (hMN : Module.support R M ⊆ Module.support R N ∪
      PrimeSpectrum.zeroLocus (maximalIdeal R : Set R))
    (hNM : Module.support R N ⊆ Module.support R M)
    (hpos : 0 < Module.supportDim R M) :
    Module.support R M = Module.support R N :=
  Set.Subset.antisymm (support_subset_of_subset_union_closedPoint M N hMN hpos) hNM

omit [IsLocalRing R] in
/-- Middle exactness alone bounds the middle support by the two outside
supports; the maps need not be injective or surjective. -/
theorem support_subset_union_of_exact (A B C : ModuleCat.{u} R)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g) :
    Module.support R B ⊆ Module.support R A ∪ Module.support R C := by
  intro p
  contrapose
  simp only [Set.mem_union, not_or, and_imp, Module.notMem_support_iff']
  intro hA hC b
  obtain ⟨r, hr, he⟩ := hC (g b)
  rw [← map_smul, h] at he
  obtain ⟨a, ha⟩ := he
  obtain ⟨s, hs, he⟩ := hA a
  exact ⟨_, p.asIdeal.primeCompl.mul_mem hs hr,
    by rw [mul_smul, ← ha, ← map_smul, he, map_zero]⟩

/-- In a middle-exact sequence with closed-point last term, a positive
middle support dimension is bounded by the first term's dimension. -/
theorem supportDim_le_of_exact_last_supported (A B C : ModuleCat.{u} R)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g)
    (hC : supportedModuleProperty (maximalIdeal R) C)
    (hpos : 0 < Module.supportDim R B) :
    Module.supportDim R B ≤ Module.supportDim R A := by
  have hs : Module.support R B ⊆ Module.support R A :=
    support_subset_of_subset_union_closedPoint B A
      ((support_subset_union_of_exact A B C f g h).trans (Set.union_subset_union_right _ hC)) hpos
  exact Order.krullDim_le_of_strictMono (fun p => ⟨p.val, hs p.property⟩)
    (fun _ _ h => h)

/-- An exact sequence with a closed-point first term preserves the
positive-dimensional support on the original quotient. -/
theorem support_eq_of_shortExact_left_supported
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hs : supportedModuleProperty (maximalIdeal R) S.X₁)
    (hpos : 0 < Module.supportDim R S.X₂) :
    Module.support R S.X₂ = Module.support R S.X₃ := by
  have he := Module.support_of_exact
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
    ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
    ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)
  apply support_eq_of_subset_union_closedPoint S.X₂ S.X₃ ?_ ?_ hpos
  · rw [he]
    exact Set.union_subset (fun _ hp => Or.inr (hs hp)) (fun _ hp => Or.inl hp)
  · exact Module.support_subset_of_surjective S.g.hom
      ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)

/-- An exact sequence with a closed-point last term preserves the
positive-dimensional support on the original submodule. -/
theorem support_eq_of_shortExact_right_supported
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hs : supportedModuleProperty (maximalIdeal R) S.X₃)
    (hpos : 0 < Module.supportDim R S.X₂) :
    Module.support R S.X₂ = Module.support R S.X₁ := by
  have he := Module.support_of_exact
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
    ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
    ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)
  apply support_eq_of_subset_union_closedPoint S.X₂ S.X₁ ?_ ?_ hpos
  · rw [he]
    exact Set.union_subset (fun _ hp => Or.inl hp) (fun _ hp => Or.inr (hs hp))
  · exact Module.support_subset_of_injective S.f.hom
      ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)

/-- Removing the actual power-torsion submodule preserves positive
support dimension, not merely the local-cohomology isomorphism class. -/
theorem supportDim_powerTorsion_quotient_eq (M : ModuleCat.{u} R)
    (hpos : 0 < Module.supportDim R M) :
    Module.supportDim R (M ⧸ powerTorsion (maximalIdeal R) M) = Module.supportDim R M := by
  have hs := support_eq_of_shortExact_left_supported
    (powerTorsionShortComplex (maximalIdeal R) M)
    (powerTorsionShortComplex_shortExact (maximalIdeal R) M)
    (support_powerTorsion_subset_zeroLocus (maximalIdeal R) M) hpos
  exact congrArg (fun s : Set (PrimeSpectrum R) => Order.krullDim s) hs.symm

end SGA.SGA2.ExposeV
