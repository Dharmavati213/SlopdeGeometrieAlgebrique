/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Kernel comparison used by descending local duality

An isomorphism at the middle object and a monomorphism at the right object
identify the left objects of a commutative diagram with monic left arrows
and exact source row. The proof is an actual elementwise kernel argument.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R]

/-- The kernel comparison in a genuine commutative diagram of modules. -/
theorem isIso_left_of_exact_of_isIso_of_mono
    {S T : ShortComplex (ModuleCat.{u} R)} (φ : S ⟶ T) (hS : S.Exact)
    [Mono S.f] [Mono T.f] [IsIso φ.τ₂] [Mono φ.τ₃] : IsIso φ.τ₁ := by
  have h₁ (x : S.X₁) : T.f (φ.τ₁ x) = φ.τ₂ (S.f x) :=
    ConcreteCategory.congr_hom φ.comm₁₂ x
  have h₂ (x : S.X₂) : T.g (φ.τ₂ x) = φ.τ₃ (S.g x) :=
    ConcreteCategory.congr_hom φ.comm₂₃ x
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    apply (ModuleCat.mono_iff_injective S.f).mp inferInstance
    apply (ModuleCat.mono_iff_injective φ.τ₂).mp inferInstance
    rw [← h₁, ← h₁, h]
  · intro y
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective φ.τ₂).mp inferInstance (T.f y)
    have hzero : S.g x = 0 := by
      apply (ModuleCat.mono_iff_injective φ.τ₃).mp inferInstance
      rw [← h₂, hx]
      change (T.f ≫ T.g) y = φ.τ₃ 0
      rw [T.zero]
      exact (map_zero φ.τ₃.hom).symm
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp hS x hzero
    refine ⟨z, ?_⟩
    apply (ModuleCat.mono_iff_injective T.f).mp inferInstance
    rw [h₁, hz, hx]

end SGA.SGA2.ExposeV
