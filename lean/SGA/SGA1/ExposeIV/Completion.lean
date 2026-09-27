/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# SGA 1, Exposé IV, §3: relations with completion

For a noetherian ring `A` and an ideal `I`, mathlib proves that `M ⊗ Â → M̂` is an isomorphism
for finite `M` and that the `I`-adic completion `Â` is flat over `A` (IV.3.1). We prove IV.3.2:
`Â` is faithfully flat over `A` if and only if `I` is contained in the Jacobson radical of `A`.
-/

universe u

namespace SGA.SGA1.ExposeIV

open TensorProduct

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- IV.3: for a finite module `M` over a noetherian ring, `M ⊗_A Â → M̂` is an isomorphism. -/
theorem ofTensorProduct_bijective [IsNoetherianRing A] (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] : Function.Bijective (AdicCompletion.ofTensorProduct I M) :=
  AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M

/-- IV.3.1: the `I`-adic completion of a noetherian ring is flat. -/
theorem flat_adicCompletion [IsNoetherianRing A] : Module.Flat A (AdicCompletion I A) :=
  AdicCompletion.flat_of_isNoetherian I

/-- IV.3.2: for a noetherian ring `A`, the `I`-adic completion `Â` is faithfully flat over `A`
if and only if `I` is contained in the Jacobson radical of `A`. -/
theorem faithfullyFlat_adicCompletion_iff [IsNoetherianRing A] :
    Module.FaithfullyFlat A (AdicCompletion I A) ↔ I ≤ Ideal.jacobson ⊥ := by
  have := flat_adicCompletion I
  rw [Module.faithfullyFlat_iff]
  refine ⟨fun ⟨_, h⟩ ↦ ?_, fun hI ↦ ⟨inferInstance, fun 𝔪 h𝔪 htop ↦ ?_⟩⟩
  · -- if `I ⊄ 𝔪`, some `x ∈ 𝔪` is `1 - i` with `i ∈ I`, a unit of `Â`
    rw [Ideal.jacobson, le_sInf_iff]
    rintro 𝔪 ⟨-, h𝔪⟩
    by_contra hI𝔪
    have hsup : I ⊔ 𝔪 = ⊤ :=
      h𝔪.out.2 _ (lt_of_le_of_ne le_sup_right fun h ↦ hI𝔪 (h ▸ le_sup_left))
    obtain ⟨i, hi, x, hx, hix⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top (x := (1 : A)))
    have := AdicCompletion.isAdicComplete_self I (IsNoetherian.noetherian I)
    have hi' := IsAdicComplete.le_jacobson_bot _
      (Ideal.mem_map_of_mem (algebraMap A (AdicCompletion I A)) hi)
    have hunit : IsUnit (algebraMap A (AdicCompletion I A) x) := by
      have := (Ideal.mem_jacobson_bot.1 hi') (-1)
      rwa [mul_neg_one, neg_add_eq_sub, ← map_one (algebraMap A _), ← map_sub,
        ← hix, add_sub_cancel_left] at this
    refine h h𝔪 (eq_top_iff.2 fun y _ ↦ ?_)
    obtain ⟨u, hu⟩ := hunit
    have : y = x • ((u⁻¹ : (AdicCompletion I A)ˣ) * y) := by
      rw [Algebra.smul_def, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
    rw [this]
    exact Submodule.smul_mem_smul hx trivial
  · -- the evaluation `Â → A/I` would give `𝔪 (A/I) = A/I`, i.e. `𝔪 + I = A`
    have hI𝔪 : I ≤ 𝔪 := hI.trans (sInf_le ⟨bot_le, h𝔪⟩)
    let g : AdicCompletion I A →ₗ[A] A ⧸ 𝔪 :=
      ((Ideal.Quotient.factorₐ A hI𝔪).comp (AdicCompletion.evalOneₐ I)).toLinearMap
    have hg : Function.Surjective g :=
      (Ideal.Quotient.factor_surjective hI𝔪).comp (AdicCompletion.evalOneₐ_surjective I)
    have hmap := Submodule.map_smul'' 𝔪 ⊤ g
    rw [htop, Submodule.map_top, LinearMap.range_eq_top.2 hg] at hmap
    have hbot : 𝔪 • (⊤ : Submodule A (A ⧸ 𝔪)) = ⊥ :=
      eq_bot_iff.2 <| Submodule.smul_le.2 fun a ha x _ ↦ by
        rw [Submodule.mem_bot, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
    rw [hbot] at hmap
    have : (1 : A ⧸ 𝔪) = 0 := by
      have h1 : (1 : A ⧸ 𝔪) ∈ (⊤ : Submodule A (A ⧸ 𝔪)) := trivial
      rwa [hmap, Submodule.mem_bot] at h1
    exact h𝔪.ne_top (Ideal.Quotient.zero_eq_one_iff.1 this.symm)

end SGA.SGA1.ExposeIV
