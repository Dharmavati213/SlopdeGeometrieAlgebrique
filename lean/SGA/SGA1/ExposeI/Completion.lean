/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# The map of completions induced by a local homomorphism

Exposé I repeatedly compares a local homomorphism `A → B` with the induced map of
`𝔪`-adic completions `Â → B̂` (I.2.1(iii), I.3.7, I.4.2–I.4.4, I.9.4). Mathlib has the
completions and their local ring structure, but not this map; it is defined here as
the lift of the compatible maps `Â → A/𝔪_Aⁿ → B/𝔪_Bⁿ`.
-/

universe u

namespace SGA.SGA1.ExposeI

open IsLocalRing AdicCompletion

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

lemma maximalIdeal_pow_le_comap (n : ℕ) :
    maximalIdeal A ^ n ≤ (maximalIdeal B ^ n).comap (algebraMap A B) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (map_maximalIdeal_le _) n

/-- The truncations `Â → A/𝔪_Aⁿ → B/𝔪_Bⁿ` of the map of completions. -/
noncomputable def completionMapAux (n : ℕ) :
    AdicCompletion (maximalIdeal A) A →+* B ⧸ maximalIdeal B ^ n :=
  (Ideal.quotientMap _ (algebraMap A B) (maximalIdeal_pow_le_comap A B n)).comp
    (evalₐ (maximalIdeal A) n).toRingHom

lemma completionMapAux_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal B) hle).comp (completionMapAux A B n) =
      completionMapAux A B m := by
  ext x
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective (maximalIdeal A) A x
  simp only [completionMapAux, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    evalₐ_mk, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]
  refine Ideal.Quotient.eq.mpr ?_
  rw [← map_sub]
  refine maximalIdeal_pow_le_comap A B m ?_
  have := c.2 hle
  rwa [SModEq, Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub] at this

/-- The map of `𝔪`-adic completions `Â → B̂` induced by a local homomorphism `A → B`. -/
noncomputable def completionMap :
    AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B :=
  AdicCompletion.liftRingHom (maximalIdeal B) (completionMapAux A B)
    (completionMapAux_compat A B)

@[simp]
lemma evalₐ_completionMap (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    evalₐ (maximalIdeal B) n (completionMap A B x) =
      Ideal.quotientMap _ (algebraMap A B) (maximalIdeal_pow_le_comap A B n)
        (evalₐ (maximalIdeal A) n x) :=
  evalₐ_liftRingHom _ _ _ _ _

/-- The square `A → B → B̂`, `A → Â → B̂` commutes. -/
lemma completionMap_algebraMap (a : A) :
    completionMap A B (algebraMap A _ a) = algebraMap B _ (algebraMap A B a) :=
  ext_evalₐ fun n ↦ by
    rw [evalₐ_completionMap, AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
      evalₐ_of, evalₐ_of, Ideal.quotientMap_mk, Algebra.algebraMap_self, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply]

/-- For noetherian local rings, `Â → B̂` is a local homomorphism. -/
instance isLocalHom_completionMap [IsNoetherianRing A] [IsNoetherianRing B] :
    IsLocalHom (completionMap A B) := by
  apply ((IsLocalRing.local_hom_TFAE _).out 1 4).mpr
  rw [maximalIdeal_eq_map, maximalIdeal_eq_map, ← Ideal.map_le_iff_le_comap, Ideal.map_map]
  have : (completionMap A B).comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp (algebraMap A B) :=
    RingHom.ext (completionMap_algebraMap A B)
  rw [this, ← Ideal.map_map]
  exact Ideal.map_mono (map_maximalIdeal_le _)

/-- If `Â → B̂` is surjective, so is every truncation `A → B/𝔪_Bⁿ`. -/
lemma surjective_quotient_pow_of_surjective_completionMap
    (h : Function.Surjective (completionMap A B)) (n : ℕ) :
    Function.Surjective ((Ideal.Quotient.mk (maximalIdeal B ^ n)).comp (algebraMap A B)) := by
  intro y
  obtain ⟨z, rfl⟩ := surjective_evalₐ (maximalIdeal B) n y
  obtain ⟨x, rfl⟩ := h z
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal A) n x)
  refine ⟨a, ?_⟩
  rw [evalₐ_completionMap, ← ha, Ideal.quotientMap_mk, RingHom.comp_apply]

end SGA.SGA1.ExposeI
