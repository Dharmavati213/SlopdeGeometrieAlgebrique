/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedModuleTorsion
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Tensoring finite ideal-power torsion modules with the completed ring

The map is the original scalar-extension map `x ↦ 1 ⊗ x`. For a finite
module killed by an ideal power, it is an isomorphism. This uses the proved
noetherian completion/tensor comparison and an explicit proof that a
nilpotently filtered module is complete.
-/

noncomputable section

universe u

open TensorProduct

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] (J : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- A filtration which is already zero at one stage is actually complete. -/
theorem isAdicComplete_of_pow_smul_eq_bot (n : ℕ)
    (hn : J ^ n • (⊤ : Submodule R M) = ⊥) : IsAdicComplete J M where
  haus' x hx := by simpa only [hn, SModEq.bot] using hx n
  prec' f hf := by
    refine ⟨f n, fun k => ?_⟩
    by_cases hkn : k ≤ n
    · exact hf hkn
    · have hnk := hf (Nat.le_of_not_ge hkn)
      have heq : f n = f k := by simpa only [hn, SModEq.bot] using hnk
      rw [heq]

/-- The literal scalar-extension map to the tensor product with the completed ring. -/
def adicTensorUnit : M →ₗ[R] AdicCompletion J R ⊗[R] M :=
  TensorProduct.mk R (AdicCompletion J R) M 1

@[simp]
theorem adicTensorUnit_apply (x : M) : adicTensorUnit J M x = 1 ⊗ₜ[R] x := rfl

variable [IsNoetherianRing R]

/-- **IV.4.5, finite nilpotent stage.** The actual scalar-extension map is
bijective, with no completeness hypothesis on the original ring. -/
theorem adicTensorUnit_bijective_of_finite_of_pow_annihilator [Module.Finite R M]
    (n : ℕ) (hn : J ^ n ≤ Module.annihilator R M) :
    Function.Bijective (adicTensorUnit J M) := by
  have hzero : J ^ n • (⊤ : Submodule R M) = ⊥ := by
    apply bot_unique
    apply Submodule.smul_le.mpr
    intro r hr x _
    exact Module.mem_annihilator.mp (hn hr) x
  let := isAdicComplete_of_pow_smul_eq_bot J M n hzero
  have ho := AdicCompletion.of_bijective J M
  have ht := AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian J M
  have hcomp (x : M) :
      AdicCompletion.ofTensorProduct J M (adicTensorUnit J M x) = AdicCompletion.of J M x := by
    simp only [adicTensorUnit_apply, AdicCompletion.ofTensorProduct_tmul, one_smul]
  constructor
  · intro x y hxy
    apply ho.1
    rw [← hcomp, ← hcomp, hxy]
  · intro y
    obtain ⟨x, hx⟩ := ho.2 (AdicCompletion.ofTensorProduct J M y)
    exact ⟨x, ht.1 ((hcomp x).trans hx)⟩

/-- The same finite-stage theorem in terms of actual module support. -/
theorem adicTensorUnit_bijective_of_finite_of_support [Module.Finite R M]
    (hM : Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    Function.Bijective (adicTensorUnit J M) := by
  obtain ⟨n, hn⟩ := (support_subset_zeroLocus_iff_exists_pow_le_annihilator J M).mp hM
  exact adicTensorUnit_bijective_of_finite_of_pow_annihilator J M n hn

end SGA.SGA2.ExposeIV
