/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.Algebra.Module.Projective

/-!
# Finite modules over a complete ring and topological Nakayama

Over a noetherian adically complete ring, the original completion map of
every finite module is an isomorphism. The comparison is obtained from
the actual tensor-product completion map, not from a replacement module.

Conversely, a Hausdorff module with finite reduction modulo the ideal is
finite. A finite free cover of that reduction is lifted through the actual
quotient map; completeness of its source makes the lift surjective.
No completeness or finite generation of the target is assumed.
-/

noncomputable section

universe u

open TensorProduct

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (J : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Tensoring with the completed ring is the identity when that ring is
already complete. This equivalence sends `x` to the actual tensor `1 ⊗ x`. -/
def completeRingTensorEquiv [IsAdicComplete J R] :
    M ≃ₗ[R] AdicCompletion J R ⊗[R] M :=
  (TensorProduct.lid R M).symm.trans
    (TensorProduct.congr (AdicCompletion.ofLinearEquiv J R) (LinearEquiv.refl R M))

@[simp]
theorem completeRingTensorEquiv_apply [IsAdicComplete J R] (x : M) :
    completeRingTensorEquiv J M x = 1 ⊗ₜ[R] x := by
  have h : AdicCompletion.of J R 1 = 1 := by
    change (algebraMap R (AdicCompletion J R)) 1 = 1
    exact map_one _
  simp [completeRingTensorEquiv, h]

/-- The tensor-product comparison recovers the original completion map. -/
@[simp]
theorem ofTensorProduct_completeRingTensorEquiv [IsAdicComplete J R] (x : M) :
    AdicCompletion.ofTensorProduct J M (completeRingTensorEquiv J M x) =
      AdicCompletion.of J M x := by
  simp

/-- The original completion map of a finite module is bijective over a
noetherian complete ring. -/
theorem completion_of_bijective_of_finite [IsNoetherianRing R]
    [IsAdicComplete J R] [Module.Finite R M] :
    Function.Bijective (AdicCompletion.of J M) := by
  have h := (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian J M).comp
    (completeRingTensorEquiv J M).bijective
  simpa only [Function.comp_def, ofTensorProduct_completeRingTensorEquiv] using h

/-- Every finite module over a noetherian complete ring is complete for
the original ideal-adic filtration. -/
theorem isAdicComplete_of_finite [IsNoetherianRing R]
    [IsAdicComplete J R] [Module.Finite R M] : IsAdicComplete J M :=
  AdicCompletion.of_bijective_iff.mp (completion_of_bijective_of_finite J M)

omit M [AddCommGroup M] [Module R M] in
/-- Finite free modules are complete over any complete ring; no
noetherianity is needed for this special case. -/
theorem isAdicComplete_finite_free [IsAdicComplete J R] (n : ℕ) :
    IsAdicComplete J (Fin n → R) := by
  apply AdicCompletion.of_bijective_iff.mp
  have h := (AdicCompletion.ofTensorProduct_bijective_of_pi_of_fintype J (Fin n)).comp
    (completeRingTensorEquiv J (Fin n → R)).bijective
  simpa only [Function.comp_def, ofTensorProduct_completeRingTensorEquiv] using h

/-- A finite free cover of the reduction lifts to an actual surjection
onto a Hausdorff module. This records the map used in topological Nakayama. -/
theorem exists_finite_free_surjection_of_finite_reduction
    [IsAdicComplete J R] [IsHausdorff J M]
    [Module.Finite R (M ⧸ (J • ⊤ : Submodule R M))] :
    ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Function.Surjective f := by
  let N : Submodule R M := J • ⊤
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R (M ⧸ N)
  obtain ⟨f, hf⟩ := Module.projective_lifting_property N.mkQ g N.mkQ_surjective
  have : IsAdicComplete J (Fin n → R) := isAdicComplete_finite_free J n
  refine ⟨n, f, surjective_of_mkQ_comp_surjective (I := J) ?_⟩
  change Function.Surjective (N.mkQ ∘ₗ f)
  rwa [hf]

/-- **Topological Nakayama.** Separatedness and finite reduction suffice
for finite generation; target completeness is a conclusion, not a hypothesis. -/
theorem finite_of_isHausdorff_of_finite_reduction
    [IsAdicComplete J R] [IsHausdorff J M]
    [Module.Finite R (M ⧸ (J • ⊤ : Submodule R M))] : Module.Finite R M := by
  obtain ⟨n, f, hf⟩ := exists_finite_free_surjection_of_finite_reduction J M
  exact Module.Finite.of_surjective f hf

/-- The same separated module is consequently complete. -/
theorem isAdicComplete_of_isHausdorff_of_finite_reduction [IsNoetherianRing R]
    [IsAdicComplete J R] [IsHausdorff J M]
    [Module.Finite R (M ⧸ (J • ⊤ : Submodule R M))] : IsAdicComplete J M := by
  have := finite_of_isHausdorff_of_finite_reduction J M
  exact isAdicComplete_of_finite J M

end SGA.SGA2.ExposeIV
