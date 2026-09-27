/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.Serre
import SGA.Foundations.Cohomology.CechFinite

/-!
# Serre's finiteness theorem on projective space

Let `A` be a noetherian ring and `F` a quasi-coherent module on `ℙʳ_A = Proj A[x₀, …, x_r]` whose
sections over the standard affines `D₊(xᵢ)` are finitely generated (e.g. a coherent module). Then
every `Hᵖ(ℙʳ_A, F)` is a finitely generated `Γ(ℙʳ_A, 𝒪) = A`-module
(`projectiveSpace.finite_H`; Serre, FAC §66; EGA III 2.2.1 (i); Hartshorne III.5.2 (a)).

The proof is by descending induction on `p`, using `Hᵖ = 0` for `p > r`, the finiteness of the
cohomology of `𝒪(d)` (`projectiveSpace.finite_H_twist`), and the exact sequence
`Hᵖ(𝒪(-m)^k) → Hᵖ(F) → Hᵖ⁺¹(R)` attached to a presentation `0 → R → 𝒪(-m)^k → F → 0`.
-/

universe v u

open CategoryTheory TopologicalSpace Opposite Limits MvPolynomial

namespace AlgebraicGeometry.CohomologyAux

/-- In an exact sequence `M → N → P` of modules over a noetherian ring with `M` and `P` finitely
generated, `N` is finitely generated. -/
lemma finite_of_exact {R M N P : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N)
    (g : N →ₗ[R] P) (h : Function.Exact f g) [Module.Finite R M] [Module.Finite R P] :
    Module.Finite R N := by
  have : _root_.IsNoetherian R P := isNoetherian_of_isNoetherianRing_of_finite R P
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker g ?_ ?_⟩
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq, h.linearMap_ker_eq, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map f

end AlgebraicGeometry.CohomologyAux

namespace AlgebraicGeometry.projectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `Γ(Proj A[xᵢ], 𝒪) ≅ A` is noetherian when `A` is. -/
instance isNoetherianRing_top {σ : Type v} {A : Type u} [CommRing A] [Finite σ] [Nonempty σ]
    [IsNoetherianRing A] : IsNoetherianRing Γ(Proj (homogeneousSubmodule σ A), ⊤) := by
  have := isIso_toSpecZero_appTop (σ := σ) (A := A)
  exact isNoetherianRing_of_ringEquiv _
    ((Scheme.ΓSpecIso (CommRingCat.of (homogeneousSubmodule σ A 0))).symm ≪≫
      asIso (Proj.toSpecZero (homogeneousSubmodule σ A)).appTop).commRingCatIsoToRingEquiv

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ}

/-- The cohomology of `(𝒪^k)(d)` on `ℙʳ_A` is finitely generated. -/
lemma finite_H_twist_unitBiproduct (k q : ℕ) (d : ℤ) :
    Module.Finite Γ(Proj (homogeneousSubmodule (Fin (r + 1)) A), ⊤)
      (((twistingBundle (Fin (r + 1)) A).twist
        (CohomologyAux.unitBiproduct (Proj (homogeneousSubmodule (Fin (r + 1)) A)) k) d).H q) := by
  let L := twistingBundle (Fin (r + 1)) A
  have h := Scheme.Modules.finite_H'_biproduct (n := q) (U := ⊤)
    (fun _ : Fin k ↦ L.twist (CohomologyAux.unitModule _) d)
    fun _ ↦ finite_H_twist (A := A) r d q
  exact Scheme.Modules.finite_H'_of_iso (L.twistBiproductIso d _).symm

/-- **Serre's finiteness theorem**, induction step form. -/
theorem finite_H_aux :
    ∀ (j q : ℕ), r + 1 ≤ q + j → ∀ F : (Proj (homogeneousSubmodule (Fin (r + 1)) A)).Modules,
      IsStdFinite (Fin (r + 1)) A F →
        Module.Finite Γ(Proj (homogeneousSubmodule (Fin (r + 1)) A), ⊤) (F.H q)
  | 0, q, hq, F, hF => by
      obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
      have hsub : Subsingleton (F.H' (p + 1) ⊤) :=
        @H_subsingleton_of_lt (CommRingCat.of A) r F hF.isQuasicoherent p (by omega)
      exact Module.Finite.of_surjective (0 : (Fin 0 → Γ(Proj (homogeneousSubmodule
        (Fin (r + 1)) A), ⊤)) →ₗ[_] F.H' (p + 1) ⊤) fun x ↦ ⟨0, @Subsingleton.elim _ hsub _ _⟩
  | j + 1, q, hq, F, hF => by
      obtain ⟨m, k, π, hπ⟩ := exists_epi_twist hF
      let S := ShortComplex.kernelSequence π
      have hS : S.ShortExact := CohomologyAux.shortExact_kernelSequence π
      have hR : IsStdFinite (Fin (r + 1)) A S.X₁ :=
        IsStdFinite.of_shortExact hS ((IsStdFinite.unitBiproduct k).twist _) hF
      have h₁ : Module.Finite Γ(Proj (homogeneousSubmodule (Fin (r + 1)) A), ⊤)
          (S.X₁.H' (q + 1) ⊤) := finite_H_aux j (q + 1) (by omega) S.X₁ hR
      have h₂ : Module.Finite Γ(Proj (homogeneousSubmodule (Fin (r + 1)) A), ⊤)
          (S.X₂.H' q ⊤) := finite_H_twist_unitBiproduct k q _
      exact CohomologyAux.finite_of_exact (Scheme.Modules.H'.map S.g q ⊤)
        (Scheme.Modules.H'.δ hS q ⊤) (Scheme.Modules.H'.exact_map_δ hS q ⊤)

/-- **Serre's finiteness theorem** (Serre, FAC §66; EGA III 2.2.1 (i); Hartshorne III.5.2 (a)):
for `A` noetherian and `F` a quasi-coherent module on `ℙʳ_A` whose sections over the standard
affines `D₊(xᵢ)` are finitely generated (e.g. a coherent module), every `Hᵖ(ℙʳ_A, F)` is a finitely
generated module over `Γ(ℙʳ_A, 𝒪) = A`. -/
theorem finite_H {F : (Proj (homogeneousSubmodule (Fin (r + 1)) A)).Modules}
    (hF : IsStdFinite (Fin (r + 1)) A F) (p : ℕ) :
    Module.Finite Γ(Proj (homogeneousSubmodule (Fin (r + 1)) A), ⊤) (F.H p) :=
  finite_H_aux (r + 1) p (by omega) F hF

/-- Serre's theorems together (EGA III 2.2.1; Hartshorne III.5.2): for `F` as in `finite_H`, all
`Hᵖ(ℙʳ_A, F(n))` are finitely generated, and they vanish for `p > 0` and `n ≫ 0`. -/
theorem finite_H_twist_and_eventually_subsingleton
    {F : (Proj (homogeneousSubmodule (Fin (r + 1)) A)).Modules}
    (hF : IsStdFinite (Fin (r + 1)) A F) :
    (∀ (n : ℤ) (p : ℕ), Module.Finite Γ(Proj (homogeneousSubmodule (Fin (r + 1)) A), ⊤)
      (((twistingBundle (Fin (r + 1)) A).twist F n).H p)) ∧
    ∃ n₀ : ℤ, ∀ n ≥ n₀, ∀ p : ℕ,
      Subsingleton (((twistingBundle (Fin (r + 1)) A).twist F n).H (p + 1)) :=
  ⟨fun n p ↦ finite_H (hF.twist n) p, exists_H_twist_subsingleton hF⟩

end AlgebraicGeometry.projectiveSpace
