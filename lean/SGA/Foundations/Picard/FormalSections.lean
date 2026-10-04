/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.AdicSheafSystem
import SGA.Foundations.Cohomology.BaseChangeCover
import SGA.Foundations.Cohomology.ExistenceFullyFaithful
import SGA.Foundations.Cohomology.FormalFunctions

/-!
# Lifting compatible local sections modulo powers of an ideal

Let `A` be a noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` proper and `F` a coherent
`𝒪_X`-module. Given a finite cover of `X` by affine opens `Uᵢ` with affine intersections and, for
every `n`, sections `sₙ,ᵢ ∈ Γ(F, Uᵢ)` which agree on the `Uᵢ ∩ Uⱼ` modulo `Iⁿ⁺¹` and satisfy
`sₙ₊₁,ᵢ ≡ sₙ,ᵢ (mod Iⁿ⁺¹)`, there is a global section `t ∈ Γ(F, X)` with `t ≡ s₀,ᵢ (mod I)` on
every `Uᵢ` (`AlgebraicGeometry.CohomologyAux.exists_section_sub_mem_of_compatible`). This is the
theorem on formal functions in degree `0` (EGA III 4.1.5, in the form
`exists_H'_map_toQuotientIdealPow_eq`), stated for local sections; for `F = 𝒪_X` it is
`CohomologyAux.exists_lift`. We use it for the modules `L.toModules n` of line bundles.

## References

* [A. Grothendieck, J. Dieudonné, *EGA* III 4.1.5][EGA]
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A) (F : X.Modules) [F.IsCoherent]

/-- The theorem on formal functions for local sections of a coherent module: compatible families
of local sections over the thickenings lift, modulo `I`, to a global section. -/
theorem exists_section_sub_mem_of_compatible [IsProper f] {ι : Type*} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
    (hUa₂ : ∀ i j, IsAffineOpen (U i ⊓ U j)) (s : ℕ → ∀ i, Γ(F, U i))
    (h₁ : ∀ n i j, F.presheaf.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op (s n i) -
      F.presheaf.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op (s n j) ∈
        (idealV f I (U i ⊓ U j) 1 ^ (n + 1) • ⊤ : Submodule Γ(X, U i ⊓ U j) Γ(F, U i ⊓ U j)))
    (h₂ : ∀ n i, s (n + 1) i - s n i ∈
      (idealV f I (U i) 1 ^ (n + 1) • ⊤ : Submodule Γ(X, U i) Γ(F, U i))) :
    ∃ t : Γ(F, ⊤), ∀ i, F.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op t - s 0 i ∈
      (idealV f I (U i) 1 ^ (0 + 1) • ⊤ : Submodule Γ(X, U i) Γ(F, U i)) := by
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  -- glue the images of the `sₙ,ᵢ` in `F / Iⁿ⁺¹ F`
  have hglue (n : ℕ) : ∃ z : Γ(F.quotientIdealPow f I n, ⊤), ∀ i,
      (F.quotientIdealPow f I n).presheaf.map (homOfLE le_top : U i ⟶ ⊤).op z =
        (F.toQuotientIdealPow f I n).app (U i) (s n i) := by
    refine exists_glue_of_iSup_eq_top (F.quotientIdealPow f I n) U hU _ fun i j ↦ ?_
    rw [← sub_eq_zero, ← hom_app_presheaf_map, ← hom_app_presheaf_map, ← map_sub,
      quotientIdealPow_app_eq_zero_iff I f F n (hUa₂ i j)]
    exact h₁ n i j
  choose z hz using hglue
  -- the glued sections are compatible
  have hcompat (n : ℕ) : (F.quotientIdealPowMap f I n).app ⊤ (z (n + 1)) = z n := by
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_map_eq_zero (F.quotientIdealPow f I n) U hU _ fun i ↦ ?_
    rw [map_sub, ← hom_app_presheaf_map, hz, hz, ← ConcreteCategory.comp_apply,
      ← Scheme.Modules.Hom.comp_app, Scheme.Modules.toQuotientIdealPow_comp_map, ← map_sub,
      quotientIdealPow_app_eq_zero_iff I f F n (hUa i)]
    exact h₂ n i
  -- the theorem on formal functions
  obtain ⟨y, hy⟩ := exists_H'_map_toQuotientIdealPow_eq I f F 0
    ⟨_, mem_formalLimit_of_compat' I f F z hcompat⟩ 0
  refine ⟨Scheme.Modules.H.equiv₀ _ y, fun i ↦ ?_⟩
  have ht : (F.toQuotientIdealPow f I 0).app ⊤ (Scheme.Modules.H.equiv₀ _ y) = z 0 := by
    rw [← equiv₀_H'_map_toQuotientIdealPow', hy]
    exact (Scheme.Modules.H.equiv₀ _).apply_symm_apply _
  rw [← quotientIdealPow_app_eq_zero_iff I f F 0 (hUa i), map_sub, hom_app_presheaf_map, ht,
    hz, sub_self]

end AlgebraicGeometry.CohomologyAux
