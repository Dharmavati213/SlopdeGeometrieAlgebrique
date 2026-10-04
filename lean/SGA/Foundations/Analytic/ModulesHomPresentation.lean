/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ModulesHomFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Hom-stalk comparison for finite presentations

The canonical map from the stalk of the Hom sheaf to homomorphisms of stalk modules
is bijective for a source with a finite presentation. The proof compares the kernels
obtained by applying Hom to a finite free presentation before and after taking stalks.

Adopted from the unmerged branch `codex/foundations-missing-inputs` (commit `c65c9a0`, file
`ModuleHomPresentation.lean`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}} (N : X.Modules) (x : X)

/-- The Hom-stalk comparison descends through a right exact source presentation. -/
theorem bijective_homStalkMap_of_rightExact (C : ShortComplex X.Modules) (hC : C.Exact)
    [Epi C.g] (h₁ : Function.Injective (homStalkMap C.X₁ N x))
    (h₂ : Function.Bijective (homStalkMap C.X₂ N x)) :
    Function.Bijective (homStalkMap C.X₃ N x) := by
  have hgi : Function.Injective (stalkMap (sheafHomPrecomp C.g N) x) :=
    (ModuleCat.mono_iff_injective ((stalkFunctor x).map (sheafHomPrecomp C.g N))).mp inferInstance
  have hgs : Function.Surjective (stalkMap C.g x) :=
    (ModuleCat.epi_iff_surjective ((stalkFunctor x).map C.g)).mp inferInstance
  have hzero : (stalkMap C.g x).comp (stalkMap C.f x) = 0 := by
    have h : (stalkFunctor x).map C.f ≫ (stalkFunctor x).map C.g = 0 := by
      rw [← Functor.map_comp, C.zero, Functor.map_zero]
    exact congrArg ModuleCat.Hom.hom h
  constructor
  · intro s t hst
    apply hgi
    apply h₂.injective
    rw [homStalkMap_precomp, homStalkMap_precomp, hst]
  · intro t
    obtain ⟨s₂, hs₂⟩ := h₂.surjective (t.comp (stalkMap C.g x))
    have hs₁ : stalkMap (sheafHomPrecomp C.f N) x s₂ = 0 := by
      apply h₁
      rw [homStalkMap_precomp, hs₂, map_zero, LinearMap.comp_assoc, hzero, LinearMap.comp_zero]
    have hH := (exact_sheafHomComplex C hC N).map (stalkFunctor x)
    obtain ⟨s₃, hs₃⟩ := (ShortComplex.moduleCat_exact_iff _).mp hH s₂ hs₁
    change stalkMap (sheafHomPrecomp C.g N) x s₃ = s₂ at hs₃
    refine ⟨s₃, ?_⟩
    apply LinearMap.ext
    intro m
    obtain ⟨m₂, rfl⟩ := hgs m
    have h := homStalkMap_precomp C.X₃ N x C.g s₃
    rw [hs₃, hs₂] at h
    exact (congrArg (fun f ↦ f m₂) h).symm

/-- The canonical Hom-stalk comparison is bijective for a source with a specified
finite global presentation. -/
theorem bijective_homStalkMap_of_finitePresentation {M : X.Modules}
    (P : M.Presentation) [P.IsFinite] : Function.Bijective (homStalkMap M N x) := by
  let C : ShortComplex X.Modules :=
    ShortComplex.mk (P.relations.π ≫ kernel.ι P.generators.π) P.generators.π (by simp)
  have hC : C.Exact := ShortComplex.exact_of_g_is_cokernel C P.isColimit
  have : Epi C.g := (inferInstance : Epi P.generators.π)
  exact bijective_homStalkMap_of_rightExact N x C hC
    (bijective_homStalkMap_free N x P.relations.I).injective
    (bijective_homStalkMap_free N x P.generators.I)

/-- The stalk of the Hom sheaf agrees with Hom of stalks for a finitely presented
source, given a finite global presentation. -/
def homStalkEquivOfPresentation {M : X.Modules} (P : M.Presentation) [P.IsFinite] :
    (sheafHom M N).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x) :=
  LinearEquiv.ofBijective (homStalkMap M N x)
    (bijective_homStalkMap_of_finitePresentation N x P)

end AlgebraicGeometry.LocallyRingedSpace.Modules
