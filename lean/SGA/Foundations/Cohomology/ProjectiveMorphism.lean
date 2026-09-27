/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.Coherent
import SGA.Foundations.Cohomology.Pushforward

/-!
# Finiteness of cohomology for closed subschemes of projective space

Let `A` be a noetherian ring, `j : X ⟶ ℙʳ_A` a closed immersion and `M` a coherent `𝒪_X`-module.
Then `j_* M` is coherent on `ℙʳ_A` (`projectiveSpace.IsStdFinite.pushforward`) and
`Hᵖ(X, M) ≅ Hᵖ(ℙʳ_A, j_* M)` (`CohomologyAux.finite_H'_of_pushforward`), so every `Hᵖ(X, M)` is a
finitely generated `A`-module (`projectiveSpace.finite_H_of_isClosedImmersion`; EGA III 2.2.1,
Hartshorne III.5.2 (a)). With respect to any morphism `f : X ⟶ Spec A` factoring as `j` followed by
a morphism `ℙʳ_A ⟶ Spec A` which is surjective on global sections, this gives the finiteness of
`Hᵖ(X, M)` over `A` for the `A`-module structure of `ProperFinitenessStatement`.
-/

universe v u

open CategoryTheory TopologicalSpace Opposite Limits MvPolynomial

namespace AlgebraicGeometry.CohomologyAux

variable {X P : Scheme.{u}}

/-- If `f = j ≫ π` with `π : P ⟶ Spec A` surjective on global sections, a cohomology module of an
`𝒪_X`-module which is finitely generated over `Γ(P, 𝒪_P)` (acting through `j`) is finitely
generated over `A` (acting through `f`). -/
lemma finite_moduleOver_of_comp {A : CommRingCat.{u}} (j : X ⟶ P) (π : P ⟶ Spec A)
    (hπ : Function.Surjective π.specStructureRingHom) (M : X.Modules) (p : ℕ) (U : X.Opens)
    (h : letI := Module.compHom (M.H' p U) j.appTop.hom
      Module.Finite Γ(P, ⊤) (M.H' p U)) :
    letI := M.moduleOver (j ≫ π) p U
    Module.Finite A (M.H' p U) := by
  have e : (j ≫ π).specStructureRingHom = j.appTop.hom.comp π.specStructureRingHom := by
    rw [Scheme.Hom.specStructureRingHom, Scheme.Hom.specStructureRingHom, Scheme.Hom.comp_appTop]
    rfl
  let _ := Module.compHom (M.H' p U) j.appTop.hom
  have := finite_compHom_of_surjective (M := M.H' p U) π.specStructureRingHom hπ
  unfold Scheme.Modules.moduleOver
  rw [e]
  exact this

end AlgebraicGeometry.CohomologyAux

namespace AlgebraicGeometry.projectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ : Type v} {A : Type u} [CommRing A] [Fintype σ] [DecidableEq σ] [Nonempty σ]

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
/-- **Direct images of coherent modules along closed immersions into `Proj A[xᵢ]` are coherent**
(EGA I 9.2.2, 9.1.13 for finite type): they belong to the class of Serre's theorems. -/
lemma IsStdFinite.pushforward {X : Scheme.{max u v}} (j : X ⟶ Proj (homogeneousSubmodule σ A))
    [IsClosedImmersion j] (M : X.Modules) [M.IsCoherent] :
    IsStdFinite σ A ((Scheme.Modules.pushforward j).obj M) where
  isQuasicoherent := by
    have := (Scheme.Modules.IsCoherent.isQuasicoherent : M.IsQuasicoherent)
    exact CohomologyAux.isQuasicoherent_pushforward j M
  finite i := by
    have := (Scheme.Modules.IsCoherent.isQuasicoherent : M.IsQuasicoherent)
    have := (Scheme.Modules.IsCoherent.isFiniteType : M.IsFiniteType)
    have := CohomologyAux.finite_sections_of_isFiniteType M ((isAffineOpen_topStd i).preimage j)
    exact CohomologyAux.finite_compHom_of_surjective (M := Γ(M, j ⁻¹ᵁ topStd σ A i))
      (j.app (topStd σ A i)).hom
      (j.app_surjective _ (isAffineOpen_topStd i))

/-- **Serre's finiteness theorem for closed subschemes of projective space**
(EGA III 2.2.1; Hartshorne III.5.2 (a)): for `A` noetherian, `j : X ⟶ ℙʳ_A` a closed immersion and
`M` coherent on `X`, every `Hᵖ(X, M)` is a finitely generated `Γ(ℙʳ_A, 𝒪) = A`-module (acting
through `j`). -/
theorem finite_H_of_isClosedImmersion {A : Type u} [CommRing A] [IsNoetherianRing A] (r : ℕ)
    {X : Scheme.{u}} (j : X ⟶ Proj (homogeneousSubmodule (Fin (r + 1)) A))
    [hj : IsClosedImmersion j] (M : X.Modules) [M.IsCoherent] (p : ℕ) :
    letI := Module.compHom (M.H p) j.appTop.hom
    Module.Finite Γ(Proj (homogeneousSubmodule (Fin (r + 1)) A), ⊤) (M.H p) := by
  have := (Scheme.Modules.IsCoherent.isQuasicoherent : M.IsQuasicoherent)
  have hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin (r + 1)),
      IsAffineOpen (TopCat.Presheaf.cechOpen (stdCover (Fin (r + 1)) A) x) := fun x ↦ by
    rw [cechOpen_stdCover]
    exact Proj.isAffineOpen_basicOpen _ _ (prodX_mem _) (image_nonempty x).card_pos
  have h1 : Module.Finite Γ(Proj (homogeneousSubmodule (Fin (r + 1)) A), ⊤)
      (((Scheme.Modules.pushforward j).obj M).H' p (⨆ i, stdCover (Fin (r + 1)) A i)) := by
    rw [iSup_stdCover]
    exact finite_H (IsStdFinite.pushforward j M) p
  have h2 := CohomologyAux.finite_H'_of_pushforward j M (stdCover (Fin (r + 1)) A) hU p
  have e : (⨆ i, j ⁻¹ᵁ stdCover (Fin (r + 1)) A i) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_stdCover]
    rfl
  rw [e] at h2
  exact h2

/-- **Finiteness of cohomology for closed subschemes of `ℙʳ_A`, over the base** (EGA III 2.2.1;
Hartshorne III.5.2 (a)): let `A` be noetherian, `j : X ⟶ ℙʳ_A` a closed immersion, `M` coherent on
`X`, and `f = j ≫ toSpec A r : X ⟶ Spec A`. Then every `Hᵖ(X, M)` is a finitely generated `A`-module
for the `A`-module structure given by `f`. -/
theorem finite_H_moduleOver_of_isClosedImmersion (A : CommRingCat.{u}) [IsNoetherianRing A]
    (r : ℕ) {X : Scheme.{u}} (j : X ⟶ projectiveSpace A r) [hj : IsClosedImmersion j]
    (M : X.Modules) [M.IsCoherent] (p : ℕ) :
    letI := M.moduleOver (j ≫ toSpec A r) p ⊤
    Module.Finite A (M.H p) :=
  CohomologyAux.finite_moduleOver_of_comp j (toSpec A r)
    (surjective_specStructureRingHom_toSpec A r) M p ⊤
    (finite_H_of_isClosedImmersion (A := A) r j (hj := hj) M p)

end AlgebraicGeometry.projectiveSpace
