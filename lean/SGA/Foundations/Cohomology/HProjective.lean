/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.ProjectiveMorphism
import SGA.Foundations.Projective.Morphisms
import SGA.Foundations.Projective.ProjectiveSpaceSpec

/-!
# Finiteness of cohomology for H-projective morphisms

**Serre's finiteness theorem for projective morphisms over an affine noetherian base**
(EGA III 2.2.1 / 3.2.1 in the projective case; Hartshorne III.5.2 (a)): let `A` be a noetherian
ring, `f : X ⟶ Spec A` an H-projective morphism (a closed immersion into some `ℙ(σ; Spec A)`
followed by the projection, `AlgebraicGeometry.IsHProjective`) and `M` a coherent `𝒪_X`-module.
Then every `Hᵖ(X, M)` is a finitely generated `A`-module (`properFiniteness_of_isHProjective`).
This is the case of H-projective morphisms of `ProperFinitenessStatement`.

The proof identifies `ℙ(σ; Spec A)` with `Proj A[x₀, …, x_r]` (`ProjectiveSpace.isoProj`,
`ProjectiveSpace.projRenameIso`) and applies `projectiveSpace.finite_H_of_isClosedImmersion`; if
`σ` is empty, `X` is empty and its cohomology vanishes.
-/

universe u

open CategoryTheory TopologicalSpace Opposite Limits MvPolynomial

namespace AlgebraicGeometry

/-- On an empty scheme, all cohomology groups of a quasi-coherent module vanish. -/
lemma Scheme.Modules.subsingleton_H_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (M : X.Modules)
    [M.IsQuasicoherent] (p : ℕ) : Subsingleton (M.H p) := by
  cases p with
  | zero =>
    refine ⟨fun a b ↦ (Scheme.Modules.H.equiv₀ M).injective ?_⟩
    exact TopCat.Sheaf.eq_of_locally_eq' M.toAbSheaf (fun i : PEmpty.{1} ↦ i.elim) ⊤
      (fun i ↦ i.elim) (fun x _ ↦ (IsEmpty.false x).elim) _ _ (fun i ↦ i.elim)
  | succ p =>
    have h := M.H'_subsingleton_of_card_le (fun i : Fin 0 ↦ i.elim0)
      (fun x ↦ (x 0).elim0) (p := p) (by omega)
    change Subsingleton (M.H' (p + 1) ⊤)
    have e : (⊤ : X.Opens) = ⨆ i : Fin 0, (i.elim0 : X.Opens) :=
      le_antisymm (fun x _ ↦ (IsEmpty.false x).elim) le_top
    rw [e]
    exact h

namespace ProjectiveSpace

/-- `Proj R[σ]` is empty for `σ` empty: the irrelevant ideal of `R[∅] = R` is zero. -/
lemma isEmpty_proj_of_isEmpty {σ : Type*} {R : Type*} [CommRing R] [IsEmpty σ] :
    IsEmpty (Proj (grading σ R)) := by
  refine ⟨fun x ↦ x.not_irrelevant_le fun p hp ↦ ?_⟩
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hp
  have h0 : (DirectSum.decompose (grading σ R) p 0 : MvPolynomial σ R) =
      homogeneousComponent 0 p := decomposition.decompose'_apply p 0
  rw [hp, homogeneousComponent_zero] at h0
  rw [eq_C_of_isEmpty p, ← h0]
  exact zero_mem _

/-- The structure morphism `Proj R[σ] ⟶ Spec R` is surjective on global sections (it is even an
isomorphism, for `σ` finite and non-empty). -/
lemma surjective_specStructureRingHom_projToSpec (σ R : Type u) [CommRing R] [Finite σ]
    [Nonempty σ] : Function.Surjective (projToSpec σ R).specStructureRingHom := by
  have hiso : IsIso (Proj.toSpecZero (grading σ R)).appTop :=
    projectiveSpace.isIso_toSpecZero_appTop (σ := σ) (A := R)
  have e : (projToSpec σ R).specStructureRingHom =
      ((CommRingCat.ofHom (algebraMap R (grading σ R 0))) ≫
        (Scheme.ΓSpecIso _).inv ≫ (Proj.toSpecZero (grading σ R)).appTop).hom := by
    rw [Scheme.Hom.specStructureRingHom, projToSpec, Scheme.Hom.comp_appTop,
      Scheme.ΓSpecIso_inv_naturality_assoc]
  rw [e, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Surjective.comp ?_ (bijective_algebraMap_grading_zero (σ := σ) (R := R)).2
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).2.comp
    (ConcreteCategory.bijective_of_isIso _).2

end ProjectiveSpace

open ProjectiveSpace in
/-- **Finiteness of cohomology for projective morphisms over an affine noetherian base**
(EGA III 2.2.1 and 3.2.1 in the projective case; Stacks Tag 02O5; Hartshorne III.5.2 (a) and
III.8.8 (b)): for `A` noetherian, `f : X ⟶ Spec A` H-projective and `M` coherent, every
`Hᵖ(X, M)` is a finitely generated `A`-module. This is `ProperFinitenessStatement` for H-projective
morphisms. -/
theorem properFiniteness_of_isHProjective (A : CommRingCat.{u}) [IsNoetherianRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec A) [hf : IsHProjective f] (M : X.Modules) [hM : M.IsCoherent]
    (p : ℕ) :
    letI := M.moduleOver f p ⊤
    Module.Finite A (M.H p) := by
  obtain ⟨σ, _, i, hi, rfl⟩ := hf.exists_isClosedImmersion
  have hMq : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · have : IsEmpty X := ⟨fun x ↦ (isEmpty_proj_of_isEmpty (σ := σ) (R := ULift.{u} ℤ)).false
      ((i ≫ toProj σ _).base x)⟩
    have := M.subsingleton_H_of_isEmpty p
    let _ := M.moduleOver (i ≫ ℙ(σ; Spec A) ↘ Spec A) p ⊤
    exact Module.Finite.of_surjective (0 : (Fin 0 → A) →ₗ[A] M.H' p ⊤)
      fun x ↦ ⟨0, Subsingleton.elim _ _⟩
  · obtain ⟨r, hr⟩ : ∃ r, Nat.card σ = r + 1 :=
      ⟨Nat.card σ - 1, by have := Nat.card_pos (α := σ); omega⟩
    let e : Fin (r + 1) ≃ σ := ((Finite.equivFin σ).trans (finCongr hr)).symm
    let iso : Proj (grading (Fin (r + 1)) A) ≅ ℙ(σ; Spec A) :=
      projRenameIso e ≪≫ isoProj σ A
    let j : X ⟶ Proj (grading (Fin (r + 1)) A) := i ≫ iso.inv
    have hj : IsClosedImmersion j := inferInstance
    let π : Proj (grading (Fin (r + 1)) A) ⟶ Spec A := iso.hom ≫ ℙ(σ; Spec A) ↘ Spec A
    have hjπ : j ≫ π = i ≫ ℙ(σ; Spec A) ↘ Spec A := by
      simp [j, π]
    have hπ : Function.Surjective π.specStructureRingHom := by
      have e1 : π = (projRenameIso e).hom ≫ projToSpec σ A := by
        simp only [π, iso, Iso.trans_hom, Category.assoc]
        exact congrArg ((projRenameIso e).hom ≫ ·) (isoProj_hom_over σ A)
      have e2 : π.specStructureRingHom =
          (projRenameIso e).hom.appTop.hom.comp (projToSpec σ A).specStructureRingHom := by
        rw [e1, Scheme.Hom.specStructureRingHom, Scheme.Hom.specStructureRingHom,
          Scheme.Hom.comp_appTop]
        rfl
      have : IsIso ((projRenameIso (R := A) e).hom.app ⊤) := inferInstance
      rw [e2, RingHom.coe_comp]
      exact (ConcreteCategory.bijective_of_isIso ((projRenameIso (R := A) e).hom.app ⊤)).2.comp
        (surjective_specStructureRingHom_projToSpec σ A)
    have h := projectiveSpace.finite_H_of_isClosedImmersion (A := A) r j (hj := hj) M p
    have h' := CohomologyAux.finite_moduleOver_of_comp j π hπ M p ⊤ h
    rw [hjπ] at h'
    exact h'

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- The structure sheaf is coherent: it is quasi-coherent and generated by the global section
`1`. -/
instance CohomologyAux.isCoherent_unitModule (X : Scheme.{u}) :
    (CohomologyAux.unitModule X).IsCoherent where
  isQuasicoherent := inferInstance
  isFiniteType := by
    have : (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}).IsFiniteType :=
      Scheme.Modules.isFiniteType_of_generatingSections
        (SheafOfModules.free.generatingSections PUnit.{u + 1})
        (hσ := ⟨inferInstanceAs (Finite PUnit)⟩)
    have : (∐ fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit X.ringCatSheaf).IsFiniteType := this
    exact Scheme.Modules.isFiniteType_of_iso
      (Limits.coproductUniqueIso fun _ : PUnit ↦ SheafOfModules.unit X.ringCatSheaf)

/-- **Global functions on a projective scheme over a noetherian ring** (EGA III 3.2.1 for `p = 0`,
in the projective case; Hartshorne III.8.8 (b) for `f_* 𝒪_X`): for `A` noetherian and
`f : X ⟶ Spec A` H-projective, `Γ(X, 𝒪_X)` is a finite `A`-algebra. -/
theorem finite_specStructureRingHom_of_isHProjective (A : CommRingCat.{u}) [IsNoetherianRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec A) [IsHProjective f] : f.specStructureRingHom.Finite := by
  have h := properFiniteness_of_isHProjective A X f (CohomologyAux.unitModule X) 0
  let _ := (CohomologyAux.unitModule X).moduleOver f 0 ⊤
  let _ : Algebra A Γ(X, ⊤) := f.specStructureRingHom.toAlgebra
  let e0 := Scheme.Modules.H.equiv₀ (CohomologyAux.unitModule X)
  let e : (CohomologyAux.unitModule X).H 0 ≃ₗ[A] Γ(X, ⊤) :=
    { toAddEquiv := e0.toAddEquiv
      map_smul' := fun a x ↦ by
        change e0 (f.specStructureRingHom a • x) = _
        rw [LinearEquiv.map_smul]
        rfl }
  change Module.Finite A Γ(X, ⊤)
  exact Module.Finite.equiv e

end AlgebraicGeometry
