/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.SerreFiniteness
import SGA.Foundations.Cohomology.Statements
import SGA.Foundations.QuasiCoherent.Tilde
import SGA.Foundations.QuasiCoherent.SpecSections

/-!
# Coherent modules on projective space

* `CohomologyAux.finite_sections_of_isFiniteType`: the sections of a quasi-coherent module of
  finite type over an affine open `V` form a finitely generated `Γ(X, V)`-module (EGA I 1.3.12,
  1.4.3; Stacks Tag 01PB).
* `projectiveSpace.IsStdFinite.of_isCoherent`: coherent modules on `Proj A[xᵢ]` belong to the class
  of Serre's theorems.
* `CohomologyAux.finite_compHom_of_surjective`: finiteness descends along a surjective ring map.
* `projectiveSpace.finite_H_moduleOver`: **Serre's finiteness theorem over the base**: for `A`
  noetherian and `M` coherent on `ℙʳ_A`, every `Hᵖ(ℙʳ_A, M)` is a finitely generated `A`-module
  (EGA III 2.2.1; Hartshorne III.5.2 (a)), for the `A`-module structure given by the structure
  morphism `ℙʳ_A ⟶ Spec A` (`Scheme.Modules.moduleOver`). This is the case
  `X = ℙʳ_A` of `ProperFinitenessStatement`.
-/

universe v u

open CategoryTheory TopologicalSpace Opposite Limits MvPolynomial

namespace AlgebraicGeometry.CohomologyAux

variable {X : Scheme.{u}}

/-- **Sections of coherent modules over affines are finitely generated** (EGA I 1.3.12 and
1.4.3; Stacks Tag 01PB): for `F` quasi-coherent of finite type and `V` an affine open, `Γ(V, F)` is
a finitely generated `Γ(V, 𝒪_X)`-module. -/
theorem finite_sections_of_isFiniteType (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    {V : X.Opens} (hV : IsAffineOpen V) : Module.Finite Γ(X, V) Γ(F, V) := by
  let G := F.restrict hV.fromSpec
  have : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).app F).symm
  have : G.IsFiniteType := Scheme.Modules.isFiniteType_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).app F).symm
  have : (tilde G.ΓSpec).IsFiniteType := Scheme.Modules.isFiniteType_of_iso G.tildeΓIso.symm
  have hfin : Module.Finite Γ(X, V) G.ΓSpec := (isFiniteType_tilde_iff _).mp this
  have hW : ⊤ ⊓ V = hV.fromSpec ''ᵁ ⊤ := by
    rw [top_inf_eq, Scheme.Hom.image_top_eq_opensRange, hV.opensRange_fromSpec]
  have hfin' : Module.Finite Γ(X, V) Γ(G, ⊤) := hfin
  have h2 : Module.Finite Γ(X, V) ((F.presheafInf V).obj (op ⊤)) :=
    Module.Finite.of_surjective (F.restrictFromSpecₗ hV ⊤ ⊤ hW.le)
      (F.bijective_restrictFromSpecₗ hV ⊤ ⊤ hW).2
  let res : (F.presheafInf V).obj (op ⊤) →ₗ[Γ(X, V)] Γ(F, V) :=
    { toFun := fun s ↦ F.presheaf.map (homOfLE (le_inf le_top le_rfl : V ≤ ⊤ ⊓ V)).op s
      map_add' := fun _ _ ↦ map_add _ _ _
      map_smul' := fun r s ↦ by
        change F.presheaf.map (homOfLE (le_inf le_top le_rfl : V ≤ ⊤ ⊓ V)).op
            (X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op r • @id Γ(F, ⊤ ⊓ V) s) =
          r • F.presheaf.map (homOfLE (le_inf le_top le_rfl : V ≤ ⊤ ⊓ V)).op s
        rw [Scheme.Modules.map_smul, presheaf_map_map, presheaf_map_self]
        rfl }
  refine Module.Finite.of_surjective res fun t ↦
    ⟨F.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op t, ?_⟩
  change F.presheaf.map _ (F.presheaf.map _ t) = t
  rw [TopCat.Presheaf.map_map_apply, CohomologyAux.modules_map_self]

/-- **Finite type from finitely generated sections** (EGA I 1.3.12; Stacks Tag 01PB): a
quasi-coherent module whose sections over each member of an affine open cover are finitely
generated is of finite type. -/
theorem isFiniteType_of_finite_sections (F : X.Modules) [F.IsQuasicoherent] {ι : Type u}
    (V : ι → X.Opens) (hV : ⨆ i, V i = ⊤) (hVa : ∀ i, IsAffineOpen (V i))
    (hfin : ∀ i, Module.Finite Γ(X, V i) Γ(F, V i)) : F.IsFiniteType := by
  refine Scheme.Modules.isFiniteType_of_forall_pullback (fun i ↦ (hVa i).fromSpec)
    (fun x ↦ ?_) fun i ↦ ?_
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hV.ge (Set.mem_univ x))
    refine ⟨i, ?_⟩
    rw [← Scheme.Hom.coe_opensRange, (hVa i).opensRange_fromSpec]
    exact hi
  · let G := F.restrict (hVa i).fromSpec
    have : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (hVa i).fromSpec).app F).symm
    have hW : ⊤ ⊓ V i = (hVa i).fromSpec ''ᵁ ⊤ := by
      rw [top_inf_eq, Scheme.Hom.image_top_eq_opensRange, (hVa i).opensRange_fromSpec]
    have := hfin i
    let res : Γ(F, V i) →ₗ[Γ(X, V i)] (F.presheafInf (V i)).obj (op ⊤) :=
      { toFun := fun t ↦ F.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V i ≤ V i)).op t
        map_add' := fun _ _ ↦ map_add _ _ _
        map_smul' := fun r t ↦ by
          change F.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V i ≤ V i)).op (r • t) =
            X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V i ≤ V i)).op r •
              F.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V i ≤ V i)).op t
          rw [Scheme.Modules.map_smul] }
    have h1 : Module.Finite Γ(X, V i) ((F.presheafInf (V i)).obj (op ⊤)) :=
      Module.Finite.of_surjective res fun s ↦
        ⟨F.presheaf.map (homOfLE (le_inf le_top le_rfl : V i ≤ ⊤ ⊓ V i)).op s, by
          change F.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V i ≤ V i)).op
              (F.presheaf.map (homOfLE (le_inf le_top le_rfl : V i ≤ ⊤ ⊓ V i)).op
                (@id Γ(F, ⊤ ⊓ V i) s)) = @id Γ(F, ⊤ ⊓ V i) s
          rw [TopCat.Presheaf.map_map_apply, CohomologyAux.modules_map_self]⟩
    have h2 : Module.Finite Γ(X, V i) Γ(G, ⊤) := Module.Finite.equiv
      (LinearEquiv.ofBijective (F.restrictFromSpecₗ (hVa i) ⊤ ⊤ hW.le)
        (F.bijective_restrictFromSpecₗ (hVa i) ⊤ ⊤ hW)).symm
    have h3 : Module.Finite Γ(X, V i) G.ΓSpec := h2
    have : (tilde G.ΓSpec).IsFiniteType := (isFiniteType_tilde_iff _).mpr h3
    have : G.IsFiniteType := Scheme.Modules.isFiniteType_of_iso G.tildeΓIso
    exact Scheme.Modules.isFiniteType_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (hVa i).fromSpec).app F)

/-- Finiteness descends along a surjective ring homomorphism `A → R`: a finitely generated
`R`-module is a finitely generated `A`-module. -/
lemma finite_compHom_of_surjective {A R M : Type*} [CommRing A] [CommRing R] [AddCommGroup M]
    [Module R M] (φ : A →+* R) (hφ : Function.Surjective φ) [Module.Finite R M] :
    letI := Module.compHom M φ
    Module.Finite A M := by
  let _ := Module.compHom M φ
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := M)
  refine ⟨⟨S, eq_top_iff.mpr fun x hx0 ↦ ?_⟩⟩
  clear hx0
  have hx : x ∈ Submodule.span R (S : Set M) := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul r y _ hy =>
    obtain ⟨a, rfl⟩ := hφ r
    exact Submodule.smul_mem _ a hy

/-- For `f : X ⟶ Spec A` with `A → Γ(X, 𝒪_X)` surjective, a cohomology module which is finitely
generated over `Γ(X, 𝒪_X)` is finitely generated over `A`. -/
lemma finite_moduleOver_of_surjective {A : CommRingCat.{u}} (f : X ⟶ Spec A)
    (hf : Function.Surjective f.specStructureRingHom) (M : X.Modules) (p : ℕ) (U : X.Opens)
    [Module.Finite Γ(X, ⊤) (M.H' p U)] :
    letI := M.moduleOver f p U
    Module.Finite A (M.H' p U) :=
  finite_compHom_of_surjective _ hf

end AlgebraicGeometry.CohomologyAux

namespace AlgebraicGeometry.projectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ : Type v} {A : Type u} [CommRing A] [Fintype σ] [DecidableEq σ] [Nonempty σ]

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
/-- Coherent modules (quasi-coherent of finite type) on `Proj A[xᵢ]` have finitely generated
sections over the standard affines `D₊(xᵢ)`. -/
lemma IsStdFinite.of_isCoherent (F : (Proj (homogeneousSubmodule σ A)).Modules) [F.IsCoherent] :
    IsStdFinite σ A F where
  isQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  finite i := by
    have := (Scheme.Modules.IsCoherent.isQuasicoherent : F.IsQuasicoherent)
    have := (Scheme.Modules.IsCoherent.isFiniteType : F.IsFiniteType)
    exact CohomologyAux.finite_sections_of_isFiniteType F (isAffineOpen_topStd i)

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
/-- Conversely, the modules of the class of Serre's theorems are coherent: on `Proj A[xᵢ]`,
`IsStdFinite` is exactly coherence. -/
lemma IsStdFinite.isCoherent {F : (Proj (homogeneousSubmodule σ A)).Modules}
    (hF : IsStdFinite σ A F) : F.IsCoherent where
  isQuasicoherent := hF.isQuasicoherent
  isFiniteType := by
    have := hF.isQuasicoherent
    exact CohomologyAux.isFiniteType_of_finite_sections F
      (fun i : ULift.{max u v} σ ↦ topStd σ A i.down)
      (by rw [← iSup_topStd (σ := σ) (A := A)]; exact (Equiv.ulift.iSup_comp (g := fun i ↦
        topStd σ A i)))
      (fun i ↦ isAffineOpen_topStd i.down) fun i ↦ hF.finite i.down

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
/-- **Coherence of kernels on projective space** (EGA I 1.5.1 for noetherian schemes): for `A`
noetherian, in a short exact sequence `0 → R → E → F → 0` of modules on `Proj A[xᵢ]` with `E`, `F`
coherent, `R` is coherent. -/
lemma isCoherent_X₁_of_shortExact [Finite σ] [IsNoetherianRing A]
    {S : ShortComplex (Proj (homogeneousSubmodule σ A)).Modules} (hS : S.ShortExact)
    [S.X₂.IsCoherent] [S.X₃.IsCoherent] : S.X₁.IsCoherent :=
  (IsStdFinite.of_shortExact hS (IsStdFinite.of_isCoherent S.X₂)
    (IsStdFinite.of_isCoherent S.X₃)).isCoherent

end AlgebraicGeometry.projectiveSpace

namespace AlgebraicGeometry.projectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The structure morphism `ℙʳ_A ⟶ Spec A`: the morphism to `Spec A₀` followed by the
identification `A₀ = A`. -/
noncomputable def toSpec (A : CommRingCat.{u}) (r : ℕ) : projectiveSpace A r ⟶ Spec A :=
  toSpecZero A r ≫ Spec.map (CommRingCat.ofHom
    (algebraMap A (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A 0)))

lemma surjective_specStructureRingHom_toSpec (A : CommRingCat.{u}) (r : ℕ) :
    Function.Surjective (toSpec A r).specStructureRingHom := by
  have hiso : IsIso (toSpecZero A r).appTop := isIso_toSpecZero_appTop (σ := Fin (r + 1)) (A := A)
  have e : (toSpec A r).specStructureRingHom =
      ((CommRingCat.ofHom (algebraMap A (homogeneousSubmodule (Fin (r + 1)) A 0))) ≫
        (Scheme.ΓSpecIso _).inv ≫ (toSpecZero A r).appTop).hom := by
    rw [Scheme.Hom.specStructureRingHom, toSpec, Scheme.Hom.comp_appTop,
      Scheme.ΓSpecIso_inv_naturality_assoc]
    rfl
  rw [e, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Surjective.comp ?_ surjective_algebraMap_gradeZero
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).2.comp
    (ConcreteCategory.bijective_of_isIso _).2

/-- **Serre's finiteness theorem over the base** (EGA III 2.2.1; Hartshorne III.5.2 (a)): for `A`
noetherian and `M` coherent on `ℙʳ_A`, every `Hᵖ(ℙʳ_A, M)` is a finitely generated `A`-module, for
the `A`-module structure given by the structure morphism `ℙʳ_A ⟶ Spec A`. -/
theorem finite_H_moduleOver (A : CommRingCat.{u}) [IsNoetherianRing A] (r : ℕ)
    (M : (projectiveSpace A r).Modules) [hM : M.IsCoherent] (p : ℕ) :
    letI := M.moduleOver (toSpec A r) p ⊤
    Module.Finite A (M.H p) := by
  have : Module.Finite Γ(projectiveSpace A r, ⊤) (M.H' p ⊤) :=
    finite_H (A := A) (r := r) (@IsStdFinite.of_isCoherent (Fin (r + 1)) A _ M hM) p
  exact CohomologyAux.finite_moduleOver_of_surjective (toSpec A r)
    (surjective_specStructureRingHom_toSpec A r) M p ⊤

end AlgebraicGeometry.projectiveSpace
