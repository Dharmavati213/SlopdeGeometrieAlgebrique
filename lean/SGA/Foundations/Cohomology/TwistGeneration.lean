/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.RelativeSerre
import SGA.Foundations.Cohomology.Serre
import SGA.Foundations.Cohomology.TwistProjection
import SGA.Foundations.Cohomology.ProperFiniteness
import SGA.Foundations.Cohomology.SheafHomCoherent


/-!
# Global generation of twists on closed subschemes of projective space

Serre's theorem (EGA III 2.2.1 (i); Hartshorne II.5.17) for the projective space
`ℙ(τ; Spec A)` of `SGA.Foundations.Projective` with its twisting sheaf `𝒪(1)`, and for closed
subschemes `κ : X ⟶ ℙ(τ; Spec A)` with `𝒪_X(1) = κ^* 𝒪(1)`:

* `span_eq_top_of_restrict_iso`, `span_eq_top_of_pushforward_iso`: generation of sections over an
  open transfers along isomorphisms `N|_Y ≅ N'` (open immersions) and `κ_* M ≅ F`;
* `exists_generating_twist_sections_projSpace`: for `F` coherent on `ℙ(τ; Spec A)` and `n ≫ 0`,
  finitely many global sections of `F(n)` generate it over a finite affine open cover
  (transported from `Proj A[x₀, …, x_r]`, `projectiveSpace.exists_generating_twist_sections`,
  along the chart `ProjectiveSpace.affineChart`);
* `exists_epi_homOfSection_twist`: for `M` coherent on `X` and `n ≫ 0`, finitely many global
  sections of `M(n)` define an epimorphism `𝒪_X^k ⟶ M(n)`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

section Transfer

/-- Generation of sections over an open transfers along an isomorphism `N|_Y ≅ N'` for an open
immersion `g : Y ⟶ X`. -/
lemma span_eq_top_of_restrict_iso {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    {N : X.Modules} {N' : Y.Modules} (e : N.restrict g ≅ N') {J : Type*} (s : J → Γ(N', ⊤))
    {V : Y.Opens}
    (hs : Submodule.span Γ(Y, V)
      (Set.range fun j ↦ N'.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (s j)) = ⊤) :
    Submodule.span Γ(X, g ''ᵁ V) (Set.range fun j ↦
      N.presheaf.map (homOfLE (g.image_mono le_top) : g ''ᵁ V ⟶ g ''ᵁ ⊤).op
        (e.inv.app ⊤ (s j))) = ⊤ := by
  rw [eq_top_iff]
  intro m₀ _
  let m : Γ(N.restrict g, V) := m₀
  have hm : e.hom.app V m ∈ Submodule.span Γ(Y, V)
      (Set.range fun j ↦ N'.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (s j)) := by
    rw [hs]; exact Submodule.mem_top
  have key : ∀ x ∈ Submodule.span Γ(Y, V)
      (Set.range fun j ↦ N'.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (s j)),
      (show Γ(N, g ''ᵁ V) from e.inv.app V x) ∈ Submodule.span Γ(X, g ''ᵁ V) (Set.range fun j ↦
        N.presheaf.map (homOfLE (g.image_mono le_top) : g ''ᵁ V ⟶ g ''ᵁ ⊤).op
          (e.inv.app ⊤ (s j))) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      refine Submodule.subset_span ⟨j, ?_⟩
      rw [hom_app_presheaf_map]
      rfl
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [Scheme.Modules.Hom.app_smul]
      exact Submodule.smul_mem _ ((g.appIso V).inv c) hx
  have e2 : e.inv.app V (e.hom.app V m) = m := by
    rw [← Scheme.Modules.Hom.comp_app_apply, e.hom_inv_id]
    rfl
  have := key _ hm
  rw [e2] at this
  exact this

/-- Generation of sections transfers along an isomorphism `κ_* M ≅ F`: global sections of `F`
generating it over `V` give global sections of `M` generating it over `κ⁻¹ V`. -/
lemma span_eq_top_of_pushforward_iso {X P : Scheme.{u}} (κ : X ⟶ P) {M : X.Modules}
    {F : P.Modules} (e : (Scheme.Modules.pushforward κ).obj M ≅ F) {J : Type*} (s : J → Γ(F, ⊤))
    {V : P.Opens}
    (hs : Submodule.span Γ(P, V)
      (Set.range fun j ↦ F.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (s j)) = ⊤) :
    Submodule.span Γ(X, κ ⁻¹ᵁ V) (Set.range fun j ↦
      M.presheaf.map (homOfLE (κ.preimage_mono le_top) : κ ⁻¹ᵁ V ⟶ κ ⁻¹ᵁ ⊤).op
        (e.inv.app ⊤ (s j))) = ⊤ := by
  rw [eq_top_iff]
  intro m₀ _
  let m : Γ((Scheme.Modules.pushforward κ).obj M, V) := m₀
  have hm : e.hom.app V m ∈ Submodule.span Γ(P, V)
      (Set.range fun j ↦ F.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (s j)) := by
    rw [hs]; exact Submodule.mem_top
  have key : ∀ x ∈ Submodule.span Γ(P, V)
      (Set.range fun j ↦ F.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (s j)),
      (show Γ(M, κ ⁻¹ᵁ V) from e.inv.app V x) ∈ Submodule.span Γ(X, κ ⁻¹ᵁ V)
        (Set.range fun j ↦
          M.presheaf.map (homOfLE (κ.preimage_mono le_top) : κ ⁻¹ᵁ V ⟶ κ ⁻¹ᵁ ⊤).op
            (e.inv.app ⊤ (s j))) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      refine Submodule.subset_span ⟨j, ?_⟩
      rw [hom_app_presheaf_map]
      rfl
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [Scheme.Modules.Hom.app_smul]
      exact Submodule.smul_mem _ (κ.app V c) hx
  have e2 : e.inv.app V (e.hom.app V m) = m := by
    rw [← Scheme.Modules.Hom.comp_app_apply, e.hom_inv_id]
    rfl
  have := key _ hm
  rw [e2] at this
  exact this

end Transfer

section ProjectiveSpaceGeneration

open ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : CommRingCat.{u}} {τ : Type u} [Finite τ]

/-- **Global generation on `ℙ(τ; Spec A)`** (Serre; EGA III 2.2.1 (i), Hartshorne II.5.17): for
`F` coherent, `F(n)` is generated by finitely many global sections over the members of a finite
affine open cover, for all `n ≫ 0`. Transported from `Proj A[x₀, …, x_r]` along the chart
`ProjectiveSpace.affineChart`. -/
theorem exists_generating_twist_sections_projSpace (F : ℙ(τ; Spec A).Modules)
    [F.IsCoherent] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ (J : Type u) (_ : Fintype J)
      (t : J → Γ((twistingSheaf τ (Spec A)).twist F n, ⊤)) (N : ℕ)
      (V : Fin N → ℙ(τ; Spec A).Opens), ⨆ i, V i = ⊤ ∧ (∀ i, IsAffineOpen (V i)) ∧
      ∀ i, Submodule.span Γ(ℙ(τ; Spec A), V i)
        (Set.range fun j ↦ ((twistingSheaf τ (Spec A)).twist F n).presheaf.map
          (homOfLE le_top : V i ⟶ ⊤).op (t j)) = ⊤ := by
  classical
  rcases isEmpty_or_nonempty τ with hτ | hτ
  · have : IsEmpty ℙ(τ; Spec A) := ⟨fun x ↦
      (isEmpty_proj_of_isEmpty (σ := τ) (R := ULift.{u} ℤ)).false ((toProj τ _).base x)⟩
    refine ⟨0, fun n _ ↦ ⟨PEmpty, inferInstance, fun j ↦ j.elim, 0, fun i ↦ i.elim0, ?_,
      fun i ↦ i.elim0, fun i ↦ i.elim0⟩⟩
    ext x
    exact (IsEmpty.false x).elim
  obtain ⟨r, ⟨e⟩⟩ := CohomologyAux.exists_equiv_fin_succ τ
  let S := Spec A
  have hW : IsAffineOpen (⊤ : S.Opens) := isAffineOpen_top S
  let L := twistingSheaf τ S
  let g := affineChart e hW
  have hgo : IsOpenImmersion g := inferInstanceAs (IsOpenImmersion (affineChart e hW))
  have hFq : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have hFt : F.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  let F' := F.restrict g
  have hF'q : F'.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor g F
  have hF't : F'.IsFiniteType := Scheme.Modules.isFiniteType_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback g).app F).symm
  have hF' : F'.IsCoherent := ⟨hF'q, hF't⟩
  let F'' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(S, ⊤))).Modules := F'
  have : F''.IsQuasicoherent := hF'q
  obtain ⟨n₀, hn₀⟩ := projectiveSpace.exists_generating_twist_sections F''
    (@projectiveSpace.IsStdFinite.of_isCoherent (Fin (r + 1)) Γ(S, ⊤) _ F' hF').finite
  refine ⟨n₀, fun n hn ↦ ?_⟩
  obtain ⟨J, _, gs, hgs⟩ := hn₀ n hn
  let τ' := projectiveSpace.twistingBundle (Fin (r + 1)) Γ(S, ⊤)
  let e' : τ'.ι ≃ (L.pullback g).ι := Equiv.ulift.trans e
  have hU : ∀ i, (L.pullback g).U (e' i) = τ'.U i := fun i ↦
    affineChart_preimage_basicOpen e hW i.down
  let e1 : (L.twist F n).restrict g ≅ τ'.twist F' n :=
    L.twistRestrictPullbackIso F n g ≪≫
      Scheme.LineBundle.twistTransferIso F' n τ' (L.pullback g) e' hU
        (fun i j ↦ affineChart_cocycle e hW i.down j.down _)
  let g' : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(S, ⊤)) ⟶ ℙ(τ; S) := g
  have hgo' : IsOpenImmersion g' := hgo
  let e1' : (L.twist F n).restrict g' ≅ τ'.twist F'' n := e1
  have htop : (⊤ : ℙ(τ; S).Opens) ≤ g' ''ᵁ ⊤ := by
    change ⊤ ≤ g ''ᵁ ⊤
    rw [Scheme.Hom.image_top_eq_opensRange, opensRange_affineChart, Scheme.Hom.preimage_top]
  refine ⟨J, inferInstance, fun j ↦ (L.twist F n).presheaf.map (homOfLE htop).op
      (e1'.inv.app ⊤ (gs j)), r + 1,
    fun i ↦ g' ''ᵁ projectiveSpace.topStd (Fin (r + 1)) Γ(S, ⊤) i, ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [← Scheme.Hom.image_iSup, projectiveSpace.iSup_topStd]
    exact top_le_iff.mp htop
  · exact (projectiveSpace.isAffineOpen_topStd i).image_of_isOpenImmersion g'
  · have h := span_eq_top_of_restrict_iso g' e1' gs (hgs i)
    convert h using 3
    funext j
    exact modules_map_map_apply _ _ _ _ _

end ProjectiveSpaceGeneration

section ClosedSubscheme

open ProjectiveSpace

variable {A : CommRingCat.{u}} {τ : Type u} [Finite τ] {X : Scheme.{u}}
  (κ : X ⟶ ℙ(τ; Spec A)) [IsClosedImmersion κ]

/-- **Global generation on a closed subscheme of `ℙ(τ; Spec A)`** (Serre; EGA III 2.2.1 (i),
Hartshorne II.5.17): for `M` coherent on `X` and `n ≫ 0`, `M(n) = M ⊗ 𝒪_X(n)` is a quotient of a
free module of finite rank, via finitely many global sections. -/
theorem exists_epi_homOfSection_twist (M : X.Modules) [M.IsCoherent] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ (k : ℕ)
      (t : Fin k → Γ(((twistingSheaf τ (Spec A)).pullback κ).twist M n, ⊤)),
      Epi (biproduct.desc fun j ↦ homOfSection _ (t j)) := by
  classical
  let L := twistingSheaf τ (Spec A)
  have hMq : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : ((Scheme.Modules.pushforward κ).obj M).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion κ M
  obtain ⟨n₀, hn₀⟩ := exists_generating_twist_sections_projSpace
    ((Scheme.Modules.pushforward κ).obj M)
  refine ⟨n₀, fun n hn ↦ ?_⟩
  obtain ⟨J, _, t, N, V, hcov, haff, hgen⟩ := hn₀ n hn
  let E := L.twistPushforwardIso κ M n
  let t' : J → Γ((L.pullback κ).twist M n, ⊤) := fun j ↦
    ((L.pullback κ).twist M n).presheaf.map (homOfLE le_top : ⊤ ⟶ κ ⁻¹ᵁ ⊤).op
      (E.inv.app ⊤ (t j))
  let k := Fintype.card J
  refine ⟨k, fun j ↦ t' ((Fintype.equivFin J).symm j), ?_⟩
  have : ((L.pullback κ).twist M n).IsQuasicoherent := inferInstance
  refine epi_biproduct_desc_homOfSection _ _ (fun i ↦ κ ⁻¹ᵁ V i) ?_
    (fun i ↦ (haff i).preimage κ) fun i ↦ ?_
  · rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
  · have h := span_eq_top_of_pushforward_iso κ E t (hgen i)
    rw [← h, ← (Fintype.equivFin J).symm.surjective.range_comp]
    congr 2
    funext j
    exact modules_map_map_apply _ _ _ _ _

end ClosedSubscheme

end AlgebraicGeometry.CohomologyAux
