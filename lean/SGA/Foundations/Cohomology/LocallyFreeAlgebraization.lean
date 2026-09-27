/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.ExistenceLocallyFree


/-!
# Algebraizations of locally free adic systems are locally free

Let `A` be a noetherian `I`-adically complete ring and `X` proper over `Spec A`. If a coherent
`B` has all its reductions `B / I^{n+1} B` locally free over `X_n` (in the sense that their
sections over affine opens are projective over `Γ(X, V) / I^{n+1}`, `LiftingProperty`), and `B`
is a quotient of a coherent module with projective sections, then `B` has projective sections over
all affine opens (`projective_sections_of_liftingProperty`; EGA III 5.1.4 and Stacks 0DEM for the
flatness of algebraizations). The proof: `C = coker(ℋom(B, E) ⟶ ℋom(B, B))` satisfies `C = I C` by
Artin–Rees for `Hom` (`exists_sub_comp_mem_pow_smul`), hence `C = 0` by the uniqueness half of the
existence theorem, so `E ⟶ B` splits over affine opens.

* `sheafHomPostcomp`: the morphism `ℋom(M, N) ⟶ ℋom(M, N')` induced by `N ⟶ N'`;
* `projective_sections_of_isLocallyFree`: sections of a locally free module of finite type over an
  affine open are projective; `projective_sections_twistFree`;
* `biproductSectionsEquiv`: sections of a finite biproduct;
* `AdicSystem.exists_iso_quotientIdealPow_projective`: Grothendieck's existence theorem for
  locally free adic systems on a projective scheme, with a locally free algebraization.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

section LocalAlgebra

variable {R : Type u} [CommRing R] (J : Ideal R)

variable {J}

lemma smul_eq_zero_of_mem_quotient {E : Type u} [AddCommGroup E] [Module R E] (k : ℕ) {c : R}
    (hc : c ∈ J ^ k) (x : E ⧸ (J ^ k • ⊤ : Submodule R E)) : c • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hc Submodule.mem_top

/-- **Splitting modulo powers** (the local step of the algebraization of locally free modules):
let `R` be noetherian, `π : E → M` a surjection of finite `R`-modules such that every
`M / J^{k+1} M` is projective over `R / J^{k+1}`. Then every endomorphism of `M` is congruent to
one factoring through `π`, modulo `Jⁿ End(M)`. -/
theorem exists_sub_comp_mem_pow_smul [IsNoetherianRing R] {M E : Type u} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [AddCommGroup E] [Module R E] [Module.Finite R E]
    (π : E →ₗ[R] M) (hπ : Function.Surjective π)
    (hM : ∀ k : ℕ, LiftingProperty (J ^ (k + 1)) (M ⧸ (J ^ (k + 1) • ⊤ : Submodule R M)))
    (n : ℕ) (φ : M →ₗ[R] M) :
    ∃ ψ : M →ₗ[R] E, φ - π ∘ₗ ψ ∈ (J ^ n • ⊤ : Submodule R (M →ₗ[R] M)) := by
  obtain ⟨c₁, hc₁⟩ := exists_mem_pow_smul_of_forall_apply_mem J (M := M) (N := M)
  obtain ⟨c₂, hc₂⟩ := exists_lift_comp_eq.{u, u, u} J (M := M) (N := E)
  set N₀ := n + c₁
  set K := N₀ + c₂
  let SM : Submodule R M := J ^ (K + 1) • ⊤
  let SE : Submodule R E := J ^ (K + 1) • ⊤
  let TM : Submodule R M := J ^ N₀ • ⊤
  let TE : Submodule R E := J ^ N₀ • ⊤
  have hπS : SE ≤ SM.comap π := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  have hπT : TE ≤ TM.comap π := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  have hφS : SM ≤ SM.comap φ := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  have hSTM : SM ≤ TM := Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl
  have hSTE : SE ≤ TE := Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl
  let πK : (E ⧸ SE) →ₗ[R] (M ⧸ SM) := SE.mapQ SM π hπS
  have hπK : Function.Surjective πK := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨e, rfl⟩ := hπ m
    exact ⟨Submodule.mkQ _ e, rfl⟩
  obtain ⟨s, hs⟩ := hM K (fun c hc x ↦ smul_eq_zero_of_mem_quotient (K + 1) hc x) πK hπK
  let φK : (M ⧸ SM) →ₗ[R] (M ⧸ SM) := SM.mapQ SM φ hφS
  let w : M →ₗ[R] (E ⧸ SE) := s ∘ₗ φK ∘ₗ SM.mkQ
  let T : (E ⧸ SE) →ₗ[R] (E ⧸ TE) := Submodule.factor hSTE
  have hk1 : LinearMap.ker SE.mkQ ≤ J ^ (N₀ + c₂) • ⊤ := by
    rw [Submodule.ker_mkQ]
    exact Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl
  have hk2 : J ^ N₀ • ⊤ ≤ LinearMap.ker TE.mkQ := by rw [Submodule.ker_mkQ]
  have hk3 : T ∘ₗ SE.mkQ = TE.mkQ := by ext; rfl
  obtain ⟨ψ, hψ⟩ := hc₂ N₀ SE.mkQ TE.mkQ T (Submodule.mkQ_surjective _) hk1 hk2 hk3 w
  refine ⟨ψ, hc₁ n _ fun m ↦ ?_⟩
  change (φ - π ∘ₗ ψ) m ∈ TM
  rw [← Submodule.Quotient.mk_eq_zero, LinearMap.sub_apply, Submodule.Quotient.mk_sub,
    sub_eq_zero]
  have h1 := LinearMap.congr_fun hψ m
  have h2 := LinearMap.congr_fun hs (φK (SM.mkQ m))
  let TπM : (E ⧸ TE) →ₗ[R] (M ⧸ TM) := TE.mapQ TM π hπT
  let TMf : (M ⧸ SM) →ₗ[R] (M ⧸ TM) := Submodule.factor hSTM
  have key : TπM ∘ₗ T = TMf ∘ₗ πK := by ext; rfl
  have h3 := LinearMap.congr_fun key (s (φK (SM.mkQ m)))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2 h3
  symm
  calc (Submodule.Quotient.mk ((π ∘ₗ ψ) m) : M ⧸ TM) = TπM (TE.mkQ (ψ m)) := rfl
    _ = TπM (T (w m)) := by rw [h1]
    _ = TMf (πK (s (φK (SM.mkQ m)))) := h3
    _ = TMf (φK (SM.mkQ m)) := by rw [h2]
    _ = Submodule.Quotient.mk (φ m) := rfl

end LocalAlgebra

section Postcomp

variable {X : Scheme.{u}}

open Scheme.Modules in
/-- Postcomposition `ℋom(M, N) ⟶ ℋom(M, N')` with a morphism `g : N ⟶ N'`. -/
def sheafHomPostcomp {M N N' : X.Modules} (g : N ⟶ N') : sheafHom M N ⟶ sheafHom M N' :=
  ⟨_root_.PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := fun φ : HomOn M N U.unop ↦ homOnPostcomp φ g
          map_zero' := HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun m ↦
            (g.app V).hom.map_zero)
          map_add' := fun φ ψ ↦ HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun m ↦
            (g.app V).hom.map_add _ _) }
      naturality U V i := by ext φ; rfl }
    fun U r φ ↦ HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun m ↦
      Scheme.Modules.Hom.app_smul g _ _)⟩

open Scheme.Modules in
lemma sheafHomPostcomp_app {M N N' : X.Modules} (g : N ⟶ N') (U : X.Opens)
    (φ : Γ(sheafHom M N, U)) :
    ((sheafHomPostcomp g).app U φ : HomOn M N' U) = homOnPostcomp (φ : HomOn M N U) g :=
  rfl

open Scheme.Modules in
lemma sheafHomAffineEquiv_postcomp {M N N' : X.Modules} [M.IsQuasicoherent] (g : N ⟶ N')
    {V : X.Opens} (hV : IsAffineOpen V) (φ : Γ(sheafHom M N, V)) :
    sheafHomAffineEquiv hV M N' ((sheafHomPostcomp g).app V φ) =
      appLinearMap g V ∘ₗ sheafHomAffineEquiv hV M N φ :=
  rfl

end Postcomp

section ProjectiveSections

variable {X : Scheme.{u}}

/-- **Sections of a locally free module of finite type over an affine open are projective**. -/
theorem projective_sections_of_isLocallyFree (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    [F.IsLocallyFree] {V : X.Opens} (hV : IsAffineOpen V) : Module.Projective Γ(X, V) Γ(F, V) := by
  let G := F.restrict hV.fromSpec
  have : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).app F).symm
  have : G.IsFiniteType := Scheme.Modules.isFiniteType_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).app F).symm
  have : G.IsLocallyFree := Scheme.Modules.isLocallyFree_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).app F).symm
  have : (tilde G.ΓSpec).IsFiniteType := Scheme.Modules.isFiniteType_of_iso G.tildeΓIso.symm
  have : (tilde G.ΓSpec).IsLocallyFree := Scheme.Modules.isLocallyFree_of_iso G.tildeΓIso.symm
  obtain ⟨hproj, -⟩ := (isLocallyFree_and_isFiniteType_tilde_iff G.ΓSpec).mp
    ⟨inferInstance, inferInstance⟩
  have hproj' : Module.Projective Γ(X, V) Γ(G, ⊤) := hproj
  have hW : ⊤ ⊓ V = hV.fromSpec ''ᵁ ⊤ := by
    rw [top_inf_eq, Scheme.Hom.image_top_eq_opensRange, hV.opensRange_fromSpec]
  let e₁ := LinearEquiv.ofBijective (F.restrictFromSpecₗ hV ⊤ ⊤ hW.le)
    (F.bijective_restrictFromSpecₗ hV ⊤ ⊤ hW)
  let res : (F.presheafInf V).obj (op ⊤) →ₗ[Γ(X, V)] Γ(F, V) :=
    { toFun := fun s ↦ F.presheaf.map (homOfLE (le_inf le_top le_rfl : V ≤ ⊤ ⊓ V)).op s
      map_add' := fun _ _ ↦ map_add _ _ _
      map_smul' := fun r s ↦ by
        change F.presheaf.map (homOfLE (le_inf le_top le_rfl : V ≤ ⊤ ⊓ V)).op
            (X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op r • @id Γ(F, ⊤ ⊓ V) s) =
          r • F.presheaf.map (homOfLE (le_inf le_top le_rfl : V ≤ ⊤ ⊓ V)).op s
        rw [Scheme.Modules.map_smul, presheaf_map_map, presheaf_map_self]
        rfl }
  have hres : Function.Bijective res := by
    have : IsIso (homOfLE (le_inf le_top le_rfl : V ≤ ⊤ ⊓ V)).op :=
      ⟨(homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    exact ConcreteCategory.bijective_of_isIso
      (F.presheaf.map (homOfLE (le_inf le_top le_rfl : V ≤ ⊤ ⊓ V)).op)
  exact Module.Projective.of_equiv (e₁.trans (LinearEquiv.ofBijective res hres))

/-- The sections of a finite biproduct are the product of the sections. -/
def biproductSectionsEquiv {J : Type} [Fintype J] (G : J → X.Modules) (V : X.Opens) :
    Γ(⨁ G, V) ≃ₗ[Γ(X, V)] (∀ j, Γ(G j, V)) where
  toFun s j := (biproduct.π G j).app V s
  invFun t := ∑ j, (biproduct.ι G j).app V (t j)
  map_add' s s' := by ext j; exact map_add _ _ _
  map_smul' r s := by ext j; exact Scheme.Modules.Hom.app_smul _ _ _
  left_inv s := by
    let ev : (⨁ G ⟶ ⨁ G) →+ Γ(⨁ G, V) :=
      { toFun := fun φ ↦ φ.app V s, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    have h := congrArg ev (biproduct.total (f := G))
    rw [map_sum] at h
    exact h
  right_inv t := by
    funext j
    classical
    change (biproduct.π G j).app V (∑ k, (biproduct.ι G k).app V (t k)) = t j
    rw [map_sum]
    rw [Finset.sum_eq_single j]
    · rw [← Scheme.Modules.Hom.comp_app_apply, biproduct.ι_π_self]
      rfl
    · intro k _ hk
      rw [← Scheme.Modules.Hom.comp_app_apply, biproduct.ι_π_ne _ hk]
      rfl
    · intro h; exact absurd (Finset.mem_univ j) h

theorem projective_sections_twistFree (L : X.LineBundle) (d : ℤ) (k : ℕ) [IsLocallyNoetherian X]
    {V : X.Opens} (hV : IsAffineOpen V) : Module.Projective Γ(X, V) Γ(twistFree L d k, V) := by
  have : (L.toModules (-d)).IsCoherent :=
    inferInstanceAs (L.twist (unitModule X) (-d)).IsCoherent
  have : (L.toModules (-d)).IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : (L.toModules (-d)).IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have : (L.toModules (-d)).IsLocallyFree := L.isLocallyFree_toModules (-d)
  have := projective_sections_of_isLocallyFree (L.toModules (-d)) hV
  have : Module.Projective Γ(X, V) (Π₀ _ : Fin k, Γ(L.toModules (-d), V)) := inferInstance
  exact Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype.trans
    (biproductSectionsEquiv (fun _ : Fin k ↦ L.toModules (-d)) V).symm)

end ProjectiveSections

section Algebraization

lemma LiftingProperty.of_equiv {R : Type u} [CommRing R] {K : Ideal R} {P P' : Type u}
    [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module R P'] (e : P ≃ₗ[R] P')
    (h : LiftingProperty K P) : LiftingProperty K P' := by
  intro N _ _ hN φ hφ
  obtain ⟨ψ, hψ⟩ := h hN (e.symm.toLinearMap ∘ₗ φ) (e.symm.surjective.comp hφ)
  refine ⟨ψ ∘ₗ e.symm.toLinearMap, LinearMap.ext fun x ↦ ?_⟩
  have := LinearMap.congr_fun hψ (e.symm x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at this ⊢
  exact e.symm.injective this

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A)

/-- The sections of `B / I^{n+1} B` over an affine open `V` are `Γ(B, V) / J^{n+1} Γ(B, V)`. -/
def quotientIdealPowSectionsEquiv (B : X.Modules) [B.IsQuasicoherent] (n : ℕ) {V : X.Opens}
    (hV : IsAffineOpen V) :
    (Γ(B, V) ⧸ (idealV f I V 1 ^ (n + 1) • ⊤ : Submodule Γ(X, V) Γ(B, V))) ≃ₗ[Γ(X, V)]
      Γ(B.quotientIdealPow f I n, V) :=
  (Submodule.quotEquivOfEq _ _ (by
    ext s
    rw [LinearMap.mem_ker]
    exact (quotientIdealPow_app_eq_zero_iff I f B n hV s).symm)).trans
    (LinearMap.quotKerEquivOfSurjective (appLinearMap (B.toQuotientIdealPow f I n) V)
      (toQuotientIdealPow_app_surjective I f n hV (M := B)))

variable [IsAdicComplete I A] [IsProper f]

/-- **Algebraizations of locally free systems are locally free** (EGA III 5.1.4 / Stacks 0DEM for
the flatness of the algebraization): let `A` be noetherian and `I`-adically complete, `X` proper
over `Spec A`, `B` coherent on `X` such that every `Γ(B / I^{n+1} B, V)` (`V` affine) is projective
over `Γ(X, V) / I^{n+1}`, and `π : E ⟶ B` an epimorphism from a coherent module with projective
sections over affine opens. Then `Γ(B, V)` is projective for every affine open `V`.

Proof: the cokernel `C` of `ℋom(B, E) ⟶ ℋom(B, B)` satisfies `C = I C` by Artin–Rees
(`exists_sub_comp_mem_pow_smul`), hence vanishes by the uniqueness half of the existence theorem;
so `π` splits over every affine open. -/
theorem projective_sections_of_liftingProperty (B E : X.Modules) [B.IsCoherent] [E.IsCoherent]
    (π : E ⟶ B) [Epi π]
    (hE : ∀ {V : X.Opens}, IsAffineOpen V → Module.Projective Γ(X, V) Γ(E, V))
    (hB : ∀ (n : ℕ) {V : X.Opens} (_ : IsAffineOpen V),
      LiftingProperty (idealV f I V 1 ^ (n + 1)) Γ(B.quotientIdealPow f I n, V))
    {V : X.Opens} (hV : IsAffineOpen V) : Module.Projective Γ(X, V) Γ(B, V) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : B.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : E.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : B.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have : E.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  let P : Scheme.Modules.sheafHom B E ⟶ Scheme.Modules.sheafHom B B := sheafHomPostcomp π
  have : (Scheme.Modules.sheafHom B E).IsCoherent := isCoherent_sheafHom B E
  have : (Scheme.Modules.sheafHom B B).IsCoherent := isCoherent_sheafHom B B
  have : (Scheme.Modules.sheafHom B E).IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : (Scheme.Modules.sheafHom B B).IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : (cokernel P).IsCoherent := isCoherent_cokernel' P
  have : (cokernel P).IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have hC : ∀ (n : ℕ) {W : X.Opens} (hW : IsAffineOpen W) (c : Γ(cokernel P, W)),
      ((cokernel P).toQuotientIdealPow f I n).app W c = 0 := by
    intro n W hW c
    rw [toQuotientIdealPow_app_eq_zero_iff' I f (cokernel P) hW n c]
    obtain ⟨t, rfl⟩ := cokernel_π_app_surjective P hW c
    have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    have : Module.Finite Γ(X, W) Γ(B, W) := finite_sections_of_isFiniteType B hW
    have : Module.Finite Γ(X, W) Γ(E, W) := finite_sections_of_isFiniteType E hW
    have hM : ∀ k : ℕ, LiftingProperty (idealV f I W 1 ^ (k + 1))
        (Γ(B, W) ⧸ (idealV f I W 1 ^ (k + 1) • ⊤ : Submodule Γ(X, W) Γ(B, W))) := fun k ↦
      LiftingProperty.of_equiv (quotientIdealPowSectionsEquiv I f B k hW).symm (hB k hW)
    obtain ⟨ψ, hψ⟩ := exists_sub_comp_mem_pow_smul (appLinearMap π W)
      (app_surjective_of_epi π hW) hM (n + 1) (sheafHomAffineEquiv hW B B t)
    let t' := (sheafHomAffineEquiv hW B E).symm ψ
    have hPt' : P.app W t' = (sheafHomAffineEquiv hW B B).symm (appLinearMap π W ∘ₗ ψ) := by
      apply (sheafHomAffineEquiv hW B B).injective
      rw [LinearEquiv.apply_symm_apply]
      exact (sheafHomAffineEquiv_postcomp π hW t').trans (by rw [LinearEquiv.apply_symm_apply])
    have h1 : t - P.app W t' ∈
        (idealV f I W 1 ^ (n + 1) • ⊤ : Submodule Γ(X, W) Γ(Scheme.Modules.sheafHom B B, W)) := by
      have := mem_smul_top_of_linearMap _ (sheafHomAffineEquiv hW B B).symm.toLinearMap hψ
      rw [LinearEquiv.coe_coe, map_sub, LinearEquiv.symm_apply_apply] at this
      rw [hPt']
      exact this
    have h2 := mem_smul_top_of_linearMap _ (appLinearMap (cokernel.π P) W) h1
    have h3 : (cokernel.π P).app W (P.app W t') = 0 := by
      rw [← Scheme.Modules.Hom.comp_app_apply, cokernel.condition]
      rfl
    change (cokernel.π P).app W (t - P.app W t') ∈ _ at h2
    rw [map_sub, h3, sub_zero] at h2
    exact h2
  have hzero : 𝟙 (cokernel P) = 0 :=
    eq_zero_of_comp_toQuotientIdealPow_eq_zero I f (𝟙 (cokernel P)) fun n ↦ by
      rw [Category.id_comp]
      refine hom_ext_of_affine fun W hW c ↦ ?_
      rw [hC n hW c]
      rfl
  have hepi : Epi P := Preadditive.epi_of_isZero_cokernel P ((IsZero.iff_id_eq_zero _).mpr hzero)
  obtain ⟨t', ht'⟩ := app_surjective_of_epi P hV ((sheafHomAffineEquiv hV B B).symm LinearMap.id)
  have hsplit : appLinearMap π V ∘ₗ sheafHomAffineEquiv hV B E t' = LinearMap.id := by
    rw [← sheafHomAffineEquiv_postcomp]
    change sheafHomAffineEquiv hV B B (P.app V t') = _
    rw [ht', LinearEquiv.apply_symm_apply]
  have := hE hV
  exact Module.Projective.of_split (sheafHomAffineEquiv hV B E t') (appLinearMap π V) hsplit

end Algebraization

section ProjectiveExistence

/-- The linear equivalence of sections induced by an isomorphism of modules. -/
def appLinearEquiv {X : Scheme.{u}} {P Q : X.Modules} (e : P ≅ Q) (V : X.Opens) :
    Γ(P, V) ≃ₗ[Γ(X, V)] Γ(Q, V) where
  __ := appLinearMap e.hom V
  invFun := e.inv.app V
  left_inv x := by
    change e.inv.app V (e.hom.app V x) = x
    rw [← Scheme.Modules.Hom.comp_app_apply, e.hom_inv_id]
    rfl
  right_inv y := by
    change e.hom.app V (e.inv.app V y) = y
    rw [← Scheme.Modules.Hom.comp_app_apply, e.inv_hom_id]
    rfl

open ProjectiveSpace

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} {τ : Type u} [Finite τ] (κ : X ⟶ ℙ(τ; Spec A)) [IsClosedImmersion κ]

/-- **Grothendieck's existence theorem for locally free adic systems on a projective scheme, with
local freeness of the algebraization** (EGA III 5.1.4, 5.2; Stacks 0DEM): for `A` noetherian and
`I`-adically complete, `X` closed in `ℙ(τ; Spec A)` and `(Gₙ)` a locally free adic system with
`G₀` coherent, there is a coherent `F` with compatible isomorphisms `F / I^{n+1} F ≅ Gₙ`, and the
sections of `F` over affine opens are projective. -/
theorem AdicSystem.exists_iso_quotientIdealPow_projective
    (G : AdicSystem I (κ ≫ ℙ(τ; Spec A) ↘ Spec A)) [(G.obj 0).IsCoherent]
    (hG : G.IsLocallyFree) :
    ∃ (F : X.Modules) (_ : F.IsCoherent)
      (e : ∀ n, F.quotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n ≅ G.obj n),
      (∀ n, (e (n + 1)).hom ≫ G.map n =
        F.quotientIdealPowMap (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n ≫ (e n).hom) ∧
      ∀ {V : X.Opens}, IsAffineOpen V → Module.Projective Γ(X, V) Γ(F, V) := by
  obtain ⟨F, hF, e, he⟩ := G.exists_iso_quotientIdealPow_of_isLocallyFree I κ hG
  refine ⟨F, hF, e, he, fun {V} hV ↦ ?_⟩
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (κ ≫ ℙ(τ; Spec A) ↘ Spec A)
  obtain ⟨n₀, hn₀⟩ := exists_epi_homOfSection_twist κ F
  obtain ⟨k, t, ht⟩ := hn₀ n₀ le_rfl
  have hπ : Epi (twistFreeDesc t) := epi_twistFreeDesc t (h := ht)
  exact projective_sections_of_liftingProperty I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) F _
    (twistFreeDesc t) (fun hV ↦ projective_sections_twistFree _ _ _ hV)
    (fun n V hV ↦ LiftingProperty.of_equiv (appLinearEquiv (e n).symm V) (hG n hV)) hV

end ProjectiveExistence

end AlgebraicGeometry.CohomologyAux
