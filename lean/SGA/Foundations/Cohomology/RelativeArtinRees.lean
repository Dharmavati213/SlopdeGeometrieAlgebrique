/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.ProIsoAlgebraization
import SGA.Foundations.Cohomology.FormalFunctions
import SGA.Foundations.Cohomology.PushforwardProjective

/-!
# Relative Artin–Rees for sections over the preimage of an affine open

For `π : X ⟶ Y` proper over `Spec A` (`A` noetherian), `W ⊆ Y` affine and `M` coherent on `X`,
the two Artin–Rees statements behind the theorem on formal functions (EGA III 4.1.5), for the
proper morphism `π⁻¹ W ⟶ W ≅ Spec Γ(Y, W)` and the ideal `I Γ(Y, W)`:

* `exists_relative_ker_le`: sections of `M` over `π⁻¹ W` vanishing in `M / I^{n+c+1} M` lie in
  `I^{n+1} Γ(M, π⁻¹ W)`;
* `exists_relative_lift`: the image in `M / I^{n+1} M` of a section of `M / I^{n+c+1} M` over
  `π⁻¹ W` lifts to `M`.

They are deduced from the absolute statements for `H⁰` (`exists_H0_ker_toQuotientIdealPow_le`,
`exists_H0_lift_quotMap`, from `exists_range_ιPow_le` and `exists_inclPow_eq_zero`) applied to
the restriction of `M` to the open subscheme `π⁻¹ W`, whose reductions are identified with the
restrictions of the reductions of `M` (`relQuotientIso`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

section Absolute

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A) [IsProper f] (M : X.Modules) [M.IsCoherent]

/-- **Artin–Rees for `H⁰`** (EGA III 4.1.5, proof): there is `c` such that a global section of
`M` vanishing in `M / I^{n+c+1} M` lies in `I^{n+1} H⁰(X, M)`. -/
theorem exists_H0_ker_toQuotientIdealPow_le :
    letI := M.moduleOver f 0 ⊤
    ∃ c, ∀ n (y : M.H 0),
      Scheme.Modules.H'.map (M.toQuotientIdealPow f I (n + c)) 0 ⊤ y = 0 →
        y ∈ (I ^ (n + 1) • ⊤ : Submodule A (M.H 0)) := by
  let _ := M.moduleOver f 0 ⊤
  have : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  obtain ⟨c, hc⟩ := exists_range_ιPow_le I f M 0
  refine ⟨c, fun n y hy ↦ ?_⟩
  obtain ⟨x, rfl⟩ := (Scheme.Modules.H'.exact_map_map
    (shortExact_quotientIdealPow f I M (n + c)) 0 ⊤ y).mp hy
  exact hc (n + c + 1) (n + 1) (by omega) x

/-- **Artin–Rees for the lifting of sections** (EGA III 4.1.5, proof): there is `c` such that
the image of a global section of `M / I^{n+c+1} M` in `M / I^{n+1} M` lifts to `M`. -/
theorem exists_H0_lift_quotMap :
    ∃ c, ∀ n (z : (M.quotientIdealPow f I (n + c)).H 0), ∃ y : M.H 0,
      Scheme.Modules.H'.map (M.toQuotientIdealPow f I n) 0 ⊤ y =
        Scheme.Modules.H'.map (quotMap I f M (Nat.le_add_right n c)) 0 ⊤ z := by
  have : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  obtain ⟨c, hc⟩ := exists_inclPow_eq_zero I f M 1
  refine ⟨c, fun n z ↦ ?_⟩
  have hS (k : ℕ) := shortExact_quotientIdealPow f I M k
  have hδ : Scheme.Modules.H'.δ (hS n) 0 ⊤
      (Scheme.Modules.H'.map (quotMap I f M (Nat.le_add_right n c)) 0 ⊤ z) = 0 := by
    have hnat := Scheme.Modules.H'.δ_naturality (hS (n + c)) (hS n)
      (quotSESMap I f M (Nat.le_add_right n c)) 0 ⊤ z
    refine hnat.trans ?_
    exact hc (n + c + 1) (n + 1) (by omega) _
      ((Scheme.Modules.H'.exact_δ_map (hS (n + c)) 0 ⊤ _).mpr ⟨z, rfl⟩)
  exact (Scheme.Modules.H'.exact_map_δ (hS n) 0 ⊤ _).mp hδ

end Absolute

/-- Scalars act on the restriction of a module to an open subscheme as on the module itself. -/
lemma restrict_ι_smul {X : Scheme.{u}} (O : X.Opens) (N : X.Modules) (V : O.toScheme.Opens)
    (r : Γ(O.toScheme, V)) (x : Γ(N.restrict O.ι, V)) :
    (r • x : Γ(N.restrict O.ι, V)) =
      HSMul.hSMul (α := Γ(X, O.ι ''ᵁ V)) (β := Γ(N, O.ι ''ᵁ V)) (γ := Γ(N, O.ι ''ᵁ V)) r x := by
  have := Scheme.Modules.smul_restrictAppIso_hom_apply (f := O.ι) N V r x
  simp only [Scheme.Modules.restrictAppIso, Iso.refl_hom, Scheme.Opens.ι_appIso,
    Iso.refl_inv] at this
  exact this

open Scheme.Modules in
/-- The module structure on the sections of the restriction of `N` to an open subscheme is that
of `N`. -/
lemma restrict_ι_module_eq {X : Scheme.{u}} (O : X.Opens) (N : X.Modules)
    (V : O.toScheme.Opens) :
    @instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
        O.toScheme (N.restrict O.ι) V =
      (@instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
        X N (O.ι ''ᵁ V) : Module Γ(X, O.ι ''ᵁ V) Γ(N, O.ι ''ᵁ V)) :=
  Module.ext (funext₂ fun r x ↦ restrict_ι_smul O N V r x)

lemma mem_smul_top_restrict_iff {X : Scheme.{u}} (O : X.Opens) (N : X.Modules)
    (V : O.toScheme.Opens) (J : Ideal Γ(O.toScheme, V)) (x : Γ(N.restrict O.ι, V)) :
    x ∈ (J • ⊤ : Submodule Γ(O.toScheme, V) Γ(N.restrict O.ι, V)) ↔
      @Membership.mem Γ(N, O.ι ''ᵁ V) (Submodule Γ(X, O.ι ''ᵁ V) Γ(N, O.ι ''ᵁ V)) _
        (@HSMul.hSMul (Ideal Γ(X, O.ι ''ᵁ V)) (Submodule Γ(X, O.ι ''ᵁ V) Γ(N, O.ι ''ᵁ V)) _ _
          J ⊤) x := by
  rw [restrict_ι_module_eq]
  rfl

lemma equiv₀_H'_map {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (y : M.H 0) :
    Scheme.Modules.H.equiv₀ N (Scheme.Modules.H'.map φ 0 ⊤ y) =
      φ.app ⊤ (Scheme.Modules.H.equiv₀ M y) :=
  CategoryTheory.Sheaf.H'.equiv₀_naturality (Scheme.Modules.Hom.toAbSheaf φ) (U := ⊤) y

section Relative

variable {A : CommRingCat.{u}} (I : Ideal A) {X Y : Scheme.{u}}
  (f : Y ⟶ Spec A) (π : X ⟶ Y) {W : Y.Opens} (hW : IsAffineOpen W)

/-- The structure morphism `π⁻¹ W ⟶ W ≅ Spec Γ(Y, W)`. -/
abbrev relStruct : (π ⁻¹ᵁ W).toScheme ⟶ Spec Γ(Y, W) := (π ∣_ W) ≫ hW.isoSpec.hom

lemma structMapV_relStruct (V : (π ⁻¹ᵁ W).toScheme.Opens) (a : Γ(Y, W)) :
    structMapV (relStruct π hW) V a =
      X.presheaf.map (homOfLE (((π ⁻¹ᵁ W).ι.image_le_opensRange V).trans
        (π ⁻¹ᵁ W).opensRange_ι.le)).op (π.app W a) := by
  have h := map_specStructureRingHom_morphismRestrict π hW a
  rw [structMapV_eq_map, ← h]
  have hle : (π ⁻¹ᵁ W).ι ''ᵁ V ≤ (π ⁻¹ᵁ W).ι ''ᵁ ⊤ := Scheme.Hom.image_mono _ le_top
  refine (show _ = X.presheaf.map (homOfLE hle).op
    ((relStruct π hW).specStructureRingHom a) from rfl).trans ?_
  exact (CohomologyAux.presheaf_map_map _ _ _).symm

lemma structMapV_comp_preimage (a : A) :
    structMapV (π ≫ f) (π ⁻¹ᵁ W) a = π.app W (structMapV f W a) := by
  have e : (π ≫ f).specStructureRingHom a = π.appTop (f.specStructureRingHom a) := by
    rw [Scheme.Hom.specStructureRingHom, Scheme.Hom.comp_appTop]
    rfl
  rw [structMapV_eq_map, structMapV_eq_map, e, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.naturality]
  rfl

lemma structMapV_comp_relStruct (V : (π ⁻¹ᵁ W).toScheme.Opens) (a : A) :
    structMapV (π ≫ f) ((π ⁻¹ᵁ W).ι ''ᵁ V) a =
      structMapV (relStruct π hW) V (structMapV f W a) := by
  rw [structMapV_relStruct, ← structMapV_comp_preimage, AdicSystem.structMapV_res]

lemma idealV_relStruct (V : (π ⁻¹ᵁ W).toScheme.Opens) (k : ℕ) :
    idealV (relStruct π hW) (idealV f I W 1) V k = idealV (π ≫ f) I ((π ⁻¹ᵁ W).ι ''ᵁ V) k := by
  rw [idealV, idealV, idealV, pow_one, ← Ideal.map_pow, Ideal.map_map]
  congr 1
  exact (RingHom.ext fun a ↦ structMapV_comp_relStruct f π hW V a).symm

section Kappa

variable [IsNoetherianRing A] [IsNoetherianRing Γ(Y, W)] (M : X.Modules) [M.IsQuasicoherent]

/-- The restriction of `M → M / I^{n+1} M` to `π⁻¹ W`. -/
abbrev relRestrictMap (n : ℕ) :
    M.restrict (π ⁻¹ᵁ W).ι ⟶ (M.quotientIdealPow (π ≫ f) I n).restrict (π ⁻¹ᵁ W).ι :=
  (Scheme.Modules.restrictFunctor (π ⁻¹ᵁ W).ι).map (M.toQuotientIdealPow (π ≫ f) I n)

omit [IsNoetherianRing A] [IsNoetherianRing Γ(Y, W)] [M.IsQuasicoherent] in
lemma relRestrictMap_app (n : ℕ) (V : (π ⁻¹ᵁ W).toScheme.Opens) (x : Γ(M, (π ⁻¹ᵁ W).ι ''ᵁ V)) :
    (relRestrictMap I f π M n).app V x =
      (M.toQuotientIdealPow (π ≫ f) I n).app ((π ⁻¹ᵁ W).ι ''ᵁ V) x := rfl

omit [IsNoetherianRing Γ(Y, W)] in
lemma relRestrictMap_smul_eq_zero (n : ℕ) :
    ∀ a ∈ idealV f I W 1 ^ (n + 1),
      smulA ((M.quotientIdealPow (π ≫ f) I n).restrict (π ⁻¹ᵁ W).ι) (relStruct π hW) a = 0 := by
  intro a ha
  refine hom_ext_of_affine fun V hV s ↦ ?_
  rw [smulA_app]
  have hV' : IsAffineOpen ((π ⁻¹ᵁ W).ι ''ᵁ V) := hV.image_of_isOpenImmersion _
  have hmem : structMapV (relStruct π hW) V a ∈ idealV (π ≫ f) I ((π ⁻¹ᵁ W).ι ''ᵁ V) (n + 1) := by
    rw [← idealV_relStruct I f π hW V (n + 1), idealV]
    exact Ideal.mem_map_of_mem _ ha
  rw [AdicSystem.idealV_eq_pow] at hmem
  rw [restrict_ι_smul]
  exact (ofModule I (π ≫ f) M).smul_eq_zero n hV' hmem s

omit [IsNoetherianRing Γ(Y, W)] in
lemma relRestrictMap_surj_ker (n : ℕ) {V : (π ⁻¹ᵁ W).toScheme.Opens} (hV : IsAffineOpen V) :
    Function.Surjective ((relRestrictMap I f π M n).app V) ∧
      ∀ x, (relRestrictMap I f π M n).app V x = 0 ↔
        x ∈ (idealV (relStruct π hW) (idealV f I W 1) V 1 ^ (n + 1) • ⊤ :
          Submodule Γ((π ⁻¹ᵁ W).toScheme, V) Γ(M.restrict (π ⁻¹ᵁ W).ι, V)) := by
  have hV' : IsAffineOpen ((π ⁻¹ᵁ W).ι ''ᵁ V) := hV.image_of_isOpenImmersion _
  have hJ : idealV (relStruct π hW) (idealV f I W 1) V 1 ^ (n + 1) =
      idealV (π ≫ f) I ((π ⁻¹ᵁ W).ι ''ᵁ V) 1 ^ (n + 1) := by
    rw [← AdicSystem.idealV_eq_pow, ← AdicSystem.idealV_eq_pow, idealV_relStruct]
  refine ⟨toQuotientIdealPow_app_surjective I (π ≫ f) n hV' (M := M), fun x ↦ ?_⟩
  change (M.toQuotientIdealPow (π ≫ f) I n).app ((π ⁻¹ᵁ W).ι ''ᵁ V) x = 0 ↔ _
  rw [toQuotientIdealPow_app_eq_zero_iff' I (π ≫ f) M hV' n x, mem_smul_top_restrict_iff, hJ]

/-- `(M|_{π⁻¹ W}) / I^{n+1} ≅ (M / I^{n+1} M)|_{π⁻¹ W}`, for the ideal `I Γ(Y, W)` of the base
`Spec Γ(Y, W)` of `π⁻¹ W`. -/
def relQuotientIso (n : ℕ) :
    (M.restrict (π ⁻¹ᵁ W).ι).quotientIdealPow (relStruct π hW) (idealV f I W 1) n ≅
      (M.quotientIdealPow (π ≫ f) I n).restrict (π ⁻¹ᵁ W).ι :=
  have := isIso_descQuotientIdealPow (idealV f I W 1) (relStruct π hW) n
    (relRestrictMap I f π M n) (fun hV ↦ relRestrictMap_surj_ker I f π hW M n hV)
    (relRestrictMap_smul_eq_zero I f π hW M n)
  asIso (descQuotientIdealPow (idealV f I W 1) (relStruct π hW) n (relRestrictMap I f π M n)
    (relRestrictMap_smul_eq_zero I f π hW M n))

@[reassoc]
lemma toQuotientIdealPow_relQuotientIso (n : ℕ) :
    (M.restrict (π ⁻¹ᵁ W).ι).toQuotientIdealPow (relStruct π hW) (idealV f I W 1) n ≫
      (relQuotientIso I f π hW M n).hom = relRestrictMap I f π M n :=
  toQuotientIdealPow_descQuotientIdealPow _ _ n _ (relRestrictMap_smul_eq_zero I f π hW M n)

lemma quotMap_relQuotientIso {m n : ℕ} (h : n ≤ m) :
    quotMap (idealV f I W 1) (relStruct π hW) (M.restrict (π ⁻¹ᵁ W).ι) h ≫
        (relQuotientIso I f π hW M n).hom =
      (relQuotientIso I f π hW M m).hom ≫
        (Scheme.Modules.restrictFunctor (π ⁻¹ᵁ W).ι).map (quotMap I (π ≫ f) M h) := by
  rw [← cancel_epi ((M.restrict (π ⁻¹ᵁ W).ι).toQuotientIdealPow (relStruct π hW)
      (idealV f I W 1) m), toQuotientIdealPow_quotMap_assoc, toQuotientIdealPow_relQuotientIso,
    toQuotientIdealPow_relQuotientIso_assoc, ← Functor.map_comp, toQuotientIdealPow_quotMap]

end Kappa

section Translation

variable [IsNoetherianRing A] [IsLocallyNoetherian Y] [IsProper π] (M : X.Modules) [M.IsCoherent]

omit [IsNoetherianRing A] [IsLocallyNoetherian Y] [IsProper π] [M.IsCoherent] in
lemma pushforward_smul (r : Γ(Y, W)) (b : Γ((Scheme.Modules.pushforward π).obj M, W)) :
    r • b = (show Γ(M, π ⁻¹ᵁ W) from (π.app W r) • (show Γ(M, π ⁻¹ᵁ W) from b)) := rfl

include hW in
/-- **Relative Artin–Rees for sections** (EGA III 4.1.5 for `π⁻¹ W ⟶ W`): for `π : X ⟶ Y` proper,
`W ⊆ Y` affine and `M` coherent, there is `c` such that a section of `M` over `π⁻¹ W` vanishing in
`M / I^{n+c+1} M` lies in `I^{n+1} Γ(M, π⁻¹ W)`. -/
theorem exists_relative_ker_le :
    ∃ c, ∀ n (b : Γ((Scheme.Modules.pushforward π).obj M, W)),
      (M.toQuotientIdealPow (π ≫ f) I (n + c)).app (π ⁻¹ᵁ W) b = 0 →
        b ∈ (idealV f I W 1 ^ (n + 1) • ⊤ :
          Submodule Γ(Y, W) Γ((Scheme.Modules.pushforward π).obj M, W)) := by
  have : IsNoetherianRing Γ(Y, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : M.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  let O := π ⁻¹ᵁ W
  let M' := M.restrict O.ι
  have : M'.IsCoherent := ⟨inferInstance, inferInstance⟩
  let _ := M'.moduleOver (relStruct π hW) 0 ⊤
  obtain ⟨c, hc⟩ := exists_H0_ker_toQuotientIdealPow_le (idealV f I W 1) (relStruct π hW) M'
  refine ⟨c, fun n b hb ↦ ?_⟩
  let b' : Γ(M', ⊤) := M.presheaf.map (homOfLE O.ι_image_top.le).op b
  let y := (Scheme.Modules.H.equiv₀ M').symm b'
  have hy : Scheme.Modules.H'.map (M'.toQuotientIdealPow (relStruct π hW) (idealV f I W 1)
      (n + c)) 0 ⊤ y = 0 := by
    apply (Scheme.Modules.H.equiv₀ _).injective
    rw [equiv₀_H'_map, LinearEquiv.apply_symm_apply, map_zero]
    have h1 : (relQuotientIso I f π hW M (n + c)).hom.app ⊤
        ((M'.toQuotientIdealPow (relStruct π hW) (idealV f I W 1) (n + c)).app ⊤ b') = 0 := by
      rw [← Scheme.Modules.Hom.comp_app_apply, toQuotientIdealPow_relQuotientIso]
      change (M.toQuotientIdealPow (π ≫ f) I (n + c)).app (O.ι ''ᵁ ⊤)
        (M.presheaf.map (homOfLE O.ι_image_top.le).op b) = 0
      refine (hom_app_presheaf_map _ (homOfLE O.ι_image_top.le) (b : Γ(M, O))).trans ?_
      rw [hb, map_zero]
    calc (M'.toQuotientIdealPow (relStruct π hW) (idealV f I W 1) (n + c)).app ⊤ b'
        = (relQuotientIso I f π hW M (n + c)).inv.app ⊤ ((relQuotientIso I f π hW M (n + c)).hom.app
            ⊤ ((M'.toQuotientIdealPow (relStruct π hW) (idealV f I W 1) (n + c)).app ⊤ b')) := by
          rw [← Scheme.Modules.Hom.comp_app_apply, Iso.hom_inv_id]
          rfl
      _ = 0 := by rw [h1, map_zero]
  have hmem := hc n y hy
  let L : M'.H 0 →ₗ[Γ(Y, W)] Γ((Scheme.Modules.pushforward π).obj M, W) :=
    { toFun := fun z ↦ M.presheaf.map (homOfLE O.ι_image_top.ge).op
        (Scheme.Modules.H.equiv₀ M' z)
      map_add' := fun z z' ↦ by
        rw [map_add]
        exact map_add _ _ _
      map_smul' := fun a z ↦ by
        change M.presheaf.map (homOfLE O.ι_image_top.ge).op (Scheme.Modules.H.equiv₀ M'
          ((relStruct π hW).specStructureRingHom a • z)) = _
        rw [LinearEquiv.map_smul, restrict_ι_smul]
        refine (Scheme.Modules.map_smul M (homOfLE O.ι_image_top.ge) _ _).trans ?_
        refine Eq.trans ?_ (pushforward_smul (π := π) (M := M) a _).symm
        congr 1
        exact map_specStructureRingHom_morphismRestrict π hW a }
  have hL := mem_smul_top_of_linearMap _ L hmem
  have hLy : L y = b := by
    change M.presheaf.map (homOfLE O.ι_image_top.ge).op
      (Scheme.Modules.H.equiv₀ M' ((Scheme.Modules.H.equiv₀ M').symm b')) = b
    rw [LinearEquiv.apply_symm_apply]
    have key : ∀ s : Γ(M, O), M.presheaf.map (homOfLE O.ι_image_top.ge).op
        (M.presheaf.map (homOfLE O.ι_image_top.le).op s) = s := fun s ↦ by
      rw [TopCat.Presheaf.map_map_apply, CohomologyAux.modules_map_self]
    exact key b
  rwa [hLy] at hL

omit [IsNoetherianRing A] [IsLocallyNoetherian Y] [IsProper π] in
lemma map_image_top_ge_le (N : X.Modules) (s : Γ(N, π ⁻¹ᵁ W)) :
    N.presheaf.map (homOfLE (π ⁻¹ᵁ W).ι_image_top.ge).op
      (N.presheaf.map (homOfLE (π ⁻¹ᵁ W).ι_image_top.le).op s) = s := by
  rw [TopCat.Presheaf.map_map_apply, CohomologyAux.modules_map_self]

include hW in
/-- **Relative Artin–Rees for lifting sections** (EGA III 4.1.5, proof, for `π⁻¹ W ⟶ W`): for
`π : X ⟶ Y` proper, `W ⊆ Y` affine and `M` coherent, there is `c` such that the image in
`Γ(M / I^{n+1} M, π⁻¹ W)` of a section of `M / I^{n+c+1} M` over `π⁻¹ W` lifts to
`Γ(M, π⁻¹ W)`. -/
theorem exists_relative_lift :
    ∃ c, ∀ n (z : Γ(M.quotientIdealPow (π ≫ f) I (n + c), π ⁻¹ᵁ W)), ∃ b : Γ(M, π ⁻¹ᵁ W),
      (M.toQuotientIdealPow (π ≫ f) I n).app (π ⁻¹ᵁ W) b =
        (quotMap I (π ≫ f) M (Nat.le_add_right n c)).app (π ⁻¹ᵁ W) z := by
  have : IsNoetherianRing Γ(Y, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : M.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  let O := π ⁻¹ᵁ W
  let M' := M.restrict O.ι
  have : M'.IsCoherent := ⟨inferInstance, inferInstance⟩
  obtain ⟨c, hc⟩ := exists_H0_lift_quotMap (idealV f I W 1) (relStruct π hW) M'
  refine ⟨c, fun n z ↦ ?_⟩
  let Q := M.quotientIdealPow (π ≫ f) I (n + c)
  let z₁ : Γ(Q.restrict O.ι, ⊤) := Q.presheaf.map (homOfLE O.ι_image_top.le).op z
  let z' := (relQuotientIso I f π hW M (n + c)).inv.app ⊤ z₁
  obtain ⟨y, hy⟩ := hc n ((Scheme.Modules.H.equiv₀ _).symm z')
  let Y₀ : Γ(M', ⊤) := Scheme.Modules.H.equiv₀ M' y
  refine ⟨M.presheaf.map (homOfLE O.ι_image_top.ge).op Y₀, ?_⟩
  have h1 : (M'.toQuotientIdealPow (relStruct π hW) (idealV f I W 1) n).app ⊤ Y₀ =
      (quotMap (idealV f I W 1) (relStruct π hW) M' (Nat.le_add_right n c)).app ⊤ z' := by
    have := congrArg (Scheme.Modules.H.equiv₀ _) hy
    rwa [equiv₀_H'_map, equiv₀_H'_map, LinearEquiv.apply_symm_apply] at this
  have h2 : (M.toQuotientIdealPow (π ≫ f) I n).app (O.ι ''ᵁ ⊤) Y₀ =
      (quotMap I (π ≫ f) M (Nat.le_add_right n c)).app (O.ι ''ᵁ ⊤) z₁ := by
    have := congrArg ((relQuotientIso I f π hW M n).hom.app ⊤) h1
    rw [← Scheme.Modules.Hom.comp_app_apply, toQuotientIdealPow_relQuotientIso,
      ← Scheme.Modules.Hom.comp_app_apply, quotMap_relQuotientIso] at this
    have e : ((relQuotientIso I f π hW M (n + c)).hom ≫
        (Scheme.Modules.restrictFunctor O.ι).map (quotMap I (π ≫ f) M
          (Nat.le_add_right n c))).app ⊤ z' =
        ((Scheme.Modules.restrictFunctor O.ι).map (quotMap I (π ≫ f) M
          (Nat.le_add_right n c))).app ⊤ z₁ := by
      change ((relQuotientIso I f π hW M (n + c)).inv ≫ (relQuotientIso I f π hW M (n + c)).hom ≫
        (Scheme.Modules.restrictFunctor O.ι).map (quotMap I (π ≫ f) M
          (Nat.le_add_right n c))).app ⊤ z₁ = _
      rw [Iso.inv_hom_id_assoc]
    exact this.trans e
  have h3 := hom_app_presheaf_map (M.toQuotientIdealPow (π ≫ f) I n)
    (homOfLE O.ι_image_top.ge) Y₀
  refine h3.trans ?_
  have h4 := hom_app_presheaf_map (quotMap I (π ≫ f) M (Nat.le_add_right n c))
    (homOfLE O.ι_image_top.ge) z₁
  rw [h2, ← h4]
  exact congrArg _ (map_image_top_ge_le π Q z)

end Translation

end Relative

end AlgebraicGeometry.CohomologyAux
