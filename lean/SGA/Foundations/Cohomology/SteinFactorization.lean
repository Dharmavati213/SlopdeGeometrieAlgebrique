/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.ZariskiConnectedness
import SGA.Foundations.Cohomology.PushforwardProjective
import SGA.Foundations.Cohomology.ProperFiniteness
import Mathlib.AlgebraicGeometry.Normalization

/-!
# Stein factorization

`AlgebraicGeometry.steinFactorizationStatement` (EGA III 4.3.3; Stacks Tag 03H0; Hartshorne
III.11.5): a proper `f : X ⟶ Y` to a locally noetherian scheme factors as `X ⟶ Y' ⟶ Y` with
`Y' ⟶ Y` finite and `g : X ⟶ Y'` proper, `𝒪_{Y'} ≅ g_* 𝒪_X`, with connected fibres.

We take for `Y'` mathlib's relative normalization `f.normalization` of `Y` in `X`
(`Scheme.Hom.toNormalization`, `Scheme.Hom.fromNormalization`). Since `f` is proper,
`Γ(f⁻¹ U, 𝒪_X)` is a finite `Γ(U, 𝒪_Y)`-module for `U` affine
(`CohomologyAux.finite_sections_preimage_of_isProper`, EGA III 3.2.1 in degree `0`), hence
integral, so `Y' = Spec_Y f_* 𝒪_X`:

* `CohomologyAux.isFinite_fromNormalization`: `Y' ⟶ Y` is finite;
* `CohomologyAux.isIso_toNormalization_app`: `g^♯ : 𝒪_{Y'} → g_* 𝒪_X` is an isomorphism. It is one
  on the preimages of affine opens of `Y`, hence on their basic opens (localization,
  `CohomologyAux.isIso_app_basicOpen`), hence everywhere (`CohomologyAux.isIso_app_of_basis`);
* the fibres of `g` are connected by Zariski's connectedness theorem
  (`AlgebraicGeometry.zariskiConnectednessStatement`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

section Finite

variable {X Z : Scheme.{u}}

/-- **Finiteness of direct images along proper morphisms in degree `0`** (EGA III 3.2.1): for
`π : X ⟶ Z` proper with `Z` locally noetherian and `F` coherent, the sections of `F` over the
inverse image of an affine open `W` form a finitely generated `Γ(Z, W)`-module. -/
theorem finite_sections_preimage_of_isProper [IsLocallyNoetherian Z] (π : X ⟶ Z)
    [IsProper π] (F : X.Modules) [F.IsCoherent] {W : Z.Opens} (hW : IsAffineOpen W) :
    letI := Module.compHom Γ(F, π ⁻¹ᵁ W) (π.app W).hom
    Module.Finite Γ(Z, W) Γ(F, π ⁻¹ᵁ W) := by
  have hR : IsNoetherianRing Γ(Z, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let π' : (π ⁻¹ᵁ W).toScheme ⟶ W.toScheme := π ∣_ W
  let f' : (π ⁻¹ᵁ W).toScheme ⟶ Spec Γ(Z, W) := π' ≫ hW.isoSpec.hom
  let F' := F.restrict (π ⁻¹ᵁ W).ι
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : F.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have : F'.IsCoherent := ⟨inferInstance, inferInstance⟩
  have h := properFinitenessStatement Γ(Z, W) _ f' F' 0
  let _ := F'.moduleOver f' 0 ⊤
  let _ := Module.compHom Γ(F', ⊤) f'.specStructureRingHom
  let _ := Module.compHom Γ(F, π ⁻¹ᵁ W) (π.app W).hom
  let e0 := Scheme.Modules.H.equiv₀ F'
  let e1 : F'.H 0 ≃ₗ[Γ(Z, W)] Γ(F', ⊤) :=
    { toAddEquiv := e0.toAddEquiv
      map_smul' := fun a x ↦ by
        change e0 (f'.specStructureRingHom a • x) = f'.specStructureRingHom a • e0 x
        rw [LinearEquiv.map_smul] }
  let θ : Γ(F, (π ⁻¹ᵁ W).ι ''ᵁ ⊤) ≃+ Γ(F, π ⁻¹ᵁ W) :=
    { toFun := F.presheaf.map (homOfLE ((π ⁻¹ᵁ W).ι_image_top.ge)).op
      invFun := F.presheaf.map (homOfLE ((π ⁻¹ᵁ W).ι_image_top.le)).op
      left_inv := fun x ↦ by
        rw [TopCat.Presheaf.map_map_apply, CohomologyAux.modules_map_self]
      right_inv := fun x ↦ by
        rw [TopCat.Presheaf.map_map_apply, CohomologyAux.modules_map_self]
      map_add' := map_add _ }
  let e2 : Γ(F', ⊤) ≃ₗ[Γ(Z, W)] Γ(F, π ⁻¹ᵁ W) :=
    { toAddEquiv := θ
      map_smul' := fun a x ↦ by
        change F.presheaf.map (homOfLE ((π ⁻¹ᵁ W).ι_image_top.ge)).op
          (@id Γ(F, (π ⁻¹ᵁ W).ι ''ᵁ ⊤)
            (((π ⁻¹ᵁ W).ι.appIso ⊤).inv (f'.specStructureRingHom a) •
              @id Γ(F, (π ⁻¹ᵁ W).ι ''ᵁ ⊤) x)) =
          @id Γ(X, π ⁻¹ᵁ W) (π.app W a) •
            F.presheaf.map (homOfLE ((π ⁻¹ᵁ W).ι_image_top.ge)).op
              (@id Γ(F, (π ⁻¹ᵁ W).ι ''ᵁ ⊤) x)
        rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
        erw [Scheme.Modules.map_smul]
        congr 1
        exact map_specStructureRingHom_morphismRestrict π hW a }
  exact Module.Finite.equiv (e1.trans e2)

/-- For `π` proper over a locally noetherian base, `Γ(X, π⁻¹ W)` is a finite `Γ(Z, W)`-algebra
for `W` affine. -/
theorem finite_app_of_isProper [IsLocallyNoetherian Z] (π : X ⟶ Z) [IsProper π] {W : Z.Opens}
    (hW : IsAffineOpen W) : (π.app W).hom.Finite := by
  have h := finite_sections_preimage_of_isProper π (unitModule X) hW
  let _ := (π.app W).hom.toAlgebra
  exact h

end Finite

section IsoApp

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- If `g^♯ : Γ(Y, U) → Γ(X, g⁻¹ U)` is bijective for an affine open `U` with `g⁻¹ U` qcqs, then
so is `g^♯` on every basic open `D(s) ⊆ U`: both sides are the localizations at `s`. -/
lemma isIso_app_basicOpen {U : Y.Opens} (hU : IsAffineOpen U) (hc : IsCompact (g ⁻¹ᵁ U : Set X))
    (hqs : IsQuasiSeparated (g ⁻¹ᵁ U : Set X)) (hg : IsIso (g.app U)) (s : Γ(Y, U)) :
    IsIso (g.app (Y.basicOpen s)) := by
  let t := g.app U s
  have e : g ⁻¹ᵁ Y.basicOpen s = X.basicOpen t := Scheme.preimage_basicOpen g s
  have hL₁ : IsLocalization.Away s Γ(Y, Y.basicOpen s) := hU.isLocalization_basicOpen s
  have hL₂ : IsLocalization.Away t Γ(X, X.basicOpen t) := isLocalization_basicOpen_of_qcqs hc hqs t
  let ρ : Γ(X, g ⁻¹ᵁ Y.basicOpen s) ⟶ Γ(X, X.basicOpen t) := X.presheaf.map (eqToHom e.symm).op
  let ψ : Γ(Y, Y.basicOpen s) →+* Γ(X, X.basicOpen t) := (g.app (Y.basicOpen s) ≫ ρ).hom
  let φ : Γ(Y, U) ≃+* Γ(X, g ⁻¹ᵁ U) := (asIso (g.app U)).commRingCatIsoToRingEquiv
  have H : (Submonoid.powers s).map φ.toMonoidHom = Submonoid.powers t := Submonoid.map_powers _ s
  have hψ : ψ = (IsLocalization.ringEquivOfRingEquiv Γ(Y, Y.basicOpen s) Γ(X, X.basicOpen t) φ H :
      Γ(Y, Y.basicOpen s) →+* Γ(X, X.basicOpen t)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun a ↦ ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom,
      IsLocalization.ringEquivOfRingEquiv_eq]
    change (X.presheaf.map (eqToHom e.symm).op) (g.app (Y.basicOpen s)
      (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op a)) =
      X.presheaf.map (homOfLE (X.basicOpen_le t)).op (g.app U a)
    have hn := ConcreteCategory.congr_hom (g.naturality (homOfLE (Y.basicOpen_le s)).op) a
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
    rw [hn, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hbij : Function.Bijective ψ := by
    rw [hψ]
    exact (IsLocalization.ringEquivOfRingEquiv _ _ φ H).bijective
  have hρ : IsIso ρ := inferInstance
  have hbij' : Function.Bijective (g.app (Y.basicOpen s)).hom := by
    have hρb := ConcreteCategory.bijective_of_isIso ρ
    exact (Function.Bijective.of_comp_iff' hρb _).mp hbij
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij'

/-- Naturality of `g^♯` for an inclusion of opens `U ≤ V`, elementwise. -/
lemma app_map_apply {U V : Y.Opens} (hUV : U ≤ V) (s : Γ(Y, V)) :
    g.app U (Y.presheaf.map (homOfLE hUV).op s) =
      X.presheaf.map (homOfLE (g.preimage_mono hUV)).op (g.app V s) :=
  ConcreteCategory.congr_hom (g.naturality (homOfLE hUV).op) s

/-- **`g^♯` is an isomorphism as soon as it is one on a basis of opens.** -/
lemma isIso_app_of_basis
    (h : ∀ (V : Y.Opens) (y : Y), y ∈ V → ∃ U : Y.Opens, y ∈ U ∧ U ≤ V ∧ IsIso (g.app U))
    (V : Y.Opens) : IsIso (g.app V) := by
  choose U hyU hUV hU using h
  have hbij : ∀ (V : Y.Opens) (y : Y) (hy : y ∈ V), Function.Bijective (g.app (U V y hy)) :=
    fun V y hy ↦ ConcreteCategory.bijective_of_isIso (g.app (U V y hy))
  -- injectivity on all opens
  have hinj : ∀ V : Y.Opens, Function.Injective (g.app V) := by
    intro V s t hst
    refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf (fun y : V ↦ U V y.1 y.2) V
      (fun y ↦ homOfLE (hUV V y.1 y.2)) (fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyU V y hy⟩)
      s t fun y ↦ (hbij V y.1 y.2).1 ?_
    change g.app _ (Y.presheaf.map (homOfLE (hUV V y.1 y.2)).op s) =
      g.app _ (Y.presheaf.map (homOfLE (hUV V y.1 y.2)).op t)
    rw [app_map_apply, app_map_apply, hst]
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj V, fun u ↦ ?_⟩
  -- local preimages
  let W : V → Y.Opens := fun y ↦ U V y.1 y.2
  let sf : ∀ y : V, Γ(Y, W y) := fun y ↦ (hbij V y.1 y.2).2
    (X.presheaf.map (homOfLE (g.preimage_mono (hUV V y.1 y.2))).op u) |>.choose
  have hsf : ∀ y : V, g.app (W y) (sf y) =
      X.presheaf.map (homOfLE (g.preimage_mono (hUV V y.1 y.2))).op u := fun y ↦
    ((hbij V y.1 y.2).2 _).choose_spec
  have hc : TopCat.Presheaf.IsCompatible Y.sheaf.1 W sf := by
    intro y z
    apply hinj
    change g.app _ (Y.presheaf.map (homOfLE inf_le_left).op (sf y)) =
      g.app _ (Y.presheaf.map (homOfLE inf_le_right).op (sf z))
    rw [app_map_apply, app_map_apply, hsf, hsf, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf W V
    (fun y ↦ homOfLE (hUV V y.1 y.2)) (fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyU V y hy⟩) sf hc
  refine ⟨s, TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun y : V ↦ g ⁻¹ᵁ W y) (g ⁻¹ᵁ V)
    (fun y ↦ homOfLE (g.preimage_mono (hUV V y.1 y.2)))
    (fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨g x, hx⟩, hyU V (g x) hx⟩) _ _ fun y ↦ ?_⟩
  change X.presheaf.map _ (g.app V s) = X.presheaf.map _ u
  rw [← hsf y, ← hs y]
  exact (app_map_apply g (hUV V y.1 y.2) s).symm

end IsoApp

section Stein

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]

lemma isIntegral_app_of_isProper {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    Algebra.IsIntegral Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  let _ := (f.app U).hom.toAlgebra
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := finite_app_of_isProper f hU
  infer_instance

/-- For `f` proper over a locally noetherian base, `f_* 𝒪_X` is finite over `𝒪_Y`, so the relative
normalization `Y'` of `Y` in `X` is finite over `Y`. -/
theorem isFinite_fromNormalization : IsFinite f.fromNormalization := by
  rw [isFinite_iff]
  refine ⟨inferInstance, fun U hU ↦ ?_⟩
  let _ := (f.app U).hom.toAlgebra
  have hfin : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := finite_app_of_isProper f hU
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : _root_.IsNoetherian Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  have : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) :=
    Module.Finite.of_injective (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)).val.toLinearMap
      Subtype.val_injective
  rw [Scheme.Hom.fromNormalization_app f hU, CommRingCat.hom_comp]
  refine RingHom.Finite.comp ?_ (RingHom.finite_algebraMap.mpr this)
  exact RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2

lemma isIso_toNormalization_app_preimage {U : Y.Opens} (hU : IsAffineOpen U) :
    IsIso (f.toNormalization.app (f.fromNormalization ⁻¹ᵁ U)) := by
  let _ := (f.app U).hom.toAlgebra
  have hint := isIntegral_app_of_isProper f hU
  have e := f.toNormalization_app_preimage ⟨U, hU⟩
  have hval : IsIso (CommRingCat.ofHom
      (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, Algebra.IsIntegral.isIntegral x⟩, rfl⟩⟩
  rw [e]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (@IsIso.comp_isIso _ _ _ _ _ _ _ hval
    inferInstance)

/-- **`𝒪_{Y'} ≅ g_* 𝒪_X`** for the Stein factorization `X ⟶ Y' ⟶ Y` of a proper `f`. -/
theorem isIso_toNormalization_app (V : f.normalization.Opens) :
    IsIso (f.toNormalization.app V) := by
  refine isIso_app_of_basis f.toNormalization (fun V y hy ↦ ?_) V
  obtain ⟨U, hU, hyU, -⟩ : ∃ U : Y.Opens, IsAffineOpen U ∧ f.fromNormalization y ∈ U ∧ U ≤ ⊤ :=
    Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (show f.fromNormalization y ∈ (⊤ : Y.Opens)
      from trivial)
  have hU' : IsAffineOpen (f.fromNormalization ⁻¹ᵁ U) := hU.preimage _
  obtain ⟨s, hsV, hys⟩ := hU'.exists_basicOpen_le ⟨y, hy⟩ hyU
  refine ⟨_, hys, hsV, isIso_app_basicOpen f.toNormalization hU'
    (f.toNormalization.isCompact_preimage hU'.isCompact)
    (f.toNormalization.isQuasiSeparated_preimage hU'.isQuasiSeparated)
    (isIso_toNormalization_app_preimage f hU) s⟩

end Stein

end AlgebraicGeometry.CohomologyAux

namespace AlgebraicGeometry

open CohomologyAux

/-- **Stein factorization** (EGA III 4.3.3; Stacks Tag 03H0; Hartshorne III.11.5): a proper
`f : X ⟶ Y` to a locally noetherian scheme factors as `X ⟶ Y' ⟶ Y` with `Y' ⟶ Y` finite and
`g : X ⟶ Y'` proper with `𝒪_{Y'} ≅ g_* 𝒪_X` and connected fibres; here `Y'` is the relative
normalization of `Y` in `X` (which is `Spec_Y f_* 𝒪_X`, since `f_* 𝒪_X` is finite over `𝒪_Y`). -/
theorem steinFactorizationStatement : SteinFactorizationStatement.{u} := by
  intro X Y f _ _
  have hfin : IsFinite f.fromNormalization := isFinite_fromNormalization f
  have : IsProper f.toNormalization := by
    have : IsProper (f.toNormalization ≫ f.fromNormalization) := by
      rw [f.toNormalization_fromNormalization]
      infer_instance
    exact IsProper.of_comp _ f.fromNormalization
  have : IsLocallyNoetherian f.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian f.fromNormalization
  have hiso : ∀ V, IsIso (f.toNormalization.app V) := isIso_toNormalization_app f
  exact ⟨f.normalization, f.toNormalization, f.fromNormalization, inferInstance, hfin,
    f.toNormalization_fromNormalization, hiso,
    zariskiConnectednessStatement _ _ f.toNormalization hiso⟩

end AlgebraicGeometry
