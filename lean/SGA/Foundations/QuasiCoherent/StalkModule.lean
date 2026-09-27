/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Stalk
import SGA.Foundations.QuasiCoherent.Glue
import SGA.Foundations.QuasiCoherent.Stalk
import SGA.Foundations.QuasiCoherent.Tilde

/-!
# Stalks of quasi-coherent modules as modules

For an `𝒪_X`-module `F` and `x ∈ X`, the stalk `F_x` is an `𝒪_{X,x}`-module
(`Scheme.Modules.moduleStalk`, from mathlib's `PresheafOfModules` stalks), and for `x` in an open
`U` a `Γ(X, U)`-module through the germ map; `germₗ` is the germ map `Γ(F, U) → F_x` as a linear
map.

For `F` quasi-coherent and `V` an affine open:

* `exists_pow_smul_eq_map`, `exists_pow_smul_eq_zero`: the restriction `Γ(F, V) → Γ(F, D(c))` is
  the localization at `c ∈ Γ(X, V)` (EGA I, 1.4.1);
* `isLocalizedModule_germₗ`, `stalkLinearEquiv`: for `x ∈ V`, `F_x ≅ Γ(F, V)_𝔭` as
  `Γ(X, V)`-modules, `𝔭` the prime of `x`; `isBaseChange_germₗ`: `F_x ≅ 𝒪_{X,x} ⊗ Γ(F, V)` as
  `𝒪_{X,x}`-modules;
* `finite_sections`: if `F` is moreover of finite type, `Γ(F, V)` is a finite `Γ(X, V)`-module.

`isQuasicoherent_unit`: the structure sheaf `𝒪_X` is quasi-coherent.

For a morphism `f : X ⟶ Y`, `FlatAt f F x` says that `F` is flat over `Y` at `x`, i.e. `F_x` is a
flat `𝒪_{Y, f x}`-module; `flatAt_iff` computes it on affine opens.
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)

/-- Restricting `r ∈ Γ(X, V)` to `fromSpec(W)` corresponds, under `fromSpec`, to restricting the
global section `r` of `Spec Γ(X, V)` to `W`. -/
lemma IsAffineOpen.appIso_fromSpec_map (W : (Spec Γ(X, V)).Opens)
    (h : hV.fromSpec ''ᵁ W ≤ V) (r : Γ(X, V)) :
    (hV.fromSpec.appIso W).hom (X.presheaf.map (homOfLE h).op r) =
      (Spec Γ(X, V)).presheaf.map W.leTop.op ((Scheme.ΓSpecIso Γ(X, V)).inv r) := by
  rw [Scheme.Hom.appIso_hom, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality_assoc,
    IsAffineOpen.fromSpec_app_self]
  simp only [Category.assoc, ← Functor.map_comp, ConcreteCategory.comp_apply]
  rfl

lemma IsAffineOpen.image_fromSpec_le (W : (Spec Γ(X, V)).Opens) : hV.fromSpec ''ᵁ W ≤ V :=
  (Scheme.Hom.image_mono _ le_top).trans
    ((Scheme.Hom.image_top_eq_opensRange _).le.trans hV.opensRange_fromSpec.le)

namespace Scheme.Modules

variable (F : X.Modules)

/-- The `Γ(X, V)`-module structure of the sections of `F|_{Spec Γ(X, V)}` is that of the
sections of `F` over `fromSpec(W)`, through restriction `Γ(X, V) → Γ(X, fromSpec(W))`. -/
lemma restrict_fromSpec_smul (W : (Spec Γ(X, V)).Opens) (r : Γ(X, V))
    (x : Γ(F.restrict hV.fromSpec, W)) :
    (F.restrictAppIso hV.fromSpec W).hom (r • x) =
      X.presheaf.map (homOfLE (hV.image_fromSpec_le W)).op r •
        (F.restrictAppIso hV.fromSpec W).hom x := by
  rw [smul_Spec_def]
  refine (smul_restrictAppIso_hom_apply hV.fromSpec F W _ x).trans ?_
  rw [← hV.appIso_fromSpec_map W (hV.image_fromSpec_le W) r, Iso.hom_inv_id_apply]

lemma presheaf_map_map_apply {Y : Scheme.{u}} {U₁ U₂ U₃ : Y.Opens} (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃)
    (c : U₁ ⟶ U₃) (x : Γ(Y, U₃)) :
    Y.presheaf.map a.op (Y.presheaf.map b.op x) = Y.presheaf.map c.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (a ≫ b) c]

variable [F.IsQuasicoherent]

lemma isLocalizing_restrict_fromSpec :
    IsLocalizing (modulesSpecToSheaf.obj (F.restrict hV.fromSpec)) :=
  (isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance

include hV in
/-- Sections over a basic open are fractions (EGA I, 1.4.1): for `F` quasi-coherent, `V` affine
and `c ∈ Γ(X, V)`, every section of `F` over `D(c)` becomes, after multiplication by a power of
`c`, the restriction of a section over `V`. -/
lemma exists_pow_smul_eq_map (c : Γ(X, V)) (t : Γ(F, X.basicOpen c)) :
    ∃ (m : Γ(F, V)) (k : ℕ), X.presheaf.map (homOfLE (X.basicOpen_le c)).op (c ^ k) • t =
      F.presheaf.map (homOfLE (X.basicOpen_le c)).op m := by
  have hc := F.isLocalizing_restrict_fromSpec hV c
  obtain ⟨D, hDc⟩ : ∃ D : (Spec Γ(X, V)).Opens, D = PrimeSpectrum.basicOpen c := ⟨_, rfl⟩
  have hD : hV.fromSpec ''ᵁ D = X.basicOpen c := hDc ▸ hV.fromSpec_image_basicOpen c
  have hT : hV.fromSpec ''ᵁ ⊤ = V := by
    rw [Scheme.Hom.image_top_eq_opensRange, hV.opensRange_fromSpec]
  rw [← hDc] at hc
  let y : Γ(F.restrict hV.fromSpec, D) := F.presheaf.map (homOfLE hD.le).op t
  obtain ⟨⟨m', ⟨_, k, rfl⟩⟩, hm'⟩ := IsLocalizedModule.surj (Submonoid.powers c)
    ((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map D.leTop.op).hom y
  refine ⟨F.presheaf.map (homOfLE hT.ge).op m', k, ?_⟩
  change (c ^ k) • y = F.presheaf.map (homOfLE
    ((Scheme.Hom.image_mono _ le_top) : _ ≤ hV.fromSpec ''ᵁ ⊤)).op m' at hm'
  have e : F.presheaf.map (homOfLE hD.ge).op
      ((F.restrictAppIso hV.fromSpec D).hom ((c ^ k) • y)) =
      F.presheaf.map (homOfLE hD.ge).op (F.presheaf.map (homOfLE
        ((Scheme.Hom.image_mono _ le_top) : _ ≤ hV.fromSpec ''ᵁ ⊤)).op m') :=
    congrArg (F.presheaf.map (homOfLE hD.ge).op) hm'
  rw [F.restrict_fromSpec_smul hV D (c ^ k) y, map_smul] at e
  refine Eq.trans ?_ (e.trans ?_)
  · congr 1
    · exact (presheaf_map_map_apply _ _ _ _).symm
    · simp only [y]
      change t = F.presheaf.map (homOfLE hD.ge).op (F.presheaf.map (homOfLE hD.le).op t)
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
        Subsingleton.elim (homOfLE hD.ge ≫ homOfLE hD.le) (𝟙 _), op_id,
        CategoryTheory.Functor.map_id]
      rfl
  · exact presheaf_map_map_eq _ _ _ _ _ _

lemma presheaf_map_id_of_le {Y : Scheme.{u}} (P : Y.Modules) {U U' : Y.Opens} (a : U ⟶ U')
    (b : U' ⟶ U) (x : Γ(P, U)) : P.presheaf.map a.op (P.presheaf.map b.op x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (a ≫ b) (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

lemma presheaf_map_id_of_le' {Y : Scheme.{u}} {U U' : Y.Opens} (a : U ⟶ U')
    (b : U' ⟶ U) (x : Γ(Y, U)) : Y.presheaf.map a.op (Y.presheaf.map b.op x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (a ≫ b) (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

include hV in
/-- A section over an affine open `V` vanishing on `D(c)` is killed by a power of `c`
(EGA I, 1.4.1). -/
lemma exists_pow_smul_eq_zero (c : Γ(X, V)) (m : Γ(F, V))
    (hm : F.presheaf.map (homOfLE (X.basicOpen_le c)).op m = 0) : ∃ k : ℕ, c ^ k • m = 0 := by
  have hc := F.isLocalizing_restrict_fromSpec hV c
  obtain ⟨D, hDc⟩ : ∃ D : (Spec Γ(X, V)).Opens, D = PrimeSpectrum.basicOpen c := ⟨_, rfl⟩
  have hD : hV.fromSpec ''ᵁ D = X.basicOpen c := hDc ▸ hV.fromSpec_image_basicOpen c
  have hT : hV.fromSpec ''ᵁ ⊤ = V := by
    rw [Scheme.Hom.image_top_eq_opensRange, hV.opensRange_fromSpec]
  rw [← hDc] at hc
  let m' : Γ(F.restrict hV.fromSpec, ⊤) := F.presheaf.map (homOfLE hT.le).op m
  have h0 : ((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map D.leTop.op).hom m' =
      ((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map D.leTop.op).hom 0 := by
    rw [map_zero]
    change F.presheaf.map (homOfLE ((Scheme.Hom.image_mono _ le_top) :
      hV.fromSpec ''ᵁ D ≤ hV.fromSpec ''ᵁ ⊤)).op (F.presheaf.map (homOfLE hT.le).op m) = 0
    rw [presheaf_map_map_eq F _ _ (homOfLE hD.le) (homOfLE (X.basicOpen_le c)), hm, map_zero]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c) h0
  refine ⟨k, ?_⟩
  rw [smul_zero] at hk
  have hk' : (c ^ k) • m' = 0 := hk
  have e : F.presheaf.map (homOfLE hT.ge).op
      ((F.restrictAppIso hV.fromSpec ⊤).hom ((c ^ k) • m')) = 0 := by
    rw [hk', map_zero, map_zero]
  rw [F.restrict_fromSpec_smul hV ⊤ (c ^ k) m', map_smul] at e
  rw [← e]
  congr 1
  · exact (presheaf_map_id_of_le' _ _ _).symm
  · exact (presheaf_map_id_of_le F _ _ _).symm

section Stalk

variable {Y : Scheme.{u}} (G : Y.Modules)

/-- The stalk `G_y` of an `𝒪_Y`-module is a module over the local ring `𝒪_{Y,y}`. -/
noncomputable instance moduleStalk (y : Y) : Module (Y.presheaf.stalk y) (G.presheaf.stalk y) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := Y.presheaf) G.val y

lemma germ_smul (U : Y.Opens) (y : Y) (hy : y ∈ U) (r : Γ(Y, U)) (m : Γ(G, U)) :
    G.presheaf.germ U y hy (r • m) = Y.presheaf.germ U y hy r • G.presheaf.germ U y hy m :=
  PresheafOfModules.germ_smul (R := Y.presheaf) G.val y U hy r m

/-- For `y ∈ U`, the stalk `G_y` is a `Γ(Y, U)`-module through the germ map. -/
noncomputable instance moduleStalkSections {U : Y.Opens} (y : U) :
    Module Γ(Y, U) (G.presheaf.stalk (y : Y)) :=
  Module.compHom _ (algebraMap Γ(Y, U) (Y.presheaf.stalk (y : Y)))

instance {U : Y.Opens} (y : U) :
    IsScalarTower Γ(Y, U) (Y.presheaf.stalk (y : Y)) (G.presheaf.stalk (y : Y)) :=
  IsScalarTower.of_compHom _ _ _

lemma smul_stalk_def {U : Y.Opens} (y : U) (r : Γ(Y, U)) (z : G.presheaf.stalk (y : Y)) :
    r • z = Y.presheaf.germ U y y.2 r • z := rfl

/-- The germ map `Γ(G, U) → G_y`, as a `Γ(Y, U)`-linear map. -/
noncomputable def germₗ {U : Y.Opens} (y : U) : Γ(G, U) →ₗ[Γ(Y, U)] G.presheaf.stalk (y : Y) where
  toFun := G.presheaf.germ U y y.2
  map_add' := map_add _
  map_smul' r m := G.germ_smul U y y.2 r m

lemma germₗ_apply {U : Y.Opens} (y : U) (m : Γ(G, U)) :
    G.germₗ y m = G.presheaf.germ U y y.2 m := rfl

end Stalk

lemma _root_.AlgebraicGeometry.IsAffineOpen.mem_primeIdealOf_iff (x : V) (s : Γ(X, V)) :
    s ∈ (hV.primeIdealOf x).asIdeal ↔ (x : X) ∉ X.basicOpen s := by
  have e := hV.fromSpec_primeIdealOf x
  have e₂ : (hV.fromSpec ⁻¹ᵁ X.basicOpen s : Set (Spec Γ(X, V))) =
      (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum Γ(X, V))) :=
    congrArg SetLike.coe (hV.fromSpec_preimage_basicOpen s)
  have h₁ : (x : X) ∈ X.basicOpen s ↔ hV.primeIdealOf x ∈ PrimeSpectrum.basicOpen s := by
    rw [← SetLike.mem_coe (x := hV.primeIdealOf x), ← e₂]
    change _ ↔ hV.fromSpec (hV.primeIdealOf x) ∈ X.basicOpen s
    rw [e]
  rw [h₁, PrimeSpectrum.mem_basicOpen, not_not]

/-- The stalk of a quasi-coherent module at a point `x` of an affine open `V` is the localization
of `Γ(F, V)` at the prime of `x` (EGA I, 1.4.1; the germ map is the localization map). -/
theorem isLocalizedModule_germₗ (x : V) :
    IsLocalizedModule (hV.primeIdealOf x).asIdeal.primeCompl (F.germₗ x) where
  map_units s := by
    have := hV.isLocalization_stalk x
    have hs : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk (x : X)) s) :=
      IsLocalization.map_units (M := (hV.primeIdealOf x).asIdeal.primeCompl)
        (X.presheaf.stalk (x : X)) s
    rw [Module.End.isUnit_iff]
    obtain ⟨u, hu⟩ := hs
    refine ⟨fun z₁ z₂ h ↦ ?_, fun z ↦ ⟨(↑u⁻¹ : X.presheaf.stalk (x : X)) • z, ?_⟩⟩
    · change (s : Γ(X, V)) • z₁ = (s : Γ(X, V)) • z₂ at h
      rw [smul_stalk_def, smul_stalk_def] at h
      have := congrArg ((↑u⁻¹ : X.presheaf.stalk (x : X)) • ·) h
      simp only [smul_smul] at this
      change (↑u⁻¹ * algebraMap Γ(X, V) (X.presheaf.stalk (x : X)) s) • z₁ =
        (↑u⁻¹ * algebraMap Γ(X, V) (X.presheaf.stalk (x : X)) s) • z₂ at this
      rwa [← hu, Units.inv_mul, one_smul, one_smul] at this
    · change (s : Γ(X, V)) • ((↑u⁻¹ : X.presheaf.stalk (x : X)) • z) = z
      rw [smul_stalk_def, smul_smul]
      change (algebraMap Γ(X, V) (X.presheaf.stalk (x : X)) s * ↑u⁻¹) • z = z
      rw [← hu, Units.mul_inv, one_smul]
  surj z := by
    obtain ⟨U, hxU, t, rfl⟩ := F.presheaf.exists_germ_eq z
    obtain ⟨f, hfU, hxf⟩ := hV.exists_basicOpen_le ⟨x, hxU⟩ x.2
    obtain ⟨m, k, hmk⟩ := F.exists_pow_smul_eq_map hV f (F.presheaf.map (homOfLE hfU).op t)
    have hf : f ∈ (hV.primeIdealOf x).asIdeal.primeCompl := fun h ↦
      ((hV.mem_primeIdealOf_iff x f).1 h) hxf
    refine ⟨⟨m, ⟨f ^ k, (hV.primeIdealOf x).asIdeal.primeCompl.pow_mem hf k⟩⟩, ?_⟩
    change (f ^ k) • F.presheaf.germ U x hxU t = F.presheaf.germ V x x.2 m
    have e := congrArg (F.presheaf.germ (X.basicOpen f) x hxf) hmk
    rw [germ_smul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply] at e
    exact e
  exists_of_eq {m₁ m₂} h := by
    obtain ⟨W, hxW, i₁, i₂, hW⟩ := F.presheaf.germ_eq x x.2 x.2 m₁ m₂ h
    obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le ⟨x, hxW⟩ x.2
    have hf : f ∈ (hV.primeIdealOf x).asIdeal.primeCompl := fun h ↦
      ((hV.mem_primeIdealOf_iff x f).1 h) hxf
    obtain ⟨k, hk⟩ := F.exists_pow_smul_eq_zero hV f (m₁ - m₂) (by
      rw [map_sub, sub_eq_zero]
      have := congrArg (F.presheaf.map (homOfLE hfW).op) hW
      rwa [presheaf_map_map_eq' F _ _ (homOfLE (X.basicOpen_le f)),
        presheaf_map_map_eq' F _ _ (homOfLE (X.basicOpen_le f))] at this)
    refine ⟨⟨f ^ k, (hV.primeIdealOf x).asIdeal.primeCompl.pow_mem hf k⟩, ?_⟩
    rw [smul_sub, sub_eq_zero] at hk
    exact hk

/-- For `x ∈ V` affine, the stalk `F_x` of a quasi-coherent module is the localization of
`Γ(F, V)` at the prime of `x`, as a `Γ(X, V)`-module. -/
noncomputable def stalkLinearEquiv (x : V) :
    F.presheaf.stalk (x : X) ≃ₗ[Γ(X, V)]
      LocalizedModule (hV.primeIdealOf x).asIdeal.primeCompl Γ(F, V) :=
  have := F.isLocalizedModule_germₗ hV x
  (IsLocalizedModule.iso _ (F.germₗ x)).symm

lemma stalkLinearEquiv_germ (x : V) (m : Γ(F, V)) :
    F.stalkLinearEquiv hV x (F.presheaf.germ V x x.2 m) = LocalizedModule.mk m 1 := by
  have := F.isLocalizedModule_germₗ hV x
  exact IsLocalizedModule.iso_symm_apply _ (F.germₗ x) m

include hV in
/-- The stalk `F_x` is `𝒪_{X,x} ⊗_{Γ(X, V)} Γ(F, V)`, as an `𝒪_{X,x}`-module (EGA I, 1.4.1). -/
theorem isBaseChange_germₗ (x : V) : IsBaseChange (X.presheaf.stalk (x : X)) (F.germₗ x) := by
  have := hV.isLocalization_stalk x
  have := F.isLocalizedModule_germₗ hV x
  exact IsLocalizedModule.isBaseChange (hV.primeIdealOf x).asIdeal.primeCompl _ _

omit [F.IsQuasicoherent] in
/-- The sections of `F|_{Spec Γ(X, V)}` over `Spec Γ(X, V)` are the sections of `F` over `V`, as
`Γ(X, V)`-modules. -/
noncomputable def restrictFromSpecTopLinearEquiv :
    (F.restrict hV.fromSpec).ΓSpec ≃ₗ[Γ(X, V)] Γ(F, V) :=
  have hT : hV.fromSpec ''ᵁ ⊤ = V := by
    rw [Scheme.Hom.image_top_eq_opensRange, hV.opensRange_fromSpec]
  { toFun := fun m ↦ F.presheaf.map (homOfLE hT.ge).op ((F.restrictAppIso hV.fromSpec ⊤).hom m)
    invFun := fun m ↦ F.presheaf.map (homOfLE hT.le).op m
    map_add' := fun a b ↦
      map_add ((F.restrictAppIso hV.fromSpec ⊤).hom ≫ F.presheaf.map (homOfLE hT.ge).op).hom a b
    map_smul' := fun r m ↦ by
      refine (congrArg (F.presheaf.map (homOfLE hT.ge).op)
        (F.restrict_fromSpec_smul hV ⊤ r m)).trans ?_
      rw [map_smul, presheaf_map_id_of_le']
      rfl
    left_inv := fun m ↦ presheaf_map_id_of_le F _ _ m
    right_inv := fun m ↦ presheaf_map_id_of_le F _ _ m }

omit [F.IsQuasicoherent] in
include hV in
/-- For `F` quasi-coherent of finite type and `V` affine, `Γ(F, V)` is a finite `Γ(X, V)`-module
(for `X` locally noetherian: the sections of a coherent module over affine opens are finite). -/
theorem finite_sections [F.IsQuasicoherent] [F.IsFiniteType] : Module.Finite Γ(X, V) Γ(F, V) := by
  have : (F.restrict hV.fromSpec).IsFiniteType :=
    isFiniteType_of_iso ((restrictFunctorIsoPullback hV.fromSpec).app F).symm
  have : (tilde (F.restrict hV.fromSpec).ΓSpec).IsFiniteType :=
    isFiniteType_of_iso (F.restrict hV.fromSpec).tildeΓIso.symm
  have : Module.Finite Γ(X, V) (F.restrict hV.fromSpec).ΓSpec :=
    (isFiniteType_tilde_iff _).mp this
  exact Module.Finite.equiv (F.restrictFromSpecTopLinearEquiv hV)

end Scheme.Modules

namespace Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false in
/-- The structure sheaf `𝒪_X` is quasi-coherent. -/
instance isQuasicoherent_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := by
  have hk : ∀ V : X.affineOpens, IsOpenImmersion ((fun V : X.affineOpens ↦ V.2.fromSpec) V) :=
    fun V ↦ V.2.isOpenImmersion_fromSpec
  refine isQuasicoherent_of_forall_pullback (fun V : X.affineOpens ↦ V.2.fromSpec) (fun x ↦ ?_)
    fun V ↦ ?_
  · obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨⟨V, hV⟩, by rw [hV.range_fromSpec]; exact hxV⟩
  · have : (SheafOfModules.unit (Spec Γ(X, V.1)).ringCatSheaf).IsQuasicoherent :=
      (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
    exact isQuasicoherent_of_iso (pullbackObjUnitIso V.2.fromSpec).symm

section FlatAt

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)

/-- The stalk `F_x` as a module over `𝒪_{Y, f x}`, through the stalk map of `f`. -/
noncomputable abbrev stalkModuleOver (x : X) :
    Module (Y.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
  Module.compHom _ (f.stalkMap x).hom

/-- `F` is flat over `Y` at `x` (relative to `f : X ⟶ Y`): the stalk `F_x` is a flat
`𝒪_{Y, f x}`-module. -/
def FlatAt (x : X) : Prop :=
  letI := stalkModuleOver f F x
  Module.Flat (Y.presheaf.stalk (f x)) (F.presheaf.stalk x)

lemma stalkMap_germ_eq_germ_appLE {U : Y.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U) (x : V)
    (a : Γ(Y, U)) :
    f.stalkMap x (Y.presheaf.germ U (f x) (hVU x.2) a) =
      X.presheaf.germ V x x.2 (f.appLE U V hVU a) := by
  refine (Scheme.Hom.germ_stalkMap_apply f U x (hVU x.2) a).trans ?_
  rw [Scheme.Hom.appLE, ConcreteCategory.comp_apply, TopCat.Presheaf.germ_res_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- Flatness of a quasi-coherent module at a point, over affine opens: for affine opens `U ⊆ Y`
and `V ⊆ f⁻¹ U` and `x ∈ V`, `F` is flat over `Y` at `x` iff the localization of `Γ(F, V)` at the
prime of `x` is flat over `Γ(Y, U)`. -/
theorem flatAt_iff [F.IsQuasicoherent] {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (x : V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    letI : Module Γ(Y, U) Γ(F, V) := Module.compHom _ (algebraMap Γ(Y, U) Γ(X, V))
    haveI : IsScalarTower Γ(Y, U) Γ(X, V) Γ(F, V) := IsScalarTower.of_compHom _ _ _
    F.FlatAt f x ↔
      Module.Flat Γ(Y, U) (LocalizedModule (hV.primeIdealOf x).asIdeal.primeCompl Γ(F, V)) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let : Module Γ(Y, U) Γ(F, V) := Module.compHom _ (algebraMap Γ(Y, U) Γ(X, V))
  have : IsScalarTower Γ(Y, U) Γ(X, V) Γ(F, V) := IsScalarTower.of_compHom _ _ _
  let y : U := ⟨f x, hVU x.2⟩
  let : Module Γ(Y, U) (F.presheaf.stalk (x : X)) :=
    Module.compHom _ (algebraMap Γ(Y, U) Γ(X, V))
  have : IsScalarTower Γ(Y, U) Γ(X, V) (F.presheaf.stalk (x : X)) :=
    IsScalarTower.of_compHom _ _ _
  let := stalkModuleOver f F x
  let : Algebra Γ(Y, U) (Y.presheaf.stalk (f x)) :=
    (Y.presheaf.germ U (f x) (hVU x.2)).hom.toAlgebra
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk (f x)) (F.presheaf.stalk (x : X)) := by
    refine ⟨fun a r z ↦ ?_⟩
    change (f.stalkMap x).hom (Y.presheaf.germ U (f x) (hVU x.2) a * r) • z =
      X.presheaf.germ V x x.2 (f.appLE U V hVU a) • ((f.stalkMap x).hom r • z)
    rw [map_mul, mul_smul]
    congr 1
    exact stalkMap_germ_eq_germ_appLE f hVU x a
  have : IsLocalization.AtPrime (Y.presheaf.stalk (f x)) (hU.primeIdealOf y).asIdeal :=
    hU.isLocalization_stalk y
  have hflat : F.FlatAt f x ↔ Module.Flat Γ(Y, U) (F.presheaf.stalk (x : X)) :=
    Module.flat_iff_of_isLocalization (Y.presheaf.stalk (f x))
      (hU.primeIdealOf y).asIdeal.primeCompl (F.presheaf.stalk (x : X))
  rw [hflat]
  have := F.isLocalizedModule_germₗ hV x
  let e : F.presheaf.stalk (x : X) ≃ₗ[Γ(X, V)]
      LocalizedModule (hV.primeIdealOf x).asIdeal.primeCompl Γ(F, V) :=
    (IsLocalizedModule.iso _ (F.germₗ x)).symm
  exact ⟨fun _ ↦ Module.Flat.of_linearEquiv (e.restrictScalars Γ(Y, U)).symm,
    fun _ ↦ Module.Flat.of_linearEquiv (e.restrictScalars Γ(Y, U))⟩

end FlatAt

end Scheme.Modules

end AlgebraicGeometry
