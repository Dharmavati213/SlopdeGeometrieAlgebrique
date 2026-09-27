/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.StrictLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The strict localization is the limit of the étale neighbourhoods

Let `x̄ : Spec Ω ⟶ X` be a geometric point of a scheme and `𝒪^{sh}_{X,x̄}` the strict localization
(`AlgebraicGeometry.Scheme.Hom.strictLocalization`). For every étale `X`-scheme `W`, composition
with `Spec Ω ⟶ Spec 𝒪^{sh}_{X,x̄}` is a bijection from the `X`-morphisms
`Spec 𝒪^{sh}_{X,x̄} ⟶ W` to the lifts `Spec Ω ⟶ W` of `x̄`
(`AlgebraicGeometry.Scheme.Hom.strictLocalizationHomEquiv`; EGA IV 18.8.1, SGA 4 VIII 4.5,
Stacks 04HX): `Spec 𝒪^{sh}_{X,x̄}` is the limit of the étale neighbourhoods of `x̄`, seen through
their points. The proof reduces to affine charts `V ⊆ W`, `U ⊆ X`, where `Γ(W, V)` is étale over
`Γ(X, U)`, and uses the ring-level statement `IsLocalRing.StrictHenselization.algHomEquivPoint`.
-/

universe u

open CategoryTheory IsLocalRing TensorProduct

noncomputable section

-- The carrier of `Spec R` is only defeq to `PrimeSpectrum R` beyond instance transparency (as in
-- mathlib's `AlgebraicGeometry.Stalk`).
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry

/-- A morphism `f : Spec A ⟶ W` landing in an affine open `V` is `Spec` of the ring map
`Γ(W, V) → A` it induces. -/
lemma Scheme.Hom.SpecMap_appLE_ΓSpecIso_fromSpec {A : CommRingCat.{u}} {W : Scheme.{u}}
    (f : Spec A ⟶ W) {V : W.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ f ⁻¹ᵁ V) :
    Spec.map (f.appLE V ⊤ h ≫ (Scheme.ΓSpecIso A).hom) ≫ hV.fromSpec = f := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec f hV (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Iso.eq_inv_comp, Scheme.isoSpec_Spec_hom] at this
  rw [Spec.map_comp, Category.assoc, this]

/-- Conversely, the ring map induced on an affine open by `Spec.map φ ≫ fromSpec` is `φ`. -/
lemma Scheme.Hom.appLE_ΓSpecIso_eq {A : CommRingCat.{u}} {W : Scheme.{u}}
    (f : Spec A ⟶ W) {V : W.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ f ⁻¹ᵁ V)
    (φ : Γ(W, V) ⟶ A) (hφ : Spec.map φ ≫ hV.fromSpec = f) :
    f.appLE V ⊤ h ≫ (Scheme.ΓSpecIso A).hom = φ := by
  apply Spec.map_injective
  rw [← cancel_mono hV.fromSpec, SpecMap_appLE_ΓSpecIso_fromSpec f hV h, hφ]

lemma Scheme.fromSpecStalk_eq_SpecMap_germ {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hxU : x ∈ U) :
    X.fromSpecStalk x = Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec :=
  (hU.fromSpecStalk_eq_fromSpecStalk hxU).symm

lemma Scheme.Hom.appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens)
    (V : X.Opens) (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst h
  rfl

namespace Scheme.Hom

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X)

attribute [local instance] residueFieldAlgebra stalkAlgebra isScalarTower_stalkAlgebra

instance : IsLocalHom ξ.strictLocalizationToField.hom where
  map_nonunit a ha :=
    (IsLocalRing.StrictHenselization.isUnit_iff_pointHom_ne_zero
      (R := X.presheaf.stalk ξ.imagePoint) (K := Ω) a).mpr ha.ne_zero

lemma toSpecStrictLocalization_apply (y : Spec (.of Ω)) :
    ξ.toSpecStrictLocalization y = closedPoint ξ.strictLocalization := by
  rw [Subsingleton.elim y (closedPoint Ω)]
  exact Spec_closedPoint

lemma apply_eq_imagePoint (y : Spec (.of Ω)) : ξ y = ξ.imagePoint := by
  calc ξ y = (ξ.toSpecStrictLocalization ≫ ξ.fromSpecStrictLocalization) y := by
        rw [toSpecStrictLocalization_fromSpecStrictLocalization]
    _ = ξ.imagePoint := by
      rw [Scheme.Hom.comp_apply, toSpecStrictLocalization_apply,
        fromSpecStrictLocalization_closedPoint]

/-- The ring map `Γ(X, U) → 𝒪^{sh}_{X,x̄}` for an affine open neighbourhood `U` of the image. -/
def strictLocalizationAppLE (U : X.Opens) (hU : ξ.imagePoint ∈ U) :
    Γ(X, U) ⟶ ξ.strictLocalization :=
  ξ.fromSpecStrictLocalization.appLE U ⊤ (by
    rw [preimage_eq_top_of_closedPoint_mem]
    rwa [fromSpecStrictLocalization_closedPoint]) ≫ (ΓSpecIso _).hom

/-- Uniqueness: two `X`-morphisms from `Spec 𝒪^{sh}_{X,x̄}` to an étale `X`-scheme which agree
on the geometric point are equal. -/
theorem eq_of_comp_toSpecStrictLocalization {W : Scheme.{u}} (p : W ⟶ X) [Etale p]
    {f₁ f₂ : Spec ξ.strictLocalization ⟶ W} (h₁ : f₁ ≫ p = ξ.fromSpecStrictLocalization)
    (h₂ : f₂ ≫ p = ξ.fromSpecStrictLocalization)
    (h : ξ.toSpecStrictLocalization ≫ f₁ = ξ.toSpecStrictLocalization ≫ f₂) : f₁ = f₂ := by
  have hc : f₁ (closedPoint ξ.strictLocalization) = f₂ (closedPoint ξ.strictLocalization) := by
    have := congrArg (fun g ↦ g (closedPoint Ω)) h
    simpa only [Scheme.Hom.comp_apply, toSpecStrictLocalization_apply] using this
  have hpw₀ : p (f₁ (closedPoint ξ.strictLocalization)) = ξ.imagePoint := by
    rw [← Scheme.Hom.comp_apply, h₁, fromSpecStrictLocalization_closedPoint]
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ξ.imagePoint) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, hVU⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (show f₁ (closedPoint ξ.strictLocalization) ∈ p ⁻¹ᵁ U by simpa [hpw₀] using hxU)
    (p ⁻¹ᵁ U).isOpen
  have e : V ≤ p ⁻¹ᵁ U := hVU
  have hf₁ : ⊤ ≤ f₁ ⁻¹ᵁ V := (Scheme.preimage_eq_top_of_closedPoint_mem f₁ hwV).ge
  have hf₂ : ⊤ ≤ f₂ ⁻¹ᵁ V := (Scheme.preimage_eq_top_of_closedPoint_mem f₂ (hc ▸ hwV)).ge
  let φ₁ := f₁.appLE V ⊤ hf₁ ≫ (ΓSpecIso ξ.strictLocalization).hom
  let φ₂ := f₂.appLE V ⊤ hf₂ ≫ (ΓSpecIso ξ.strictLocalization).hom
  suffices hφ : φ₁ = φ₂ by
    rw [← SpecMap_appLE_ΓSpecIso_fromSpec f₁ hV hf₁, ← SpecMap_appLE_ΓSpecIso_fromSpec f₂ hV hf₂]
    exact congrArg (fun φ ↦ Spec.map φ ≫ hV.fromSpec) hφ
  -- both are maps of `Γ(X, U)`-algebras
  have hcomp (f : Spec ξ.strictLocalization ⟶ W) (hf : f ≫ p = ξ.fromSpecStrictLocalization)
      (hfV : ⊤ ≤ f ⁻¹ᵁ V) :
      p.appLE U V e ≫ f.appLE V ⊤ hfV ≫ (ΓSpecIso ξ.strictLocalization).hom =
        ξ.strictLocalizationAppLE U hxU := by
    rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE, strictLocalizationAppLE,
      Scheme.Hom.appLE_eq_of_eq hf]
  -- and agree after composing with the point
  have hpt (f : Spec ξ.strictLocalization ⟶ W) (hfV : ⊤ ≤ f ⁻¹ᵁ V) :
      f.appLE V ⊤ hfV ≫ (ΓSpecIso ξ.strictLocalization).hom ≫ ξ.strictLocalizationToField =
        (ξ.toSpecStrictLocalization ≫ f).appLE V ⊤ (fun y _ ↦ hfV (Set.mem_univ _)) ≫
          (ΓSpecIso _).hom := by
    have e₂ : (⊤ : (Spec (.of Ω)).Opens) ≤ ξ.toSpecStrictLocalization ⁻¹ᵁ ⊤ :=
      fun _ _ ↦ Set.mem_univ _
    rw [← Scheme.Hom.appLE_comp_appLE ξ.toSpecStrictLocalization f V ⊤ ⊤ hfV e₂,
      Category.assoc]
    congr 1
    have : ξ.toSpecStrictLocalization.appLE ⊤ ⊤ e₂ = ξ.toSpecStrictLocalization.appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [this, toSpecStrictLocalization, Scheme.ΓSpecIso_naturality]
  have hpt' : φ₁ ≫ ξ.strictLocalizationToField = φ₂ ≫ ξ.strictLocalizationToField := by
    simp only [φ₁, φ₂, Category.assoc, hpt]
    exact congrArg (· ≫ _) (Scheme.Hom.appLE_eq_of_eq h V ⊤ _ _)
  -- the ring-level uniqueness
  have hét := HasRingHomProperty.appLE @Etale p ‹_› ⟨U, hU⟩ ⟨V, hV⟩ e
  algebraize [(p.appLE U V e).hom, (ξ.strictLocalizationAppLE U hxU).hom]
  let ψ₁ : Γ(W, V) →ₐ[Γ(X, U)] ξ.strictLocalization := ⟨φ₁.hom, fun r ↦ by
    change (p.appLE U V e ≫ φ₁).hom r = _
    rw [hcomp f₁ h₁ hf₁]
    rfl⟩
  let ψ₂ : Γ(W, V) →ₐ[Γ(X, U)] ξ.strictLocalization := ⟨φ₂.hom, fun r ↦ by
    change (p.appLE U V e ≫ φ₂).hom r = _
    rw [hcomp f₂ h₂ hf₂]
    rfl⟩
  have : ψ₁ = ψ₂ := Algebra.FormallyUnramified.algHom_ext_of_residue fun a ↦ by
    apply StrictHenselization.residueFieldHom_injective
    exact congrArg (fun φ ↦ φ.hom a) hpt'
  ext a
  exact congrArg (fun ψ ↦ ψ a) this

lemma strictLocalizationAppLE_eq (U : X.Opens) (hU : IsAffineOpen U) (hxU : ξ.imagePoint ∈ U) :
    ξ.strictLocalizationAppLE U hxU = X.presheaf.germ U _ hxU ≫ ξ.toStrictLocalization := by
  refine Scheme.Hom.appLE_ΓSpecIso_eq _ hU _ _ ?_
  rw [Spec.map_comp, Category.assoc, ← Scheme.fromSpecStalk_eq_SpecMap_germ hU hxU]
  rfl

lemma appLE_ΓSpecIso_eq_germ (U : X.Opens) (hU : IsAffineOpen U) (hxU : ξ.imagePoint ∈ U)
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) :
    ξ.appLE U ⊤ h ≫ (ΓSpecIso _).hom =
      X.presheaf.germ U _ hxU ≫ X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding := by
  refine Scheme.Hom.appLE_ΓSpecIso_eq _ hU _ _ ?_
  conv_rhs => rw [← ξ.fromSpecResidueField_eq]
  rw [Scheme.fromSpecResidueField, Scheme.fromSpecStalk_eq_SpecMap_germ hU hxU]
  simp only [Spec.map_comp, Category.assoc]

/-- Existence: every point of an étale `X`-scheme `W` over the geometric point `x̄` extends to an
`X`-morphism `Spec 𝒪^{sh}_{X,x̄} ⟶ W`. -/
theorem exists_comp_toSpecStrictLocalization {W : Scheme.{u}} (p : W ⟶ X) [Etale p]
    (w : Spec (.of Ω) ⟶ W) (hw : w ≫ p = ξ) :
    ∃ f : Spec ξ.strictLocalization ⟶ W, f ≫ p = ξ.fromSpecStrictLocalization ∧
      ξ.toSpecStrictLocalization ≫ f = w := by
  have hpw₀ : p (w (closedPoint Ω)) = ξ.imagePoint := by
    rw [← Scheme.Hom.comp_apply, hw, apply_eq_imagePoint]
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ξ.imagePoint) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, hVU⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (show w (closedPoint Ω) ∈ p ⁻¹ᵁ U by simpa [hpw₀] using hxU) (p ⁻¹ᵁ U).isOpen
  have e : V ≤ p ⁻¹ᵁ U := hVU
  have hwV' : ⊤ ≤ w ⁻¹ᵁ V := (Scheme.preimage_eq_top_of_closedPoint_mem w hwV).ge
  have hξU : ⊤ ≤ ξ ⁻¹ᵁ U := fun y _ ↦ by
    change ξ y ∈ U
    rw [apply_eq_imagePoint]
    exact hxU
  -- the point of `Γ(W, V)`
  let τ : Γ(W, V) ⟶ CommRingCat.of Ω := w.appLE V ⊤ hwV' ≫ (ΓSpecIso _).hom
  have hwτ : Spec.map τ ≫ hV.fromSpec = w := SpecMap_appLE_ΓSpecIso_fromSpec w hV hwV'
  have hτ : p.appLE U V e ≫ τ =
      X.presheaf.germ U _ hxU ≫ X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding := by
    rw [← appLE_ΓSpecIso_eq_germ ξ U hU hxU hξU, ← Category.assoc, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (· ≫ _) (Scheme.Hom.appLE_eq_of_eq hw U ⊤ _ _)
  -- the étale `𝒪_{X,x}`-algebra `𝒪_{X,x} ⊗_{Γ(X, U)} Γ(W, V)` and its `Ω`-point
  have hét := HasRingHomProperty.appLE @Etale p ‹_› ⟨U, hU⟩ ⟨V, hV⟩ e
  let : Algebra Γ(X, U) Γ(W, V) := (p.appLE U V e).hom.toAlgebra
  let : Algebra Γ(X, U) (X.presheaf.stalk ξ.imagePoint) :=
    (X.presheaf.germ U _ hxU).hom.toAlgebra
  have : Algebra.Etale Γ(X, U) Γ(W, V) := hét
  let : Algebra Γ(X, U) Ω :=
    ((algebraMap (X.presheaf.stalk ξ.imagePoint) Ω).comp
      (algebraMap Γ(X, U) (X.presheaf.stalk ξ.imagePoint))).toAlgebra
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk ξ.imagePoint) Ω := .of_algebraMap_eq' rfl
  let τA : Γ(W, V) →ₐ[Γ(X, U)] Ω :=
    { τ.hom with commutes' := fun a ↦ congrArg (fun φ ↦ φ.hom a) hτ }
  let B := X.presheaf.stalk ξ.imagePoint ⊗[Γ(X, U)] Γ(W, V)
  let σ : B →ₐ[X.presheaf.stalk ξ.imagePoint] Ω :=
    Algebra.TensorProduct.lift (Algebra.ofId _ Ω) τA fun _ _ ↦ .all _ _
  let ψ := (StrictHenselization.algHomEquivPoint (R := X.presheaf.stalk ξ.imagePoint) (K := Ω)
    B).symm σ
  have hψ (b : B) : StrictHenselization.pointHom (ψ b) = σ b :=
    DFunLike.congr_fun ((StrictHenselization.algHomEquivPoint B).apply_symm_apply σ) b
  let φ : Γ(W, V) ⟶ ξ.strictLocalization :=
    CommRingCat.ofHom (ψ.toRingHom.comp
      (Algebra.TensorProduct.includeRight : Γ(W, V) →ₐ[Γ(X, U)] B).toRingHom)
  refine ⟨Spec.map φ ≫ hV.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec p hU hV e, ← Category.assoc,
      ← Spec.map_comp, fromSpecStrictLocalization, Scheme.fromSpecStalk_eq_SpecMap_germ hU hxU,
      ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    change ψ ((1 : X.presheaf.stalk ξ.imagePoint) ⊗ₜ[Γ(X, U)] (p.appLE U V e).hom a) =
      algebraMap (X.presheaf.stalk ξ.imagePoint) (StrictHenselization _ Ω)
        ((X.presheaf.germ U _ hxU).hom a)
    have hab : (1 : X.presheaf.stalk ξ.imagePoint) ⊗ₜ[Γ(X, U)] (p.appLE U V e).hom a =
        algebraMap (X.presheaf.stalk ξ.imagePoint) B ((X.presheaf.germ U _ hxU).hom a) := by
      rw [Algebra.TensorProduct.algebraMap_apply]
      change _ = algebraMap Γ(X, U) (X.presheaf.stalk ξ.imagePoint) a ⊗ₜ[Γ(X, U)] 1
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      rfl
    rw [hab, AlgHom.commutes]
  · rw [toSpecStrictLocalization, ← Category.assoc, ← Spec.map_comp, ← hwτ]
    congr 2
    ext a
    change StrictHenselization.pointHom (ψ (1 ⊗ₜ a)) = τ.hom a
    rw [hψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl

/-- The strict localization is the limit of the étale neighbourhoods of the geometric point
(EGA IV 18.8.1, SGA 4 VIII 4.5, Stacks 04HX): for `W` étale over `X`, the `X`-morphisms
`Spec 𝒪^{sh}_{X,x̄} ⟶ W` correspond, by composition with `Spec Ω ⟶ Spec 𝒪^{sh}_{X,x̄}`, to the
lifts `Spec Ω ⟶ W` of `x̄`. -/
def strictLocalizationHomEquiv {W : Scheme.{u}} (p : W ⟶ X) [Etale p] :
    {f : Spec ξ.strictLocalization ⟶ W // f ≫ p = ξ.fromSpecStrictLocalization} ≃
      {w : Spec (.of Ω) ⟶ W // w ≫ p = ξ} :=
  Equiv.ofBijective (fun f ↦ ⟨ξ.toSpecStrictLocalization ≫ f.1, by
      rw [Category.assoc, f.2, toSpecStrictLocalization_fromSpecStrictLocalization]⟩)
    ⟨fun f₁ f₂ h ↦ Subtype.ext (ξ.eq_of_comp_toSpecStrictLocalization p f₁.2 f₂.2
      (congrArg Subtype.val h)), fun w ↦ by
        obtain ⟨f, hf, hfw⟩ := ξ.exists_comp_toSpecStrictLocalization p w.1 w.2
        exact ⟨⟨f, hf⟩, Subtype.ext hfw⟩⟩

@[simp]
lemma coe_strictLocalizationHomEquiv_apply {W : Scheme.{u}} (p : W ⟶ X) [Etale p]
    (f : {f : Spec ξ.strictLocalization ⟶ W // f ≫ p = ξ.fromSpecStrictLocalization}) :
    (ξ.strictLocalizationHomEquiv p f : Spec (.of Ω) ⟶ W) = ξ.toSpecStrictLocalization ≫ f.1 :=
  rfl

end Scheme.Hom

end AlgebraicGeometry
