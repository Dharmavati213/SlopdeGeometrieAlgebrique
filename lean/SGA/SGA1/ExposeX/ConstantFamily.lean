/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeV.MultiGalois
import SGA.SGA1.ExposeV.QuotientHasQuotients
import SGA.SGA1.ExposeX.BaseChangeAlgClosed

/-!
# SGA 1, Exposé X, 1.9: a family of étale coverings parametrized by a connected scheme

X.1.9 (`constantFamilyStatement`): for `k` algebraically closed, `X`, `Y` locally noetherian over
`k`, `Y` connected, `X` or `Y` proper, and `Z'` an étale covering of `X ×ₖ Y`, the coverings
`j_y⁻¹(Z')` of `X` (`y ∈ Y(k)`, `j_y = id_X ×ₖ y`) are all isomorphic. SGA deduces this from the
description of the coverings of a product given by X.1.7. We argue with fundamental groups:

* formal part (`conj_comp_eq_of_injective`, `nonempty_iso_of_conjAut_autMap`): if
  `π₁(X ×ₖ Y) → π₁(X) × π₁(Y)` is injective at `j_{y₂}(a)`, a path between the fibre functors at
  `j_{y₁}(a)` and `j_{y₂}(a)` can be chosen to intertwine the homomorphisms `π₁(j_{yᵢ})` (sections
  of `π₁(pr₁)`, killed by `π₁(pr₂)`), so the `π₁(X)`-sets `j_{yᵢ}⁻¹(Z')` are isomorphic
  (`nonempty_iso_of_injective_map_prod`);
* the injectivity: for `X` proper, connected and reduced, X.1.7 at a rational point
  (`bijective_map_prod`); for `Y` proper, connected and reduced, X.1.4 for `pr₁` and X.1.8 for
  `Y`, at a geometric point of `X` (`eq_one_of_map_fst_eq_one_of_map_snd_eq_one`);
* reductions to `X_red` (IX.1.7), to `Y_red` (the rational points lie on `Y_red`), and to the
  connected components of `X`, which are open as `X` is locally noetherian (V.9,
  `nonempty_iso_of_forall_componentOpens`).
-/

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.PreGaloisCategory

namespace SGA.SGA1.ExposeX

/-- The morphism `j_y = id_X ×ₖ y : X → X ×ₖ Y` attached to a rational point `y` of `Y`. -/
noncomputable def fibreInclusion {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (y : Spec (.of k) ⟶ Y) (hy : y ≫ sY = 𝟙 _) :
    X ⟶ pullback sX sY :=
  pullback.lift (𝟙 X) (sX ≫ y) (by rw [Category.id_comp, Category.assoc, hy, Category.comp_id])

section Formal

variable {C D : Type*} [Category* C] [Category* D]

/-- Conjugating by an isomorphism of fibre functors commutes with `π₁(H)`. -/
lemma autMap_conjAut (H : C ⥤ D) {F G : D ⥤ FintypeCat.{w}} {F' G' : C ⥤ FintypeCat.{w}}
    (e : H ⋙ F ≅ F') (e' : H ⋙ G ≅ G') (φ : F ≅ G) (σ : Aut F) :
    ExposeV.autMap H e' (φ.conjAut σ) =
      (e.symm ≪≫ Functor.isoWhiskerLeft H φ ≪≫ e').conjAut (ExposeV.autMap H e σ) := by
  apply Iso.ext
  refine NatTrans.ext (funext fun X ↦ ?_)
  simp [ExposeV.autMap_hom_app, Iso.conjAut_hom, Iso.conj_apply]

/-- `π₁(H)` for an isomorphism `H ⋙ F ≅ F'` followed by `F' ≅ F''` is `π₁(H)` followed by the
conjugation. -/
lemma autMap_trans (H : C ⥤ D) {F : D ⥤ FintypeCat.{w}} {F' F'' : C ⥤ FintypeCat.{w}}
    (e : H ⋙ F ≅ F') (φ : F' ≅ F'') (σ : Aut F) :
    ExposeV.autMap H (e ≪≫ φ) σ = φ.conjAut (ExposeV.autMap H e σ) := by
  apply Iso.ext
  refine NatTrans.ext (funext fun X ↦ ?_)
  simp [ExposeV.autMap_hom_app, Iso.conjAut_hom, Iso.conj_apply]

/-- Conjugation by an automorphism in the group `Aut X`. -/
lemma Aut.conjAut_eq {E : Type*} [Category* E] {X : E} (τ σ : Aut X) :
    τ.conjAut σ = τ * σ * τ⁻¹ :=
  Iso.ext ((Iso.conjAut_hom τ σ).trans rfl)

/-- X.1.9, group-theoretic part. Let `jᵢ : G → Gᵢ` (`i = 1, 2`) be homomorphisms with retractions
`pᵢ` and with `qᵢ ∘ jᵢ` trivial, and let `c : G₁ ≃ G₂` be compatible with the `pᵢ` up to the inner
automorphism of `η` and with the `qᵢ` up to an isomorphism. If `(p₂, q₂)` is injective, then
`j₁` and `j₂` agree up to `c` and an inner automorphism of `G₁`. -/
theorem conj_comp_eq_of_injective {G G₁ G₂ H₁ H₂ : Type*} [Group G] [Group G₁] [Group G₂]
    [Group H₁] [Group H₂] (j₁ : G →* G₁) (j₂ : G →* G₂) (p₁ : G₁ →* G) (p₂ : G₂ →* G)
    (q₁ : G₁ →* H₁) (q₂ : G₂ →* H₂) (c : G₁ ≃* G₂) (d : H₁ ≃* H₂) (η : G)
    (hp₁ : ∀ g, p₁ (j₁ g) = g) (hp₂ : ∀ g, p₂ (j₂ g) = g) (hq₁ : ∀ g, q₁ (j₁ g) = 1)
    (hq₂ : ∀ g, q₂ (j₂ g) = 1) (hc : ∀ σ, p₂ (c σ) = η * p₁ σ * η⁻¹)
    (hd : ∀ σ, q₂ (c σ) = d (q₁ σ)) (hinj : ∀ σ, p₂ σ = 1 → q₂ σ = 1 → σ = 1) (g : G) :
    c (j₁ η⁻¹ * j₁ g * (j₁ η⁻¹)⁻¹) = j₂ g := by
  rw [← mul_inv_eq_one]
  refine hinj _ ?_ ?_
  · simp only [map_mul, map_inv, hc, hp₁, hp₂]
    group
  · simp only [map_mul, map_inv, hd, hq₁, hq₂]
    simp

variable {FX : D ⥤ FintypeCat.{w}} {F₁ F₂ : C ⥤ FintypeCat.{w}} (J₁ J₂ : C ⥤ D)
  (e₁ : J₁ ⋙ FX ≅ F₁) (e₂ : J₂ ⋙ FX ≅ F₂)

/-- X.1.9, formal part. If an isomorphism `δ` of fibre functors on `C` intertwines the
homomorphisms `π₁(Jᵢ) : Aut FX → Aut Fᵢ`, then `J₁ W ≅ J₂ W` for every object `W` (the fibres
`FX(Jᵢ W) = Fᵢ(W)` are isomorphic `Aut FX`-sets). -/
theorem nonempty_iso_of_conjAut_autMap [GaloisCategory D] [FiberFunctor FX] (δ : F₁ ≅ F₂)
    (hδ : ∀ g : Aut FX, δ.conjAut (ExposeV.autMap J₁ e₁ g) = ExposeV.autMap J₂ e₂ g) (W : C) :
    Nonempty (J₁.obj W ≅ J₂.obj W) := by
  let ψ : FX.obj (J₁.obj W) ≅ FX.obj (J₂.obj W) := e₁.app W ≪≫ δ.app W ≪≫ e₂.symm.app W
  have hψ (g : Aut FX) : g.hom.app (J₁.obj W) ≫ ψ.hom = ψ.hom ≫ g.hom.app (J₂.obj W) := by
    have h := congrArg (fun σ : Aut F₂ ↦ σ.hom.app W) (hδ g)
    simp only [Iso.conjAut_hom, Iso.conj_apply, ExposeV.autMap_hom_app, NatTrans.comp_app] at h
    simp only [ψ, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
    calc g.hom.app (J₁.obj W) ≫ e₁.hom.app W ≫ δ.hom.app W ≫ e₂.inv.app W
        = e₁.hom.app W ≫ δ.hom.app W ≫ (δ.inv.app W ≫ (e₁.inv.app W ≫ g.hom.app (J₁.obj W) ≫
            e₁.hom.app W) ≫ δ.hom.app W) ≫ e₂.inv.app W := by simp
      _ = e₁.hom.app W ≫ δ.hom.app W ≫ (e₂.inv.app W ≫ g.hom.app (J₂.obj W) ≫ e₂.hom.app W) ≫
            e₂.inv.app W :=
          congrArg (fun t ↦ e₁.hom.app W ≫ δ.hom.app W ≫ t ≫ e₂.inv.app W) h
      _ = e₁.hom.app W ≫ δ.hom.app W ≫ e₂.inv.app W ≫ g.hom.app (J₂.obj W) := by simp
  let ψ' : (functorToAction FX).obj (J₁.obj W) ≅ (functorToAction FX).obj (J₂.obj W) :=
    Action.mkIso ψ fun g ↦ hψ g
  exact ⟨(functorToAction FX).preimageIso ψ'⟩

end Formal

section Core

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))

lemma fibreInclusion_fst (y : Spec (.of k) ⟶ Y) (hy : y ≫ sY = 𝟙 _) :
    fibreInclusion sX sY y hy ≫ pullback.fst sX sY = 𝟙 X :=
  pullback.lift_fst _ _ _

lemma fibreInclusion_snd (y : Spec (.of k) ⟶ Y) (hy : y ≫ sY = 𝟙 _) :
    fibreInclusion sX sY y hy ≫ pullback.snd sX sY = sX ≫ y :=
  pullback.lift_snd _ _ _

/-- The inverse of the conjugation by an isomorphism is the conjugation by the inverse. -/
lemma Iso.symm_conjAut_apply {E : Type*} [Category* E] {A B : E} (φ : A ≅ B) (σ : Aut B) :
    φ.symm.conjAut σ = φ.conjAut.symm σ := by
  apply φ.conjAut.injective
  rw [MulEquiv.apply_symm_apply, ← Iso.trans_conjAut]
  exact Iso.ext (by simp [Iso.conjAut_hom, Iso.conj_apply])

set_option backward.isDefEq.respectTransparency false in
/-- X.1.9 for a connected `X`, given the Künneth injectivity at `j_{y₂}(a)`: if `π₁(X ×ₖ Y) →
π₁(X) × π₁(Y)` is injective at the geometric point `j_{y₂} ∘ a` (X.1.7), then the coverings
`j_{y₁}⁻¹(Z')` and `j_{y₂}⁻¹(Z')` of `X` are isomorphic. -/
theorem nonempty_iso_of_injective_map_prod [IsSepClosed k] [ConnectedSpace X]
    [ConnectedSpace ↥(pullback sX sY)] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ X) (y₁ y₂ : Spec (.of k) ⟶ Y) (h₁ : y₁ ≫ sY = 𝟙 _) (h₂ : y₂ ≫ sY = 𝟙 _)
    (hinj : ∀ σ : ExposeV.etaleFundamentalGroup Ω (a ≫ fibreInclusion sX sY y₂ h₂),
      ExposeV.etaleFundamentalGroup.map Ω (pullback.fst sX sY) _ σ = 1 →
        ExposeV.etaleFundamentalGroup.map Ω (pullback.snd sX sY) _ σ = 1 → σ = 1)
    (Z' : FEt (pullback sX sY)) :
    Nonempty ((FEt.pullback (fibreInclusion sX sY y₁ h₁)).obj Z' ≅
      (FEt.pullback (fibreInclusion sX sY y₂ h₂)).obj Z') := by
  set J₁ := fibreInclusion sX sY y₁ h₁
  set J₂ := fibreInclusion sX sY y₂ h₂
  let pr₁ := pullback.fst sX sY
  let pr₂ := pullback.snd sX sY
  let j₁ := ExposeV.etaleFundamentalGroup.map Ω J₁ a
  let j₂ := ExposeV.etaleFundamentalGroup.map Ω J₂ a
  obtain ⟨φ₁, hφ₁⟩ := ExposeV.etaleFundamentalGroup.exists_map_comp_map_eq_conjAut Ω J₁ pr₁
    (fibreInclusion_fst sX sY y₁ h₁) a
  obtain ⟨φ₂, hφ₂⟩ := ExposeV.etaleFundamentalGroup.exists_map_comp_map_eq_conjAut Ω J₂ pr₁
    (fibreInclusion_fst sX sY y₂ h₂) a
  let p₁ := φ₁.conjAut.symm.toMonoidHom.comp (ExposeV.etaleFundamentalGroup.map Ω pr₁ (a ≫ J₁))
  let p₂ := φ₂.conjAut.symm.toMonoidHom.comp (ExposeV.etaleFundamentalGroup.map Ω pr₁ (a ≫ J₂))
  let q₁ := ExposeV.etaleFundamentalGroup.map Ω pr₂ (a ≫ J₁)
  let q₂ := ExposeV.etaleFundamentalGroup.map Ω pr₂ (a ≫ J₂)
  have hp₁ (g : _) : p₁ (j₁ g) = g := by
    have := congrArg (fun f : _ →* _ ↦ f g) hφ₁
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    simp only [p₁, j₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [this, MulEquiv.symm_apply_apply]
  have hp₂ (g : _) : p₂ (j₂ g) = g := by
    have := congrArg (fun f : _ →* _ ↦ f g) hφ₂
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    simp only [p₂, j₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [this, MulEquiv.symm_apply_apply]
  have hSpec (τ : ExposeV.etaleFundamentalGroup Ω (a ≫ sX)) : τ = 1 :=
    ExposeV.etaleFundamentalGroup.eq_one_of_isSepClosed Ω k _ τ
  have hq₁ (g : _) : q₁ (j₁ g) = 1 := by
    have := ExposeV.etaleFundamentalGroup.map_comp_map_eq_one Ω J₁ pr₂ sX y₁
      (fibreInclusion_snd sX sY y₁ h₁) a hSpec
    exact congrArg (fun f : _ →* _ ↦ f g) this
  have hq₂ (g : _) : q₂ (j₂ g) = 1 := by
    have := ExposeV.etaleFundamentalGroup.map_comp_map_eq_one Ω J₂ pr₂ sX y₂
      (fibreInclusion_snd sX sY y₂ h₂) a hSpec
    exact congrArg (fun f : _ →* _ ↦ f g) this
  -- a path `γ` between the fibre functors at `j_{y₁}(a)` and `j_{y₂}(a)`
  obtain ⟨γ⟩ := ExposeV.nonempty_iso_of_fiberFunctor (ExposeV.FEt.fiber Ω (a ≫ J₁))
    (ExposeV.FEt.fiber Ω (a ≫ J₂))
  let γ₁ := (ExposeV.FEt.pullbackFiberIso Ω pr₁ (a ≫ J₁)).symm ≪≫
    Functor.isoWhiskerLeft (ExposeV.FEt.pullback pr₁) γ ≪≫
      ExposeV.FEt.pullbackFiberIso Ω pr₁ (a ≫ J₂)
  let γ₂ := (ExposeV.FEt.pullbackFiberIso Ω pr₂ (a ≫ J₁)).symm ≪≫
    Functor.isoWhiskerLeft (ExposeV.FEt.pullback pr₂) γ ≪≫
      ExposeV.FEt.pullbackFiberIso Ω pr₂ (a ≫ J₂)
  let η : Aut (ExposeV.FEt.fiber Ω a) := φ₁ ≪≫ γ₁ ≪≫ φ₂.symm
  have hc (σ : _) : p₂ (γ.conjAut σ) = η * p₁ σ * η⁻¹ := by
    have h1 : ExposeV.etaleFundamentalGroup.map Ω pr₁ (a ≫ J₂) (γ.conjAut σ) =
        γ₁.conjAut (ExposeV.etaleFundamentalGroup.map Ω pr₁ (a ≫ J₁) σ) :=
      autMap_conjAut _ (ExposeV.FEt.pullbackFiberIso Ω pr₁ (a ≫ J₁))
        (ExposeV.FEt.pullbackFiberIso Ω pr₁ (a ≫ J₂)) γ σ
    have h2 : ExposeV.etaleFundamentalGroup.map Ω pr₁ (a ≫ J₁) σ = φ₁.conjAut (p₁ σ) := by
      simp only [p₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    simp only [p₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [h1, h2, ← Aut.conjAut_eq]
    change _ = (φ₁ ≪≫ γ₁ ≪≫ φ₂.symm).conjAut _
    simp only [γ₁, Iso.trans_conjAut, Iso.symm_conjAut_apply]
  have hd (σ : _) : q₂ (γ.conjAut σ) = γ₂.conjAut (q₁ σ) :=
    autMap_conjAut _ (ExposeV.FEt.pullbackFiberIso Ω pr₂ (a ≫ J₁))
      (ExposeV.FEt.pullbackFiberIso Ω pr₂ (a ≫ J₂)) γ σ
  have hinj' (σ : _) (h1 : p₂ σ = 1) (h2 : q₂ σ = 1) : σ = 1 := by
    refine hinj σ ?_ h2
    simp only [p₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
    rwa [MulEquiv.symm_apply_eq, map_one] at h1
  have key := conj_comp_eq_of_injective j₁ j₂ p₁ p₂ q₁ q₂ γ.conjAut γ₂.conjAut η hp₁ hp₂ hq₁ hq₂
    hc hd hinj'
  refine nonempty_iso_of_conjAut_autMap (FEt.pullback J₁) (FEt.pullback J₂)
    (ExposeV.FEt.pullbackFiberIso Ω J₁ a) (ExposeV.FEt.pullbackFiberIso Ω J₂ a)
    ((j₁ η⁻¹ : Aut (ExposeV.FEt.fiber Ω (a ≫ J₁))) ≪≫ γ) (fun g ↦ ?_) Z'
  rw [Iso.trans_conjAut, Aut.conjAut_eq]
  exact key g

end Core

section Connected

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k))

omit [IsAlgClosed k] in
/-- A morphism from a nonempty scheme to the spectrum of a field is surjective. -/
lemma surjective_of_nonempty {T : Scheme.{u}} [Nonempty T] (s : T ⟶ Spec (.of k)) :
    Surjective s :=
  ⟨fun _ ↦ ⟨Classical.arbitrary T, Subsingleton.elim _ _⟩⟩

/-- For `Y` proper, connected and reduced over `k`, the first projection `pr₁ : X ×ₖ Y ⟶ X` has
`𝒪_X = pr₁_* 𝒪_{X ×ₖ Y}` (flat base change of `Γ(Y, 𝒪_Y) = k`). -/
theorem isIso_app_fst [IsProper sY] [IsReduced Y] [ConnectedSpace Y] (V : X.Opens) :
    IsIso ((pullback.fst sX sY).app V) := by
  have h₁ := CohomologyAux.isIso_app_pullback_snd sY sX (isIso_app_of_isProper sY) V
  have h₂ : IsIso ((pullbackSymmetry sX sY).hom.app ((pullback.snd sY sX) ⁻¹ᵁ V)) :=
    inferInstance
  rw [← pullbackSymmetry_hom_comp_snd, Scheme.Hom.comp_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂

set_option backward.isDefEq.respectTransparency false in
/-- X.1.7, injectivity, at a geometric point of a fibre of `pr₁ : X ×ₖ Y ⟶ X` (`Y` proper,
connected and reduced): an element of `π₁(X ×ₖ Y)` trivial in `π₁(X)` and in `π₁(Y)` is trivial.
By X.1.4 it comes from the geometric fibre `Y ⊗ₖ K` of `pr₁`, and `π₁(Y ⊗ₖ K) → π₁(Y)` is
bijective by X.1.8. -/
theorem eq_one_of_map_fst_eq_one_of_map_snd_eq_one [IsLocallyNoetherian X] [ConnectedSpace X]
    [IsProper sY] [IsReduced Y] [ConnectedSpace Y] (x₀ : X)
    (a' : Spec (.of (AlgebraicClosure (X.residueField x₀))) ⟶
      pullback (pullback.fst sX sY) (geometricPoint X x₀))
    (σ : ExposeV.etaleFundamentalGroup _ (a' ≫ pullback.fst _ (geometricPoint X x₀)))
    (h₁ : ExposeV.etaleFundamentalGroup.map _ (pullback.fst sX sY) _ σ = 1)
    (h₂ : ExposeV.etaleFundamentalGroup.map _ (pullback.snd sX sY) _ σ = 1) : σ = 1 := by
  let g₀ := geometricPoint X x₀
  let K := AlgebraicClosure (X.residueField x₀)
  let f := pullback.fst sX sY
  have : IsSeparable sY :=
    (isSeparable_iff_of_field sY).mpr (GeometricallyReduced.of_perfectField sY)
  obtain ⟨hex, -⟩ := range_map_eq_ker_map_and_surjective f (isIso_app_fst sX sY) x₀ K a'
  have hσ : σ ∈ (ExposeV.etaleFundamentalGroup.map K f (a' ≫ pullback.fst f g₀)).ker := h₁
  rw [← hex] at hσ
  obtain ⟨τ, rfl⟩ := hσ
  -- the geometric fibre of `pr₁` is `Y ⊗ₖ K`, and its projection to `Y` is the base change
  have hsq : IsPullback (pullback.fst f g₀ ≫ pullback.snd sX sY) (pullback.snd f g₀) sY
      (g₀ ≫ sX) :=
    (IsPullback.of_hasPullback f g₀).paste_horiz (IsPullback.of_hasPullback sX sY).flip
  let _ : Algebra k K := (Spec.preimage (g₀ ≫ sX)).hom.toAlgebra
  have hρ : Spec.map (CommRingCat.ofHom (algebraMap k K)) = g₀ ≫ sX := Spec.map_preimage _
  rw [← hρ] at hsq
  have := baseChangeAlgClosedStatement k K sY
  have : (FEt.pullback (hsq.isoPullback.hom ≫
      pullback.fst sY (Spec.map (CommRingCat.ofHom (algebraMap k K))))).IsEquivalence :=
    ExposeV.FEt.isEquivalence_pullback_comp _ _
  have : (FEt.pullback (pullback.fst f g₀ ≫ pullback.snd sX sY)).IsEquivalence :=
    Functor.isEquivalence_of_iso (MorphismProperty.Over.pullbackCongr
      (IsPullback.isoPullback_hom_fst hsq))
  have : (FEt.pullback (pullback.snd sX sY) ⋙ FEt.pullback (pullback.fst f g₀)).IsEquivalence :=
    Functor.isEquivalence_of_iso (MorphismProperty.Over.pullbackComp _ _)
  have hbij : Function.Bijective
      ((ExposeV.etaleFundamentalGroup.map K (pullback.snd sX sY) (a' ≫ pullback.fst f g₀)).comp
        (ExposeV.etaleFundamentalGroup.map K (pullback.fst f g₀) a')) := by
    rw [ExposeV.etaleFundamentalGroup.map, ExposeV.etaleFundamentalGroup.map,
      ExposeV.autMap_comp]
    exact ExposeV.autMap_bijective _ _
  have : τ = 1 := hbij.1 (by rw [MonoidHom.comp_apply, map_one]; exact h₂)
  rw [this, map_one]

set_option backward.isDefEq.respectTransparency false in
/-- X.1.9 for `Y` proper, connected and reduced and `X` connected. -/
theorem nonempty_iso_of_isProper_right [IsLocallyNoetherian X] [ConnectedSpace X] [IsProper sY]
    [IsReduced Y] [ConnectedSpace Y] (Z' : FEt (pullback sX sY)) (y₁ y₂ : Spec (.of k) ⟶ Y)
    (h₁ : y₁ ≫ sY = 𝟙 _) (h₂ : y₂ ≫ sY = 𝟙 _) :
    Nonempty ((FEt.pullback (fibreInclusion sX sY y₁ h₁)).obj Z' ≅
      (FEt.pullback (fibreInclusion sX sY y₂ h₂)).obj Z') := by
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  have : GeometricallyConnected (pullback.fst sX sY) :=
    geometricallyConnected_of_isIso_app _ (isIso_app_fst sX sY)
  have : Surjective sY := surjective_of_nonempty sY
  have : ConnectedSpace ↥(pullback sX sY) :=
    ExposeIX.connectedSpace_of_universally_isQuotientMap (pullback.fst sX sY)
      (ExposeIX.universally_isQuotientMap_of_universallyClosed _)
  refine nonempty_iso_of_injective_map_prod sX sY _ (geometricPoint X x₀) y₁ y₂ h₁ h₂ ?_ Z'
  obtain ⟨a', ha'⟩ : ∃ a' : Spec (.of (AlgebraicClosure (X.residueField x₀))) ⟶
      pullback (pullback.fst sX sY) (geometricPoint X x₀),
      a' ≫ pullback.fst _ _ = geometricPoint X x₀ ≫ fibreInclusion sX sY y₂ h₂ :=
    ⟨pullback.lift (geometricPoint X x₀ ≫ fibreInclusion sX sY y₂ h₂) (𝟙 _) (by
      rw [Category.assoc, fibreInclusion_fst, Category.comp_id, Category.id_comp]),
      pullback.lift_fst _ _ _⟩
  rw [← ha']
  exact eq_one_of_map_fst_eq_one_of_map_snd_eq_one sX sY x₀ a'

/-- X.1.9 for `X` proper, connected and reduced: at a rational point `x` of `X`, X.1.7
(`bijective_map_prod`) gives the injectivity needed in `nonempty_iso_of_injective_map_prod`. -/
theorem nonempty_iso_of_isProper_left [IsProper sX] [IsReduced X] [ConnectedSpace X]
    [IsLocallyNoetherian Y] [ConnectedSpace Y] (Z' : FEt (pullback sX sY))
    (y₁ y₂ : Spec (.of k) ⟶ Y) (h₁ : y₁ ≫ sY = 𝟙 _) (h₂ : y₂ ≫ sY = 𝟙 _) :
    Nonempty ((FEt.pullback (fibreInclusion sX sY y₁ h₁)).obj Z' ≅
      (FEt.pullback (fibreInclusion sX sY y₂ h₂)).obj Z') := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨x, hx⟩ := exists_comp_eq_id sX
  have : GeometricallyConnected (pullback.snd sX sY) :=
    geometricallyConnected_of_isIso_app _ (isIso_app_snd sX sY)
  have : Surjective sX := surjective_of_nonempty sX
  have : ConnectedSpace ↥(pullback sX sY) :=
    ExposeIX.connectedSpace_of_universally_isQuotientMap (pullback.snd sX sY)
      (ExposeIX.universally_isQuotientMap_of_universallyClosed _)
  refine nonempty_iso_of_injective_map_prod sX sY k x y₁ y₂ h₁ h₂ (fun σ hσ₁ hσ₂ ↦ ?_) Z'
  have hc : (x ≫ fibreInclusion sX sY y₂ h₂) ≫ pullback.snd sX sY ≫ sY = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc (fibreInclusion _ _ _ _), fibreInclusion_snd,
      Category.assoc, h₂, Category.comp_id, hx]
  exact (bijective_map_prod sX sY _ hc).1 (Prod.ext (by simpa using hσ₁) (by simpa using hσ₂))

end Connected

section Components

open TopologicalSpace

/-- In a noetherian space the connected components are open (there are finitely many, and
they are closed). -/
lemma isOpen_connectedComponent_of_noetherianSpace {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] (x : T) : IsOpen (connectedComponent x) := by
  have := ExposeV.finite_connectedComponents_of_noetherianSpace T
  have hcompl : (connectedComponent x)ᶜ =
      ⋃ c ∈ ({ConnectedComponents.mk x}ᶜ : Set (ConnectedComponents T)),
        ConnectedComponents.mk ⁻¹' {c} := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
      exists_prop, exists_eq_right']
    rw [← connectedComponents_preimage_singleton, Set.mem_preimage, Set.mem_singleton_iff]
  rw [← isClosed_compl_iff, hcompl]
  refine (Set.toFinite _).isClosed_biUnion fun c _ ↦ ?_
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponents_preimage_singleton]
  exact isClosed_connectedComponent

/-- A locally noetherian scheme is locally connected. -/
theorem locallyConnectedSpace_of_isLocallyNoetherian (X : Scheme.{u}) [IsLocallyNoetherian X] :
    LocallyConnectedSpace X := by
  apply locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr
  intro x S hS
  obtain ⟨O, hOS, hO, hxO⟩ := mem_nhds_iff.mp hS
  obtain ⟨V, hV, hxV, hVO⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨O, hO⟩) hxO
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : NoetherianSpace (V : Set X) := noetherianSpace_of_isAffineOpen V hV
  let y : V := ⟨x, hxV⟩
  refine ⟨Subtype.val '' connectedComponent y, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact hOS (hVO z.2)
  · exact V.isOpenEmbedding.isOpenMap _ (isOpen_connectedComponent_of_noetherianSpace y)
  · exact ⟨y, mem_connectedComponent, rfl⟩
  · exact isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn

variable (X : Scheme.{u}) [LocallyConnectedSpace X]

/-- The connected component `c` of a locally connected scheme, as an open subscheme. -/
def componentOpens (c : ConnectedComponents X) : X.Opens :=
  ⟨ConnectedComponents.mk ⁻¹' {c}, by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact isOpen_connectedComponent⟩

lemma isClosed_componentOpens (c : ConnectedComponents X) :
    IsClosed (componentOpens X c : Set X) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  change IsClosed (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
  rw [connectedComponents_preimage_singleton]
  exact isClosed_connectedComponent

lemma iSup_componentOpens : iSup (componentOpens X) = ⊤ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, TopologicalSpace.Opens.coe_top,
    Set.mem_univ, iff_true]
  exact ⟨ConnectedComponents.mk x, rfl⟩

lemma pairwise_disjoint_componentOpens :
    Pairwise (Function.onFun Disjoint (componentOpens X)) := by
  intro c d hcd
  rw [Function.onFun, disjoint_iff]
  ext x
  simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, TopologicalSpace.Opens.coe_bot,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hc hd
  exact hcd ((Set.mem_singleton_iff.mp hc).symm.trans (Set.mem_singleton_iff.mp hd))

instance (c : ConnectedComponents X) : ConnectedSpace (componentOpens X c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have h : ((componentOpens X (ConnectedComponents.mk x) : X.Opens) : Set X) =
      connectedComponent x :=
    connectedComponents_preimage_singleton
  have := isConnected_connectedComponent (x := x)
  rw [← h] at this
  exact isConnected_iff_connectedSpace.mp this

instance (c : ConnectedComponents X) : IsClosedImmersion (componentOpens X c).ι :=
  .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact isClosed_componentOpens X c)

variable {X}

/-- V.9: étale coverings of a locally connected scheme which are isomorphic over every connected
component are isomorphic. -/
theorem nonempty_iso_of_forall_componentOpens {A B : FEt X}
    (h : ∀ c, Nonempty ((FEt.pullback (componentOpens X c).ι).obj A ≅
      (FEt.pullback (componentOpens X c).ι).obj B)) :
    Nonempty (A ≅ B) := by
  have := ExposeV.FEt.restrictFamily_full (iSup_componentOpens X)
    (pairwise_disjoint_componentOpens X)
  have := ExposeV.FEt.restrictFamily_faithful (U := componentOpens X) (iSup_componentOpens X)
  let E : (ExposeV.FEt.restrictFamily (componentOpens X)).obj A ≅
      (ExposeV.FEt.restrictFamily (componentOpens X)).obj B :=
    { hom := fun c ↦ (h c).some.hom
      inv := fun c ↦ (h c).some.inv
      hom_inv_id := funext fun c ↦ (h c).some.hom_inv_id
      inv_hom_id := funext fun c ↦ (h c).some.inv_hom_id }
  exact ⟨(ExposeV.FEt.restrictFamily (componentOpens X)).preimageIso E⟩

end Components

section Transport

variable {X X' Z Z'' : Scheme.{u}}

/-- Base change of `J⁻¹(W)` along `φ`, for `φ ≫ J = J' ≫ ψ`. -/
noncomputable def pullbackPullbackIsoOfCommSq (φ : X' ⟶ X) (ψ : Z'' ⟶ Z) (J : X ⟶ Z)
    (J' : X' ⟶ Z'') (w : φ ≫ J = J' ≫ ψ) (W : FEt Z) :
    (FEt.pullback φ).obj ((FEt.pullback J).obj W) ≅
      (FEt.pullback J').obj ((FEt.pullback ψ).obj W) :=
  ((MorphismProperty.Over.pullbackComp φ J).app W).symm ≪≫
    (MorphismProperty.Over.pullbackCongr w).app W ≪≫
      (MorphismProperty.Over.pullbackComp J' ψ).app W

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k))

set_option backward.isDefEq.respectTransparency false in
/-- `j_y` is compatible with base change on `X`. -/
lemma comp_fibreInclusion {X' : Scheme.{u}} (φ : X' ⟶ X) (y : Spec (.of k) ⟶ Y)
    (hy : y ≫ sY = 𝟙 _) :
    φ ≫ fibreInclusion sX sY y hy = fibreInclusion (φ ≫ sX) sY y hy ≫
      pullback.map (φ ≫ sX) sY sX sY φ (𝟙 _) (𝟙 _) (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [fibreInclusion, pullback.map, Category.assoc, limit.lift_π, limit.lift_π_assoc,
      PullbackCone.mk_π_app, Category.comp_id]
    exact (Category.id_comp φ).symm
  · simp only [fibreInclusion, pullback.map, Category.assoc, limit.lift_π, limit.lift_π_assoc,
      PullbackCone.mk_π_app]
    exact (congrArg (φ ≫ sX ≫ ·) (Category.comp_id y)).symm

set_option backward.isDefEq.respectTransparency false in
/-- `j_y` is compatible with base change on `Y`. -/
lemma fibreInclusion_comp {Y' : Scheme.{u}} (ψ : Y' ⟶ Y) (y : Spec (.of k) ⟶ Y')
    (hy : y ≫ ψ ≫ sY = 𝟙 _) :
    fibreInclusion sX sY (y ≫ ψ) (by rw [Category.assoc, hy]) =
      fibreInclusion sX (ψ ≫ sY) y hy ≫
        pullback.map sX (ψ ≫ sY) sX sY (𝟙 _) ψ (𝟙 _) (by simp) (by simp) := by
  apply pullback.hom_ext <;> simp [fibreInclusion, pullback.map]

end Transport

section General

/-- A morphism from a reduced scheme factors through the reduced closed subscheme `Y_red`. -/
lemma exists_lift_nilradical {T Y : Scheme.{u}} [IsReduced T] (f : T ⟶ Y) :
    ∃ g : T ⟶ Y.nilradical.subscheme, g ≫ Y.nilradical.subschemeι = f := by
  have H : Y.nilradical.subschemeι.ker ≤ f.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker,
      Scheme.IdealSheafData.le_ofIdeals_iff]
    intro U x hx
    obtain ⟨n, hn⟩ := hx
    have : IsNilpotent ((f.app U).hom x) := ⟨n, by
      rw [← map_pow, show x ^ n = 0 by simpa using hn, map_zero]⟩
    exact this.eq_zero
  exact ⟨IsClosedImmersion.lift _ f H, IsClosedImmersion.lift_fac _ _ _⟩

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k))

omit [IsAlgClosed k] in
/-- X.1.9 is local on the connected components of `X`. -/
theorem nonempty_iso_of_forall_component [LocallyConnectedSpace X] (Z' : FEt (pullback sX sY))
    (y₁ y₂ : Spec (.of k) ⟶ Y) (h₁ : y₁ ≫ sY = 𝟙 _) (h₂ : y₂ ≫ sY = 𝟙 _)
    (h : ∀ (c : ConnectedComponents X) (W : FEt (pullback ((componentOpens X c).ι ≫ sX) sY)),
      Nonempty ((FEt.pullback (fibreInclusion _ sY y₁ h₁)).obj W ≅
        (FEt.pullback (fibreInclusion _ sY y₂ h₂)).obj W)) :
    Nonempty ((FEt.pullback (fibreInclusion sX sY y₁ h₁)).obj Z' ≅
      (FEt.pullback (fibreInclusion sX sY y₂ h₂)).obj Z') := by
  refine nonempty_iso_of_forall_componentOpens fun c ↦ ?_
  let ι := (componentOpens X c).ι
  let ψ := pullback.map (ι ≫ sX) sY sX sY ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  obtain ⟨e⟩ := h c ((FEt.pullback ψ).obj Z')
  exact ⟨pullbackPullbackIsoOfCommSq ι ψ _ _ (comp_fibreInclusion sX sY ι y₁ h₁) Z' ≪≫ e ≪≫
    (pullbackPullbackIsoOfCommSq ι ψ _ _ (comp_fibreInclusion sX sY ι y₂ h₂) Z').symm⟩

/-- X.1.9 for `X` proper and reduced: reduction to the connected components of `X`. -/
theorem nonempty_iso_of_isProper_left_of_isReduced [IsProper sX] [IsReduced X]
    [IsLocallyNoetherian Y] [ConnectedSpace Y] (Z' : FEt (pullback sX sY))
    (y₁ y₂ : Spec (.of k) ⟶ Y) (h₁ : y₁ ≫ sY = 𝟙 _) (h₂ : y₂ ≫ sY = 𝟙 _) :
    Nonempty ((FEt.pullback (fibreInclusion sX sY y₁ h₁)).obj Z' ≅
      (FEt.pullback (fibreInclusion sX sY y₂ h₂)).obj Z') := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := locallyConnectedSpace_of_isLocallyNoetherian X
  exact nonempty_iso_of_forall_component sX sY Z' y₁ y₂ h₁ h₂ fun c W ↦
    nonempty_iso_of_isProper_left ((componentOpens X c).ι ≫ sX) sY W y₁ y₂ h₁ h₂

/-- X.1.9 for `X` proper: the étale coverings do not change on passing to `X_red` (the base change
along `X_red ⟶ X` is fully faithful, IX.1.7). -/
theorem nonempty_iso_of_isProper_left' [IsProper sX] [IsLocallyNoetherian Y] [ConnectedSpace Y]
    (Z' : FEt (pullback sX sY)) (y₁ y₂ : Spec (.of k) ⟶ Y) (h₁ : y₁ ≫ sY = 𝟙 _)
    (h₂ : y₂ ≫ sY = 𝟙 _) :
    Nonempty ((FEt.pullback (fibreInclusion sX sY y₁ h₁)).obj Z' ≅
      (FEt.pullback (fibreInclusion sX sY y₂ h₂)).obj Z') := by
  let i := X.nilradical.subschemeι
  have := isReduced_nilradical_subscheme X
  have := FEt.isEquivalence_pullback_of_isClosedImmersion i
  let ψ := pullback.map (i ≫ sX) sY sX sY i (𝟙 _) (𝟙 _) (by simp) (by simp)
  obtain ⟨e⟩ := nonempty_iso_of_isProper_left_of_isReduced (i ≫ sX) sY ((FEt.pullback ψ).obj Z')
    y₁ y₂ h₁ h₂
  exact ⟨(FEt.pullback i).preimageIso
    (pullbackPullbackIsoOfCommSq i ψ _ _ (comp_fibreInclusion sX sY i y₁ h₁) Z' ≪≫ e ≪≫
      (pullbackPullbackIsoOfCommSq i ψ _ _ (comp_fibreInclusion sX sY i y₂ h₂) Z').symm)⟩

/-- X.1.9 for `Y` proper: reduction to `Y` reduced (the rational points of `Y` lie on `Y_red`) and
to the connected components of `X`. -/
theorem nonempty_iso_of_isProper_right' [IsLocallyNoetherian X] [IsProper sY] [ConnectedSpace Y]
    (Z' : FEt (pullback sX sY)) (y₁ y₂ : Spec (.of k) ⟶ Y) (h₁ : y₁ ≫ sY = 𝟙 _)
    (h₂ : y₂ ≫ sY = 𝟙 _) :
    Nonempty ((FEt.pullback (fibreInclusion sX sY y₁ h₁)).obj Z' ≅
      (FEt.pullback (fibreInclusion sX sY y₂ h₂)).obj Z') := by
  let j := Y.nilradical.subschemeι
  have := isReduced_nilradical_subscheme Y
  have hj : IsHomeomorph j :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨j.isClosedEmbedding.isEmbedding, j.surjective⟩
  have : ConnectedSpace Y.nilradical.subscheme :=
    (IsHomeomorph.homeomorph _ hj).symm.surjective.connectedSpace
      (IsHomeomorph.homeomorph _ hj).symm.continuous
  obtain ⟨y₁', rfl⟩ := exists_lift_nilradical y₁
  obtain ⟨y₂', rfl⟩ := exists_lift_nilradical y₂
  have h₁' : y₁' ≫ j ≫ sY = 𝟙 _ := by rw [← Category.assoc]; exact h₁
  have h₂' : y₂' ≫ j ≫ sY = 𝟙 _ := by rw [← Category.assoc]; exact h₂
  have := locallyConnectedSpace_of_isLocallyNoetherian X
  let ψ := pullback.map sX (j ≫ sY) sX sY (𝟙 _) j (𝟙 _) (by simp) (by simp)
  obtain ⟨e⟩ := nonempty_iso_of_forall_component sX (j ≫ sY) ((FEt.pullback ψ).obj Z') y₁' y₂'
    h₁' h₂' fun c W ↦
      nonempty_iso_of_isProper_right ((componentOpens X c).ι ≫ sX) (j ≫ sY) W y₁' y₂' h₁' h₂'
  let e₁ : (FEt.pullback (fibreInclusion sX sY (y₁' ≫ j) h₁)).obj Z' ≅
      (FEt.pullback (fibreInclusion sX (j ≫ sY) y₁' h₁')).obj ((FEt.pullback ψ).obj Z') :=
    (MorphismProperty.Over.pullbackCongr (fibreInclusion_comp sX sY j y₁' h₁')).app Z' ≪≫
      (MorphismProperty.Over.pullbackComp _ ψ).app Z'
  let e₂ : (FEt.pullback (fibreInclusion sX sY (y₂' ≫ j) h₂)).obj Z' ≅
      (FEt.pullback (fibreInclusion sX (j ≫ sY) y₂' h₂')).obj ((FEt.pullback ψ).obj Z') :=
    (MorphismProperty.Over.pullbackCongr (fibreInclusion_comp sX sY j y₂' h₂')).app Z' ≪≫
      (MorphismProperty.Over.pullbackComp _ ψ).app Z'
  exact ⟨e₁ ≪≫ e ≪≫ e₂.symm⟩

/-- X.1.9. Let `k` be algebraically closed, `X`, `Y` locally noetherian over `k` with `Y`
connected and `X` or `Y` proper, and `Z'` an étale covering of `X ×ₖ Y`. Then the coverings
`X'_y = j_y⁻¹(Z')` of `X`, for `y` a rational point of `Y`, are all isomorphic: a family of étale
coverings parametrized by a connected scheme is constant when `X` or the parameter space is
proper (proved in `constantFamilyStatement`; see `ArtinSchreier` for the counterexample X.1.10
without properness). -/
def ConstantFamilyStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] ⦃X Y : Scheme.{u}⦄ (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [ConnectedSpace Y],
    (IsProper sX ∨ IsProper sY) → ∀ (Z' : FEt (pullback sX sY))
    (y₁ y₂ : Spec (.of k) ⟶ Y) (h₁ : y₁ ≫ sY = 𝟙 _) (h₂ : y₂ ≫ sY = 𝟙 _),
    Nonempty ((FEt.pullback (fibreInclusion sX sY y₁ h₁)).obj Z' ≅
      (FEt.pullback (fibreInclusion sX sY y₂ h₂)).obj Z')

/-- **X.1.9**: let `k` be algebraically closed, `X`, `Y` locally noetherian over `k` with `Y`
connected and `X` or `Y` proper, and `Z'` an étale covering of `X ×ₖ Y`. Then the coverings
`X'_y = j_y⁻¹(Z')` of `X`, for `y` a rational point of `Y`, are all isomorphic. -/
theorem constantFamilyStatement : ConstantFamilyStatement.{u} := by
  intro k _ _ X Y sX sY _ _ _ hprop Z' y₁ y₂ h₁ h₂
  rcases hprop with hX | hY
  · exact nonempty_iso_of_isProper_left' sX sY Z' y₁ y₂ h₁ h₂
  · exact nonempty_iso_of_isProper_right' sX sY Z' y₁ y₂ h₁ h₂

end General

end SGA.SGA1.ExposeX
