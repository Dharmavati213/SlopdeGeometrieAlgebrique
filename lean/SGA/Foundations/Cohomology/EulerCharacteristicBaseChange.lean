/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.EulerCharacteristicPullback
import SGA.Foundations.Cohomology.FlatBaseChange
import SGA.Foundations.Cohomology.Thickening

/-!
# Affine base change and the Euler characteristic

Consider a cartesian square of schemes with `ι : Z ⟶ X` affine and `π : Y ⟶ X` flat and affine,

```
  Z ×_X Y --p₂--> Y
     |p₁          |π
     v            v
     Z  ---ι--->  X
```

and a quasi-coherent `𝒪_Z`-module `G`. The base change morphism `π^* ι_* G ⟶ p₂_* p₁^* G`
(`Scheme.Modules.baseChangeMap`, the adjoint of `ι_* G → ι_* p₁_* p₁^* G = π_* p₂_* p₁^* G`) is
bijective on sections over `π⁻¹ U` for every affine `U ⊆ X` (EGA I 9.3.2, Stacks Tag 02KG):
there it is `Γ(Y, π⁻¹ U) ⊗_{Γ(X, U)} M → Γ(Z ×_X Y, …) ⊗_{Γ(Z, ι⁻¹ U)} M`,
`M = Γ(G, ι⁻¹ U)`, and the rings form a pushout (`CohomologyAux.isPushout_app_pullback_snd`),
so this is mathlib's `Algebra.IsPushout.cancelBaseChange`. Consequently
(`Scheme.Modules.eulerChar_pullback_pushforward`), over a proper scheme over a field,

`χ(Y, π^* ι_* G) = χ(Z ×_X Y, p₁^* G)`.

* `ModuleCat.exists_extendScalars_restrictScalars_addEquiv`: the algebra, for a pushout of rings;
* `Scheme.Modules.baseChangeMap`, `Scheme.Modules.baseChangeMap_app_pullbackApp`;
* `Scheme.Modules.baseChangeMap_app_bijective`;
* `Scheme.Modules.eulerChar_congr`: `χ` is invariant under isomorphisms;
* `Scheme.Modules.eulerChar_pullback_pushforward`.
-/

universe u

open CategoryTheory Limits

namespace ModuleCat

open ChangeOfRings

/-- **Base change for a pushout of rings**: for a pushout square `R → A → B`, `R → S → B` of
commutative rings and an `A`-module `M`, `c ⊗ m ↦ ψ(c) ⊗ m` is an isomorphism
`S ⊗_R M ≅ B ⊗_A M` (mathlib's `Algebra.IsPushout.cancelBaseChange`). -/
lemma exists_extendScalars_restrictScalars_addEquiv {R S A B : CommRingCat.{u}} {α : R ⟶ S}
    {ι : R ⟶ A} {φ : A ⟶ B} {ψ : S ⟶ B} (h : IsPushout ι α φ ψ) (M : ModuleCat.{u} A) :
    ∃ Φ : (extendScalars α.hom).obj ((restrictScalars ι.hom).obj M) ≃+
        (extendScalars φ.hom).obj M,
      (∀ (c : S) (m : M), Φ (c ⊗ₜ[R, α.hom] m) = ψ c ⊗ₜ[A, φ.hom] m) ∧
      ∀ (c : S) y, Φ (c • y) = ψ c • Φ y := by
  let : Algebra R S := α.hom.toAlgebra
  let : Algebra R A := ι.hom.toAlgebra
  let : Algebra A B := φ.hom.toAlgebra
  let : Algebra S B := ψ.hom.toAlgebra
  let : Algebra R B := (ι ≫ φ).hom.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change (ι ≫ φ).hom r = (α ≫ ψ).hom r
    rw [h.w]
  let : Module R M := Module.compHom M ι.hom
  have : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Algebra.IsPushout R A S B :=
    CommRingCat.isPushout_iff_isPushout.mp h
  have : Algebra.IsPushout R S A B := Algebra.IsPushout.symm ‹_›
  let e := Algebra.IsPushout.cancelBaseChange R S A B M
  refine ⟨e.symm.toAddEquiv, fun c m ↦ Algebra.IsPushout.cancelBaseChange_symm_tmul R S A B M c m,
    fun c y ↦ ?_⟩
  exact (e.symm.map_smul c y).trans (algebraMap_smul B c (e.symm y)).symm

end ModuleCat

namespace AlgebraicGeometry.Scheme.Modules

open ModuleCat ChangeOfRings

variable {X Y Z : Scheme.{u}} (ι : Z ⟶ X) (π : Y ⟶ X)

/-- `ι_* p₁_* ≅ π_* p₂_*` for the cartesian square `p₁ ≫ ι = p₂ ≫ π`. -/
noncomputable def pushforwardSquareIso :
    pushforward (pullback.fst ι π) ⋙ pushforward ι ≅
      pushforward (pullback.snd ι π) ⋙ pushforward π :=
  pushforwardComp _ _ ≪≫ pushforwardCongr pullback.condition ≪≫ (pushforwardComp _ _).symm

/-- The **base change morphism** `π^* ι_* G ⟶ p₂_* p₁^* G` for the cartesian square
`Z ×_X Y` (EGA I 9.3.2; Stacks Tag 02KG): the adjoint of
`ι_* G → ι_* p₁_* p₁^* G ≅ π_* p₂_* p₁^* G`. -/
noncomputable def baseChangeMap (G : Z.Modules) :
    (pullback π).obj ((pushforward ι).obj G) ⟶
      (pushforward (pullback.snd ι π)).obj ((pullback (pullback.fst ι π)).obj G) :=
  ((pullbackPushforwardAdjunction π).homEquiv _ _).symm
    ((pushforward ι).map ((pullbackPushforwardAdjunction (pullback.fst ι π)).unit.app G) ≫
      (pushforwardSquareIso ι π).hom.app _)

lemma preimage_snd_preimage_eq (U : X.Opens) :
    pullback.snd ι π ⁻¹ᵁ (π ⁻¹ᵁ U) = pullback.fst ι π ⁻¹ᵁ (ι ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← pullback.condition, Scheme.Hom.comp_preimage]

/-- The base change morphism on inverse images of sections. -/
lemma baseChangeMap_app_pullbackApp (G : Z.Modules) (U : X.Opens)
    (s : Γ((pushforward ι).obj G, U)) :
    (baseChangeMap ι π G).app (π ⁻¹ᵁ U) (pullbackApp π ((pushforward ι).obj G) U s) =
      ((pullback (pullback.fst ι π)).obj G).presheaf.map
        (eqToHom (preimage_snd_preimage_eq ι π U)).op
        (pullbackApp (pullback.fst ι π) G (ι ⁻¹ᵁ U) s) := by
  have h := ((pullbackPushforwardAdjunction π).homEquiv _ _).apply_symm_apply
    ((pushforward ι).map ((pullbackPushforwardAdjunction (pullback.fst ι π)).unit.app G) ≫
      (pushforwardSquareIso ι π).hom.app _)
  rw [Adjunction.homEquiv_unit] at h
  have h' := congrArg (fun φ ↦ (Hom.app φ U) s) h
  simp only [Hom.comp_app, pushforward_map_app, pushforwardSquareIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app] at h'
  exact h'

/-- **Affine base change on sections** (EGA I 9.3.2; Stacks Tag 02KG): for `ι` affine, `π` flat
and affine, `G` quasi-coherent and `U ⊆ X` affine, the base change morphism is bijective on
sections over `π⁻¹ U`. -/
theorem baseChangeMap_app_bijective [Flat π] [IsAffineHom π] [IsAffineHom ι] (G : Z.Modules)
    [G.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective ((baseChangeMap ι π G).app (π ⁻¹ᵁ U)) := by
  have hιU : IsAffineOpen (ι ⁻¹ᵁ U) := hU.preimage ι
  have hπU : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  have hB : IsAffineOpen (pullback.fst ι π ⁻¹ᵁ (ι ⁻¹ᵁ U)) := hιU.preimage _
  have heq := preimage_snd_preimage_eq ι π U
  have : ((pushforward ι).obj G).IsQuasicoherent := CohomologyAux.isQuasicoherent_pushforward ι G
  -- The square of rings is a pushout.
  have hpo : IsPushout (ι.app U) (π.appLE U (π ⁻¹ᵁ U) le_rfl)
      ((pullback.fst ι π).appLE (ι ⁻¹ᵁ U) (pullback.fst ι π ⁻¹ᵁ (ι ⁻¹ᵁ U)) le_rfl)
      ((pullback.snd ι π).appLE (π ⁻¹ᵁ U) (pullback.fst ι π ⁻¹ᵁ (ι ⁻¹ᵁ U)) heq.ge) := by
    refine (CohomologyAux.isPushout_app_pullback_snd ι π hU hπU le_rfl).of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      ((Limits.pullback ι π).presheaf.mapIso (eqToIso heq.symm).op) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [Scheme.Hom.app_eq_appLE]
  obtain ⟨Φ, hΦ, hΦs⟩ := exists_extendScalars_restrictScalars_addEquiv hpo
    (ModuleCat.of Γ(Z, ι ⁻¹ᵁ U) Γ(G, ι ⁻¹ᵁ U))
  let e₁ := pullbackSectionsEquiv π ((pushforward ι).obj G) hU hπU
  let e₂ := pullbackSectionsEquiv (pullback.fst ι π) G hιU hB
  let N := (pullback (pullback.fst ι π)).obj G
  let ρ : Γ((pushforward (pullback.snd ι π)).obj N, π ⁻¹ᵁ U) ≃+
      Γ(N, pullback.fst ι π ⁻¹ᵁ (ι ⁻¹ᵁ U)) :=
    ((N.presheaf.mapIso (eqToIso heq.symm).op).addCommGroupIsoToAddEquiv)
  have hρ : ∀ x, ρ (N.presheaf.map (eqToHom heq).op x) = x := fun x ↦ by
    change N.presheaf.map (eqToHom heq.symm).op (N.presheaf.map (eqToHom heq).op x) = x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans,
      eqToHom_refl, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  let ψ := (pullback.snd ι π).appLE (π ⁻¹ᵁ U) (pullback.fst ι π ⁻¹ᵁ (ι ⁻¹ᵁ U)) heq.ge
  have hρs : ∀ (c : Γ(Y, π ⁻¹ᵁ U)) (x : Γ((pushforward (pullback.snd ι π)).obj N, π ⁻¹ᵁ U)),
      ρ (c • x) = ψ c • ρ x := fun c x ↦ by
    change N.presheaf.map (eqToHom heq.symm).op ((pullback.snd ι π).app (π ⁻¹ᵁ U) c •
      (show Γ(N, pullback.snd ι π ⁻¹ᵁ (π ⁻¹ᵁ U)) from x)) = _
    rw [Scheme.Modules.map_smul]
    congr 1
  -- Identify `Γ(ι_* G, U)` with the restriction of scalars of `Γ(G, ι⁻¹ U)`.
  let iM : ModuleCat.of Γ(X, U) Γ((pushforward ι).obj G, U) ≅
      (restrictScalars (ι.app U).hom).obj (ModuleCat.of Γ(Z, ι ⁻¹ᵁ U) Γ(G, ι ⁻¹ᵁ U)) :=
    Iso.refl _
  let Φ' :=
    ((extendScalars (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom).mapIso iM).toLinearEquiv.toAddEquiv.trans Φ
  -- The composite is `Φ'`.
  let _ : Module Γ(Y, π ⁻¹ᵁ U)
      ((extendScalars ((pullback.fst ι π).appLE (ι ⁻¹ᵁ U) _ le_rfl).hom).obj
        (ModuleCat.of Γ(Z, ι ⁻¹ᵁ U) Γ(G, ι ⁻¹ᵁ U))) := Module.compHom _ ψ.hom
  have key := AlgebraicGeometry.extendScalars_addHom_ext
    (α := π.appLE U (π ⁻¹ᵁ U) le_rfl) (M := ModuleCat.of Γ(X, U) Γ((pushforward ι).obj G, U))
    (AddMonoidHom.mk' (fun y ↦ e₂ (ρ ((baseChangeMap ι π G).app (π ⁻¹ᵁ U) (e₁.symm y))))
      (fun a b ↦ by rw [map_add, map_add, map_add, map_add]))
    Φ'.toAddMonoidHom
    (fun c y ↦ by
      simp only [AddMonoidHom.mk'_apply]
      have h1 : e₁.symm (c • y) = c • e₁.symm y := by
        apply e₁.injective
        rw [pullbackSectionsEquiv_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      rw [h1, Hom.app_smul, hρs, pullbackSectionsEquiv_smul]
      rfl)
    (fun c y ↦ by
      change Φ (((extendScalars (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom).map iM.hom) (c • y)) =
        ψ c • Φ (((extendScalars (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom).map iM.hom) y)
      rw [LinearMap.map_smul_of_tower, hΦs])
    (fun m ↦ by
      have e1 : e₁.symm (oneTmul (ModuleCat.of Γ(X, U) Γ((pushforward ι).obj G, U))
          (π.appLE U (π ⁻¹ᵁ U) le_rfl) m) = pullbackApp π ((pushforward ι).obj G) U m :=
        (AddEquiv.symm_apply_eq _).mpr
          (pullbackSectionsEquiv_pullbackApp π ((pushforward ι).obj G) hU hπU m).symm
      simp only [AddMonoidHom.mk'_apply, AddEquiv.coe_toAddMonoidHom]
      rw [e1, baseChangeMap_app_pullbackApp, hρ]
      refine (pullbackSectionsEquiv_pullbackApp (pullback.fst ι π) G hιU hB m).trans ?_
      rw [oneTmul_apply]
      change _ = Φ (((extendScalars (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom).map iM.hom)
        ((1 : Γ(Y, π ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U), (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom] m))
      rw [ExtendScalars.map_tmul]
      refine Eq.trans ?_ (hΦ 1 (iM.hom m)).symm
      congr 1
      exact (map_one _).symm)
  have hcomp : ∀ x, (baseChangeMap ι π G).app (π ⁻¹ᵁ U) x = ρ.symm (e₂.symm (Φ' (e₁ x))) := by
    intro x
    have := congrArg (fun F ↦ F (e₁ x)) key
    simp only [AddMonoidHom.mk'_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.symm_apply_apply] at this
    rw [← this, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  have hb := ρ.symm.bijective.comp (e₂.symm.bijective.comp (Φ'.bijective.comp e₁.bijective))
  convert hb using 1
  funext x
  exact hcomp x

/-- The direct image along `π` of the base change morphism is an isomorphism. -/
theorem isIso_pushforward_map_baseChangeMap [Flat π] [IsAffineHom π] [IsAffineHom ι]
    (G : Z.Modules) [G.IsQuasicoherent] :
    IsIso ((pushforward π).map (baseChangeMap ι π G)) := by
  have := CohomologyAux.isAffineHom_of_isPullback (IsPullback.of_hasPullback ι π).flip
  have : ((pushforward (pullback.snd ι π)).obj
      ((pullback (pullback.fst ι π)).obj G)).IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_pushforward _ _
  have : ((pushforward π).obj ((pushforward (pullback.snd ι π)).obj
      ((pullback (pullback.fst ι π)).obj G))).IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_pushforward _ _
  exact CohomologyAux.isIso_of_bijective_app_affine _ fun U hU ↦
    baseChangeMap_app_bijective ι π G hU

section EulerCharacteristic

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

lemma H'_map_id_apply (M : X.Modules) {n : ℕ} {U : X.Opens} (x : M.H' n U) :
    H'.map (𝟙 M) n U x = x := by
  rw [H'.map_apply, show Hom.toAbSheaf (𝟙 M) = 𝟙 _ from (toAbSheafFunctor X).map_id M]
  exact Sheaf.H'.map_id_apply (F := M.toAbSheaf) x

/-- `hᵖ` is invariant under isomorphisms. -/
lemma finrankH_congr {M N : X.Modules} (e : M ≅ N) (p : ℕ) : finrankH f M p = finrankH f N p := by
  let _ := M.moduleOver f p ⊤
  let _ := N.moduleOver f p ⊤
  let E : M.H p ≃ₗ[k] N.H p :=
    { toFun := H'.map e.hom p ⊤
      invFun := H'.map e.inv p ⊤
      map_add' := map_add _
      map_smul' := fun r x ↦ (H'.map e.hom p ⊤).map_smul (f.specStructureRingHom r) x
      left_inv := fun x ↦ by
        change H'.map e.inv p ⊤ (H'.map e.hom p ⊤ x) = x
        rw [← H'.map_comp_apply, e.hom_inv_id, H'_map_id_apply]
      right_inv := fun x ↦ by
        change H'.map e.hom p ⊤ (H'.map e.inv p ⊤ x) = x
        rw [← H'.map_comp_apply, e.inv_hom_id, H'_map_id_apply] }
  exact E.finrank_eq

/-- `χ` is invariant under isomorphisms. -/
lemma eulerChar_congr {M N : X.Modules} (e : M ≅ N) : eulerChar f M = eulerChar f N := by
  simp only [eulerChar_def, finrankH_congr f e]

/-- **Affine base change for `χ`**: for `X` proper over a field, `ι : Z ⟶ X` affine, `π : Y ⟶ X`
finite and flat, and `G` quasi-coherent on `Z`,
`χ(Y, π^* ι_* G) = χ(Z ×_X Y, p₁^* G)`. -/
theorem eulerChar_pullback_pushforward [IsProper f] [Flat π] [IsFinite π] [IsAffineHom ι]
    (G : Z.Modules) [G.IsQuasicoherent] :
    eulerChar (π ≫ f) ((pullback π).obj ((pushforward ι).obj G)) =
      eulerChar (pullback.snd ι π ≫ π ≫ f) ((pullback (pullback.fst ι π)).obj G) := by
  have : ((pushforward ι).obj G).IsQuasicoherent := CohomologyAux.isQuasicoherent_pushforward ι G
  have := CohomologyAux.isAffineHom_of_isPullback (IsPullback.of_hasPullback ι π).flip
  have := isIso_pushforward_map_baseChangeMap ι π G
  have : ((pushforward (pullback.snd ι π)).obj
      ((pullback (pullback.fst ι π)).obj G)).IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_pushforward _ _
  rw [← eulerChar_pushforward f π,
    eulerChar_congr f (asIso ((pushforward π).map (baseChangeMap ι π G))),
    eulerChar_pushforward f π, eulerChar_pushforward (π ≫ f) (pullback.snd ι π)]

end EulerCharacteristic

end AlgebraicGeometry.Scheme.Modules
