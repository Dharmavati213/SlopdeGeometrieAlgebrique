/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.EulerCharacteristicBasic
import SGA.Foundations.Cohomology.BaseChangeSections
import SGA.Foundations.QuasiCoherent.Pullback

/-!
# Inverse images along flat affine morphisms are exact

Let `π : Y ⟶ X` be flat and affine. The inverse image functor `π^*` is exact on quasi-coherent
modules (EGA IV 2.1.1, Stacks Tag 02N4 for the flat case): it is a left adjoint, hence right
exact, and it preserves monomorphisms of quasi-coherent modules, since over an affine `U`,
`Γ(π^* M, π⁻¹ U) = Γ(Y, π⁻¹ U) ⊗_{Γ(X, U)} Γ(M, U)` (`Scheme.Modules.pullbackSectionsEquiv`) and
`Γ(Y, π⁻¹ U)` is flat over `Γ(X, U)`.

* `Scheme.Modules.pullbackSectionsEquiv_map`: naturality of `pullbackSectionsEquiv`;
* `Scheme.Modules.mono_pullback_map_of_flat`: `π^*` preserves monomorphisms of quasi-coherent
  modules;
* `Scheme.Modules.shortExact_map_pullback_of_flat`: `π^*` preserves short exact sequences of
  quasi-coherent modules;
* `Scheme.Modules.eulerChar_pullback_of_shortExact`: if moreover `Y` is proper over a field, then
  `M ↦ χ(Y, π^* M)` is additive on short exact sequences of coherent modules.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

open ModuleCat

section Naturality

variable {T X : Scheme.{u}} (g : T ⟶ X) {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
  (φ : M ⟶ N) {U : X.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen (g ⁻¹ᵁ U))

/-- `Γ(X, U)`-linear map `Γ(M, U) → Γ(N, U)` of a morphism of modules, as a morphism in
`ModuleCat Γ(X, U)`. -/
noncomputable abbrev appModuleCatHom :
    ModuleCat.of Γ(X, U) Γ(M, U) ⟶ ModuleCat.of Γ(X, U) Γ(N, U) :=
  ModuleCat.ofHom
    { toFun := φ.app U
      map_add' := map_add _
      map_smul' := fun r s ↦ Hom.app_smul φ r s }

/-- **Naturality of `pullbackSectionsEquiv`**: under `Γ(g^* M, g⁻¹ U) ≅ Γ(T, g⁻¹ U) ⊗ Γ(M, U)`,
the map induced by `φ : M ⟶ N` is `id ⊗ φ`. -/
lemma pullbackSectionsEquiv_map (z : Γ((pullback g).obj M, g ⁻¹ᵁ U)) :
    pullbackSectionsEquiv g N hU hW (((pullback g).map φ).app (g ⁻¹ᵁ U) z) =
      (extendScalars (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom).map (appModuleCatHom φ)
        (pullbackSectionsEquiv g M hU hW z) := by
  have hsymm : ∀ (c : Γ(T, g ⁻¹ᵁ U)) y, (pullbackSectionsEquiv g M hU hW).symm (c • y) =
      c • (pullbackSectionsEquiv g M hU hW).symm y := fun c y ↦ by
    apply (pullbackSectionsEquiv g M hU hW).injective
    rw [pullbackSectionsEquiv_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have key := extendScalars_addHom_ext (α := g.appLE U (g ⁻¹ᵁ U) le_rfl)
    (M := ModuleCat.of Γ(X, U) Γ(M, U))
    (((pullbackSectionsEquiv g N hU hW).toAddMonoidHom.comp
      (((pullback g).map φ).app (g ⁻¹ᵁ U)).hom).comp
        (pullbackSectionsEquiv g M hU hW).symm.toAddMonoidHom)
    ((extendScalars (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom).map (appModuleCatHom φ)).hom.toAddMonoidHom
    (fun c y ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
      rw [hsymm, Hom.app_smul, pullbackSectionsEquiv_smul])
    (fun c y ↦ ((extendScalars _).map (appModuleCatHom φ)).hom.map_smul c y)
    (fun m ↦ by
      have e1 : (pullbackSectionsEquiv g M hU hW).symm
          (oneTmul (ModuleCat.of Γ(X, U) Γ(M, U)) (g.appLE U (g ⁻¹ᵁ U) le_rfl) m) =
            pullbackApp g M U m :=
        (AddEquiv.symm_apply_eq _).mpr (pullbackSectionsEquiv_pullbackApp g M hU hW m).symm
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
        LinearMap.toAddMonoidHom_coe]
      rw [e1, ← pullbackApp_naturality, pullbackSectionsEquiv_pullbackApp]
      rfl)
  have := congrArg (fun F ↦ F (pullbackSectionsEquiv g M hU hW z)) key
  simpa only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    LinearMap.toAddMonoidHom_coe, AddEquiv.symm_apply_apply] using this

end Naturality

section Flat

variable {Y X : Scheme.{u}} (π : Y ⟶ X)

/-- Over an affine open `U` with affine inverse image, the inverse image along a flat morphism of
an injective map of sections of quasi-coherent modules is injective. -/
lemma pullback_map_app_injective_of_flat [Flat π] {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (φ : M ⟶ N) {U : X.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen (π ⁻¹ᵁ U)) (hφ : Function.Injective (φ.app U)) :
    Function.Injective (((pullback π).map φ).app (π ⁻¹ᵁ U)) := by
  have hflat : (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.Flat := π.flat_appLE hU hW le_rfl
  let α := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom
  have key : Function.Injective ((extendScalars α).map (appModuleCatHom (U := U) φ)) := by
    let _ : Algebra Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := α.toAlgebra
    have : Module.Flat Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := hflat
    exact Module.Flat.lTensor_preserves_injective_linearMap
      (M := Γ(Y, π ⁻¹ᵁ U)) (appModuleCatHom (U := U) φ).hom hφ
  intro x y hxy
  apply (pullbackSectionsEquiv π M hU hW).injective
  apply key
  rw [← pullbackSectionsEquiv_map, ← pullbackSectionsEquiv_map, hxy]

/-- **Inverse images along flat affine morphisms preserve monomorphisms of quasi-coherent
modules** (EGA IV 2.1.1). -/
theorem mono_pullback_map_of_flat [Flat π] [IsAffineHom π] {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (φ : M ⟶ N) [Mono φ] : Mono ((pullback π).map φ) := by
  have : (kernel ((pullback π).map φ)).IsQuasicoherent := CohomologyAux.isQuasicoherent_kernel _
  have hzero : ∀ (V : Y.Opens) (s : Γ(kernel ((pullback π).map φ), V)), s = 0 := by
    refine CohomologyAux.eq_zero_of_affine_cover _ (fun U : X.affineOpens ↦ π ⁻¹ᵁ U.1)
      (fun U ↦ U.2.preimage π) ?_ fun U s ↦ ?_
    · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
    · apply CohomologyAux.app_injective_of_mono (kernel.ι ((pullback π).map φ))
      apply pullback_map_app_injective_of_flat π φ U.2 (U.2.preimage π)
        (CohomologyAux.app_injective_of_mono φ U.1)
      rw [map_zero, map_zero, ← Hom.comp_app_apply, kernel.condition]
      rfl
  have hι : kernel.ι ((pullback π).map φ) = 0 :=
    Scheme.Modules.hom_ext _ _ fun V ↦ by
      ext s
      rw [hzero V s, map_zero]
      rfl
  exact Abelian.mono_of_kernel_ι_eq_zero _ hι

/-- **Inverse images along flat affine morphisms are exact on quasi-coherent modules**
(EGA IV 2.1.1). -/
theorem shortExact_map_pullback_of_flat [Flat π] [IsAffineHom π] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    (S.map (pullback π)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have : Mono (S.map (pullback π)).f := mono_pullback_map_of_flat π S.f
  have : Epi (S.map (pullback π)).g := inferInstanceAs (Epi ((pullback π).map S.g))
  exact ⟨hS.exact.map_of_epi_of_preservesCokernel (pullback π) hS.epi_g inferInstance⟩

end Flat

section EulerCharacteristic

variable {k : Type u} [Field k] {Y X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (π : Y ⟶ X)

/-- The inverse image of a coherent module is coherent. -/
lemma isCoherent_pullback (M : X.Modules) [M.IsCoherent] : ((pullback π).obj M).IsCoherent where
  isQuasicoherent := by
    have : M.IsQuasicoherent := IsCoherent.isQuasicoherent
    infer_instance
  isFiniteType := by
    have : M.IsFiniteType := IsCoherent.isFiniteType
    infer_instance

/-- **Additivity of `χ(Y, π^* -)`**: for `π : Y ⟶ X` flat and affine with `Y` proper over a field,
`M ↦ χ(Y, π^* M)` is additive on short exact sequences of coherent `𝒪_X`-modules. -/
theorem eulerChar_pullback_of_shortExact [Flat π] [IsAffineHom π] [IsProper (π ≫ f)]
    {S : ShortComplex X.Modules} (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₂.IsCoherent]
    [S.X₃.IsCoherent] :
    eulerChar (π ≫ f) ((pullback π).obj S.X₂) =
      eulerChar (π ≫ f) ((pullback π).obj S.X₁) + eulerChar (π ≫ f) ((pullback π).obj S.X₃) := by
  have : S.X₁.IsQuasicoherent := IsCoherent.isQuasicoherent
  have : S.X₂.IsQuasicoherent := IsCoherent.isQuasicoherent
  have hS' := shortExact_map_pullback_of_flat π hS
  have h₁ : ((pullback π).obj S.X₁).IsCoherent := isCoherent_pullback π S.X₁
  have h₂ : ((pullback π).obj S.X₂).IsCoherent := isCoherent_pullback π S.X₂
  have h₃ : ((pullback π).obj S.X₃).IsCoherent := isCoherent_pullback π S.X₃
  exact @eulerChar_of_shortExact k _ Y (π ≫ f) _ (S.map (pullback π)) hS' h₁ h₂ h₃

end EulerCharacteristic

end AlgebraicGeometry.Scheme.Modules
