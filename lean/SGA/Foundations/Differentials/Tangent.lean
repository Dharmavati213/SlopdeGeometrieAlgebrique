/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Differentials.SheafHom
import SGA.Foundations.Differentials.Restrict

/-!
# The tangent sheaf

For a morphism of schemes `f : X ⟶ Y` and an `𝒪_X`-module `J`, `Hom_{𝒪_X}(Ω_{X/Y}, J)` is the
set of `f⁻¹ 𝒪_Y`-derivations of `𝒪_X` into `J` (`Scheme.Hom.relativeDifferentialsHomEquiv`, the
form used in SGA 1 III.5.1). The tangent sheaf is `𝒯_{X/Y} = ℋom(Ω_{X/Y}, 𝒪_X)`
(`Scheme.Hom.tangentSheaf`; EGA IV 16.5.7); its sections over an open `U` are the
`f⁻¹ 𝒪_Y`-derivations of `𝒪_U` (`Scheme.Hom.tangentSheafSectionsEquiv`).

More generally the sections of `ℋom(Ω_{X/Y}, J)` over `U` are the derivations of `𝒪_U` into
`J|_U` (`Scheme.Hom.sheafHomRelativeDifferentialsSectionsEquiv`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules} (U : X.Opens)

lemma ι_image_le (W : U.toScheme.Opens) : U.ι ''ᵁ W ≤ U :=
  (U.ι.image_le_opensRange W).trans (Scheme.Opens.opensRange_ι U).le

lemma le_ι_image_preimage {V : X.Opens} (hV : V ≤ U) : V ≤ U.ι ''ᵁ U.ι ⁻¹ᵁ V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact le_inf hV le_rfl

/-- The morphism `M.restrict U.ι ⟶ N.restrict U.ι` defined by `φ : HomOn M N U`. -/
def HomOn.toRestrict (φ : HomOn M N U) : M.restrict U.ι ⟶ N.restrict U.ι where
  val := PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom (φ.app (U.ι ''ᵁ W.unop) (ι_image_le U W.unop)).toAddMonoidHom
      naturality W W' i := by
        ext m
        exact φ.naturality (U.ι.image_mono i.unop.le) _ m }
    fun W r m ↦ (φ.app (U.ι ''ᵁ W.unop) (ι_image_le U W.unop)).map_smul _ m

@[simp]
lemma HomOn.toRestrict_app (φ : HomOn M N U) (W : U.toScheme.Opens) (m : Γ(M, U.ι ''ᵁ W)) :
    (φ.toRestrict U).app W m = φ.app (U.ι ''ᵁ W) (ι_image_le U W) m :=
  rfl

/-- The map `Γ(M, V) → Γ(N, V)`, for `V ⊆ U`, induced by `α : M.restrict U.ι ⟶ N.restrict U.ι`. -/
def homOnOfRestrictApp (α : M.restrict U.ι ⟶ N.restrict U.ι) {V : X.Opens} (hV : V ≤ U)
    (m : Γ(M, V)) : Γ(N, V) :=
  N.presheaf.map (homOfLE (le_ι_image_preimage U hV)).op
    (α.app (U.ι ⁻¹ᵁ V) (M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op m))

lemma homOnOfRestrictApp_add (α : M.restrict U.ι ⟶ N.restrict U.ι) {V : X.Opens} (hV : V ≤ U)
    (m m' : Γ(M, V)) :
    homOnOfRestrictApp U α hV (m + m') =
      homOnOfRestrictApp U α hV m + homOnOfRestrictApp U α hV m' := by
  unfold homOnOfRestrictApp
  rw [map_add]
  exact (congrArg _ (map_add (α.app (U.ι ⁻¹ᵁ V)).hom _ _)).trans (map_add _ _ _)

lemma homOnOfRestrictApp_smul (α : M.restrict U.ι ⟶ N.restrict U.ι) {V : X.Opens} (hV : V ≤ U)
    (r : Γ(X, V)) (m : Γ(M, V)) :
    homOnOfRestrictApp U α hV (r • m) = r • homOnOfRestrictApp U α hV m := by
  have e : X.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op r =
      (U.ι.appIso (U.ι ⁻¹ᵁ V)).inv (U.ι.app V r) := by
    rw [← CommRingCat.comp_apply, U.ι.app_appIso_inv]
    rfl
  have h₁ : M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op (r • m) =
      (show Γ(M.restrict U.ι, U.ι ⁻¹ᵁ V) from U.ι.app V r • (show Γ(M.restrict U.ι, U.ι ⁻¹ᵁ V) from
        M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op m)) := by
    rw [map_smul, e]
    rfl
  have h₂ := Hom.app_smul α (U := U.ι ⁻¹ᵁ V) (U.ι.app V r)
    (M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op m)
  unfold homOnOfRestrictApp
  rw [h₁, h₂]
  change N.presheaf.map (homOfLE (le_ι_image_preimage U hV)).op
    ((U.ι.appIso (U.ι ⁻¹ᵁ V)).inv (U.ι.app V r) • (show Γ(N, U.ι ''ᵁ U.ι ⁻¹ᵁ V) from
      α.app (U.ι ⁻¹ᵁ V) (M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op m))) = _
  rw [map_smul, ← e, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE (le_ι_image_preimage U hV) ≫ homOfLE _) (𝟙 V), op_id,
    CategoryTheory.Functor.map_id, CommRingCat.id_apply]

lemma homOnOfRestrictApp_naturality (α : M.restrict U.ι ⟶ N.restrict U.ι) {V W : X.Opens}
    (hWV : W ≤ V) (hV : V ≤ U) (m : Γ(M, V)) :
    homOnOfRestrictApp U α (hWV.trans hV) (M.presheaf.map (homOfLE hWV).op m) =
      N.presheaf.map (homOfLE hWV).op (homOnOfRestrictApp U α hV m) := by
  unfold homOnOfRestrictApp
  rw [presheaf_map_map M (homOfLE (U.ι.image_preimage_le W)) (homOfLE hWV)
    (homOfLE (U.ι.image_mono (U.ι.preimage_mono hWV))) (homOfLE (U.ι.image_preimage_le V))]
  have h := congr($(α.mapPresheaf.naturality (homOfLE (U.ι.preimage_mono hWV)).op)
    (M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op m))
  change α.app (U.ι ⁻¹ᵁ W) (M.presheaf.map (homOfLE (U.ι.image_mono (U.ι.preimage_mono hWV))).op
      (M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op m)) =
    N.presheaf.map (homOfLE (U.ι.image_mono (U.ι.preimage_mono hWV))).op
      (α.app (U.ι ⁻¹ᵁ V) (M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op m)) at h
  rw [h]
  exact presheaf_map_map N _ _ (homOfLE hWV) (homOfLE (le_ι_image_preimage U hV)) _

lemma homOnOfRestrictApp_toRestrict (φ : HomOn M N U) {V : X.Opens} (hV : V ≤ U)
    (m : Γ(M, V)) : homOnOfRestrictApp U (φ.toRestrict U) hV m = φ.app V hV m := by
  unfold homOnOfRestrictApp
  change N.presheaf.map (homOfLE (le_ι_image_preimage U hV)).op
    (φ.app (U.ι ''ᵁ U.ι ⁻¹ᵁ V) (ι_image_le U (U.ι ⁻¹ᵁ V))
      (M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op m)) = φ.app V hV m
  rw [φ.naturality, presheaf_map_map N _ _ (𝟙 V) (𝟙 V), op_id, CategoryTheory.Functor.map_id,
    AddCommGrpCat.id_apply, AddCommGrpCat.id_apply]

/-- The `HomOn M N U` defined by a morphism `M.restrict U.ι ⟶ N.restrict U.ι`. -/
def homOnOfRestrict (α : M.restrict U.ι ⟶ N.restrict U.ι) : HomOn M N U where
  app _ hV :=
    { toFun := homOnOfRestrictApp U α hV
      map_add' := homOnOfRestrictApp_add U α hV
      map_smul' := homOnOfRestrictApp_smul U α hV }
  naturality hWV hV m := homOnOfRestrictApp_naturality U α hWV hV m

lemma homOnOfRestrictApp_image (α : M.restrict U.ι ⟶ N.restrict U.ι) (W : U.toScheme.Opens)
    (m : Γ(M, U.ι ''ᵁ W)) : homOnOfRestrictApp U α (ι_image_le U W) m = α.app W m := by
  have e : U.ι ⁻¹ᵁ U.ι ''ᵁ W = W := U.ι.preimage_image_eq W
  have h := congr($(α.mapPresheaf.naturality (eqToHom e).op) m)
  change α.app (U.ι ⁻¹ᵁ U.ι ''ᵁ W) ((M.restrict U.ι).presheaf.map (eqToHom e).op m) =
    (N.restrict U.ι).presheaf.map (eqToHom e).op (α.app W m) at h
  unfold homOnOfRestrictApp
  rw [show M.presheaf.map (homOfLE (U.ι.image_preimage_le (U.ι ''ᵁ W))).op m =
    (M.restrict U.ι).presheaf.map (eqToHom e).op m from rfl, h]
  refine (presheaf_map_map N _ (U.ι.opensFunctor.map (eqToHom e)) (𝟙 _) (𝟙 _) (α.app W m)).trans ?_
  rw [op_id, CategoryTheory.Functor.map_id, AddCommGrpCat.id_apply]
  rfl

/-- `𝒪_U`-linear maps `M|_U → N|_U`, given as families over the opens `V ⊆ U` of `X`, are the
morphisms `M.restrict U.ι ⟶ N.restrict U.ι` of `𝒪_U`-modules. -/
def homOnEquivRestrict : HomOn M N U ≃ (M.restrict U.ι ⟶ N.restrict U.ι) where
  toFun φ := φ.toRestrict U
  invFun α := homOnOfRestrict U α
  left_inv φ := HomOn.ext (funext fun _ ↦ funext fun hV ↦ LinearMap.ext fun m ↦
    homOnOfRestrictApp_toRestrict U φ hV m)
  right_inv α := Scheme.Modules.hom_ext _ _ fun W ↦ by
    ext m
    exact homOnOfRestrictApp_image U α W m

/-- Derivations with values in isomorphic modules correspond. -/
@[simps]
def Derivation.postcompEquiv {Y : Scheme.{u}} {f : X ⟶ Y} (e : M ≅ N) :
    M.Derivation f ≃ N.Derivation f where
  toFun D := D.postcomp e.hom
  invFun D := D.postcomp e.inv
  left_inv D := by
    dsimp only
    rw [← Derivation.postcomp_comp, e.hom_inv_id, Derivation.postcomp_id]
  right_inv D := by
    dsimp only
    rw [← Derivation.postcomp_comp, e.inv_hom_id, Derivation.postcomp_id]

end Scheme.Modules

namespace Scheme.Hom

open Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `Hom_{𝒪_X}(Ω_{X/Y}, J) ≃ Der_Y(𝒪_X, J)`: the global sections of `ℋom(Ω_{X/Y}, J)` are the
`f⁻¹ 𝒪_Y`-derivations of `𝒪_X` into `J` (EGA IV 16.5.3). -/
def sheafHomRelativeDifferentialsTopEquiv (J : X.Modules) :
    Γ(sheafHom f.relativeDifferentials J, ⊤) ≃ J.Derivation f :=
  sheafHomTopEquiv.trans (f.relativeDifferentialsHomEquiv J)

/-- The sections of `ℋom(Ω_{X/Y}, J)` over an open `U` are the derivations of `𝒪_U` into
`J|_U` relative to `U ⟶ Y`. -/
def sheafHomRelativeDifferentialsSectionsEquiv (J : X.Modules) (U : X.Opens) :
    Γ(sheafHom f.relativeDifferentials J, U) ≃ (J.restrict U.ι).Derivation (U.ι ≫ f) :=
  (homOnEquivRestrict U).trans ((f.isUniversal.restrict U.ι).homEquiv _)

/-- The tangent sheaf `𝒯_{X/Y} = ℋom(Ω_{X/Y}, 𝒪_X)` (EGA IV 16.5.7). -/
def tangentSheaf : X.Modules :=
  sheafHom f.relativeDifferentials (SheafOfModules.unit X.ringCatSheaf)

/-- The global sections of `𝒯_{X/Y}` are the `f⁻¹ 𝒪_Y`-derivations of `𝒪_X`. -/
def tangentSheafTopEquiv :
    Γ(f.tangentSheaf, ⊤) ≃ Derivation (SheafOfModules.unit X.ringCatSheaf) f :=
  f.sheafHomRelativeDifferentialsTopEquiv _

/-- The sections of `𝒯_{X/Y}` over `U` are the `f⁻¹ 𝒪_Y`-derivations of `𝒪_U`. -/
def tangentSheafSectionsEquiv (U : X.Opens) :
    Γ(f.tangentSheaf, U) ≃
      Derivation (SheafOfModules.unit U.toScheme.ringCatSheaf) (U.ι ≫ f) :=
  (f.sheafHomRelativeDifferentialsSectionsEquiv _ U).trans
    (Derivation.postcompEquiv (restrictUnitIso U.ι))

end Scheme.Hom

end AlgebraicGeometry
