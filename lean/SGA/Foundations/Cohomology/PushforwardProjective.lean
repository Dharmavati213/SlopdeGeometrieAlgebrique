/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.HProjective
import SGA.Foundations.Cohomology.PushforwardLeray

/-!
# Direct images along H-projective morphisms

* `CohomologyAux.isQuasicoherent_pushforward_of_quasiCompact`: direct images of quasi-coherent
  modules along quasi-compact morphisms from schemes with affine diagonal are quasi-coherent
  (EGA I 9.2.1).
* `CohomologyAux.finite_sections_preimage_of_isHProjective`,
  `CohomologyAux.isCoherent_pushforward_of_isHProjective`: for `π : X ⟶ Z` H-projective over a
  locally noetherian `Z`, `π_* F` is coherent for `F` coherent (EGA III 3.2.1 for `p = 0` in the
  projective case, Hartshorne II.5.20), deduced from the affine case
  (`properFiniteness_of_isHProjective`) over the affine opens of `Z`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

variable {X Z : Scheme.{u}}

/-- A compact open of a scheme is a finite union of affine opens. -/
lemma exists_affine_cover_of_isCompact (V : X.Opens) (hV : IsCompact (V : Set X)) :
    ∃ (n : ℕ) (W : Fin n → X.Opens), (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = V := by
  have hx : ∀ x : V, ∃ W : X.Opens, IsAffineOpen W ∧ x.1 ∈ W ∧ W ≤ V := fun x ↦ by
    obtain ⟨W, hW, hxW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      x.2
    exact ⟨W, hW, hxW, hWV⟩
  choose W hW hxW hWV using hx
  obtain ⟨t, ht⟩ := hV.elim_finite_subcover (fun x : V ↦ (W x : Set X))
    (fun x ↦ (W x).2) (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
  refine ⟨t.card, fun k ↦ W (t.equivFin.symm k), fun k ↦ hW _,
    le_antisymm (iSup_le fun k ↦ hWV _) ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

/-- Direct images of quasi-coherent modules along quasi-compact morphisms from schemes with affine
diagonal are quasi-coherent (EGA I 9.2.1). -/
theorem isQuasicoherent_pushforward_of_quasiCompact (π : X ⟶ Z) [QuasiCompact π]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward π).obj F).IsQuasicoherent := by
  refine isQuasicoherent_pushforward_of_cover π F fun U hU ↦ ?_
  obtain ⟨n, W, hW, hWU⟩ := exists_affine_cover_of_isCompact (π ⁻¹ᵁ U)
    (QuasiCompact.isCompact_preimage (f := π) _ U.2 hU.isCompact)
  exact ⟨n, W, hW, fun i k ↦ (hW i).inf (hW k), hWU⟩

/-- The action of `Γ(Z, W)` on the sections of an `𝒪_X`-module over `π⁻¹ W` through the
structure morphism of `π⁻¹ W ⟶ W ≅ Spec Γ(Z, W)`. -/
lemma map_specStructureRingHom_morphismRestrict (π : X ⟶ Z) {W : Z.Opens} (hW : IsAffineOpen W)
    (a : Γ(Z, W)) :
    X.presheaf.map (homOfLE ((π ⁻¹ᵁ W).ι_image_top.ge)).op
      (((π ∣_ W) ≫ hW.isoSpec.hom).specStructureRingHom a) = π.app W a := by
  have e : (π ∣_ W) ≫ hW.isoSpec.hom = (π ⁻¹ᵁ W).toSpecΓ ≫ Spec.map (π.app W) :=
    (Scheme.Opens.toSpecΓ_naturality π W).symm
  rw [Scheme.Hom.specStructureRingHom, e, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
    ← Scheme.ΓSpecIso_inv_naturality_assoc]
  simp only [Iso.inv_hom_id_assoc, Scheme.Opens.topIso]
  change X.presheaf.map (homOfLE (π ⁻¹ᵁ W).ι_image_top.ge).op
    (X.presheaf.map (homOfLE (π ⁻¹ᵁ W).ι_image_top.le).op (π.app W a)) = π.app W a
  rw [CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_self]

/-- **Coherence of direct images along H-projective morphisms** (EGA III 3.2.1 for `p = 0`, the
projective case; Hartshorne II.5.20): for `π : X ⟶ Z` H-projective with `Z` locally noetherian,
`X` with affine diagonal, and `F` coherent, the sections of `F` over the inverse image of an affine
open `W` form a finitely generated `Γ(Z, W)`-module. -/
theorem finite_sections_preimage_of_isHProjective [IsLocallyNoetherian Z] (π : X ⟶ Z)
    [IsHProjective π] (F : X.Modules) [F.IsCoherent] {W : Z.Opens} (hW : IsAffineOpen W) :
    letI := Module.compHom Γ(F, π ⁻¹ᵁ W) (π.app W).hom
    Module.Finite Γ(Z, W) Γ(F, π ⁻¹ᵁ W) := by
  have hR : IsNoetherianRing Γ(Z, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let π' : (π ⁻¹ᵁ W).toScheme ⟶ W.toScheme := π ∣_ W
  have : IsHProjective π' :=
    IsHProjective.of_isPullback (isPullback_morphismRestrict π W).flip
  let f' : (π ⁻¹ᵁ W).toScheme ⟶ Spec Γ(Z, W) := π' ≫ hW.isoSpec.hom
  have : IsHProjective f' :=
    IsHProjective.of_isPullback (f := π') (IsPullback.of_horiz_isIso (fst := 𝟙 _)
      (g := hW.isoSpec.inv) ⟨by simp [f']⟩)
  let F' := F.restrict (π ⁻¹ᵁ W).ι
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : F.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have : F'.IsCoherent := ⟨inferInstance, inferInstance⟩
  have h := properFiniteness_of_isHProjective Γ(Z, W) _ f' F' 0
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

/-- **Direct images of coherent modules along H-projective morphisms are coherent** (EGA III 3.2.1
in the projective case; Hartshorne II.5.20). -/
theorem isCoherent_pushforward_of_isHProjective [IsLocallyNoetherian Z] (π : X ⟶ Z)
    [IsHProjective π] [IsAffineHom (pullback.diagonal (terminal.from X))] (F : X.Modules)
    [F.IsCoherent] : ((Scheme.Modules.pushforward π).obj F).IsCoherent := by
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have hq := isQuasicoherent_pushforward_of_quasiCompact π F
  refine ⟨hq, isFiniteType_of_finite_sections _ (fun U : Z.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top Z) (fun U ↦ U.2) fun U ↦ ?_⟩
  exact finite_sections_preimage_of_isHProjective π F U.2

end AlgebraicGeometry.CohomologyAux
