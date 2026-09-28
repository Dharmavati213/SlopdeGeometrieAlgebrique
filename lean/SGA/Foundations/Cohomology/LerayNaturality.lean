/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.LerayTransfer

/-!
# Naturality of Leray's comparison for direct images

For `j : X ⟶ Y` and a finite open cover `U` of `Y` with affine finite intersections, the
comparison `Hᵖ(X, M) ≅ Hᵖ(Y, j_* M)` of `CohomologyAux.pushforwardHAddEquiv` is natural in `M`
(`pushforwardHAddEquiv_naturality`): it intertwines `Hᵖ(φ)` and `Hᵖ(j_* φ)` for every morphism of
`𝒪_X`-modules `φ`. This applies in particular to multiplication by sections of `𝒪_X` which do not
come from `Y` (compare `pushforwardHAddEquiv_smul`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TopCat.Presheaf

namespace AlgebraicGeometry.CohomologyAux

variable {X Y : Scheme.{u}} (j : X ⟶ Y)

lemma H'CongrOpens_map {M N : X.Modules} (φ : M.toAbSheaf ⟶ N.toAbSheaf) (p : ℕ)
    {V V' : X.Opens} (h : V = V') (x : M.H' p V) :
    H'CongrOpens N p h (CategoryTheory.Sheaf.H'.map φ p V x) =
      CategoryTheory.Sheaf.H'.map φ p V' (H'CongrOpens M p h x) := by
  subst h
  rfl

/-- The identification of the Čech complexes of `j_* M` and `M` is natural in `M`. -/
lemma cechComplexPushforwardIso_naturality {M N : X.Modules} (φ : M ⟶ N) {n : ℕ}
    (U : Fin n → Y.Opens) :
    cechComplexMap U
        (Scheme.Modules.Hom.toAbSheaf ((Scheme.Modules.pushforward j).map φ)).hom ≫
        (cechComplexPushforwardIso j N U).hom =
      (cechComplexPushforwardIso j M U).hom ≫
        cechComplexMap (fun i ↦ j ⁻¹ᵁ U i) (Scheme.Modules.Hom.toAbSheaf φ).hom := by
  ext m : 1
  refine AddCommGrpCat.ext fun c ↦ funext fun x ↦ ?_
  exact (hom_app_presheaf_map φ (homOfLE (cechOpen_preimage j U x).le)
    (@id Γ(M, j ⁻¹ᵁ cechOpen U x) (c x))).symm

variable {n : ℕ} (U : Fin n → Y.Opens) (p : ℕ)

/-- **Naturality of Leray's comparison** `Hᵖ(⋃ j⁻¹ Uᵢ, M) ≅ Hᵖ(⋃ Uᵢ, j_* M)` in `M`. -/
lemma pushforwardH'AddEquiv_naturality {M N : X.Modules} (φ : M ⟶ N)
    [((Scheme.Modules.pushforward j).obj M).IsQuasicoherent]
    [((Scheme.Modules.pushforward j).obj N).IsQuasicoherent]
    (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (cechOpen U x))
    (hM : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ),
      Subsingleton (M.H' (q + 1) (j ⁻¹ᵁ cechOpen U x)))
    (hN : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ),
      Subsingleton (N.H' (q + 1) (j ⁻¹ᵁ cechOpen U x)))
    (x : M.H' p (⨆ i, j ⁻¹ᵁ U i)) :
    pushforwardH'AddEquiv N U p j hU hN
        (CategoryTheory.Sheaf.H'.map (Scheme.Modules.Hom.toAbSheaf φ) p _ x) =
      CategoryTheory.Sheaf.H'.map
        (Scheme.Modules.Hom.toAbSheaf ((Scheme.Modules.pushforward j).map φ)) p _
        (pushforwardH'AddEquiv M U p j hU hM x) := by
  let hLM : TopCat.Sheaf.IsLerayAcyclic (X := X.carrier) (fun i ↦ j ⁻¹ᵁ U i) M.toAbSheaf :=
    ⟨fun x q ↦ by rw [cechOpen_preimage]; exact hM x q⟩
  let hLN : TopCat.Sheaf.IsLerayAcyclic (X := X.carrier) (fun i ↦ j ⁻¹ᵁ U i) N.toAbSheaf :=
    ⟨fun x q ↦ by rw [cechOpen_preimage]; exact hN x q⟩
  let eXM := cechHomologyLinearEquivOfLeray p M (fun i ↦ j ⁻¹ᵁ U i) hLM
  let eXN := cechHomologyLinearEquivOfLeray p N (fun i ↦ j ⁻¹ᵁ U i) hLN
  let eYM := ((Scheme.Modules.pushforward j).obj M).cechHomologyLinearEquiv U p hU
  let eYN := ((Scheme.Modules.pushforward j).obj N).cechHomologyLinearEquiv U p hU
  let ecM := cechHomologyPushforwardAddEquiv j M U p
  let ecN := cechHomologyPushforwardAddEquiv j N U p
  change eYN (ecN.symm (eXN.symm (CategoryTheory.Sheaf.H'.map
      (Scheme.Modules.Hom.toAbSheaf φ) p _ x))) =
    CategoryTheory.Sheaf.H'.map
      (Scheme.Modules.Hom.toAbSheaf ((Scheme.Modules.pushforward j).map φ)) p _
      (eYM (ecM.symm (eXM.symm x)))
  obtain ⟨d, rfl⟩ : ∃ d, x = eXM (ecM d) :=
    ⟨ecM.symm (eXM.symm x), by rw [AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩
  rw [LinearEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  -- naturality of `eX`
  have hX : CategoryTheory.Sheaf.H'.map (Scheme.Modules.Hom.toAbSheaf φ) p _ (eXM (ecM d)) =
      eXN (HomologicalComplex.homologyMap
        (cechComplexMap (fun i ↦ j ⁻¹ᵁ U i) (Scheme.Modules.Hom.toAbSheaf φ).hom) p (ecM d)) :=
    (ConcreteCategory.congr_hom
      (TopCat.Sheaf.cechHomologyIso_naturality p hLM hLN (Scheme.Modules.Hom.toAbSheaf φ))
      (ecM d)).symm
  -- naturality of `ec`
  have hC : HomologicalComplex.homologyMap
      (cechComplexMap (fun i ↦ j ⁻¹ᵁ U i) (Scheme.Modules.Hom.toAbSheaf φ).hom) p (ecM d) =
      ecN (HomologicalComplex.homologyMap (cechComplexMap U
        (Scheme.Modules.Hom.toAbSheaf ((Scheme.Modules.pushforward j).map φ)).hom) p d) := by
    have h := congrArg (fun ψ ↦ HomologicalComplex.homologyMap ψ p)
      (cechComplexPushforwardIso_naturality j φ U)
    have h' := (HomologicalComplex.homologyMap_comp _ _ p).symm.trans
      (h.trans (HomologicalComplex.homologyMap_comp _ _ p))
    exact (ConcreteCategory.congr_hom h' d).symm
  -- naturality of `eY`
  have hY : eYN (HomologicalComplex.homologyMap (cechComplexMap U
        (Scheme.Modules.Hom.toAbSheaf ((Scheme.Modules.pushforward j).map φ)).hom) p d) =
      CategoryTheory.Sheaf.H'.map
        (Scheme.Modules.Hom.toAbSheaf ((Scheme.Modules.pushforward j).map φ)) p _ (eYM d) :=
    ConcreteCategory.congr_hom (TopCat.Sheaf.cechHomologyIso_naturality p _ _
      (Scheme.Modules.Hom.toAbSheaf ((Scheme.Modules.pushforward j).map φ))) d
  refine (congrArg (fun y ↦ eYN (ecN.symm (eXN.symm y))) hX).trans ?_
  refine (congrArg (fun y ↦ eYN (ecN.symm (eXN.symm (eXN y)))) hC).trans ?_
  rw [LinearEquiv.symm_apply_apply]
  exact (congrArg eYN (ecN.symm_apply_apply _)).trans hY

/-- **Naturality of Leray's comparison** `Hᵖ(X, M) ≅ Hᵖ(Y, j_* M)` in `M`. -/
lemma pushforwardHAddEquiv_naturality {M N : X.Modules} (φ : M ⟶ N)
    [((Scheme.Modules.pushforward j).obj M).IsQuasicoherent]
    [((Scheme.Modules.pushforward j).obj N).IsQuasicoherent]
    (hcov : ⨆ i, U i = ⊤)
    (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (cechOpen U x))
    (hM : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ),
      Subsingleton (M.H' (q + 1) (j ⁻¹ᵁ cechOpen U x)))
    (hN : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ),
      Subsingleton (N.H' (q + 1) (j ⁻¹ᵁ cechOpen U x)))
    (x : M.H p) :
    pushforwardHAddEquiv j N U hcov hU hN p
        (CategoryTheory.Sheaf.H'.map (Scheme.Modules.Hom.toAbSheaf φ) p ⊤ x) =
      CategoryTheory.Sheaf.H'.map
        (Scheme.Modules.Hom.toAbSheaf ((Scheme.Modules.pushforward j).map φ)) p ⊤
        (pushforwardHAddEquiv j M U hcov hU hM p x) := by
  have e₁ : (⊤ : X.Opens) = ⨆ i, j ⁻¹ᵁ U i := by rw [← Scheme.Hom.preimage_iSup, hcov]; rfl
  change (H'CongrOpens _ p hcov) (pushforwardH'AddEquiv N U p j hU hN
      ((H'CongrOpens N p e₁)
        (CategoryTheory.Sheaf.H'.map (Scheme.Modules.Hom.toAbSheaf φ) p ⊤ x))) =
    CategoryTheory.Sheaf.H'.map
      (Scheme.Modules.Hom.toAbSheaf ((Scheme.Modules.pushforward j).map φ)) p ⊤
      ((H'CongrOpens _ p hcov) (pushforwardH'AddEquiv M U p j hU hM ((H'CongrOpens M p e₁) x)))
  rw [H'CongrOpens_map, pushforwardH'AddEquiv_naturality, H'CongrOpens_map]

end AlgebraicGeometry.CohomologyAux
