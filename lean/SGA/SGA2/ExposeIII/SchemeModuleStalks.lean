/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.AffineStalkDepth
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Literal stalk modules of scheme modules

We expose the actual structure-stalk action on the actual abelian stalk
of a scheme module, and prove compatibility of this action with stalk maps.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- The canonical actual structure-stalk action on a scheme-module stalk. -/
instance schemeModuleStalkModule (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  inferInstanceAs (Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.val.presheaf x))

/-- The literal stalk module over the actual local structure ring. -/
def schemeModuleStalk (M : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x) (M.presheaf.stalk x)

/-- Depth of the actual stalk module over its actual local structure ring. -/
def moduleStalkDepth (M : X.Modules) (x : X) : ℕ∞ :=
  depth (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (schemeModuleStalk M x)

/-- Genuine germs respect the scalar action of the actual structure sheaf. -/
theorem schemeModule_germ_smul (M : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
    (r : Γ(X, U)) (m : Γ(M, U)) :
    M.presheaf.germ U x hx (r • m) =
      X.presheaf.germ U x hx r • M.presheaf.germ U x hx m :=
  M.val.germ_smul x U hx r m

/-- A module-sheaf morphism induces an actual linear map of stalk modules. -/
def schemeModuleStalkMap {M N : X.Modules} (φ : M ⟶ N) (x : X) :
    schemeModuleStalk M x ⟶ schemeModuleStalk N x :=
  ModuleCat.ofHom
    { ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.mapPresheaf).hom with
      map_smul' := by
        intro r m
        obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
        rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r]
        rw [← schemeModule_germ_smul]
        change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.mapPresheaf)
          (M.presheaf.germ V x hxV _) =
          X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hVU).op r) •
            (show N.presheaf.stalk x from
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.mapPresheaf)
                (M.presheaf.germ V x hxV m))
        rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
          TopCat.Presheaf.stalkFunctor_map_germ_apply]
        change N.presheaf.germ V x hxV (φ.app V (_ • m)) = _
        rw [Scheme.Modules.Hom.app_smul, schemeModule_germ_smul]
        rfl }

@[simp] theorem schemeModuleStalkMap_germ {M N : X.Modules} (φ : M ⟶ N)
    (x : X) (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)) :
    schemeModuleStalkMap φ x (M.presheaf.germ U x hx m) =
      N.presheaf.germ U x hx (φ.app U m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ.mapPresheaf m

@[simp] theorem schemeModuleStalkMap_id (M : X.Modules) (x : X) :
    schemeModuleStalkMap (𝟙 M) x = 𝟙 (schemeModuleStalk M x) := by
  ext m
  obtain ⟨U, hxU, m, rfl⟩ := M.presheaf.exists_germ_eq m
  simp

@[simp] theorem schemeModuleStalkMap_comp {M N P : X.Modules}
    (φ : M ⟶ N) (ψ : N ⟶ P) (x : X) :
    schemeModuleStalkMap (φ ≫ ψ) x = schemeModuleStalkMap φ x ≫ schemeModuleStalkMap ψ x := by
  ext m
  obtain ⟨U, hxU, m, rfl⟩ := M.presheaf.exists_germ_eq m
  simp

/-- The genuine functor to modules over an actual structure stalk. -/
def schemeModuleStalkFunctor (x : X) : X.Modules ⥤ ModuleCat (X.presheaf.stalk x) where
  obj M := schemeModuleStalk M x
  map φ := schemeModuleStalkMap φ x
  map_id M := schemeModuleStalkMap_id M x
  map_comp φ ψ := schemeModuleStalkMap_comp φ ψ x

/-- Isomorphic scheme modules have genuinely linearly isomorphic stalks. -/
def schemeModuleStalkLinearEquiv {M N : X.Modules} (e : M ≅ N) (x : X) :
    schemeModuleStalk M x ≃ₗ[X.presheaf.stalk x] schemeModuleStalk N x :=
  ((schemeModuleStalkFunctor x).mapIso e).toLinearEquiv

/-- Literal stalk depth is invariant under an actual module-sheaf isomorphism. -/
theorem moduleStalkDepth_eq_of_iso [IsLocallyNoetherian X]
    {M N : X.Modules} (e : M ≅ N) (x : X)
    [Module.Finite (X.presheaf.stalk x) (schemeModuleStalk M x)]
    [Module.Finite (X.presheaf.stalk x) (schemeModuleStalk N x)] :
    moduleStalkDepth M x = moduleStalkDepth N x :=
  depth_eq_of_linearEquiv _ (schemeModuleStalkLinearEquiv e x)

section OpenRestriction

variable {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- The actual local-ring equivalence for restriction along an open immersion,
oriented from the restricted scheme to the ambient scheme. -/
def openImmersionStalkRingEquiv (x : Y) :
    Y.presheaf.stalk x ≃+* X.presheaf.stalk (f x) :=
  (asIso (f.stalkMap x)).symm.commRingCatIsoToRingEquiv

instance openImmersionStalkRingEquivInvPair (x : Y) :
    RingHomInvPair (openImmersionStalkRingEquiv f x).toRingHom
    (openImmersionStalkRingEquiv f x).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (openImmersionStalkRingEquiv f x)

instance openImmersionStalkRingEquivInvPair_symm (x : Y) :
    RingHomInvPair (openImmersionStalkRingEquiv f x).symm.toRingHom
    (openImmersionStalkRingEquiv f x).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (openImmersionStalkRingEquiv f x)

/-- The affine/open section-ring identification and the actual stalk-ring
map commute with germs. -/
theorem openImmersion_appIso_germ (x : Y) (U : Y.Opens) (hx : x ∈ U) :
    (f.appIso U).hom ≫ Y.presheaf.germ U x hx =
      X.presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩ ≫ f.stalkMap x := by
  rw [f.appIso_hom, Category.assoc, Y.presheaf.germ_res, f.germ_stalkMap]

@[simp] theorem openImmersionStalkRingEquiv_germ (x : Y) (U : Y.Opens)
    (hx : x ∈ U) (r : Γ(Y, U)) :
    openImmersionStalkRingEquiv f x (Y.presheaf.germ U x hx r) =
      X.presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩ ((f.appIso U).inv r) := by
  have h := openImmersion_appIso_germ f x U hx
  have he : Y.presheaf.germ U x hx ≫ inv (f.stalkMap x) =
      (f.appIso U).inv ≫ X.presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩ := by
    rw [← cancel_mono (f.stalkMap x), Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Category.assoc, ← h]
    simp
  exact congrArg (fun k : Γ(Y, U) ⟶ X.presheaf.stalk (f x) => k r) he

/-- The actual restriction-stalk comparison on underlying additive groups. -/
def schemeModuleRestrictStalkAddEquiv (M : X.Modules) (x : Y) :
    (M.restrict f).presheaf.stalk x ≃+ M.presheaf.stalk (f x) :=
  ((Scheme.Modules.restrictStalkNatIso f x).app M).addCommGroupIsoToAddEquiv

@[simp] theorem schemeModuleRestrictStalkAddEquiv_germ (M : X.Modules)
    (x : Y) (U : Y.Opens) (hx : x ∈ U) (m : Γ(M.restrict f, U)) :
    schemeModuleRestrictStalkAddEquiv f M x ((M.restrict f).presheaf.germ U x hx m) =
      M.presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩ ((M.restrictAppIso f U).hom m) :=
  congrArg (fun k : Γ(M.restrict f, U) ⟶ M.presheaf.stalk (f x) => k m)
    (Scheme.Modules.germ_restrictStalkNatIso_hom_app f x M hx)

/-- The actual restriction-stalk comparison is semilinear over the
canonical actual local-ring equivalence. -/
def schemeModuleRestrictStalkSemilinearEquiv (M : X.Modules) (x : Y) :
    LinearEquiv (openImmersionStalkRingEquiv f x).toRingHom
      (σ' := (openImmersionStalkRingEquiv f x).symm.toRingHom)
      ((M.restrict f).presheaf.stalk x) (M.presheaf.stalk (f x)) :=
  { schemeModuleRestrictStalkAddEquiv f M x with
    map_smul' := by
      intro r m
      change schemeModuleRestrictStalkAddEquiv f M x (r • m) =
        openImmersionStalkRingEquiv f x r • schemeModuleRestrictStalkAddEquiv f M x m
      obtain ⟨U, hxU, r, rfl⟩ := Y.presheaf.exists_germ_eq r
      obtain ⟨V, hVU, hxV, m, rfl⟩ := (M.restrict f).presheaf.exists_le_germ_eq m hxU
      rw [← Y.presheaf.germ_res_apply (homOfLE hVU) x hxV r,
        ← schemeModule_germ_smul, schemeModuleRestrictStalkAddEquiv_germ,
        schemeModuleRestrictStalkAddEquiv_germ, openImmersionStalkRingEquiv_germ]
      rw [Scheme.Modules.smul_restrictAppIso_hom_apply, schemeModule_germ_smul] }

/-- Literal module-stalk depth is unchanged under genuine open restriction. -/
theorem moduleStalkDepth_restrict [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (M : X.Modules) (x : Y)
    [Module.Finite (Y.presheaf.stalk x) (schemeModuleStalk (M.restrict f) x)]
    [Module.Finite (X.presheaf.stalk (f x)) (schemeModuleStalk M (f x))] :
    moduleStalkDepth (M.restrict f) x = moduleStalkDepth M (f x) := by
  have h := depth_eq_of_semilinearEquiv (openImmersionStalkRingEquiv f x)
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
    (M := schemeModuleStalk (M.restrict f) x) (N := schemeModuleStalk M (f x))
    (schemeModuleRestrictStalkSemilinearEquiv f M x)
  rw [IsLocalRing.map_maximalIdeal_of_surjective (openImmersionStalkRingEquiv f x).toRingHom
    (openImmersionStalkRingEquiv f x).surjective] at h
  exact h

end OpenRestriction

end SGA.SGA2.ExposeIII
