/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Localization of the original categorical Hom modules

The finite-presentation localization theorem for linear maps gives the
comparison for the actual Hom objects used by module-valued Ext. The map
sends an original homomorphism to its original localization.
-/

noncomputable section
universe u
open CategoryTheory

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- Localizing the original rank-one module gives the actual localized ring. -/
def localizedRingModuleIso :
    (ModuleCat.of R R).localizedModule S ≅ ModuleCat.of (Localization S) (Localization S) := by
  have := ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of R R) S
  exact (LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.linearEquiv S ((ModuleCat.of R R).localizedModuleMkLinearMap S)
      (Algebra.linearMap R (Localization S)))).toModuleIso

/-- Maps out of an actual localized module are determined on original
elements. The target can be any module over the localized ring. -/
theorem localizedModule_hom_ext (M : ModuleCat.{u} R)
    {N : ModuleCat.{u} (Localization S)} {f g : M.localizedModule S ⟶ N}
    (h : ∀ x : M, f (M.localizedModuleMkLinearMap S x) =
      g (M.localizedModuleMkLinearMap S x)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S (M.localizedModuleMkLinearMap S) y
  apply (IsLocalization.map_units (Localization S) s).smul_left_cancel.mp
  rw [← f.hom.map_smul, ← g.hom.map_smul]
  rw [IsScalarTower.algebraMap_smul]
  change f ((s : R) • y) = g ((s : R) • y)
  rw [show (s : R) • y = M.localizedModuleMkLinearMap S x from hs]
  exact h x

@[simp]
theorem localizedModuleFunctor_map_mk {M N : ModuleCat.{u} R} (f : M ⟶ N) (x : M) :
    (ModuleCat.localizedModuleFunctor S).map f (M.localizedModuleMkLinearMap S x) =
      N.localizedModuleMkLinearMap S (f x) :=
  IsLocalizedModule.map_apply S (M.localizedModuleMkLinearMap S)
    (N.localizedModuleMkLinearMap S) f.hom x

/-- The linear-map Hom localization comparison over the localized ring. -/
def localizedLinearHomIso (M N : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    (ModuleCat.of R (M →ₗ[R] N)).localizedModule S ≅
      ModuleCat.of (Localization S)
        (M.localizedModule S →ₗ[Localization S] N.localizedModule S) := by
  have := ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of R (M →ₗ[R] N)) S
  have := Module.FinitePresentation.isLocalizedModule_mapExtendScalars S
    (M.localizedModuleMkLinearMap S) (N.localizedModuleMkLinearMap S) (Localization S)
  exact (LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.linearEquiv S
      ((ModuleCat.of R (M →ₗ[R] N)).localizedModuleMkLinearMap S)
      (IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
        (N.localizedModuleMkLinearMap S) (Localization S)))).toModuleIso

@[simp]
theorem localizedLinearHomIso_hom_mk (M N : ModuleCat.{u} R)
    [Module.FinitePresentation R M] (f : M →ₗ[R] N) :
    (localizedLinearHomIso S M N).hom
        ((ModuleCat.of R (M →ₗ[R] N)).localizedModuleMkLinearMap S f) =
      IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
        (N.localizedModuleMkLinearMap S) (Localization S) f := by
  have := ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of R (M →ₗ[R] N)) S
  exact IsLocalizedModule.linearEquiv_apply S _ _ f

/-- Localization commutes with the original categorical Hom module for a
finitely presented source and an arbitrary target. -/
def localizedHomIso (M N : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    (ModuleCat.of R (M ⟶ N)).localizedModule S ≅
      ModuleCat.of (Localization S) (M.localizedModule S ⟶ N.localizedModule S) :=
  (ModuleCat.localizedModuleFunctor S).mapIso ModuleCat.homLinearEquiv.toModuleIso ≪≫
    localizedLinearHomIso S M N ≪≫ ModuleCat.homLinearEquiv.symm.toModuleIso

/-- The Hom comparison sends the image of an original map to its actual
localized map, not an arbitrarily chosen isomorphic representative. -/
@[simp]
theorem localizedHomIso_hom_mk (M N : ModuleCat.{u} R) [Module.FinitePresentation R M]
    (f : M ⟶ N) :
    (localizedHomIso S M N).hom ((ModuleCat.of R (M ⟶ N)).localizedModuleMkLinearMap S f) =
      (ModuleCat.localizedModuleFunctor S).map f := by
  change ModuleCat.ofHom ((localizedLinearHomIso S M N).hom
    ((ModuleCat.localizedModuleFunctor S).map ModuleCat.homLinearEquiv.toModuleIso.hom
      ((ModuleCat.of R (M ⟶ N)).localizedModuleMkLinearMap S f))) = _
  rw [localizedModuleFunctor_map_mk]
  change ModuleCat.ofHom ((localizedLinearHomIso S M N).hom
    ((ModuleCat.of R (M →ₗ[R] N)).localizedModuleMkLinearMap S f.hom)) = _
  rw [localizedLinearHomIso_hom_mk]
  rfl

/-- The comparison intertwines precomposition by the original localized
map. This is the compatibility needed for projective-resolution differentials. -/
@[reassoc]
theorem localizedHomIso_precomp {P M : ModuleCat.{u} R}
    [Module.FinitePresentation R P] [Module.FinitePresentation R M]
    (N : ModuleCat.{u} R) (f : P ⟶ M) :
    (ModuleCat.localizedModuleFunctor S).map (((linearYoneda R (ModuleCat R)).obj N).map f.op) ≫
        (localizedHomIso S P N).hom =
      (localizedHomIso S M N).hom ≫
        ((linearYoneda (Localization S) (ModuleCat (Localization S))).obj
          (N.localizedModule S)).map ((ModuleCat.localizedModuleFunctor S).map f).op := by
  apply localizedModule_hom_ext S (ModuleCat.of R (M ⟶ N))
  intro g
  change (localizedHomIso S P N).hom
    ((ModuleCat.localizedModuleFunctor S).map
      (((linearYoneda R (ModuleCat R)).obj N).map f.op)
      ((ModuleCat.of R (M ⟶ N)).localizedModuleMkLinearMap S g)) = _
  erw [localizedModuleFunctor_map_mk S
    (((linearYoneda R (ModuleCat R)).obj N).map f.op) g]
  change (localizedHomIso S P N).hom
    ((ModuleCat.of R (P ⟶ N)).localizedModuleMkLinearMap S (f ≫ g)) =
      (ModuleCat.localizedModuleFunctor S).map f ≫
        (localizedHomIso S M N).hom ((ModuleCat.of R (M ⟶ N)).localizedModuleMkLinearMap S g)
  rw [localizedHomIso_hom_mk, localizedHomIso_hom_mk]
  exact (ModuleCat.localizedModuleFunctor S).map_comp f g

end SGA.SGA2.ExposeV
