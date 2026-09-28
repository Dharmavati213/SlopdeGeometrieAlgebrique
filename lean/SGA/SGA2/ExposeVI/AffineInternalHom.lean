/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.AffineInternalHomSections

/-!
# Actual affine internal Hom and finite-presentation localization

For a finitely presented `R`-module `M`, the actual module-valued internal
Hom from `M~` to `N~` is quasi-coherent and canonically isomorphic to
`Hom_R(M,N)~`. The proof uses the original local linear maps and restriction
maps. Finite-presentation localization clears denominators of their values
on the original source module, and finite generation detects equality after
localization. No sheaf-Hom comparison is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : CommRingCat.{u}} (M N : ModuleCat.{u} R) [Module.FinitePresentation R M]

/-- The actual Hom sheaf restriction to a principal open is the localization map. -/
theorem affineInternalHom_isLocalizing :
    IsLocalizing (modulesSpecToSheaf.obj (schemeModuleInternalHom (tilde M) (tilde N))) := by
  intro f
  let H := schemeModuleInternalHom (tilde M) (tilde N)
  let V : (Spec R).Opens := PrimeSpectrum.basicOpen f
  constructor
  · intro s
    obtain ⟨n, hn⟩ := s.property
    change IsUnit (algebraMap R (Module.End R Γ(H, V)) (s : R))
    rw [← hn, map_pow]
    exact (H.isUnit_algebraMap_end_of_le_basicOpen f le_rfl).pow n
  · intro φ
    obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
      (.powers f) (tilde.toOpen N V).hom (affineInternalHomEvaluation M N V φ)
    refine ⟨⟨affineHomSection M N ⊤ h, s⟩, ?_⟩
    apply affineInternalHomEvaluation_injective M N V
    change affineInternalHomEvaluation M N V ((s : R) • φ) =
      affineInternalHomEvaluation M N V
        (H.val.map V.leTop.op (affineHomSection M N ⊤ h))
    rw [map_smul, affineHomSection_restrict, affineHomSection_eval]
    exact hs.symm
  · intro φ ψ h
    change H.val.map V.leTop.op φ = H.val.map V.leTop.op ψ at h
    have he := congrArg (affineInternalHomEvaluation M N V) h
    rw [affineInternalHomEvaluation_restrict, affineInternalHomEvaluation_restrict] at he
    let q := ((modulesSpecToSheaf.obj (tilde N)).presheaf.map V.leTop.op).hom
    have : IsLocalizedModule (.powers f) q := isLocalizing_tilde N f
    obtain ⟨s, hs⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
      (.powers f) q (affineInternalHomEvaluation M N ⊤ φ)
        (affineInternalHomEvaluation M N ⊤ ψ) he
    refine ⟨s, ?_⟩
    apply affineInternalHomEvaluation_injective M N ⊤
    change affineInternalHomEvaluation M N ⊤ ((s : R) • φ) =
      affineInternalHomEvaluation M N ⊤ ((s : R) • ψ)
    rw [map_smul, map_smul]
    exact hs

/-- The canonical tilde-of-global-sections map for actual affine internal Hom is an isomorphism. -/
instance affineInternalHom_isIso_fromTildeΓ :
    IsIso (schemeModuleInternalHom (tilde M) (tilde N)).fromTildeΓ :=
  (isIso_fromTildeΓ_iff_isLocalizing _).mpr (affineInternalHom_isLocalizing M N)

/-- **VI.2.1, affine degree zero:** actual internal Hom is quasi-coherent for a
finitely presented source and an arbitrary affine quasi-coherent target. -/
instance affineInternalHom_isQuasicoherent :
    (schemeModuleInternalHom (tilde M) (tilde N)).IsQuasicoherent :=
  (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance

/-- The actual module sheaf of local linear morphisms is the tilde of the original linear Hom. -/
def affineInternalHomIso :
    tilde (ModuleCat.of R (M →ₗ[R] N)) ≅ schemeModuleInternalHom (tilde M) (tilde N) := by
  let : IsIso (schemeModuleInternalHom (tilde M) (tilde N)).fromTildeΓ :=
    affineInternalHom_isIso_fromTildeΓ M N
  exact (tilde.functor R).mapIso (affineGlobalHomEquiv M N).toModuleIso ≪≫
    asIso (schemeModuleInternalHom (tilde M) (tilde N)).fromTildeΓ

/-- The comparison carries an original module map to its actual local tilde morphism. -/
theorem affineInternalHomIso_hom_toOpen (U : (Spec R).Opens) (f : M →ₗ[R] N) :
    (affineInternalHomIso M N).hom.val.app (op U)
        ((tilde.toOpen (ModuleCat.of R (M →ₗ[R] N)) U) f) =
      affineHomSection M N U f := by
  let H := schemeModuleInternalHom (tilde M) (tilde N)
  let e : ModuleCat.of R (M →ₗ[R] N) ≅ (moduleSpecΓFunctor (R := R)).obj H :=
    (affineGlobalHomEquiv M N).toModuleIso
  have h₁ := ConcreteCategory.congr_hom (tilde.toOpen_map_app e.hom U) f
  have h₂ := ConcreteCategory.congr_hom (H.toOpen_fromTildeΓ_app U) (e.hom f)
  change H.fromTildeΓ.val.app (op U)
      ((tilde.map e.hom).val.app (op U)
        ((tilde.toOpen (ModuleCat.of R (M →ₗ[R] N)) U) f)) = _
  change (tilde.map e.hom).val.app (op U)
      ((tilde.toOpen (ModuleCat.of R (M →ₗ[R] N)) U) f) =
    (tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj H) U) (e.hom f) at h₁
  rw [h₁]
  change H.fromTildeΓ.val.app (op U)
      ((tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj H) U) (e.hom f)) =
    H.val.map U.leTop.op (e.hom f) at h₂
  rw [h₂]
  change H.val.map U.leTop.op (affineGlobalHomEquiv M N f) = _
  rw [affineGlobalHomEquiv_apply, affineHomSection_restrict]

/-- The same quasi-coherence assertion for arbitrary actual affine quasi-coherent modules,
with a finitely presented module of source coefficients. -/
theorem affineInternalHom_isQuasicoherent_of_coefficients
    (F G : (Spec R).Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [Module.FinitePresentation R ((moduleSpecΓFunctor (R := R)).obj F)] :
    (schemeModuleInternalHom F G).IsQuasicoherent := by
  let e := schemeModuleInternalHomIso (asIso F.fromTildeΓ) (asIso G.fromTildeΓ)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
    (affineInternalHom_isQuasicoherent
      ((moduleSpecΓFunctor (R := R)).obj F) ((moduleSpecΓFunctor (R := R)).obj G))

end SGA.SGA2.ExposeVI
