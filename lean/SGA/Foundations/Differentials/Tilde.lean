/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Differentials.Affine
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The sheaf of differentials of `Spec A → Spec R`

For a ring homomorphism `φ : R ⟶ A`, the quasi-coherent sheaf `Ω_{A/R}^~` on `Spec A` carries a
derivation `𝒪_{Spec A} → Ω_{A/R}^~` relative to `Spec.map φ`, extending `d : A → Ω_{A/R}` on
global sections (`AlgebraicGeometry.tildeKaehlerDerivation`), and this derivation is universal
(`AlgebraicGeometry.isUniversalTildeKaehlerDerivation`). Hence
`Ω_{Spec A / Spec R} ≅ Ω_{A/R}^~` (`AlgebraicGeometry.relativeDifferentialsSpecIso`;
Stacks Project, Tag 01UQ, EGA IV 16.5.4).
-/

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

variable {R A : CommRingCat.{u}} (φ : R ⟶ A)

namespace Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
-- `Γ(M, ⊤)` is an `A`-module through `A ≅ Γ(Spec A, ⊤)`.
lemma smul_top_eq (M : (Spec A).Modules) (a : A) (x : Γ(M, ⊤)) :
    a • x = (Scheme.ΓSpecIso A).inv a • x := by
  rw [smul_Spec_def]
  congr 1

namespace Derivation

variable {φ} {M : (Spec A).Modules}

/-- The derivation `A → Γ(M, ⊤)` of global sections of a derivation `𝒪_{Spec A} → M`. -/
def globalDerivation (D : M.Derivation (Spec.map φ)) : (moduleSpecΓFunctor.obj M).Derivation φ :=
  ModuleCat.Derivation.mk (fun a ↦ D.app ⊤ ((Scheme.ΓSpecIso A).inv a))
    (fun a b ↦ (congrArg (D.app ⊤) (map_add _ a b)).trans (map_add _ _ _))
    (fun a b ↦ by
      change D.app ⊤ ((Scheme.ΓSpecIso A).inv (a * b)) =
        (a • D.app ⊤ ((Scheme.ΓSpecIso A).inv b) : Γ(M, ⊤)) +
          (b • D.app ⊤ ((Scheme.ΓSpecIso A).inv a) : Γ(M, ⊤))
      rw [map_mul, app_mul, smul_top_eq, smul_top_eq])
    (fun r ↦ by
      have e : (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso A).inv (φ r) := by
        rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
      exact (congrArg (D.app ⊤) e.symm).trans (D.app_app ⊤ ((Scheme.ΓSpecIso R).inv r)))

@[simp]
lemma globalDerivation_d (D : M.Derivation (Spec.map φ)) (a : A) :
    D.globalDerivation.d a = D.app ⊤ ((Scheme.ΓSpecIso A).inv a) :=
  rfl

end Derivation

end Scheme.Modules

open Scheme.Modules

/-- The map `N → Γ(N^~, ⊤)`, as an additive map to the sections of `N^~` over `⊤`. -/
def tildeToOpenTop (N : ModuleCat A) : N →+ Γ(tilde N, ⊤) :=
  (tilde.toOpen N ⊤).hom.toAddMonoidHom

lemma tildeToOpenTop_apply (N : ModuleCat A) (m : N) :
    tildeToOpenTop N m = tilde.toOpen N ⊤ m :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma tildeToOpenTop_smul (N : ModuleCat A) (a : A) (m : N) :
    tildeToOpenTop N (a • m) = (Scheme.ΓSpecIso A).inv a • tildeToOpenTop N m := by
  rw [← smul_top_eq]
  exact (tilde.toOpen N ⊤).hom.map_smul a m

/-- The derivation `𝒪_{Spec A} → Ω_{A/R}^~`, extending `d : A → Ω_{A/R}` on global sections. -/
def tildeKaehlerDerivation :
    (tilde (CommRingCat.KaehlerDifferential φ)).Derivation (Spec.map φ) :=
  Derivation.ofGlobal
    ((tildeToOpenTop _).comp ((AddMonoidHom.mk' (CommRingCat.KaehlerDifferential.d (f := φ))
      fun a b ↦ ModuleCat.Derivation.d_add _ a b).comp
        (Scheme.ΓSpecIso A).hom.hom.toAddMonoidHom))
    (fun a b ↦ by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_coe, map_mul, ModuleCat.Derivation.d_mul, map_add, tildeToOpenTop_smul]
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply,
        ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply])
    (fun s ↦ by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_coe]
      rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
      exact (congrArg _ (ModuleCat.Derivation.d_map (CommRingCat.KaehlerDifferential.D φ) _)).trans
        (map_zero _))

@[simp]
lemma tildeKaehlerDerivation_app_top (a : Γ(Spec A, ⊤)) :
    (tildeKaehlerDerivation φ).app ⊤ a =
      tilde.toOpen _ ⊤ (CommRingCat.KaehlerDifferential.d ((Scheme.ΓSpecIso A).hom a)) :=
  Derivation.ofGlobal_app_top _ _ _ a

set_option backward.isDefEq.respectTransparency false in
lemma tilde_adjunction_homEquiv_apply {N : ModuleCat A} {M : (Spec A).Modules} (α : tilde N ⟶ M)
    (x : N) : tilde.adjunction.homEquiv N M α x = α.app ⊤ (tilde.toOpen N ⊤ x) := by
  rw [Adjunction.homEquiv_unit]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma tilde_adjunction_homEquiv_symm_app {N : ModuleCat A} {M : (Spec A).Modules}
    (l : N ⟶ moduleSpecΓFunctor.obj M) (x : N) :
    ((tilde.adjunction.homEquiv N M).symm l).app ⊤ (tilde.toOpen N ⊤ x) = l x := by
  have := (tilde.adjunction.homEquiv N M).apply_symm_apply l
  rw [Adjunction.homEquiv_unit] at this
  exact congr($this x)

set_option backward.isDefEq.respectTransparency false in
/-- The derivation `𝒪_{Spec A} → Ω_{A/R}^~` is universal: `Ω_{Spec A / Spec R} ≅ Ω_{A/R}^~`
(Stacks Project, Tag 01UQ). -/
def isUniversalTildeKaehlerDerivation : (tildeKaehlerDerivation φ).Universal where
  desc {N} D := (tilde.adjunction.homEquiv _ N).symm D.globalDerivation.desc
  fac {N} D := by
    refine Derivation.ext_of_isAffine fun a ↦ ?_
    rw [Derivation.postcomp_app, tildeKaehlerDerivation_app_top]
    refine (tilde_adjunction_homEquiv_symm_app _ _).trans ?_
    rw [ModuleCat.Derivation.desc_d, Derivation.globalDerivation_d, ← CommRingCat.comp_apply,
      Iso.hom_inv_id, CommRingCat.id_apply]
  postcomp_injective {N} α β h := by
    apply (tilde.adjunction.homEquiv _ N).injective
    ext b
    rw [tilde_adjunction_homEquiv_apply, tilde_adjunction_homEquiv_apply]
    have e : (tilde.toOpen _ ⊤ (CommRingCat.KaehlerDifferential.d b) : Γ(tilde _, ⊤)) =
        (tildeKaehlerDerivation φ).app ⊤ ((Scheme.ΓSpecIso A).inv b) := by
      rw [tildeKaehlerDerivation_app_top, ← CommRingCat.comp_apply, Iso.inv_hom_id,
        CommRingCat.id_apply]
    rw [e]
    exact congr($(h).app ⊤ ((Scheme.ΓSpecIso A).inv b))

/-- `Ω_{Spec A / Spec R} ≅ Ω_{A/R}^~` (Stacks Project, Tag 01UQ; EGA IV 16.5.4). -/
def relativeDifferentialsSpecIso :
    (Spec.map φ).relativeDifferentials ≅ tilde (CommRingCat.KaehlerDifferential φ) :=
  (Spec.map φ).isUniversal.iso (isUniversalTildeKaehlerDerivation φ)

instance : (Spec.map φ).relativeDifferentials.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso
    (relativeDifferentialsSpecIso φ).symm
      (inferInstanceAs (tilde (CommRingCat.KaehlerDifferential φ)).IsQuasicoherent)

end AlgebraicGeometry
