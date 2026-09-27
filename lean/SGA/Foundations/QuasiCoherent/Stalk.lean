/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.QuasiCoherent.SpecSections

/-!
# Stalks of quasi-coherent modules

For a quasi-coherent module `F` on `Spec R` and a point `x`, the stalk `F_x` is the localization
`Γ(F)_x` of the global sections at the prime `x` (`stalkAddEquivLocalizedModule`, with
`stalkAddEquivLocalizedModule_germ` computing it on germs). For `F` quasi-coherent on a scheme
`X` and an affine open `U`, the stalk of `F` at the image of a point `y` of `Spec Γ(X, U)` is the
localization at `y` of the sections of `F` over `U = fromSpec '' ⊤`
(`stalkAddEquivLocalizedModuleOfIsAffineOpen`).
-/

universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (F : (Spec R).Modules) [F.IsQuasicoherent] (x : PrimeSpectrum R)

/-- The stalks of isomorphic modules are isomorphic. -/
noncomputable def stalkAddEquivOfIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (y : X) :
    M.presheaf.stalk y ≃+ N.presheaf.stalk y :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
    ((toPresheaf X).mapIso e)).addCommGroupIsoToAddEquiv

lemma stalkAddEquivOfIso_germ {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (y : X)
    (U : X.Opens) (hy : y ∈ U) (m : Γ(M, U)) :
    stalkAddEquivOfIso e y (M.presheaf.germ U y hy m) = N.presheaf.germ U y hy (e.hom.app U m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy ((toPresheaf X).map e.hom) m

/-- For `F` quasi-coherent on `Spec R`, the stalk `F_x` is the localization of `Γ(F)` at `x`. -/
noncomputable def stalkAddEquivLocalizedModule :
    F.presheaf.stalk x ≃+ LocalizedModule x.asIdeal.primeCompl F.ΓSpec :=
  let e₂ : (tilde F.ΓSpec).presheaf.stalk x ≃+ LocalizedModule x.asIdeal.primeCompl F.ΓSpec :=
    (IsLocalizedModule.iso x.asIdeal.primeCompl (tilde.toStalk F.ΓSpec x).hom).symm.toAddEquiv
  (stalkAddEquivOfIso F.tildeΓIso.symm x).trans e₂

lemma stalkAddEquivLocalizedModule_germ (m : Γ(F, ⊤)) :
    stalkAddEquivLocalizedModule F x (F.presheaf.germ ⊤ x trivial m) =
      LocalizedModule.mk (M := F.ΓSpec) m 1 := by
  have h₁ := stalkAddEquivOfIso_germ F.tildeΓIso.symm x ⊤ trivial m
  simp only [stalkAddEquivLocalizedModule, AddEquiv.trans_apply]
  rw [h₁, Iso.symm_hom, tildeΓIso_inv_app]
  exact IsLocalizedModule.iso_symm_apply x.asIdeal.primeCompl (tilde.toStalk F.ΓSpec x).hom m

section Affine

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
  (y : PrimeSpectrum Γ(X, U))

/-- For `F` quasi-coherent on `X`, `U` an affine open and `y` a point of `Spec Γ(X, U) ≅ U`, the
stalk of `F` at `y` is the localization at `y` of the sections of `F` over `U`. -/
noncomputable def stalkAddEquivLocalizedModuleOfIsAffineOpen :
    F.presheaf.stalk (hU.fromSpec y) ≃+
      LocalizedModule y.asIdeal.primeCompl ((restrictFunctor hU.fromSpec).obj F).ΓSpec :=
  ((restrictStalkNatIso hU.fromSpec y).app F).addCommGroupIsoToAddEquiv.symm.trans
    (stalkAddEquivLocalizedModule ((restrictFunctor hU.fromSpec).obj F) y)

lemma stalkAddEquivLocalizedModuleOfIsAffineOpen_germ (m : Γ(F, hU.fromSpec ''ᵁ ⊤)) :
    stalkAddEquivLocalizedModuleOfIsAffineOpen F hU y
      (F.presheaf.germ (hU.fromSpec ''ᵁ ⊤) (hU.fromSpec y) ⟨y, trivial, rfl⟩ m) =
      LocalizedModule.mk (M := ((restrictFunctor hU.fromSpec).obj F).ΓSpec) m 1 := by
  have h : ((restrictStalkNatIso hU.fromSpec y).inv.app F)
      (F.presheaf.germ (hU.fromSpec ''ᵁ ⊤) (hU.fromSpec y) ⟨y, trivial, rfl⟩ m) =
      ((restrictFunctor hU.fromSpec).obj F).presheaf.germ ⊤ y trivial m :=
    congr($(germ_restrictStalkNatIso_inv_app hU.fromSpec y F (U := ⊤) trivial) m)
  change stalkAddEquivLocalizedModule ((restrictFunctor hU.fromSpec).obj F) y
    (((restrictStalkNatIso hU.fromSpec y).inv.app F)
      (F.presheaf.germ (hU.fromSpec ''ᵁ ⊤) (hU.fromSpec y) ⟨y, trivial, rfl⟩ m)) = _
  rw [h]
  exact stalkAddEquivLocalizedModule_germ ((restrictFunctor hU.fromSpec).obj F) y m

end Affine

end AlgebraicGeometry.Scheme.Modules
