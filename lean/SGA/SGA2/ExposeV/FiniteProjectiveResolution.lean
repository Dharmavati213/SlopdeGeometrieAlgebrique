/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Genuine degreewise finite projective resolutions

Finite free covers give enough projectives in the category of finite modules
over a noetherian ring. A projective object in that category is a retract of
a finite free module, so its underlying module is genuinely projective among
all modules. Forgetting a resolution therefore gives an actual projective
resolution in `ModuleCat`, with finite terms in every degree.

These resolutions will allow the finite-presentation Hom localization theorem
to be applied termwise in the Ext-localization step of V.3.5.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A projective module is projective in the original finite-module category. -/
instance finiteModule_projective_of_moduleProjective (M : FGModuleCat.{u} R)
    [Module.Projective R M] : Projective M :=
  (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).projective_of_map_projective
    (inferInstanceAs (Projective M.obj))

/-- The category of finite modules has enough projectives, using actual
surjections from finite free modules. -/
instance finiteModule_enoughProjectives : EnoughProjectives (FGModuleCat.{u} R) where
  presentation M := by
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
    let g : FGModuleCat.of R (Fin n → R) ⟶ M := FGModuleCat.ofHom f
    have : Epi ((forget₂ (FGModuleCat R) (ModuleCat R)).map g) :=
      (ModuleCat.epi_iff_surjective _).mpr hf
    have : Epi g := (forget₂ (FGModuleCat R) (ModuleCat R)).epi_of_epi_map inferInstance
    exact ⟨{ p := FGModuleCat.of R (Fin n → R), f := g }⟩

omit [IsNoetherianRing R] in
/-- Projectivity in the finite category implies projectivity among all
modules: split a finite free cover, then retain its original linear section. -/
theorem moduleProjective_of_finiteModule_projective (M : FGModuleCat.{u} R)
    [Projective M] : Module.Projective R M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let g : FGModuleCat.of R (Fin n → R) ⟶ M := FGModuleCat.ofHom f
  have : Epi ((forget₂ (FGModuleCat R) (ModuleCat R)).map g) :=
    (ModuleCat.epi_iff_surjective _).mpr hf
  have : Epi g := (forget₂ (FGModuleCat R) (ModuleCat R)).epi_of_epi_map inferInstance
  exact Module.Projective.of_split (Projective.factorThru (𝟙 M) g).hom.hom f
    (congrArg (fun k : M ⟶ M ↦ k.hom.hom) (Projective.factorThru_comp (𝟙 M) g))

/-- Forgetting finiteness preserves genuine projective objects. -/
instance finiteModule_forget_preservesProjectiveObjects :
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).PreservesProjectiveObjects where
  projective_obj {M} hM := by
    have := hM
    have := moduleProjective_of_finiteModule_projective M
    exact ModuleCat.projective_of_categoryTheory_projective M.obj

/-- An actual projective resolution in the category of all modules, whose
terms are finite. Its augmentation resolves the unchanged original module. -/
def finiteProjectiveResolution (M : ModuleCat.{u} R) [Module.Finite R M] :
    ProjectiveResolution M :=
  (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).mapProjectiveResolution
    (projectiveResolution (FGModuleCat.of R M))

instance finiteProjectiveResolution_finite (M : ModuleCat.{u} R)
    [Module.Finite R M] (i : ℕ) :
    Module.Finite R ((finiteProjectiveResolution M).complex.X i) :=
  ((projectiveResolution (FGModuleCat.of R M)).complex.X i).property

end SGA.SGA2.ExposeV
