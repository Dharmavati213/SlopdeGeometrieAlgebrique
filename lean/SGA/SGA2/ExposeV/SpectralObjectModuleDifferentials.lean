/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.SpectralObjectModulePageComparison

/-!
# Forgetting the module structure preserves the original differentials

The canonical homology comparisons respect the cycle projections used to
define the spectral-object differentials. No replacement differential is chosen.
-/

noncomputable section

universe u v

open CategoryTheory Limits ComposableArrows
open CategoryTheory.Abelian.SpectralObject

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {B : Type u} [Ring B]

private lemma shortComplex_homologyπ_forget_hom (A : ShortComplex (ModuleCat.{v} B)) :
    (A.map (forget₂ (ModuleCat B) AddCommGrpCat)).homologyπ ≫
        (A.mapHomologyIso (forget₂ (ModuleCat B) AddCommGrpCat)).hom =
      (A.mapCyclesIso (forget₂ (ModuleCat B) AddCommGrpCat)).hom ≫
        (forget₂ (ModuleCat B) AddCommGrpCat).map A.homologyπ := by
  let F := forget₂ (ModuleCat B) AddCommGrpCat
  let h := A.homologyData.left
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc,
    ShortComplex.LeftHomologyData.map_π, ← F.map_comp,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv, F.map_comp]

private lemma shortComplex_homologyπ_forget_inv (A : ShortComplex (ModuleCat.{v} B)) :
    (forget₂ (ModuleCat B) AddCommGrpCat).map A.homologyπ ≫
        (A.mapHomologyIso (forget₂ (ModuleCat B) AddCommGrpCat)).inv =
      (A.mapCyclesIso (forget₂ (ModuleCat B) AddCommGrpCat)).inv ≫
        (A.map (forget₂ (ModuleCat B) AddCommGrpCat)).homologyπ := by
  rw [← cancel_epi (A.mapCyclesIso (forget₂ (ModuleCat B) AddCommGrpCat)).hom,
    ← Category.assoc, ← shortComplex_homologyπ_forget_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

variable {ι : Type*} [Category ι]
  (S : Abelian.SpectralObject AddCommGrpCat.{v} ι) (ρ : B →+* End S)

/-- The original cycles are recovered through the canonical preserved-kernel comparison. -/
def spectralObjectModuleCyclesForgetIso {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    (forget₂ (ModuleCat B) AddCommGrpCat).obj ((spectralObjectModuleLift S ρ).cycles f g n) ≅
      S.cycles f g n :=
  PreservesKernel.iso (forget₂ (ModuleCat B) AddCommGrpCat)
    ((spectralObjectModuleLift S ρ).δ f g n (n + 1))

@[reassoc (attr := simp)]
lemma spectralObjectModuleCyclesForgetIso_hom_i {i j k : ι}
    (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    (spectralObjectModuleCyclesForgetIso S ρ f g n).hom ≫ S.iCycles f g n =
      (forget₂ (ModuleCat B) AddCommGrpCat).map ((spectralObjectModuleLift S ρ).iCycles f g n) := by
  dsimp only [spectralObjectModuleCyclesForgetIso, Abelian.SpectralObject.iCycles]
  rw [PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι _ _

@[reassoc]
lemma spectralObjectModuleToCycles_forget {i j k : ι}
    (f : i ⟶ j) (g : j ⟶ k) (fg : i ⟶ k) (hfg : f ≫ g = fg) (n : ℤ) :
    (forget₂ (ModuleCat B) AddCommGrpCat).map
        ((spectralObjectModuleLift S ρ).toCycles f g fg hfg n) ≫
        (spectralObjectModuleCyclesForgetIso S ρ f g n).hom = S.toCycles f g fg hfg n := by
  rw [← cancel_mono (S.iCycles f g n), Category.assoc,
    spectralObjectModuleCyclesForgetIso_hom_i, ← Functor.map_comp,
    Abelian.SpectralObject.toCycles_i, Abelian.SpectralObject.toCycles_i]
  rfl

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)

@[reassoc]
lemma spectralObjectModuleCyclesIso_inv_forget :
    (forget₂ (ModuleCat B) AddCommGrpCat).map
        ((spectralObjectModuleLift S ρ).cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv ≫
        (((spectralObjectModuleLift S ρ).shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).mapCyclesIso
          (forget₂ (ModuleCat B) AddCommGrpCat)).inv =
      (spectralObjectModuleCyclesForgetIso S ρ f₁ f₂ n₁).hom ≫
        (S.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv := by
  let F := forget₂ (ModuleCat B) AddCommGrpCat
  let A := (spectralObjectModuleLift S ρ).shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  have hι : (A.mapCyclesIso F).inv ≫ (A.map F).iCycles = F.map A.iCycles := by
    rw [← cancel_epi (A.mapCyclesIso F).hom, Iso.hom_inv_id_assoc,
      ShortComplex.mapCyclesIso_hom_iCycles]
  rw [← cancel_mono (S.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles,
    Category.assoc, Category.assoc]
  erw [hι]
  rw [← Functor.map_comp,
    (spectralObjectModuleLift S ρ).cyclesIso_inv_i f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂,
    S.cyclesIso_inv_i f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂,
    spectralObjectModuleCyclesForgetIso_hom_i]

/-- The canonical E-term comparison preserves the actual cycle-to-homology projection. -/
@[reassoc]
lemma spectralObjectModuleπE_forget :
    (forget₂ (ModuleCat B) AddCommGrpCat).map
        ((spectralObjectModuleLift S ρ).πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
        (spectralObjectModuleEForgetIso S ρ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
      (spectralObjectModuleCyclesForgetIso S ρ f₁ f₂ n₁).hom ≫
        S.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  dsimp only [Abelian.SpectralObject.πE, spectralObjectModuleEForgetIso, Iso.symm_hom]
  rw [Functor.map_comp, Category.assoc, shortComplex_homologyπ_forget_inv,
    spectralObjectModuleCyclesIso_inv_forget_assoc]
  rfl

end

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  {i' j' k' l' : ι} (f₁' : i' ⟶ j') (f₂' : j' ⟶ k') (f₃' : k' ⟶ l')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')
  (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)

/-- The canonical E-term comparisons respect the original interval maps. -/
@[reassoc]
lemma spectralObjectModuleMap_forget :
    (forget₂ (ModuleCat B) AddCommGrpCat).map
        ((spectralObjectModuleLift S ρ).map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂) ≫
        (spectralObjectModuleEForgetIso S ρ f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂).hom =
      (spectralObjectModuleEForgetIso S ρ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫
        S.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ :=
  ShortComplex.mapHomologyIso_inv_naturality
    ((spectralObjectModuleLift S ρ).shortComplexMap
      f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂)
    (forget₂ (ModuleCat B) AddCommGrpCat)

end

section

variable {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (n₀ n₁ n₂ n₃ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  (hn₃ : n₂ + 1 = n₃)

/-- The lifted differential forgets to the original differential through canonical comparisons. -/
@[reassoc]
lemma spectralObjectModuleD_forget :
    (forget₂ (ModuleCat B) AddCommGrpCat).map
        ((spectralObjectModuleLift S ρ).d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃) ≫
        (spectralObjectModuleEForgetIso S ρ f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃).hom =
      (spectralObjectModuleEForgetIso S ρ f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂).hom ≫
        S.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ := by
  let F := forget₂ (ModuleCat B) AddCommGrpCat
  let U := spectralObjectModuleLift S ρ
  rw [← cancel_epi (F.map (U.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂)),
    ← cancel_epi (F.map (U.toCycles f₃ f₄ (f₃ ≫ f₄) rfl n₁))]
  rw [spectralObjectModuleπE_forget_assoc, spectralObjectModuleToCycles_forget_assoc,
    S.toCycles_πE_d f₁ f₂ f₃ f₄ f₅ (f₁ ≫ f₂) rfl (f₃ ≫ f₄) rfl n₀ n₁ n₂ n₃]
  rw [← F.map_comp_assoc, ← F.map_comp_assoc, Category.assoc,
    U.toCycles_πE_d f₁ f₂ f₃ f₄ f₅ (f₁ ≫ f₂) rfl (f₃ ≫ f₄) rfl n₀ n₁ n₂ n₃,
    F.map_comp, F.map_comp, Category.assoc, Category.assoc,
    spectralObjectModuleπE_forget, spectralObjectModuleToCycles_forget_assoc]
  rfl

end

end SGA.SGA2.ExposeV
