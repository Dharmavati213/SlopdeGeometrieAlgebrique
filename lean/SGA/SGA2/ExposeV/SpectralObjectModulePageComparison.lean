/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.SpectralObjectModuleAction
import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# Canonical comparisons with the original additive page terms

Forgetting the module structure preserves the actual short-complex homology
used in every spectral-object term. Thus every term of every module-valued
page has a canonical comparison with the previously constructed additive page.
-/

noncomputable section

universe u v

open CategoryTheory Limits ComposableArrows
open CategoryTheory.Abelian.SpectralObject

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {B : Type u} [Ring B] {ι : Type*} [Category ι]
  (S : Abelian.SpectralObject AddCommGrpCat.{v} ι) (ρ : B →+* End S)

/-- Forgetting the retained module action recovers each original spectral-object page term. -/
def spectralObjectModuleEForgetIso {i j k l : ι}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) :
    (forget₂ (ModuleCat B) AddCommGrpCat).obj
        ((spectralObjectModuleLift S ρ).E f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂) ≅
      S.E f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂ :=
  (((spectralObjectModuleLift S ρ).shortComplex f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).mapHomologyIso
    (forget₂ (ModuleCat B) AddCommGrpCat)).symm

variable (T : Abelian.SpectralObject AddCommGrpCat.{v} EInt) (σ : B →+* End T)

/-- Retaining module structures does not change first-quadrant vanishing. -/
instance spectralObjectModuleLift_isFirstQuadrant [T.IsFirstQuadrant] :
    (spectralObjectModuleLift T σ).IsFirstQuadrant where
  isZero₁ i j hij hj n := ModuleCat.isZero_iff_subsingleton.mpr
    (AddCommGrpCat.isZero_iff_subsingleton.mp (T.isZero₁_of_isFirstQuadrant i j hij hj n))
  isZero₂ i j hij n hi := ModuleCat.isZero_iff_subsingleton.mpr
    (AddCommGrpCat.isZero_iff_subsingleton.mp (T.isZero₂_of_isFirstQuadrant i j hij n hi))

unseal Abelian.SpectralObject.spectralSequence in
/-- Every actual module-valued page term canonically forgets to the original additive page term. -/
def spectralObjectModulePageXForgetIso (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    (forget₂ (ModuleCat B) AddCommGrpCat).obj
        (((spectralObjectModuleLift T σ).E₂SpectralSequence.page r hr).X pq) ≅
      ((T.E₂SpectralSequence.page r hr).X pq) :=
  spectralObjectModuleEForgetIso T σ
    (homOfLE (coreE₂Cohomological.le₀₁ r pq)) (homOfLE (coreE₂Cohomological.le₁₂ pq))
    (homOfLE (coreE₂Cohomological.le₂₃ r pq))
    (coreE₂Cohomological.deg pq - 1) (coreE₂Cohomological.deg pq)
    (coreE₂Cohomological.deg pq + 1) (by lia) rfl

end SGA.SGA2.ExposeV
