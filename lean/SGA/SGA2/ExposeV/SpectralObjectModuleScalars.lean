/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.SpectralObjectModulePageComparison
import SGA.SGA2.ExposeI.SpectralSequenceCoefficientMaps

/-!
# The original page comparisons intertwine the retained scalar action

Scalar multiplication on the homology of the actual module short complex
forgets to the homology map of the original scalar spectral-object
endomorphism. This verifies scalar compatibility for the canonical page
comparison in every degree, rather than choosing new page comparisons.
-/

noncomputable section

universe u v

open CategoryTheory Limits ComposableArrows
open CategoryTheory.Abelian.SpectralObject

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {B : Type u} [Ring B] {ι : Type*} [Category ι]
  (S : Abelian.SpectralObject AddCommGrpCat.{v} ι) (ρ : B →+* End S)

/-- The canonical comparison of each actual page term retains the original scalar action. -/
@[reassoc]
theorem spectralObjectModuleEForgetIso_scalar {i j k l : ι}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) (b : B) :
    ((spectralObjectModuleLift S ρ).E f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).smul b ≫
        (spectralObjectModuleEForgetIso S ρ f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).hom =
      (spectralObjectModuleEForgetIso S ρ f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).hom ≫
        ExposeI.SpectralObjectCoefficientMaps.EMap (ρ b) f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂ := by
  let T := (spectralObjectModuleLift S ρ).shortComplex f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂
  let F := forget₂ (ModuleCat B) AddCommGrpCat
  change T.homology.smul b ≫ (T.mapHomologyIso F).inv =
    (T.mapHomologyIso F).inv ≫ ShortComplex.homologyMap (T.mapNatTrans (ModuleCat.smulNatTrans B b))
  rw [ShortComplex.homologyMap_mapNatTrans, Iso.inv_hom_id_assoc]
  rfl

variable (T : Abelian.SpectralObject AddCommGrpCat.{v} EInt) (σ : B →+* End T)

unseal Abelian.SpectralObject.spectralSequence in
/-- The original additive comparison intertwines scalar multiplication on every actual page. -/
@[reassoc]
theorem spectralObjectModulePageXForgetIso_scalar
    (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (b : B) :
    (((spectralObjectModuleLift T σ).E₂SpectralSequence.page r hr).X pq).smul b ≫
        (spectralObjectModulePageXForgetIso T σ r hr pq).hom =
      (spectralObjectModulePageXForgetIso T σ r hr pq).hom ≫
        ((ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap (σ b)
          coreE₂Cohomological).hom r hr).f pq :=
  spectralObjectModuleEForgetIso_scalar T σ
    (homOfLE (coreE₂Cohomological.le₀₁ r pq)) (homOfLE (coreE₂Cohomological.le₁₂ pq))
    (homOfLE (coreE₂Cohomological.le₂₃ r pq))
    (coreE₂Cohomological.deg pq - 1) (coreE₂Cohomological.deg pq)
    (coreE₂Cohomological.deg pq + 1) (by lia) rfl b

end SGA.SGA2.ExposeV
