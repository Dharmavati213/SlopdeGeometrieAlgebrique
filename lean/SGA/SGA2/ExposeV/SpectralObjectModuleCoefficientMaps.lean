/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.SpectralObjectModulePageComparison
import SGA.SGA2.ExposeI.SpectralSequenceCoefficientFunctor

/-!
# Equivariant coefficient maps of the actual module spectral objects

An original additive spectral-object map commuting with the retained ring
actions lifts to a genuine module spectral-object map. Its maps on every
page agree with the original additive coefficient maps under the unchanged
canonical forgetful comparisons.
-/

noncomputable section

universe u v

open CategoryTheory Limits ComposableArrows
open CategoryTheory.Abelian.SpectralObject

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {B : Type u} [Ring B] {ι : Type*} [Category ι]
  {S T U : Abelian.SpectralObject AddCommGrpCat.{v} ι}
  (ρ : B →+* End S) (σ : B →+* End T) (τ : B →+* End U)

/-- Lift an original equivariant coefficient map, keeping all of its interval maps. -/
def spectralObjectModuleMap (a : S ⟶ T) (ha : ∀ b, a ≫ σ b = ρ b ≫ a) :
    spectralObjectModuleLift S ρ ⟶ spectralObjectModuleLift T σ where
  hom n :=
    { app D := ModuleCat.ofHom
        (X := spectralObjectModuleObj S ρ n D) (Y := spectralObjectModuleObj T σ n D)
        { toFun := (a.hom n).app D
          map_add' x y := ((a.hom n).app D).hom.map_add x y
          map_smul' b x := by
            have h := congrArg (fun k : S ⟶ T ↦ (k.hom n).app D) (ha b)
            change (a.hom n).app D (((ρ b).hom n).app D x) =
              ((σ b).hom n).app D ((a.hom n).app D x)
            exact (ConcreteCategory.congr_hom h x).symm }
      naturality {D E} k := by
        ext x
        exact ConcreteCategory.congr_hom ((a.hom n).naturality k) x }
  comm n m h i j k f g := by
    ext x
    exact ConcreteCategory.congr_hom (a.comm n m h f g) x

@[simp]
theorem spectralObjectModuleMap_id :
    spectralObjectModuleMap ρ ρ (𝟙 S) (fun _ ↦ by simp) = 𝟙 _ := by
  apply Abelian.SpectralObject.Hom.ext
  funext n
  apply NatTrans.ext
  funext D
  ext x
  rfl

@[reassoc]
theorem spectralObjectModuleMap_comp (a : S ⟶ T) (b : T ⟶ U)
    (ha : ∀ r, a ≫ σ r = ρ r ≫ a) (hb : ∀ r, b ≫ τ r = σ r ≫ b) :
    spectralObjectModuleMap ρ τ (a ≫ b)
        (fun r ↦ by rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]) =
      spectralObjectModuleMap ρ σ a ha ≫ spectralObjectModuleMap σ τ b hb := by
  apply Abelian.SpectralObject.Hom.ext
  funext n
  apply NatTrans.ext
  funext D
  ext x
  rfl

/-- Canonical short-complex homology comparisons retain original equivariant coefficient maps. -/
@[reassoc]
theorem spectralObjectModuleEForgetIso_naturality
    (a : S ⟶ T) (ha : ∀ b, a ≫ σ b = ρ b ≫ a)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) :
    (forget₂ (ModuleCat B) AddCommGrpCat).map
        (ExposeI.SpectralObjectCoefficientMaps.EMap (spectralObjectModuleMap ρ σ a ha)
          f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂) ≫
        (spectralObjectModuleEForgetIso T σ f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).hom =
      (spectralObjectModuleEForgetIso S ρ f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).hom ≫
        ExposeI.SpectralObjectCoefficientMaps.EMap a f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂ :=
  ShortComplex.mapHomologyIso_inv_naturality
    (ExposeI.SpectralObjectCoefficientMaps.shortComplexMap (spectralObjectModuleMap ρ σ a ha)
      f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂) (forget₂ (ModuleCat B) AddCommGrpCat)

section Pages

variable {S T : Abelian.SpectralObject AddCommGrpCat.{v} EInt}
  (ρ : B →+* End S) (σ : B →+* End T)

unseal Abelian.SpectralObject.spectralSequence in
/-- On every page, the original forgetful comparison intertwines the actual coefficient maps. -/
@[reassoc]
theorem spectralObjectModulePageXForgetIso_naturality
    (a : S ⟶ T) (ha : ∀ b, a ≫ σ b = ρ b ≫ a)
    (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    (forget₂ (ModuleCat B) AddCommGrpCat).map
        (((ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
          (spectralObjectModuleMap ρ σ a ha) coreE₂Cohomological).hom r hr).f pq) ≫
        (spectralObjectModulePageXForgetIso T σ r hr pq).hom =
      (spectralObjectModulePageXForgetIso S ρ r hr pq).hom ≫
        ((ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap a
          coreE₂Cohomological).hom r hr).f pq :=
  spectralObjectModuleEForgetIso_naturality ρ σ a ha
    (homOfLE (coreE₂Cohomological.le₀₁ r pq)) (homOfLE (coreE₂Cohomological.le₁₂ pq))
    (homOfLE (coreE₂Cohomological.le₂₃ r pq))
    (coreE₂Cohomological.deg pq - 1) (coreE₂Cohomological.deg pq)
    (coreE₂Cohomological.deg pq + 1) (by lia) rfl

end Pages

end SGA.SGA2.ExposeV
