/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RingedModuleSpectralModuleLift
import SGA.SGA2.ExposeI.SpectralObjectConvergence

/-!
# V.3.2: first-quadrant support and the canonical finite module filtration

The actual derived direct-image complex is connective. Orthogonality of the
standard t-structure gives first-quadrant support, which is retained by the
module lift. The existing spectral-object convergence theorem then gives a
finite exhaustive filtration by submodules of the canonical total object and
module-linear comparisons with stable pages. The companion
`RingedModuleSpectralAbutment` identifies this total module with the original
source supported cohomology and transports the finite filtration to it.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat
open SGA.SGA2.ExposeI

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {R : Sheaf RingCat.{u} X} {S : Sheaf RingCat.{u} Y}
  (φ : S ⟶ (Sheaf.pushforward RingCat f).obj R) (Z : Closeds Y)

local instance : HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} Y) :=
  HasDerivedCategory.standard _

/-- Connectiveness and t-structure orthogonality give the actual first-quadrant bounds. -/
instance ringedModulePushforwardAbelianSpectralObject_isFirstQuadrant
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M) :
    (ringedModulePushforwardAbelianSpectralObject f φ Z I).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    let t := DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} Y)
    have h := t.isZero_eTruncLT_obj_obj (ringedModulePushforwardDerivedObject f φ I) 0 j hj
    have h' := (t.eTruncGE.obj i).map_isZero h
    exact ((ringedDerivedSupportedHom Z).shift n).map_isZero h'
  isZero₂ i j hij n hi := by
    let t := DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} Y)
    have hni : ((n + 1 : ℤ) : EInt) ≤ i := by
      induction i using WithBotTop.rec with
      | bot => simp at hi
      | coe i =>
        simp only [WithBotTop.coe_le_coe, WithBotTop.coe_lt_coe] at *
        lia
      | top => exact le_top
    have hge := t.isGE_eTruncGE_obj_obj (n + 1) i hni
      ((t.eTruncLT.obj j).obj (ringedModulePushforwardDerivedObject f φ I))
    have hshift := t.isGE_shift
      ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj
        (ringedModulePushforwardDerivedObject f φ I))) (n + 1) n 1 (by lia)
    change IsZero (AddCommGrpCat.of
      (((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) 0).obj (ExposeI.zZX_closed Z)) ⟶
        ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj
          (ringedModulePushforwardDerivedObject f φ I)))⟦n⟧))
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact ⟨fun a b ↦ (t.zero a 0 1).trans (t.zero b 0 1).symm⟩

/-- The retained global-ring action gives the same first-quadrant module spectral object. -/
instance ringedModulePushforwardModuleSpectralObject_isFirstQuadrant
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M) :
    (ringedModulePushforwardModuleSpectralObject f φ Z I).IsFirstQuadrant := by
  dsimp only [ringedModulePushforwardModuleSpectralObject]
  infer_instance

/-- Every actual module-valued page vanishes in negative second degree. -/
theorem ringedModulePushforwardModuleSpectralSequence_isZero_of_second_neg
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M)
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hq : q < 0) :
    IsZero (((ringedModulePushforwardModuleSpectralSequence f φ Z I).page r).X (p, q)) :=
  Abelian.SpectralObject.isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr _
    ((ringedModulePushforwardModuleSpectralObject f φ Z I).isZero₁_of_isFirstQuadrant
      _ _ _ (by simp; lia) _)

/-- Every actual module-valued page vanishes in negative first degree. -/
theorem ringedModulePushforwardModuleSpectralSequence_isZero_of_first_neg
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M)
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hp : p < 0) :
    IsZero (((ringedModulePushforwardModuleSpectralSequence f φ Z I).page r).X (p, q)) :=
  Abelian.SpectralObject.isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr _
    ((ringedModulePushforwardModuleSpectralObject f φ Z I).isZero₂_of_isFirstQuadrant
      _ _ _ _ (by simp; lia))

/-- The genuine total-interval module of the direct-image spectral construction. -/
def ringedModulePushforwardSpectralTotal {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (n : ℤ) :
    ModuleCat.{u + 1} (S.obj.obj (op (⊤ : Opens Y))) :=
  SpectralObjectConvergence.total (ringedModulePushforwardModuleSpectralObject f φ Z I) n

/-- The canonical finite filtration by submodules of the actual total object. -/
def ringedModulePushforwardSpectralFiniteFiltration {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (n : ℕ) :
    Fin (n + 2) →o Subobject (ringedModulePushforwardSpectralTotal f φ Z I n) :=
  SpectralObjectConvergence.finiteFiltration (ringedModulePushforwardModuleSpectralObject f φ Z I) n

@[simp]
theorem ringedModulePushforwardSpectralFiniteFiltration_zero {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (n : ℕ) :
    ringedModulePushforwardSpectralFiniteFiltration f φ Z I n 0 = ⊥ :=
  SpectralObjectConvergence.finiteFiltration_zero _ n

@[simp]
theorem ringedModulePushforwardSpectralFiniteFiltration_last {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (n : ℕ) :
    ringedModulePushforwardSpectralFiniteFiltration f φ Z I n (Fin.last (n + 1)) = ⊤ :=
  SpectralObjectConvergence.finiteFiltration_last _ n

/-- The actual quotient of consecutive canonical submodules of total degree `n`. -/
def ringedModulePushforwardSpectralGradedPiece {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (n q : ℤ) :
    ModuleCat.{u + 1} (S.obj.obj (op (⊤ : Opens Y))) :=
  SpectralObjectConvergence.gradedPiece (ringedModulePushforwardModuleSpectralObject f φ Z I) n q

/-- Stable pages identify module-linearly with actual associated-graded quotients.
The bound is uniform over every bidegree of a fixed total degree. -/
def ringedModulePushforwardModuleStablePageIsoGraded {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (n : ℕ) (q : Fin (n + 1)) (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((ringedModulePushforwardModuleSpectralSequence f φ Z I).page r).X ((n : ℤ) - q, q) ≅
      ringedModulePushforwardSpectralGradedPiece f φ Z I n q :=
  SpectralObjectConvergence.stablePageIsoGradedTotal
    (ringedModulePushforwardModuleSpectralObject f φ Z I) n q r hr

end SGA.SGA2.ExposeV
