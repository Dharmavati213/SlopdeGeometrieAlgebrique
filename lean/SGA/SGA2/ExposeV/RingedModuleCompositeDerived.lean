/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RingedModuleSupportedPushforward
import SGA.SGA2.ExposeI.RightDerivedPostcomposition
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# SGA 2, V.3.2: the module-valued abutment comparison

Right deriving the actual supported-section/direct-image composite gives
supported cohomology on the source, with scalars restricted along the map on
structure-sheaf sections. Restriction of scalars is exact, so the comparison
holds in all degrees and is natural in the coefficient module sheaf.

This identifies the proposed abutment in V.3.2. The construction and E₂-page
identification of the composed-functor spectral sequence are separate tasks.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

/-- Restriction of scalars preserves homology even for noncommutative rings:
the underlying functions and their exactness do not change. -/
instance ringRestrictScalars_preservesHomology {A B : Type*} [Ring A] [Ring B]
    (ρ : A →+* B) : (ModuleCat.restrictScalars.{v} ρ).PreservesHomology := by
  apply ((Functor.exact_tfae (ModuleCat.restrictScalars.{v} ρ)).out 2 3).mp
  intro T hT
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
  exact hT

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {R : Sheaf RingCat.{u} X} {S : Sheaf RingCat.{u} Y}
  (φ : S ⟶ (Sheaf.pushforward RingCat f).obj R)

/-- In every degree, the right-derived composite on an open of the target is
supported cohomology on its inverse image, with the actual restricted scalars. -/
def ringedModuleSupportedCompositeRightDerivedIso (Z : Closeds Y) (U : Opens Y) (n : ℕ) :
    (ringedModulePushforward f φ ⋙ moduleGammaZSectionsFunctor S Z U).rightDerived n ≅
      derivedModuleGammaZSections R (Z.preimage f.hom.continuous) ((Opens.map f).obj U) n ⋙
        ModuleCat.restrictScalars (φ.hom.app (op U)).hom :=
  ExposeI.rightDerivedFunctorIso (ringedModulePushforwardSupportedSectionsIso f φ Z U) n ≪≫
    ExposeI.rightDerivedPostcomposeIso
      (moduleGammaZSectionsFunctor R (Z.preimage f.hom.continuous) ((Opens.map f).obj U))
      (ModuleCat.restrictScalars (φ.hom.app (op U)).hom) n

/-- The global comparison giving V.3.2's abutment as a module over `Γ(Y,S)`. -/
def ringedModuleSupportedGlobalRightDerivedIso (Z : Closeds Y) (n : ℕ) :
    (ringedModulePushforward f φ ⋙ moduleGammaZSectionsFunctor S Z ⊤).rightDerived n ≅
      derivedModuleGammaZSections R (Z.preimage f.hom.continuous) ⊤ n ⋙
        ModuleCat.restrictScalars (ringedGlobalRingHom f φ) :=
  ringedModuleSupportedCompositeRightDerivedIso f φ Z ⊤ n

/-- The global comparison commutes with actual coefficient maps in every degree. -/
@[reassoc]
theorem ringedModuleSupportedGlobalRightDerivedIso_naturality
    (Z : Closeds Y) (n : ℕ) {M N : SheafOfModules.{u} R} (a : M ⟶ N) :
    ((ringedModulePushforward f φ ⋙ moduleGammaZSectionsFunctor S Z ⊤).rightDerived n).map a ≫
        (ringedModuleSupportedGlobalRightDerivedIso f φ Z n).hom.app N =
      (ringedModuleSupportedGlobalRightDerivedIso f φ Z n).hom.app M ≫
        (ModuleCat.restrictScalars (ringedGlobalRingHom f φ)).map
          ((derivedModuleGammaZSections R (Z.preimage f.hom.continuous) ⊤ n).map a) :=
  (ringedModuleSupportedGlobalRightDerivedIso f φ Z n).hom.naturality a

end SGA.SGA2.ExposeV
