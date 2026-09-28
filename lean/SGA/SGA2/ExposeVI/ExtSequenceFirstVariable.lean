/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.LocallyClosedSheafExtSequences
import SGA.SGA2.ExposeVI.ModuleHomBifunctor
import SGA.SGA2.ExposeI.RightDerivedSequenceNaturality

/-!
# SGA 2, VI.1.8: first-variable naturality of the exact sequences

Original local-linear precomposition acts on the supported-Hom short
complexes. Naturality of the genuine homology connecting maps then proves
the required contravariant naturality of both supported Ext sequences.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- The global-section comparison commutes with actual local-linear precomposition. -/
@[reassoc]
theorem moduleLocallyClosedSupportedHomGammaIso_precomp
    {E F : SheafOfModules.{u} R} (a : E ⟶ F) (W : ExposeI.LocallyClosedIn X)
    (G : SheafOfModules.{u} R) :
    (moduleLocallyClosedSupportedHomPrecomp R a W).app G ≫
        (moduleLocallyClosedSupportedHomGammaIso R E W).hom.app G =
      (moduleLocallyClosedSupportedHomGammaIso R F W).hom.app G ≫
        (ExposeI.gammaLocallyClosedFunctor W).map
          (moduleSheafHomAbPrecomp (Opens.grothendieckTopology X) a G) :=
  (ExposeI.underlineGammaLocallyClosedGlobalSectionsIso W).hom.naturality
    (moduleSheafHomAbPrecomp (Opens.grothendieckTopology X) a G)

variable {E F : SheafOfModules.{u} R} (a : E ⟶ F)
  (W : ExposeI.LocallyClosedIn X) (T : Closeds W.asSet)

/-- Original source precomposition acts on the actual supported-Hom sequence. -/
def moduleNestedSupportedHomSequencePrecomp :
    moduleNestedSupportedHomSequence R F W T ⟶ moduleNestedSupportedHomSequence R E W T where
  τ₁ := moduleLocallyClosedSupportedHomPrecomp R a _
  τ₂ := moduleLocallyClosedSupportedHomPrecomp R a W
  τ₃ := moduleLocallyClosedSupportedHomPrecomp R a _
  comm₁₂ := by
    apply NatTrans.ext
    funext G
    apply (cancel_mono ((moduleLocallyClosedSupportedHomGammaIso R E W).hom.app G)).mp
    dsimp only [moduleNestedSupportedHomSequence,
      moduleNestedSupportedHomInclusion, NatTrans.comp_app, Functor.whiskerLeft_app]
    simp only [Category.assoc, moduleLocallyClosedSupportedHomGammaIso_precomp,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← Category.assoc, moduleLocallyClosedSupportedHomGammaIso_precomp,
      Category.assoc]
    exact congrArg (fun k ↦ (moduleLocallyClosedSupportedHomGammaIso R F _).hom.app G ≫ k)
      ((ExposeI.locallyClosedNestedGammaInclusion W (ExposeI.nestedClosedSubspace W T)).naturality
        (moduleSheafHomAbPrecomp (Opens.grothendieckTopology X) a G))
  comm₂₃ := by
    apply NatTrans.ext
    funext G
    apply (cancel_mono ((moduleLocallyClosedSupportedHomGammaIso R E _).hom.app G)).mp
    dsimp only [moduleNestedSupportedHomSequence,
      moduleNestedSupportedHomRestriction, NatTrans.comp_app, Functor.whiskerLeft_app]
    simp only [Category.assoc, moduleLocallyClosedSupportedHomGammaIso_precomp,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← Category.assoc, moduleLocallyClosedSupportedHomGammaIso_precomp,
      Category.assoc]
    exact congrArg (fun k ↦ (moduleLocallyClosedSupportedHomGammaIso R F W).hom.app G ≫ k)
      ((ExposeI.locallyClosedNestedGammaRestriction W (ExposeI.nestedClosedSubspace W T)).naturality
        (moduleSheafHomAbPrecomp (Opens.grothendieckTopology X) a G))

/-- Original source precomposition acts on the supported-Hom sheaf sequence. -/
def moduleNestedSheafHomSequencePrecomp :
    moduleNestedSheafHomSequence R F W T ⟶ moduleNestedSheafHomSequence R E W T where
  τ₁ := moduleLocallyClosedSheafHomPrecomp R a _
  τ₂ := moduleLocallyClosedSheafHomPrecomp R a W
  τ₃ := moduleLocallyClosedSheafHomPrecomp R a _
  comm₁₂ := by
    ext G
    exact (ExposeI.locallyClosedNestedSheafInclusion W
      (ExposeI.nestedClosedSubspace W T)).naturality
        (moduleSheafHomAbPrecomp (Opens.grothendieckTopology X) a G)
  comm₂₃ := by
    ext G
    exact (ExposeI.locallyClosedNestedSheafRestriction W
      (ExposeI.nestedClosedSubspace W T)).naturality
        (moduleSheafHomAbPrecomp (Opens.grothendieckTopology X) a G)

local instance (A : SheafOfModules.{u} R) :
    (moduleNestedSupportedHomSequence R A W T).X₁.Additive :=
  inferInstanceAs (moduleLocallyClosedSupportedHomFunctor R A _).Additive

local instance (A : SheafOfModules.{u} R) :
    (moduleNestedSupportedHomSequence R A W T).X₂.Additive :=
  inferInstanceAs (moduleLocallyClosedSupportedHomFunctor R A W).Additive

local instance (A : SheafOfModules.{u} R) :
    (moduleNestedSupportedHomSequence R A W T).X₃.Additive :=
  inferInstanceAs (moduleLocallyClosedSupportedHomFunctor R A _).Additive

local instance (A : SheafOfModules.{u} R) :
    (moduleNestedSheafHomSequence R A W T).X₁.Additive :=
  inferInstanceAs (moduleLocallyClosedSheafHomFunctor R A _).Additive

local instance (A : SheafOfModules.{u} R) :
    (moduleNestedSheafHomSequence R A W T).X₂.Additive :=
  inferInstanceAs (moduleLocallyClosedSheafHomFunctor R A W).Additive

local instance (A : SheafOfModules.{u} R) :
    (moduleNestedSheafHomSequence R A W T).X₃.Additive :=
  inferInstanceAs (moduleLocallyClosedSheafHomFunctor R A _).Additive

/-- The derived support-increasing map commutes with actual source precomposition. -/
@[reassoc]
theorem moduleNestedSupportedExtInclusion_precomp (G : SheafOfModules.{u} R) (n : ℕ) :
    (moduleLocallyClosedSupportedExtPrecomp R a
          (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T)) n).app G ≫
        (moduleNestedSupportedExtInclusion R E W T n).app G =
      (moduleNestedSupportedExtInclusion R F W T n).app G ≫
        (moduleLocallyClosedSupportedExtPrecomp R a W n).app G := by
  have h := congrArg (fun α ↦ (α.rightDerived n).app G)
    (moduleNestedSupportedHomSequencePrecomp R a W T).comm₁₂
  simpa only [NatTrans.rightDerived_comp, NatTrans.comp_app,
    moduleNestedSupportedHomSequencePrecomp, moduleNestedSupportedHomSequence,
    moduleLocallyClosedSupportedExtPrecomp, moduleNestedSupportedExtInclusion] using h

/-- The derived support restriction commutes with actual source precomposition. -/
@[reassoc]
theorem moduleNestedSupportedExtRestriction_precomp (G : SheafOfModules.{u} R) (n : ℕ) :
    (moduleLocallyClosedSupportedExtPrecomp R a W n).app G ≫
        (moduleNestedSupportedExtRestriction R E W T n).app G =
      (moduleNestedSupportedExtRestriction R F W T n).app G ≫
        (moduleLocallyClosedSupportedExtPrecomp R a
          (ExposeI.nestedDifferenceSupportWitness W
            (ExposeI.nestedClosedSubspace W T)) n).app G := by
  have h := congrArg (fun α ↦ (α.rightDerived n).app G)
    (moduleNestedSupportedHomSequencePrecomp R a W T).comm₂₃
  simpa only [NatTrans.rightDerived_comp, NatTrans.comp_app,
    moduleNestedSupportedHomSequencePrecomp, moduleNestedSupportedHomSequence,
    moduleLocallyClosedSupportedExtPrecomp, moduleNestedSupportedExtRestriction] using h

/-- The supported sheaf Ext inclusion commutes with source precomposition. -/
@[reassoc]
theorem moduleNestedSheafExtInclusion_precomp (G : SheafOfModules.{u} R) (n : ℕ) :
    (moduleLocallyClosedSheafExtPrecomp R a
          (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T)) n).app G ≫
        ((moduleNestedSheafHomInclusion R E W T).rightDerived n).app G =
      ((moduleNestedSheafHomInclusion R F W T).rightDerived n).app G ≫
        (moduleLocallyClosedSheafExtPrecomp R a W n).app G := by
  have h := congrArg (fun α ↦ (α.rightDerived n).app G)
    (moduleNestedSheafHomSequencePrecomp R a W T).comm₁₂
  simpa only [NatTrans.rightDerived_comp, NatTrans.comp_app,
    moduleNestedSheafHomSequencePrecomp, moduleNestedSheafHomSequence,
    moduleLocallyClosedSheafExtPrecomp] using h

/-- The supported sheaf Ext restriction commutes with source precomposition. -/
@[reassoc]
theorem moduleNestedSheafExtRestriction_precomp (G : SheafOfModules.{u} R) (n : ℕ) :
    (moduleLocallyClosedSheafExtPrecomp R a W n).app G ≫
        ((moduleNestedSheafHomRestriction R E W T).rightDerived n).app G =
      ((moduleNestedSheafHomRestriction R F W T).rightDerived n).app G ≫
        (moduleLocallyClosedSheafExtPrecomp R a
          (ExposeI.nestedDifferenceSupportWitness W
            (ExposeI.nestedClosedSubspace W T)) n).app G := by
  have h := congrArg (fun α ↦ (α.rightDerived n).app G)
    (moduleNestedSheafHomSequencePrecomp R a W T).comm₂₃
  simpa only [NatTrans.rightDerived_comp, NatTrans.comp_app,
    moduleNestedSheafHomSequencePrecomp, moduleNestedSheafHomSequence,
    moduleLocallyClosedSheafExtPrecomp] using h

/-- **VI.1.8, first-variable naturality:** the actual supported Ext boundary
commutes with source precomposition. -/
@[reassoc]
theorem moduleNestedSupportedExtBoundary_precomp (G : SheafOfModules.{u} R) (n : ℕ) :
    (moduleNestedSupportedExtBoundary R F W T n).app G ≫
        (moduleLocallyClosedSupportedExtPrecomp R a
          (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T)) (n + 1)).app G =
      (moduleLocallyClosedSupportedExtPrecomp R a
          (ExposeI.nestedDifferenceSupportWitness W (ExposeI.nestedClosedSubspace W T)) n).app G ≫
        (moduleNestedSupportedExtBoundary R E W T n).app G :=
  ExposeI.rightDerivedFunctorBoundary_natTrans
    (moduleNestedSupportedHomSequence_injective R F W T)
    (moduleNestedSupportedHomSequence_injective R E W T)
    (moduleNestedSupportedHomSequencePrecomp R a W T) G n

/-- First-variable naturality also holds for the original supported sheaf Ext boundary. -/
@[reassoc]
theorem moduleNestedSheafExtBoundary_precomp (G : SheafOfModules.{u} R) (n : ℕ) :
    (moduleNestedSheafExtBoundary R F W T n).app G ≫
        (moduleLocallyClosedSheafExtPrecomp R a
          (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T)) (n + 1)).app G =
      (moduleLocallyClosedSheafExtPrecomp R a
          (ExposeI.nestedDifferenceSupportWitness W (ExposeI.nestedClosedSubspace W T)) n).app G ≫
        (moduleNestedSheafExtBoundary R E W T n).app G :=
  ExposeI.rightDerivedFunctorBoundary_natTrans
    (moduleNestedSheafHomSequence_injective R F W T)
    (moduleNestedSheafHomSequence_injective R E W T)
    (moduleNestedSheafHomSequencePrecomp R a W T) G n

end SGA.SGA2.ExposeVI
