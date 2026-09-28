/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleHomInjectiveFlasque
import SGA.SGA2.ExposeVI.ModuleSupportedExt
import SGA.SGA2.ExposeI.LocallyClosedNestedGamma
import SGA.SGA2.ExposeI.LocallyClosedNestedSheafSequence
import SGA.SGA2.ExposeI.LocallyClosedLocalToGlobalResolution
import SGA.SGA2.ExposeI.RightDerivedFunctorSequence
import SGA.SGA2.ExposeI.RightDerivedZeroNaturality

/-!
# SGA 2, VI.1.8: the actual supported Ext long exact sequences

Apply the original nested-support sequences to the local linear Hom sheaf,
then derive the resulting functors in the category of module sheaves.
The sequences are short exact on injective module sheaves because their
local Hom sheaves are flasque. This gives the actual supported Ext groups
and supported sheaf Ext, with genuine connecting maps, for arbitrary locally
closed supports and closed subsets of their literal support spaces.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- The original global supported Hom functor is supported sections of the
actual local-linear Hom sheaf, naturally in its coefficient module. -/
def moduleLocallyClosedSupportedHomGammaIso (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) :
    moduleLocallyClosedSupportedHomFunctor R F W ≅
      moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        ExposeI.gammaLocallyClosedFunctor W :=
  Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
    (ExposeI.underlineGammaLocallyClosedGlobalSectionsIso W)

variable (F : SheafOfModules.{u} R) (W : ExposeI.LocallyClosedIn X)
  (T : Closeds W.asSet)

/-- Inclusion of supported Hom for a closed subset of the original support. -/
def moduleNestedSupportedHomInclusion :
    moduleLocallyClosedSupportedHomFunctor R F
        (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T)) ⟶
      moduleLocallyClosedSupportedHomFunctor R F W :=
  (moduleLocallyClosedSupportedHomGammaIso R F _).hom ≫
    Functor.whiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
      (ExposeI.locallyClosedNestedGammaInclusion W (ExposeI.nestedClosedSubspace W T)) ≫
        (moduleLocallyClosedSupportedHomGammaIso R F W).inv

/-- Restriction of supported Hom to the complementary locally closed subset. -/
def moduleNestedSupportedHomRestriction :
    moduleLocallyClosedSupportedHomFunctor R F W ⟶
      moduleLocallyClosedSupportedHomFunctor R F
        (ExposeI.nestedDifferenceSupportWitness W (ExposeI.nestedClosedSubspace W T)) :=
  (moduleLocallyClosedSupportedHomGammaIso R F W).hom ≫
    Functor.whiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
      (ExposeI.locallyClosedNestedGammaRestriction W (ExposeI.nestedClosedSubspace W T)) ≫
        (moduleLocallyClosedSupportedHomGammaIso R F _).inv

/-- The supported-Hom inclusion followed by restriction is zero. -/
theorem moduleNestedSupportedHom_comp :
    moduleNestedSupportedHomInclusion R F W T ≫
      moduleNestedSupportedHomRestriction R F W T = 0 := by
  simp only [moduleNestedSupportedHomInclusion, moduleNestedSupportedHomRestriction,
    Category.assoc, Iso.inv_hom_id_assoc]
  ext G
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.app_zero]
  rw [← Category.assoc _ _ ((moduleLocallyClosedSupportedHomGammaIso R F _).inv.app G),
    ← NatTrans.comp_app, ExposeI.locallyClosedNestedGamma_comp, NatTrans.app_zero,
    zero_comp, comp_zero]

/-- The actual supported-Hom coefficient functors form a short complex. -/
def moduleNestedSupportedHomSequence :
    ShortComplex (SheafOfModules.{u} R ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.mk (moduleNestedSupportedHomInclusion R F W T)
    (moduleNestedSupportedHomRestriction R F W T) (moduleNestedSupportedHom_comp R F W T)

/-- Its objectwise comparison retains the original supported-section maps. -/
def moduleNestedSupportedHomSequenceIso (G : SheafOfModules.{u} R) :
    (moduleNestedSupportedHomSequence R F W T).map
        ((evaluation (SheafOfModules.{u} R) AddCommGrpCat.{u}).obj G) ≅
      ExposeI.locallyClosedNestedGammaSequence W (ExposeI.nestedClosedSubspace W T)
        (moduleSheafHomAb (Opens.grothendieckTopology X) F G) :=
  ShortComplex.isoMk ((moduleLocallyClosedSupportedHomGammaIso R F _).app G)
    ((moduleLocallyClosedSupportedHomGammaIso R F _).app G)
    ((moduleLocallyClosedSupportedHomGammaIso R F _).app G)
    (by simp [moduleNestedSupportedHomSequence, moduleNestedSupportedHomInclusion,
      ExposeI.locallyClosedNestedGammaSequence, ExposeI.locallyClosedNestedGammaFunctorSequence,
      moduleSheafHomAbFunctor])
    (by simp [moduleNestedSupportedHomSequence, moduleNestedSupportedHomRestriction,
      ExposeI.locallyClosedNestedGammaSequence, ExposeI.locallyClosedNestedGammaFunctorSequence,
      moduleSheafHomAbFunctor])

local instance : (moduleNestedSupportedHomSequence R F W T).X₁.Additive :=
  inferInstanceAs (moduleLocallyClosedSupportedHomFunctor R F _).Additive

local instance : (moduleNestedSupportedHomSequence R F W T).X₂.Additive :=
  inferInstanceAs (moduleLocallyClosedSupportedHomFunctor R F W).Additive

local instance : (moduleNestedSupportedHomSequence R F W T).X₃.Additive :=
  inferInstanceAs (moduleLocallyClosedSupportedHomFunctor R F _).Additive

/-- The necessary short exactness is proved for injective module coefficients. -/
theorem moduleNestedSupportedHomSequence_injective (G : SheafOfModules.{u} R)
    [Injective G] :
    ((moduleNestedSupportedHomSequence R F W T).map
      ((evaluation (SheafOfModules.{u} R) AddCommGrpCat.{u}).obj G)).ShortExact := by
  let := moduleSheafHomAb_isFlasque_of_injective R F G
  exact ShortComplex.shortExact_of_iso (moduleNestedSupportedHomSequenceIso R F W T G).symm
    (ExposeI.locallyClosedNestedGammaSequence_shortExact W (ExposeI.nestedClosedSubspace W T) _)

/-- The actual derived support-increasing map. -/
def moduleNestedSupportedExtInclusion (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F
        (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T)) n ⟶
      moduleLocallyClosedSupportedExtFunctor R F W n :=
  (moduleNestedSupportedHomInclusion R F W T).rightDerived n

/-- The actual derived restriction to the support difference. -/
def moduleNestedSupportedExtRestriction (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F W n ⟶
      moduleLocallyClosedSupportedExtFunctor R F
        (ExposeI.nestedDifferenceSupportWitness W (ExposeI.nestedClosedSubspace W T)) n :=
  (moduleNestedSupportedHomRestriction R F W T).rightDerived n

/-- In degree zero the derived support-increasing arrow is the original inclusion. -/
@[reassoc]
theorem moduleNestedSupportedExtInclusion_zero (G : SheafOfModules.{u} R) :
    (moduleNestedSupportedExtInclusion R F W T 0).app G ≫
        (moduleLocallyClosedSupportedExtZeroIso R F W).hom.app G =
      (moduleLocallyClosedSupportedExtZeroIso R F
          (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T))).hom.app G ≫
        (moduleNestedSupportedHomInclusion R F W T).app G :=
  ExposeI.rightDerivedZeroIsoSelf_natTrans (moduleNestedSupportedHomInclusion R F W T) G

/-- In degree zero the derived restriction is the original supported-Hom restriction. -/
@[reassoc]
theorem moduleNestedSupportedExtRestriction_zero (G : SheafOfModules.{u} R) :
    (moduleNestedSupportedExtRestriction R F W T 0).app G ≫
        (moduleLocallyClosedSupportedExtZeroIso R F
          (ExposeI.nestedDifferenceSupportWitness W (ExposeI.nestedClosedSubspace W T))).hom.app G =
      (moduleLocallyClosedSupportedExtZeroIso R F W).hom.app G ≫
        (moduleNestedSupportedHomRestriction R F W T).app G :=
  ExposeI.rightDerivedZeroIsoSelf_natTrans (moduleNestedSupportedHomRestriction R F W T) G

/-- The genuine connecting transformation of the supported Ext sequence. -/
def moduleNestedSupportedExtBoundary (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F
        (ExposeI.nestedDifferenceSupportWitness W (ExposeI.nestedClosedSubspace W T)) n ⟶
      moduleLocallyClosedSupportedExtFunctor R F
        (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T)) (n + 1) :=
  ExposeI.rightDerivedFunctorBoundary (moduleNestedSupportedHomSequence R F W T)
    (moduleNestedSupportedHomSequence_injective R F W T) n

/-- Six consecutive terms of VI.1.8, with the original supported Ext groups. -/
def moduleNestedSupportedExtSequence (G : SheafOfModules.{u} R) (n : ℕ) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  ComposableArrows.mk₅ ((moduleNestedSupportedExtInclusion R F W T n).app G)
    ((moduleNestedSupportedExtRestriction R F W T n).app G)
    ((moduleNestedSupportedExtBoundary R F W T n).app G)
    ((moduleNestedSupportedExtInclusion R F W T (n + 1)).app G)
    ((moduleNestedSupportedExtRestriction R F W T (n + 1)).app G)

/-- **VI.1.8:** actual supported Ext is exact for every locally closed support
and every closed subset of it, in all degrees. -/
theorem moduleNestedSupportedExtSequence_exact (G : SheafOfModules.{u} R) (n : ℕ) :
    (moduleNestedSupportedExtSequence R F W T G n).Exact :=
  ExposeI.rightDerivedFunctorSequence_exact (moduleNestedSupportedHomSequence R F W T)
    (moduleNestedSupportedHomSequence_injective R F W T) G n

/-- The supported Ext sequence starts with a monomorphism in degree zero. -/
theorem moduleNestedSupportedExtInclusion_zero_mono (G : SheafOfModules.{u} R) :
    Mono ((moduleNestedSupportedExtInclusion R F W T 0).app G) :=
  ExposeI.rightDerivedFunctorSequence_zero_mono (moduleNestedSupportedHomSequence R F W T)
    (moduleNestedSupportedHomSequence_injective R F W T) G

/-- The actual boundary commutes with every coefficient-module morphism. -/
@[reassoc]
theorem moduleNestedSupportedExtBoundary_naturality
    {G H : SheafOfModules.{u} R} (a : G ⟶ H) (n : ℕ) :
    (moduleLocallyClosedSupportedExtFunctor R F
          (ExposeI.nestedDifferenceSupportWitness W
            (ExposeI.nestedClosedSubspace W T)) n).map a ≫
        (moduleNestedSupportedExtBoundary R F W T n).app H =
      (moduleNestedSupportedExtBoundary R F W T n).app G ≫
        (moduleLocallyClosedSupportedExtFunctor R F
          (ExposeI.nestedClosedSupportWitness W
            (ExposeI.nestedClosedSubspace W T)) (n + 1)).map a :=
  (moduleNestedSupportedExtBoundary R F W T n).naturality a

end SGA.SGA2.ExposeVI
