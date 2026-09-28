/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.LocallyClosedExtSequences

/-!
# SGA 2, VI.1.8: the supported sheaf Ext sequence

The original locally closed supported Hom sheaves form a short exact sequence
on injective module coefficients. Deriving in module sheaves gives a long
exact sequence of the original supported sheaf Ext functors.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (F : SheafOfModules.{u} R)
  (W : ExposeI.LocallyClosedIn X) (T : Closeds W.asSet)

/-- Actual support inclusion for the locally closed linear Hom sheaves. -/
def moduleNestedSheafHomInclusion :
    moduleLocallyClosedSheafHomFunctor R F
        (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T)) ⟶
      moduleLocallyClosedSheafHomFunctor R F W :=
  Functor.whiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
    (ExposeI.locallyClosedNestedSheafInclusion W (ExposeI.nestedClosedSubspace W T))

/-- Actual restriction to the locally closed support difference. -/
def moduleNestedSheafHomRestriction :
    moduleLocallyClosedSheafHomFunctor R F W ⟶
      moduleLocallyClosedSheafHomFunctor R F
        (ExposeI.nestedDifferenceSupportWitness W (ExposeI.nestedClosedSubspace W T)) :=
  Functor.whiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
    (ExposeI.locallyClosedNestedSheafRestriction W (ExposeI.nestedClosedSubspace W T))

/-- The original support maps give a short complex of module-sheaf functors. -/
def moduleNestedSheafHomSequence :
    ShortComplex (SheafOfModules.{u} R ⥤ Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (moduleNestedSheafHomInclusion R F W T)
    (moduleNestedSheafHomRestriction R F W T) (by
      ext G
      exact congrArg (fun a ↦ a.app
        ((moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).obj G))
          (ExposeI.locallyClosedNestedSheaf_comp W (ExposeI.nestedClosedSubspace W T)))

local instance : (moduleNestedSheafHomSequence R F W T).X₁.Additive :=
  inferInstanceAs (moduleLocallyClosedSheafHomFunctor R F _).Additive

local instance : (moduleNestedSheafHomSequence R F W T).X₂.Additive :=
  inferInstanceAs (moduleLocallyClosedSheafHomFunctor R F W).Additive

local instance : (moduleNestedSheafHomSequence R F W T).X₃.Additive :=
  inferInstanceAs (moduleLocallyClosedSheafHomFunctor R F _).Additive

/-- Hom flasqueness proves short exactness on every injective module sheaf. -/
theorem moduleNestedSheafHomSequence_injective (G : SheafOfModules.{u} R) [Injective G] :
    ((moduleNestedSheafHomSequence R F W T).map
      ((evaluation (SheafOfModules.{u} R) (Sheaf AddCommGrpCat.{u} X)).obj G)).ShortExact := by
  let := moduleSheafHomAb_isFlasque_of_injective R F G
  exact ExposeI.locallyClosedNestedSheafSequence_shortExact W
    (ExposeI.nestedClosedSubspace W T) (moduleSheafHomAb (Opens.grothendieckTopology X) F G)

/-- The genuine connecting map between original supported sheaf Ext functors. -/
def moduleNestedSheafExtBoundary (n : ℕ) :
    moduleLocallyClosedSheafExtFunctor R F
        (ExposeI.nestedDifferenceSupportWitness W (ExposeI.nestedClosedSubspace W T)) n ⟶
      moduleLocallyClosedSheafExtFunctor R F
        (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T)) (n + 1) :=
  ExposeI.rightDerivedFunctorBoundary (moduleNestedSheafHomSequence R F W T)
    (moduleNestedSheafHomSequence_injective R F W T) n

/-- Six consecutive original supported sheaf Ext terms. -/
def moduleNestedSheafExtSequence (G : SheafOfModules.{u} R) (n : ℕ) :
    ComposableArrows (Sheaf AddCommGrpCat.{u} X) 5 :=
  ExposeI.rightDerivedFunctorSequence (moduleNestedSheafHomSequence R F W T)
    (moduleNestedSheafHomSequence_injective R F W T) G n

/-- The actual supported sheaf Ext sequence is exact in all degrees. -/
theorem moduleNestedSheafExtSequence_exact (G : SheafOfModules.{u} R) (n : ℕ) :
    (moduleNestedSheafExtSequence R F W T G n).Exact :=
  ExposeI.rightDerivedFunctorSequence_exact (moduleNestedSheafHomSequence R F W T)
    (moduleNestedSheafHomSequence_injective R F W T) G n

/-- The supported sheaf Ext sequence begins with a monomorphism. -/
theorem moduleNestedSheafExtInclusion_zero_mono (G : SheafOfModules.{u} R) :
    Mono (((moduleNestedSheafHomInclusion R F W T).rightDerived 0).app G) :=
  ExposeI.rightDerivedFunctorSequence_zero_mono (moduleNestedSheafHomSequence R F W T)
    (moduleNestedSheafHomSequence_injective R F W T) G

end SGA.SGA2.ExposeVI
