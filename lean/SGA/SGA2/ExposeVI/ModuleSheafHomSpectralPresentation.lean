/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedExt
import SGA.SGA2.ExposeVI.SheafFunctorSpectralSequence

/-!
# The topological-sheaf presentation of the original local linear Hom functor

The original functor is declared for sheaves on the open-set site. Giving
its identical topological-sheaf presentation a separate name keeps the
spectral construction from repeatedly unfolding concrete local linear maps.
An explicit natural isomorphism identifies the derived values with the
unchanged original sheaf Ext functor.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (F : SheafOfModules.{u} R)

/-- The unchanged local linear Hom functor, with its topological sheaf codomain explicit. -/
def moduleSheafHomTopFunctor : SheafOfModules.{u} R ⥤ Sheaf AddCommGrpCat.{u} X :=
  moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F

instance : (moduleSheafHomTopFunctor R F).Additive := by
  have : (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).Additive := inferInstance
  exact inferInstanceAs (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).Additive

/-- The presentation change retains the original coefficient and restriction maps. -/
def moduleSheafHomTopFunctorIso :
    moduleSheafHomTopFunctor R F ≅ moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F :=
  Iso.refl _

/-- The topological-sheaf presentation derives to the unchanged original sheaf Ext. -/
def moduleSheafHomTopRightDerivedIso (q : ℕ) :
    (moduleSheafHomTopFunctor R F).rightDerived q ≅ moduleSheafExtAbFunctor R F q :=
  letI : (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).Additive := inferInstance
  ExposeI.rightDerivedFunctorIso (moduleSheafHomTopFunctorIso R F) q ≪≫
    sheafFunctorRightDerivedPresentationIso
      (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F) q

end SGA.SGA2.ExposeVI
