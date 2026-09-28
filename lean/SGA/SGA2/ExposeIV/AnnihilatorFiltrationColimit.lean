/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedLocallyArtinian

/-!
# The representing module as the colimit of its actual annihilators

The filtration maps here are the literal submodule inclusions. The original
representation identifies the original diagram `T(R/Jⁿ)` with this filtration,
and its original colimit cocone with the actual inclusions into the representing
module. This proves a categorical colimit, not only an elementwise union.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The actual ideal-power annihilator filtration, with inclusion maps. -/
def annihilatorFiltration (J : Ideal R) (H : ModuleCat.{u} R) : ℕ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (Submodule.torsionBySet R H (J ^ n : Ideal R))
  map f := ModuleCat.ofHom (Submodule.inclusion (torsionBySet_pow_monotone J H (leOfHom f)))

/-- The actual inclusions into the original module form a cocone. -/
def annihilatorFiltrationCocone (J : Ideal R) (H : ModuleCat.{u} R) :
    Cocone (annihilatorFiltration J H) where
  pt := H
  ι := { app n := ModuleCat.ofHom (Submodule.torsionBySet R H (J ^ n : Ideal R)).subtype }

variable [IsNoetherianRing R]
variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u})
    [T.Additive] [PreservesFiniteLimits T]

/-- The original quotient-functor diagram is naturally the actual annihilator
filtration of its colimit, including all original transition maps. -/
def supportedFunctorAnnihilatorDiagramIso :
    supportedFunctorDiagram J T ≅ annihilatorFiltration J (supportedFunctorColimit J T) :=
  NatIso.ofComponents (supportedFunctorStageAnnihilatorIso J T) (fun {n m} f => by
    apply ModuleCat.hom_ext
    ext t
    apply Subtype.ext
    change ((supportedFunctorStageAnnihilatorIso J T m).hom
      (supportedFunctorTransition J T (leOfHom f) t) : supportedFunctorColimit J T) =
        ((supportedFunctorStageAnnihilatorIso J T n).hom t : supportedFunctorColimit J T)
    exact (supportedFunctorStageAnnihilatorIso_apply J T m _).trans
      ((ConcreteCategory.congr_hom (supportedFunctorColimitι_transition J T (leOfHom f)) t).trans
        (supportedFunctorStageAnnihilatorIso_apply J T n t).symm))

/-- The original colimit cocone is the actual annihilator cocone transported
along the specified diagram isomorphism. -/
def supportedFunctorAnnihilatorCoconeIso :
    colimit.cocone (supportedFunctorDiagram J T) ≅
      (Cocone.precompose (supportedFunctorAnnihilatorDiagramIso J T).hom).obj
        (annihilatorFiltrationCocone J (supportedFunctorColimit J T)) :=
  Cocone.ext (Iso.refl _) (fun n => by
    apply ModuleCat.hom_ext
    ext t
    exact (supportedFunctorStageAnnihilatorIso_apply J T n t).symm)

/-- The literal annihilator filtration has the original representing module
as its categorical colimit. -/
def supportedFunctorAnnihilatorFiltrationIsColimit :
    IsColimit (annihilatorFiltrationCocone J (supportedFunctorColimit J T)) :=
  (IsColimit.precomposeHomEquiv (supportedFunctorAnnihilatorDiagramIso J T) _)
    (IsColimit.ofIsoColimit (colimit.isColimit (supportedFunctorDiagram J T))
      (supportedFunctorAnnihilatorCoconeIso J T))

end SGA.SGA2.ExposeIV
