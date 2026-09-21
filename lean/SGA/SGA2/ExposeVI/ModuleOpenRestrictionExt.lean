/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleOpenRestriction
import SGA.SGA2.ExposeVI.ModuleSheafExtLocal

/-!
# Local module Ext on actual open restrictions

The local module Ext presheaf evaluates to Ext between the actual restricted
module sheaves. The comparison retains the coefficient maps. This proves
the ordinary-support case of VI.1.2 and supplies the restriction comparison
needed for the open-complement sequence in VI.1.9.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- The actual sheaf-over Hom equivalence is additive. -/
def moduleLocalHomSheafOverAddEquiv (F G : SheafOfModules.{u} R) (U : Opens X) :
    moduleLocalHom F.val G.val U ≃+ (F.over U ⟶ G.over U) :=
  { moduleLocalHomSheafOverEquiv F G U with map_add' := fun _ _ => rfl }

/-- Local linear Hom is naturally Hom between actual restricted module sheaves. -/
def moduleHomSectionsRestrictionIso (F : SheafOfModules.{u} R) (U : Opens X) :
    (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
      moduleOpenRestriction R U ⋙ preadditiveCoyoneda.obj (op (F.over U)) :=
  NatIso.ofComponents (fun G => (moduleLocalHomSheafOverAddEquiv R F G U).toAddCommGrpIso)
    (fun f => by ext φ; rfl)

/-- Local module Ext evaluates to genuine Ext on each open, naturally in the
coefficient module sheaf. No restriction-preserves-injectives hypothesis is needed. -/
def moduleExtPresheafEvalIso (F : SheafOfModules.{u} R) (U : Opens X) (n : ℕ) :
    moduleExtPresheafFunctor R F n ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
        moduleOpenRestriction R U ⋙ Abelian.extFunctorObj (F.over U) n := by
  let := ExposeI.abelianSheafToPresheaf_additive (X := X)
  let := ExposeI.abelianPresheafEvaluation_additive (X := X) (op U)
  let : ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).PreservesHomology :=
    inferInstance
  exact (ExposeI.rightDerivedPostcomposeIso
    (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) n).symm ≪≫
      ExposeI.rightDerivedFunctorIso (moduleHomSectionsRestrictionIso R F U) n ≪≫
      ExposeI.rightDerivedPrecomposeIso (moduleOpenRestriction R U)
        (preadditiveCoyoneda.obj (op (F.over U))) n ≪≫
      Functor.isoWhiskerLeft (moduleOpenRestriction R U)
        (ExposeI.rightDerivedCoyonedaNatIsoExt (F.over U) n)

/-- Sections of the local Ext presheaf are the actual Ext groups of restrictions. -/
def moduleExtPresheafSectionsEquiv (F G : SheafOfModules.{u} R)
    (U : Opens X) (n : ℕ) :
    ((moduleExtPresheafFunctor R F n).obj G).obj (op U) ≃+
      Abelian.Ext (F.over U) (G.over U) n :=
  ((moduleExtPresheafEvalIso R F U n).app G).addCommGroupIsoToAddEquiv

/-- The local Ext identification carries coefficient maps to Ext postcomposition. -/
theorem moduleExtPresheafSectionsEquiv_naturality (F : SheafOfModules.{u} R)
    {G G' : SheafOfModules.{u} R} (f : G ⟶ G') (U : Opens X) (n : ℕ)
    (x : ((moduleExtPresheafFunctor R F n).obj G).obj (op U)) :
    moduleExtPresheafSectionsEquiv R F G' U n
        (((moduleExtPresheafFunctor R F n).map f).app (op U) x) =
      (Abelian.Ext.mk₀ ((moduleOpenRestriction R U).map f)).postcomp _ (add_zero n)
        (moduleExtPresheafSectionsEquiv R F G U n x) :=
  ConcreteCategory.congr_hom ((moduleExtPresheafEvalIso R F U n).hom.naturality f) x

end SGA.SGA2.ExposeVI
