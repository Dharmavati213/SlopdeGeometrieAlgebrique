/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedHom
import SGA.SGA2.ExposeI.InternalHomPrecomposition
import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# I.1.7: ringed-space versions of the internal Hom identities

On an arbitrary ringed space the module-linear internal Hom is the linear
subobject of the additive internal Hom of Exposé I. Global maps out of the
structure sheaf into a supported module sheaf recover supported sections
(I.1.6 for Modules). First-variable precomposition is the already constructed
module precomposition, which sits inside additive precomposition.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- **I.1.7 / I.1.6, ringed spaces:** maps from the structure sheaf into the
supported module sheaf are the actual supported sections. -/
def ringedSpaceSupportHomEquiv (Z : Closeds X) (F : SheafOfModules.{u} R) :
    (SheafOfModules.unit R ⟶ ExposeVI.moduleGammaZSheaf R Z F) ≃
      (ExposeVI.moduleGammaZSheaf R Z F).sections :=
  SheafOfModules.unitHomEquiv _

/-- The sections of the supported structure-module sheaf are the original
supported sections of the underlying additive sheaf. -/
theorem ringedSpaceSupportSections_toAddSubgroup (Z : Closeds X)
    (F : SheafOfModules.{u} R) (U : Opens X) :
    (ExposeV.moduleGammaZSections R Z U F).toAddSubgroup =
      gammaZSections ((SheafOfModules.toSheaf R).obj F) Z U :=
  ExposeV.moduleGammaZSections_toAddSubgroup R Z U F

/-- **I.1.7:** first-variable identity precomposition of module-linear Hom
is the identity, as for additive Hom. -/
theorem moduleSheafHomAbPrecomp_id (F G : SheafOfModules.{u} R) :
    ExposeVI.moduleSheafHomAbPrecomp (Opens.grothendieckTopology X) (𝟙 F) G = 𝟙 _ := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  apply ExposeVI.moduleLocalHom_ext
  intro V x
  rfl

end SGA.SGA2.ExposeI
