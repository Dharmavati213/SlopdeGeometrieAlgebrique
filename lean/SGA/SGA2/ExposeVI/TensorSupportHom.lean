/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.SheafTensorHom
import SGA.SGA2.ExposeVI.ModuleClosedSupportObject
import SGA.SGA2.ExposeVI.ModuleSupportedExt

/-!
# SGA 2, VI.1.4: the structure-module and tensor-support Hom representations

For a commutative ring sheaf and closed support, both formulas use the actual
module support object constructed from extension by zero and the actual
sheafification of the sectionwise tensor product. The tensor-Hom adjunction
is proved in `SheafTensorHom`, not assumed. Deriving this natural comparison
identifies supported Ext with ordinary Ext from the supported tensor source.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (S : Sheaf CommRingCat.{u} X)

/-- **VI.1.4.1**, in module sheaves: the actual structure support module
represents supported sections of the actual internal Hom module sheaf. -/
def moduleSupportedHomStructureEquiv
    (F G : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (Z : Closeds X) :
    ExposeI.gammaZ (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z ≃+
      (moduleClosedSupport (commRingSheafToRing (Opens.grothendieckTopology X) S) Z ⟶
        moduleSheafHom (Opens.grothendieckTopology X) F G) :=
  (moduleClosedSupportHomEquiv _ Z (moduleSheafHom (Opens.grothendieckTopology X) F G)).symm

/-- **VI.1.4.2:** actual maps from `O_(X,Z) ⊗ F` are the original supported linear Hom. -/
def tensorSupportHomEquiv
    (F G : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (Z : Closeds X) :
    (moduleSheafTensor (Opens.grothendieckTopology X) S
      (moduleClosedSupport (commRingSheafToRing (Opens.grothendieckTopology X) S) Z) F ⟶ G) ≃+
      ExposeI.gammaZ (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z :=
  (moduleSheafTensorHomEquiv (Opens.grothendieckTopology X) S _ F G).trans
    (moduleSupportedHomStructureEquiv S F G Z).symm

/-- **VI.1.4.2**, in the direction displayed in the source. -/
def VI_1_4_2
    (F G : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (Z : Closeds X) :
    ExposeI.gammaZ (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z ≃+
      (moduleSheafTensor (Opens.grothendieckTopology X) S
        (moduleClosedSupport (commRingSheafToRing (Opens.grothendieckTopology X) S) Z) F ⟶ G) :=
  (tensorSupportHomEquiv S F G Z).symm

/-- The tensor-support representation retains the actual coefficient postcomposition. -/
theorem tensorSupportHomEquiv_naturality
    (F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    {G H : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S)}
    (a : G ⟶ H) (Z : Closeds X)
    (φ : moduleSheafTensor (Opens.grothendieckTopology X) S
      (moduleClosedSupport (commRingSheafToRing (Opens.grothendieckTopology X) S) Z) F ⟶ G) :
    tensorSupportHomEquiv S F H Z (φ ≫ a) =
      (moduleSupportedHomFunctor _ F Z).map a (tensorSupportHomEquiv S F G Z φ) := by
  change moduleClosedSupportHomEquiv _ Z _
      (moduleSheafTensorHomEquiv _ S _ F H (φ ≫ a)) = _
  rw [moduleSheafTensorHomEquiv_naturality, moduleClosedSupportHomEquiv_naturality]
  rfl

/-- The tensor-support representation also retains precomposition in the source module. -/
theorem tensorSupportHomEquiv_precomp
    {E F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S)}
    (a : E ⟶ F)
    (G : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (Z : Closeds X)
    (φ : moduleSheafTensor (Opens.grothendieckTopology X) S
      (moduleClosedSupport (commRingSheafToRing (Opens.grothendieckTopology X) S) Z) F ⟶ G) :
    tensorSupportHomEquiv S E G Z
        (moduleSheafTensorMap (Opens.grothendieckTopology X) S (𝟙 _) a ≫ φ) =
      ExposeI.gammaZSectionsMap
        (moduleSheafHomAbPrecomp (Opens.grothendieckTopology X) a G) Z ⊤
          (tensorSupportHomEquiv S F G Z φ) := by
  change moduleClosedSupportHomEquiv _ Z _
      (moduleSheafTensorHomEquiv _ S _ E G (_ ≫ φ)) = _
  rw [moduleSheafTensorHomEquiv_precomp, moduleClosedSupportHomEquiv_naturality]
  rfl

/-- The ordinary representable functor of the actual tensor source is naturally supported Hom. -/
def tensorSupportHomFunctorIso
    (F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (Z : Closeds X) :
    preadditiveCoyoneda.obj (op (moduleSheafTensor (Opens.grothendieckTopology X) S
        (moduleClosedSupport (commRingSheafToRing (Opens.grothendieckTopology X) S) Z) F)) ≅
      moduleSupportedHomFunctor _ F Z :=
  NatIso.ofComponents (fun G ↦ (tensorSupportHomEquiv S F G Z).toAddCommGrpIso)
    (fun a ↦ by ext φ; exact tensorSupportHomEquiv_naturality S F a Z φ)

/-- **VI.1.4, θ:** the original right-derived supported Hom equals ordinary
Ext from the actual tensor of the support module and the source sheaf. -/
def moduleSupportedExtTensorIso
    (F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (Z : Closeds X) (n : ℕ) :
    moduleSupportedExtFunctor _ F Z n ≅
      extFunctorObj (moduleSheafTensor (Opens.grothendieckTopology X) S
        (moduleClosedSupport (commRingSheafToRing (Opens.grothendieckTopology X) S) Z) F) n :=
  (ExposeI.rightDerivedFunctorIso (tensorSupportHomFunctorIso S F Z) n).symm ≪≫
    ExposeI.rightDerivedCoyonedaNatIsoExt _ n

end SGA.SGA2.ExposeVI
