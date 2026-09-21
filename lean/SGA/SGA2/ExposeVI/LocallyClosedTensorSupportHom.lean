/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.TensorSupportHom
import SGA.SGA2.ExposeVI.ModuleLocallyClosedSupportObject
import SGA.SGA2.ExposeVI.LocallyClosedExtSequences

/-!
# SGA 2, VI.1.4: tensor-support Hom and Ext for arbitrary locally closed supports

The structure support module is the sheafification of the actual relative
extension-by-zero cokernel. The tensor is the sheafification of the actual
local module tensor products. Their proved Hom representations give the
original locally closed supported Hom and its derived functors in every degree.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (S : Sheaf CommRingCat.{u} X)

/-- **VI.1.4.1** for an arbitrary locally closed subset, in actual module sheaves. -/
def moduleLocallyClosedSupportedHomStructureEquiv
    (F G : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (W : ExposeI.LocallyClosedIn X) :
    W.gamma (moduleSheafHomAb (Opens.grothendieckTopology X) F G) ≃+
      (moduleLocallyClosedSupport (commRingSheafToRing (Opens.grothendieckTopology X) S) W ⟶
        moduleSheafHom (Opens.grothendieckTopology X) F G) :=
  (moduleLocallyClosedSupportHomEquiv _ W
    (moduleSheafHom (Opens.grothendieckTopology X) F G)).symm

/-- **VI.1.4.2** for arbitrary locally closed support and the actual tensor product. -/
def locallyClosedTensorSupportHomEquiv
    (F G : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (W : ExposeI.LocallyClosedIn X) :
    (moduleSheafTensor (Opens.grothendieckTopology X) S
      (moduleLocallyClosedSupport
        (commRingSheafToRing (Opens.grothendieckTopology X) S) W) F ⟶ G) ≃+
      W.gamma (moduleSheafHomAb (Opens.grothendieckTopology X) F G) :=
  (moduleSheafTensorHomEquiv (Opens.grothendieckTopology X) S _ F G).trans
    (moduleLocallyClosedSupportedHomStructureEquiv S F G W).symm

/-- The locally closed tensor representation preserves the actual coefficient maps. -/
theorem locallyClosedTensorSupportHomEquiv_naturality
    (F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    {G H : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S)}
    (a : G ⟶ H) (W : ExposeI.LocallyClosedIn X)
    (φ : moduleSheafTensor (Opens.grothendieckTopology X) S
      (moduleLocallyClosedSupport (commRingSheafToRing (Opens.grothendieckTopology X) S) W) F ⟶ G) :
    locallyClosedTensorSupportHomEquiv S F H W (φ ≫ a) =
      (ExposeI.gammaLocallyClosedFunctor W).map
        ((moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).map a)
          (locallyClosedTensorSupportHomEquiv S F G W φ) := by
  change moduleLocallyClosedSupportHomEquiv _ W _
      (moduleSheafTensorHomEquiv _ S _ F H (φ ≫ a)) = _
  rw [moduleSheafTensorHomEquiv_naturality, moduleLocallyClosedSupportHomEquiv_naturality]
  rfl

/-- The locally closed tensor representation preserves actual source precomposition. -/
theorem locallyClosedTensorSupportHomEquiv_precomp
    {E F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S)}
    (a : E ⟶ F)
    (G : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (W : ExposeI.LocallyClosedIn X)
    (φ : moduleSheafTensor (Opens.grothendieckTopology X) S
      (moduleLocallyClosedSupport (commRingSheafToRing (Opens.grothendieckTopology X) S) W) F ⟶ G) :
    locallyClosedTensorSupportHomEquiv S E G W
        (moduleSheafTensorMap (Opens.grothendieckTopology X) S (𝟙 _) a ≫ φ) =
      (ExposeI.gammaLocallyClosedFunctor W).map
        (moduleSheafHomAbPrecomp (Opens.grothendieckTopology X) a G)
          (locallyClosedTensorSupportHomEquiv S F G W φ) := by
  change moduleLocallyClosedSupportHomEquiv _ W _
      (moduleSheafTensorHomEquiv _ S _ E G (_ ≫ φ)) = _
  rw [moduleSheafTensorHomEquiv_precomp, moduleLocallyClosedSupportHomEquiv_naturality]
  rfl

/-- The representable of the actual locally closed tensor source is the supported Hom functor. -/
def locallyClosedTensorSupportHomFunctorIso
    (F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (W : ExposeI.LocallyClosedIn X) :
    preadditiveCoyoneda.obj (op (moduleSheafTensor (Opens.grothendieckTopology X) S
        (moduleLocallyClosedSupport (commRingSheafToRing (Opens.grothendieckTopology X) S) W) F)) ≅
      moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        ExposeI.gammaLocallyClosedFunctor W :=
  NatIso.ofComponents (fun G ↦ (locallyClosedTensorSupportHomEquiv S F G W).toAddCommGrpIso)
    (fun a ↦ by ext φ; exact locallyClosedTensorSupportHomEquiv_naturality S F a W φ)

/-- The actual VI.1.1 locally closed supported-Hom functor has the tensor-source representation. -/
def moduleLocallyClosedSupportedHomTensorIso
    (F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (W : ExposeI.LocallyClosedIn X) :
    moduleLocallyClosedSupportedHomFunctor _ F W ≅
      preadditiveCoyoneda.obj (op (moduleSheafTensor (Opens.grothendieckTopology X) S
        (moduleLocallyClosedSupport (commRingSheafToRing (Opens.grothendieckTopology X) S) W) F)) :=
  moduleLocallyClosedSupportedHomGammaIso _ F W ≪≫
    (locallyClosedTensorSupportHomFunctorIso S F W).symm

/-- **VI.1.4, θ**, for arbitrary locally closed support: supported Ext is ordinary
module-sheaf Ext from the actual supported tensor source, in every derived degree. -/
def moduleLocallyClosedSupportedExtTensorIso
    (F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (W : ExposeI.LocallyClosedIn X) (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor _ F W n ≅
      extFunctorObj (moduleSheafTensor (Opens.grothendieckTopology X) S
        (moduleLocallyClosedSupport
          (commRingSheafToRing (Opens.grothendieckTopology X) S) W) F) n :=
  ExposeI.rightDerivedFunctorIso (moduleLocallyClosedSupportedHomTensorIso S F W) n ≪≫
    ExposeI.rightDerivedCoyonedaNatIsoExt _ n

end SGA.SGA2.ExposeVI
