/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.LocallyClosedTensorSupportHom
import SGA.SGA2.ExposeVI.ExtSequenceFirstVariable
import SGA.SGA2.ExposeI.ExtRightDerivedSource

/-!
# SGA 2, VI.1.4: source naturality of the derived tensor comparison

The canonical comparison of supported Ext with Ext from the literal tensor
source respects the actual contravariant module maps in every degree.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (S : Sheaf CommRingCat.{u} X)

/-- The original closed tensor-Hom representation commutes with source maps. -/
theorem tensorSupportHomFunctorIso_precomp
    {E F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S)}
    (a : E ⟶ F) (Z : Closeds X) :
    (tensorSupportHomFunctorIso S F Z).hom ≫ moduleSupportedHomPrecomp _ a Z =
      preadditiveCoyoneda.map
          (moduleSheafTensorMap (Opens.grothendieckTopology X) S (𝟙 _) a).op ≫
        (tensorSupportHomFunctorIso S E Z).hom := by
  apply NatTrans.ext
  funext G
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  exact (tensorSupportHomEquiv_precomp S a G Z φ).symm

/-- **VI.1.4, θ:** the actual closed-support Ext comparison is natural in its source. -/
@[reassoc]
theorem moduleSupportedExtTensorIso_precomp
    {E F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S)}
    (a : E ⟶ F)
    (G : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (Z : Closeds X) (n : ℕ) :
    (moduleSupportedExtPrecomp _ a Z n).app G ≫
        (moduleSupportedExtTensorIso S E Z n).hom.app G =
      (moduleSupportedExtTensorIso S F Z n).hom.app G ≫
        ((extFunctor n).map
          (moduleSheafTensorMap (Opens.grothendieckTopology X) S (𝟙 _) a).op).app G :=
  ExposeI.representedRightDerivedIso_precomp
    (moduleSheafTensorMap (Opens.grothendieckTopology X) S (𝟙 _) a)
    (tensorSupportHomFunctorIso S F Z) (tensorSupportHomFunctorIso S E Z)
    (moduleSupportedHomPrecomp _ a Z) (tensorSupportHomFunctorIso_precomp S a Z) G n

/-- The original locally closed tensor representation retains source precomposition. -/
theorem moduleLocallyClosedSupportedHomTensorIso_precomp
    {E F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S)}
    (a : E ⟶ F) (W : ExposeI.LocallyClosedIn X) :
    (moduleLocallyClosedSupportedHomTensorIso S F W).inv ≫
        moduleLocallyClosedSupportedHomPrecomp _ a W =
      preadditiveCoyoneda.map
          (moduleSheafTensorMap (Opens.grothendieckTopology X) S (𝟙 _) a).op ≫
        (moduleLocallyClosedSupportedHomTensorIso S E W).inv := by
  apply NatTrans.ext
  funext G
  apply (cancel_mono ((moduleLocallyClosedSupportedHomGammaIso _ E W).hom.app G)).mp
  simp only [moduleLocallyClosedSupportedHomTensorIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc, moduleLocallyClosedSupportedHomGammaIso_precomp,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  exact (locallyClosedTensorSupportHomEquiv_precomp S a G W φ).symm

/-- **VI.1.4, θ:** source naturality of the actual tensor comparison in every
degree and for every locally closed support. -/
@[reassoc]
theorem moduleLocallyClosedSupportedExtTensorIso_precomp
    {E F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S)}
    (a : E ⟶ F)
    (G : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (W : ExposeI.LocallyClosedIn X) (n : ℕ) :
    (moduleLocallyClosedSupportedExtPrecomp _ a W n).app G ≫
        (moduleLocallyClosedSupportedExtTensorIso S E W n).hom.app G =
      (moduleLocallyClosedSupportedExtTensorIso S F W n).hom.app G ≫
        ((extFunctor n).map
          (moduleSheafTensorMap (Opens.grothendieckTopology X) S (𝟙 _) a).op).app G :=
  ExposeI.representedRightDerivedIso_precomp
    (moduleSheafTensorMap (Opens.grothendieckTopology X) S (𝟙 _) a)
    (moduleLocallyClosedSupportedHomTensorIso S F W).symm
    (moduleLocallyClosedSupportedHomTensorIso S E W).symm
    (moduleLocallyClosedSupportedHomPrecomp _ a W)
    (moduleLocallyClosedSupportedHomTensorIso_precomp S a W) G n

end SGA.SGA2.ExposeVI
