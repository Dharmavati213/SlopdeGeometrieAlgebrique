/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.FiniteProjectiveResolution
import SGA.SGA2.ExposeV.HomLocalization
import SGA.SGA2.ExposeV.ModuleExtPairing
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-!
# Localization of the original module-valued Ext

A degreewise finite projective resolution remains a genuine projective
resolution after exact localization. The original Hom localization comparison
commutes with its differentials. Passing to the actual homology objects gives
an isomorphism between localized original Ext and original Ext over the
localized ring. Only the first argument has to be finite.
-/

noncomputable section
universe u
open CategoryTheory HomologicalComplex

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- Termwise Hom localization is an isomorphism of the original cochain
complexes, including their actual differentials. -/
def localizedLinearYonedaObjIso (P : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ i, Module.FinitePresentation R (P.X i)] (N : ModuleCat.{u} R) :
    ((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex _).obj
        (P.linearYonedaObj R N) ≅
      ChainComplex.linearYonedaObj
        (((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex _).obj P)
        (Localization S) (N.localizedModule S) :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ localizedHomIso S (P.X i) N)
    (fun i j _ ↦ (localizedHomIso_precomp S N (P.d j i)).symm)

variable [IsNoetherianRing R]

/-- **V.3.5, Ext base change:** original module-valued Ext localizes to
original Ext over the localized ring. The first argument is finite; the
second is arbitrary. The result is linear over the localized ring. -/
def moduleExtLocalizationIso (M N : ModuleCat.{u} R) [Module.Finite R M] (i : ℕ) :
    (moduleExtValue M N i).localizedModule S ≅
      moduleExtValue (M.localizedModule S) (N.localizedModule S) i := by
  let P := finiteProjectiveResolution M
  have (j : ℕ) : Module.FinitePresentation R (P.complex.X j) :=
    Module.finitePresentation_of_finite R _
  let G := ModuleCat.localizedModuleFunctor S
  exact G.mapIso (P.isoExt i N) ≪≫
    (((P.complex.linearYonedaObj R N).sc i).mapHomologyIso G).symm ≪≫
    (homologyFunctor (ModuleCat (Localization S)) (ComplexShape.up ℕ) i).mapIso
      (localizedLinearYonedaObjIso S P.complex N) ≪≫
    ((G.mapProjectiveResolution P).isoExt i (N.localizedModule S)).symm

/-- The same comparison with actual ring coefficients on both sides. -/
def moduleExtLocalizationRingIso (M : ModuleCat.{u} R) [Module.Finite R M] (i : ℕ) :
    (moduleExtValue M (ModuleCat.of R R) i).localizedModule S ≅
      moduleExtValue (M.localizedModule S) (ModuleCat.of (Localization S) (Localization S)) i :=
  moduleExtLocalizationIso S M (ModuleCat.of R R) i ≪≫
    ((_root_.Ext (Localization S) (ModuleCat (Localization S)) i).obj
      (Opposite.op (M.localizedModule S))).mapIso (localizedRingModuleIso S)

/-- Vanishing of the unshrunk original localization is equivalent to
vanishing of the actual Ext module over the localized ring. -/
theorem localizedModule_ext_subsingleton_iff (M N : ModuleCat.{u} R)
    [Module.Finite R M] (i : ℕ) :
    Subsingleton (LocalizedModule S (moduleExtValue M N i)) ↔
      Subsingleton (moduleExtValue (M.localizedModule S) (N.localizedModule S) i) :=
  (Equiv.subsingleton_congr (equivShrink (LocalizedModule S (moduleExtValue M N i)))).trans
    (moduleExtLocalizationIso S M N i).toLinearEquiv.toEquiv.subsingleton_congr

/-- Ring-coefficient vanishing, stated on the original localization model. -/
theorem localizedModule_ext_ring_subsingleton_iff (M : ModuleCat.{u} R)
    [Module.Finite R M] (i : ℕ) :
    Subsingleton (LocalizedModule S (moduleExtValue M (ModuleCat.of R R) i)) ↔
      Subsingleton (moduleExtValue (M.localizedModule S)
        (ModuleCat.of (Localization S) (Localization S)) i) :=
  (Equiv.subsingleton_congr
    (equivShrink (LocalizedModule S (moduleExtValue M (ModuleCat.of R R) i)))).trans
    (moduleExtLocalizationRingIso S M i).toLinearEquiv.toEquiv.subsingleton_congr

end SGA.SGA2.ExposeV
