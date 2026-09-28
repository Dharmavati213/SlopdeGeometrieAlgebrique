/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.OpenDerivedSupportedSheaves
import SGA.SGA2.ExposeI.SupportedSheafRestriction
import SGA.SGA2.ExposeII.AffineExtColimitComparison
import SGA.SGA2.ExposeIII.AffineChartSupportedCohomology
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# SGA 2, II.1–II.3: quasi-coherence of higher supported sheaves

On an open support the derived supported sheaves are higher direct images
(I.2.5). They restrict to affine charts by I.2.7. Associated sheaves on
affine schemes are quasi-coherent, and on a noetherian affine their
supported cohomology is algebraic local cohomology. This is the affine
chart form of II.3.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat AlgebraicGeometry Abelian
open SGA.SGA2.ExposeI
open SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

/-- **II.1, open support:** derived open-supported sheaves are higher
direct images of restriction. -/
def II_1_open {X : TopCat.{u}} (U : Opens X) (n : ℕ) :
    derivedUnderlineGammaLocallyClosed (LocallyClosedIn.ofOpen U) n ≅
      iShriek_open U ⋙
        (Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').rightDerived n :=
  derivedUnderlineGammaOfOpenIso U n

/-- Associated sheaves on an affine scheme are quasi-coherent. -/
instance affineTilde_isQuasicoherent (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent :=
  inferInstance

/-- **II.2 / II.4, noetherian affine:** the derived supported sheaf of an
associated module sheaf has global sections equal to algebraic local
cohomology, in every degree. -/
def II_2_affine_global [IsNoetherianRing R] (I : Ideal R)
    (M : ModuleCat.{u} R) (n : ℕ) :
    (_root_.localCohomology I n).obj M ≃+
      H_Z (affineSupportClosed I) (affineTildeAbSheaf M) n :=
  II_6_b_affine I M n

/-- **II.3, affine charts:** restriction of derived supported sheaves of a
scheme module to an affine open is the derived supported sheaf of the
restricted module, in every degree. -/
def II_3_affineChart {X : Scheme.{u}} (M : X.Modules) (Z : Closeds X)
    (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    H_Z (closedSupportOnOpen Z U) (restrictToOpen (schemeModuleAbSheaf M) U) n ≃+
      H_Z (affineChartSupport Z hU)
        (schemeModuleAbSheaf (M.restrict hU.fromSpec)) n :=
  affineChartSupportedCohomologyEquiv M Z U hU n

/-- **II.3, restriction:** derived supported sheaves commute with restriction
to every open, so quasi-coherence may be checked on affine charts. -/
def II_3_restriction {X : TopCat.{u}} (Z : Closeds X) (U : Opens X) (n : ℕ) :
    derivedUnderlineGammaZ Z n ⋙ iShriek_open U ≅
      iShriek_open U ⋙ derivedUnderlineGammaZ (closedSupportOnOpen Z U) n :=
  derivedSupportedSheafRestrictionIso Z U n

end SGA.SGA2.ExposeII
