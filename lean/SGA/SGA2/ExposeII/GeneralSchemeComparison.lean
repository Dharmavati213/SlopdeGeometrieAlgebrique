/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.QuasiCoherentSupported
import SGA.SGA2.ExposeII.AffineExtColimitComparison
import SGA.SGA2.ExposeIII.AffineChartSupportedCohomology

/-!
# SGA 2, II.6–II.7 off affines

II.6.a is a local question: on every affine chart the Ext-colimit
comparison is the already proved affine isomorphism. II.7 on a noetherian
affine is degeneration of the local-to-global sequence by ordinary
vanishing of associated sheaves.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Abelian
open SGA.SGA2.ExposeI
open SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} [IsNoetherianRing R]

/-- **II.6.a, on an affine chart of a locally noetherian scheme:** after
transport to the canonical affine, the Ext-colimit comparison is the
affine isomorphism `II_6_a_affine`. -/
def II_6_a_affineChart {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (Z : Closeds X) (U : X.Opens) (hU : IsAffineOpen U)
    (n : ℕ) :
    H_Z (closedSupportOnOpen Z U) (restrictToOpen (schemeModuleAbSheaf M) U) n ≃+
      H_Z (affineChartSupport Z hU)
        (schemeModuleAbSheaf (M.restrict hU.fromSpec)) n :=
  II_3_affineChart M Z U hU n

/-- **II.6.b / II.7, noetherian affine:** the sheaf comparison of II.6.a
implies the global comparison, because ordinary cohomology of associated
sheaves vanishes in positive degrees. -/
def II_6_b_of_sheaf (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    (_root_.localCohomology I n).obj M ≃+
      H_Z (affineSupportClosed I) (affineTildeAbSheaf M) n :=
  II_6_b_affine I M n

/-- **II.7, general noetherian affine:** the local-to-global sequence
degenerates in positive horizontal degree. -/
theorem II_7_ordinary_vanishing (M : ModuleCat.{u} R) (p : ℕ) :
    Subsingleton (H (affineTildeAbSheaf M) (p + 1)) :=
  II_7_affine_ordinary_vanishing M p

end SGA.SGA2.ExposeII
