/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.AffineChartSupportedCohomology
import SGA.SGA2.ExposeIII.SupportedSheafVanishing

/-!
# Coherent-module stalk depth and original derived supported sheaves

SGA 2, III.3.3 (i) iff (iv), for actual finitely presented module sheaves
on a locally noetherian scheme, in every nonnegative degree. The ordinary
abelian sheaf underlying the module is used in the original right-derived
supported-sheaf functor; depth is that of the literal module stalk over the
literal local structure ring. Finite affine charts, chart cohomology
comparisons, and the local-to-global vanishing criterion are all proved.

The module-valued internal sheaf-Ext conditions (v) and (vi) are not asserted.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat AlgebraicGeometry
open SGA.SGA2.ExposeI

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **III.3.3, (i) iff (iv):** original supported-sheaf vanishing below `n`
is exactly the literal coherent-module stalk-depth bound along the support. -/
theorem coherent_depth_iff_derivedSupported_vanishes
    (M : X.Modules) [M.IsFinitePresentation] (Z : Closeds X) (n : ℕ) :
    (∀ x : X, x ∈ Z → (n : ℕ∞) ≤ moduleStalkDepth M x) ↔
      ∀ i < n, IsZero ((derivedUnderlineGammaZ Z i).obj (schemeModuleAbSheaf M)) := by
  constructor
  · intro h i hi
    apply derivedSupported_isZero_of_local_H_Z_basis Z (schemeModuleAbSheaf M)
      {U : X.Opens | ∃ hU : IsAffineOpen U,
        Module.Finite Γ(X, U) (affineModuleCoefficients (M.restrict hU.fromSpec))}
      (finiteAffineModuleOpens_isBasis M) i
    intro U hU
    obtain ⟨hU, hfin⟩ := hU
    have := hfin
    exact (affineChart_H_Z_vanishes_iff_stalkDepth M Z U hU n).mpr
      (fun x _ hx => h x hx) i hi
  · intro h x hxZ
    have hlocal := (derivedSupported_vanishes_iff_local_H_Z Z (schemeModuleAbSheaf M) n).mp h
    obtain ⟨U, hU, hxU, _, hfin⟩ :=
      exists_affine_mem_subset_finiteCoefficients M (show x ∈ (⊤ : X.Opens) from trivial)
    have := hfin
    exact (affineChart_H_Z_vanishes_iff_stalkDepth M Z U hU n).mp (hlocal U) x hxU hxZ

/-- **III.3.3, (iii) iff (iv):** literal coherent stalk depth is also tested
by all lower actual supported-cohomology groups on every open subspace. -/
theorem coherent_depth_iff_local_H_Z_vanishes
    (M : X.Modules) [M.IsFinitePresentation] (Z : Closeds X) (n : ℕ) :
    (∀ x : X, x ∈ Z → (n : ℕ∞) ≤ moduleStalkDepth M x) ↔
      ∀ (U : X.Opens) (i : ℕ), i < n →
        Subsingleton (H_Z (closedSupportOnOpen Z U)
          (restrictToOpen (schemeModuleAbSheaf M) U) i) :=
  (coherent_depth_iff_derivedSupported_vanishes M Z n).trans
    (derivedSupported_vanishes_iff_local_H_Z Z (schemeModuleAbSheaf M) n)

end SGA.SGA2.ExposeIII
