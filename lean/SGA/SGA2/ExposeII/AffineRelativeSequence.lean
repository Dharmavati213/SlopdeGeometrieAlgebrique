/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.RelativeCohomologySequence
import SGA.SGA2.ExposeII.AffineCohomologyVanishing

/-!
# Relative cohomology on noetherian affine schemes

Ordinary affine vanishing reduces the actual relative cohomology sequence
to its four-term low-degree sequence and identifies higher supported
cohomology with cohomology of the open complement. These are the
group-valued formulas II.(4.2)–(4.3), under a noetherian ring hypothesis.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeII

open ExposeI

variable {R : CommRingCat.{u}} [IsNoetherianRing R]

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem relativeBoundary_surjective_of_ordinary_next_vanishing
    {X : TopCat.{u}} (Z : Closeds X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) [Subsingleton (H F (n + 1))] :
    Function.Surjective (relativeBoundary Z F n) := by
  intro y
  exact (relative_exact_at_supported Z F n y).mp (Subsingleton.elim _ _)

/-- **II.(4.2), noetherian case:** the relative degree-zero boundary is
surjective for every associated module sheaf and every closed support. -/
theorem affineRelativeBoundary_zero_surjective (M : ModuleCat.{u} R)
    (Z : Closeds (Spec R)) :
    Function.Surjective (relativeBoundary Z (affineTildeAbSheaf M) 0) := by
  have := affineTildeAb_H_pos_subsingleton M 0
  exact relativeBoundary_surjective_of_ordinary_next_vanishing Z (affineTildeAbSheaf M) 0

/-- **II.(4.2), noetherian case:** the genuine four-term cohomology sequence
is exact, starts injectively, and ends surjectively. -/
theorem affineRelativeLowDegree_exact (M : ModuleCat.{u} R)
    (Z : Closeds (Spec R)) :
    Function.Injective (relativeSupportMap Z (affineTildeAbSheaf M) 0) ∧
    Function.Exact (relativeSupportMap Z (affineTildeAbSheaf M) 0)
      (relativeRestriction Z (affineTildeAbSheaf M) 0) ∧
    Function.Exact (relativeRestriction Z (affineTildeAbSheaf M) 0)
      (relativeBoundary Z (affineTildeAbSheaf M) 0) ∧
    Function.Surjective (relativeBoundary Z (affineTildeAbSheaf M) 0) :=
  ⟨relativeSupportMap_zero_injective Z (affineTildeAbSheaf M),
    relative_exact_at_ordinary Z (affineTildeAbSheaf M) 0,
    relative_exact_at_open Z (affineTildeAbSheaf M) 0,
    affineRelativeBoundary_zero_surjective M Z⟩

/-- **II.(4.3), noetherian case:** supported cohomology in degree `n+2`
is ordinary cohomology of the open complement in degree `n+1`.
No finiteness assumption is imposed on the coefficient module. -/
def affineSupportedCohomologyEquivOpen (M : ModuleCat.{u} R)
    (Z : Closeds (Spec R)) (n : ℕ) :
    H_Z Z (affineTildeAbSheaf M) (n + 2) ≃+
      H (restrictToOpen (affineTildeAbSheaf M) Z.compl) (n + 1) := by
  have := affineTildeAb_H_pos_subsingleton M n
  have := affineTildeAb_H_pos_subsingleton M (n + 1)
  exact (relativeBoundaryEquiv Z (affineTildeAbSheaf M) (n + 1)).symm

end SGA.SGA2.ExposeII
