/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.OpenIntersectionCohomology
import SGA.SGA2.ExposeIII.CoherentDepth

/-!
# Higher ordinary restriction and coherent stalk depth

SGA 2, III.3.1 (i) iff (ii), and III.3.3 (ii) iff (iv), for every
positive threshold `n + 1`. The maps are actual ordinary sheaf cohomology
restriction: first restrict the coefficient sheaf to an arbitrary open `V`,
then restrict to the open complement of `Z ∩ V` in `V`. No comparison with
the relative-sequence maps is assumed: it is proved in every degree in
`OrdinaryCohomologyRestriction`.

The threshold-zero conditions are vacuous; we use successor thresholds to
avoid imposing an artificial degree-zero condition for degree `-1`.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat AlgebraicGeometry
open SGA.SGA2.ExposeI

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- The complement of the induced closed support is the actual open
preimage of the ambient complement. -/
theorem closedSupportOnOpen_compl_eq (Z : Closeds X) (V : Opens X) :
    (closedSupportOnOpen Z V).compl = (Opens.map V.inclusion').obj Z.compl := by
  ext x
  rfl

/-- The relative long exact sequence tests supported vanishing by ordinary
restriction in every degree, not only by its degree-zero section map. -/
theorem supported_vanishing_iff_ordinaryRestriction (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (∀ i < n + 1, Subsingleton (H_Z Z F i)) ↔
      ((∀ i < n, Function.Bijective (ordinaryCohomologyRestriction Z.compl F i)) ∧
        Function.Injective (ordinaryCohomologyRestriction Z.compl F n)) := by
  simpa only [Nat.lt_succ_iff, relativeRestriction_eq_ordinary] using
    supported_vanishing_iff_relativeRestriction Z F n

/-- **III.3.1 (i) iff (ii)** at every positive threshold: original derived
supported sheaves vanish below `n + 1` exactly when restriction is bijective
below `n` and injective in degree `n`, on every open subspace. -/
theorem derivedSupported_vanishes_iff_ordinaryRestriction (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (∀ i < n + 1, IsZero ((derivedUnderlineGammaZ Z i).obj F)) ↔
      ∀ V : Opens X,
        ((∀ i < n, Function.Bijective (ordinaryCohomologyRestriction
          (closedSupportOnOpen Z V).compl (restrictToOpen F V) i)) ∧
        Function.Injective (ordinaryCohomologyRestriction
          (closedSupportOnOpen Z V).compl (restrictToOpen F V) n)) := by
  rw [derivedSupported_vanishes_iff_local_H_Z]
  exact forall_congr' fun V =>
    supported_vanishing_iff_ordinaryRestriction (closedSupportOnOpen Z V)
      (restrictToOpen F V) n

/-- **III.3.3 (ii) iff (iv)**: the literal coherent-module stalk-depth bound
`n + 1` along the support is equivalent to the higher ordinary cohomology
restriction condition on every open of the locally noetherian scheme. -/
theorem coherent_depth_iff_ordinaryRestriction
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsFinitePresentation] (Z : Closeds X) (n : ℕ) :
    (∀ x : X, x ∈ Z → (n + 1 : ℕ∞) ≤ moduleStalkDepth M x) ↔
      ∀ V : X.Opens,
        ((∀ i < n, Function.Bijective (ordinaryCohomologyRestriction
          (closedSupportOnOpen Z V).compl (restrictToOpen (schemeModuleAbSheaf M) V) i)) ∧
        Function.Injective (ordinaryCohomologyRestriction
          (closedSupportOnOpen Z V).compl (restrictToOpen (schemeModuleAbSheaf M) V) n)) := by
  exact (coherent_depth_iff_derivedSupported_vanishes M Z (n + 1)).trans
    (derivedSupported_vanishes_iff_ordinaryRestriction Z (schemeModuleAbSheaf M) n)

/-- **III.3.1 (i) iff (ii)** with the literal ambient intersection in the
target: `Hⁱ(V,F) → Hⁱ(V ∩ (X ∖ Z),F)` is bijective for `i < n` and
injective for `i = n`. The intersection comparison is proved, not assumed. -/
theorem derivedSupported_vanishes_iff_intersectionRestriction (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (∀ i < n + 1, IsZero ((derivedUnderlineGammaZ Z i).obj F)) ↔
      ∀ V : Opens X,
        ((∀ i < n, Function.Bijective
          (ordinaryCohomologyRestrictionToIntersection V Z.compl F i)) ∧
        Function.Injective (ordinaryCohomologyRestrictionToIntersection V Z.compl F n)) := by
  refine (derivedSupported_vanishes_iff_ordinaryRestriction Z F n).trans
    (forall_congr' fun V => ?_)
  have h := congrArg (fun W : Opens ((Opens.toTopCat X).obj V) =>
    ((∀ i < n, Function.Bijective (ordinaryCohomologyRestriction W (restrictToOpen F V) i)) ∧
      Function.Injective (ordinaryCohomologyRestriction W (restrictToOpen F V) n)))
    (closedSupportOnOpen_compl_eq Z V)
  refine h.to_iff.trans (and_congr ?_ ?_)
  · exact forall_congr' fun i => forall_congr' fun _ =>
      (ordinaryCohomologyRestrictionToIntersection_bijective_iff V Z.compl F i).symm
  · exact (ordinaryCohomologyRestrictionToIntersection_injective_iff V Z.compl F n).symm

/-- **III.3.3 (ii) iff (iv)** with literal ordinary cohomology of the ambient
opens `V` and `V ∩ (X ∖ Z)`, in every positive threshold. -/
theorem coherent_depth_iff_intersectionRestriction
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsFinitePresentation] (Z : Closeds X) (n : ℕ) :
    (∀ x : X, x ∈ Z → (n + 1 : ℕ∞) ≤ moduleStalkDepth M x) ↔
      ∀ V : X.Opens,
        ((∀ i < n, Function.Bijective
          (ordinaryCohomologyRestrictionToIntersection V Z.compl (schemeModuleAbSheaf M) i)) ∧
        Function.Injective
          (ordinaryCohomologyRestrictionToIntersection V Z.compl (schemeModuleAbSheaf M) n)) :=
  (coherent_depth_iff_derivedSupported_vanishes M Z (n + 1)).trans
    (derivedSupported_vanishes_iff_intersectionRestriction Z (schemeModuleAbSheaf M) n)

end SGA.SGA2.ExposeIII
