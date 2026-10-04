/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties

/-!
# The reduced induced structure on a closed subset

For a closed subset `Z` of a scheme `X`, the closed subscheme cut out by the vanishing ideal of
`Z` (mathlib's `Scheme.IdealSheafData.vanishingIdeal`) is the reduced induced subscheme structure
on `Z` (EGA I 5.1.1; Hartshorne II Ex. 3.11 (d)): it is reduced
(`Scheme.IdealSheafData.isReduced_vanishingIdeal_subscheme`), its underlying set is `Z`, and it is
integral when `Z` is irreducible (`Scheme.IdealSheafData.isIntegral_vanishingIdeal_subscheme`).
We use it to restrict line bundles to integral closed subschemes.

## References

* [A. Grothendieck, J. Dieudonné, *EGA* I 5.1.1][EGA]
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The reduced induced subscheme structure on a closed subset is reduced. -/
theorem isReduced_vanishingIdeal_subscheme (Z : Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme := by
  have (U : (vanishingIdeal Z).subschemeCover.openCover.I₀) :
      IsReduced ((vanishingIdeal Z).subschemeCover.openCover.X U) := by
    let V : X.affineOpens := U
    have : _root_.IsReduced (Γ(X, V) ⧸ (vanishingIdeal Z).ideal V) := by
      rw [← Ideal.isRadical_iff_quotient_reduced, vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    exact (inferInstance : IsReduced (Spec (.of (Γ(X, V) ⧸ (vanishingIdeal Z).ideal V))))
  exact IsReduced.of_openCover (𝒰 := (vanishingIdeal Z).subschemeCover.openCover)

lemma range_vanishingIdeal_subschemeι (Z : Closeds X) :
    Set.range (vanishingIdeal Z).subschemeι = Z := by
  rw [range_subschemeι, coe_support_vanishingIdeal]

/-- The reduced induced subscheme structure on an irreducible closed subset is integral. -/
theorem isIntegral_vanishingIdeal_subscheme (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) :
    IsIntegral (vanishingIdeal Z).subscheme := by
  have := isReduced_vanishingIdeal_subscheme Z
  let ι := (vanishingIdeal Z).subschemeι
  have : IrreducibleSpace (Set.range ι) :=
    Subtype.irreducibleSpace (by rw [range_vanishingIdeal_subschemeι]; exact hZ)
  have : IrreducibleSpace (vanishingIdeal Z).subscheme :=
    (Homeomorph.irreducibleSpace_iff ι.isClosedEmbedding.isEmbedding.toHomeomorph).mpr this
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end AlgebraicGeometry.Scheme.IdealSheafData
