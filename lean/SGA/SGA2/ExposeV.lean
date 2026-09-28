/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.LocalCohomologyBoundaryComparison
import SGA.SGA2.ExposeV.InjectiveResolutionSequenceNaturality
import SGA.SGA2.ExposeV.RingedModuleSpectralE2Naturality
import SGA.SGA2.ExposeV.RingedModuleSpectralAbutmentNaturality
import SGA.SGA2.ExposeV.LocalCohomologyFiniteness
import SGA.SGA2.ExposeV.LocalRingUpperVanishing
import SGA.SGA2.ExposeV.CompleteTopLocalCohomology
import SGA.SGA2.ExposeV.SupportedFunctorComponents
import SGA.SGA2.ExposeV.ExtSupportDimension
import SGA.SGA2.ExposeV.SurjectiveDualityChange
import SGA.SGA2.ExposeV.LocalCohomologyFiniteLengthCriterion

/-!
# SGA 2, Exposé V: local duality and the structure of local cohomology

## Hom complexes and Ext (§1)

`SourceHomComplex` implements the displayed differential. The degreewise
factor `(-1)^(n(n+1)/2)` identifies it with Mathlib's Hom complex.
`InjectiveHomComplexExt` computes Ext using two injective resolutions;
`InjectiveHomComplexProduct` compares composition with the Yoneda product.
Both Hom long exact sequences, their pairing compatibility, and their
comparison with Ext boundaries are proved. `InjectiveHorseshoe` constructs
compatible resolutions; `InjectiveResolutionSequenceNaturality` handles
comparison maps and independence of the chosen resolutions.

The signs are part of these statements. The normalized source product
contributes `(-1)^(ij)`. On unsigned projective representatives, the Yoneda
coefficient boundary is `(-1)^(n+1)` times the lifted boundary, including
degree zero; `LocalCohomologyBoundaryComparison` transports this equality
to local cohomology. The source's incompatible unsigned formulas are not
asserted.

## Canonical local duality (§2)

`LocalDualityMap` constructs the natural map from quotient Ext stages.
`LocalDuality` proves it invertible on finite modules over a regular local
ring in every complementary degree. `LocalDualityTranspose` identifies the
dual of local cohomology with completed complementary Ext; over a complete
base this is formula (22).

## Structure theorems (§3)

* V.3.1: `ModuleDimensionVanishing` proves upper vanishing;
  `LocalRingFiniteness` and `CompletedDualDimension` prove finiteness and
  the dimension bound for completed duals. `LocalRingTopNonvanishing`
  proves top nonvanishing, and `TopLocalCohomologyAssociatedPrimes` gives
  the associated-prime formula. These hold over noetherian local bases.
  `ExtSupportDimension` supplies the support criteria (a)–(c) after (22).
* V.3.2: the `RingedModuleSpectral*` files construct the module-valued
  spectral sequence for closed supports, its E₂ and abutment comparisons,
  and a finite convergence filtration, natural in coefficients and
  independent of resolutions.
* V.3.3: `SupportedFunctorComponents` identifies the associated primes of
  the representing module from the chosen irreducible components.
* V.3.4: `AffineComplementCodimension` bounds the codimension of each
  component of a closed subset with affine complement by one.
* V.3.5–V.3.6: `LocalCohomologyFiniteLengthCriterion` proves the punctured
  vanishing and depth criteria over quotients of regular local rings.
  Prime-localization regularity, the dimension formula, and quotient
  transport are proved in the imported supporting files.

Cohen's presentation theorem is not formalized. The general local-ring
results use direct proofs and do not depend on it. Detailed statement
coverage is recorded in `docs/formalization.md`.
-/
