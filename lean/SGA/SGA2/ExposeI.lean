/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.GammaZ
import SGA.SGA2.ExposeI.Flasque
import SGA.SGA2.ExposeI.InjectiveFlasque
import SGA.SGA2.ExposeI.FlasqueCohomology
import SGA.SGA2.ExposeI.SupportedSectionExactness
import SGA.SGA2.ExposeI.DerivedSupportedSections
import SGA.SGA2.ExposeI.RightDerivedPostcomposition
import SGA.SGA2.ExposeI.RightDerivedPrecomposition
import SGA.SGA2.ExposeI.FlasqueResolution
import SGA.SGA2.ExposeI.ClosedSupportHom
import SGA.SGA2.ExposeI.ExtRightDerived
import SGA.SGA2.ExposeI.SupportedCohomologyComparison
import SGA.SGA2.ExposeI.OpenExtensionByZero
import SGA.SGA2.ExposeI.ExtAdjunction
import SGA.SGA2.ExposeI.OpenSupportCohomology
import SGA.SGA2.ExposeI.SupportedExcision
import SGA.SGA2.ExposeI.SupportedSheafSections
import SGA.SGA2.ExposeI.ClosedSupportAdjunction
import SGA.SGA2.ExposeI.DerivedSupportedSheaves
import SGA.SGA2.ExposeI.SupportedSheafSequence
import SGA.SGA2.ExposeI.SupportedSheafDimensionShift
import SGA.SGA2.ExposeI.DerivedSupportedSheafOne
import SGA.SGA2.ExposeI.SupportedSheafModel
import SGA.SGA2.ExposeI.InternalHom
import SGA.SGA2.ExposeI.TopologicalInternalHom
import SGA.SGA2.ExposeI.SheafExtLocalComparison
import SGA.SGA2.ExposeI.ClosedSupportRestriction
import SGA.SGA2.ExposeI.ClosedSupportInternalHomSections
import SGA.SGA2.ExposeI.ClosedSupportInternalHom
import SGA.SGA2.ExposeI.LocallyClosedSupportInternalHom
import SGA.SGA2.ExposeI.SupportedSheafInjective
import SGA.SGA2.ExposeI.LocalToGlobalResolution
import SGA.SGA2.ExposeI.LocalToGlobalSpectralObject
import SGA.SGA2.ExposeI.HomologicalSpectralObject
import SGA.SGA2.ExposeI.LocalToGlobalSpectralSequence
import SGA.SGA2.ExposeI.DerivedTruncationHomology
import SGA.SGA2.ExposeI.LocalToGlobalE2
import SGA.SGA2.ExposeI.DerivedTruncationNaturality
import SGA.SGA2.ExposeI.SpectralSequenceFirstPageNaturality
import SGA.SGA2.ExposeI.LocalToGlobalE2Naturality
import SGA.SGA2.ExposeI.LocalToGlobalFirstQuadrant
import SGA.SGA2.ExposeI.HomComplexSingleComparison
import SGA.SGA2.ExposeI.LocalToGlobalTotalCohomology
import SGA.SGA2.ExposeI.HomComplexNaturality
import SGA.SGA2.ExposeI.LocalToGlobalSpectralFunctoriality
import SGA.SGA2.ExposeI.LocalToGlobalTotalNaturality
import SGA.SGA2.ExposeI.SpectralObjectCoefficientMaps
import SGA.SGA2.ExposeI.SpectralSequenceCoefficientMaps
import SGA.SGA2.ExposeI.SpectralSequenceFirstPageExt
import SGA.SGA2.ExposeI.LocalToGlobalPageMaps
import SGA.SGA2.ExposeI.LocalToGlobalCoefficientFunctor
import SGA.SGA2.ExposeI.SpectralObjectConvergence
import SGA.SGA2.ExposeI.LocalToGlobalConvergence
import SGA.SGA2.ExposeI.SpectralObjectConvergenceNaturality
import SGA.SGA2.ExposeI.LocalToGlobalConvergenceNaturality
import SGA.SGA2.ExposeI.LocallyClosedLocalToGlobalConvergenceNaturality
import SGA.SGA2.ExposeI.LocallyClosedCohomology
import SGA.SGA2.ExposeI.LocallyClosedIndependence
import SGA.SGA2.ExposeI.OpenSupportedSections
import SGA.SGA2.ExposeI.LocallyClosedSupportedSheaves
import SGA.SGA2.ExposeI.OpenDerivedSupportedSheaves
import SGA.SGA2.ExposeI.SupportedSheafRestriction
import SGA.SGA2.ExposeI.SupportedSheafBoundary
import SGA.SGA2.ExposeI.SupportedSheafStalkBoundary
import SGA.SGA2.ExposeI.LocallyClosedSheafBoundary
import SGA.SGA2.ExposeI.ClosedSupportCohomology
import SGA.SGA2.ExposeI.LocallyClosedSupportCohomology
import SGA.SGA2.ExposeI.ConstantSupportSequenceCompatibility
import SGA.SGA2.ExposeI.FlasqueVanishingCriterion
import SGA.SGA2.ExposeI.RelativeCohomologySequence
import SGA.SGA2.ExposeI.RelativeCohomologySections
import SGA.SGA2.ExposeI.NestedSupportSubspace
import SGA.SGA2.ExposeI.LocallyClosedNestedGamma
import SGA.SGA2.ExposeI.LocallyClosedNestedSheafSequence
import SGA.SGA2.ExposeI.LocallyClosedNestedSheafCohomology
import SGA.SGA2.ExposeI.NestedSupportInternalHom
import SGA.SGA2.ExposeI.LocallyClosedExtensionSequence
import SGA.SGA2.ExposeI.LocallyClosedExtensionEndpoints
import SGA.SGA2.ExposeI.LocallyClosedComposition
import SGA.SGA2.ExposeI.LocalCohomology
import SGA.SGA2.ExposeI.UnderlineGammaZ
import SGA.SGA2.ExposeI.LocallyClosed
import SGA.SGA2.ExposeI.ExtensionByZero
import SGA.SGA2.ExposeI.DerivedFunctors
import SGA.SGA2.ExposeI.ExactSequences
import SGA.SGA2.ExposeI.InternalHomBifunctor
import SGA.SGA2.ExposeI.SheafExtRestriction
import SGA.SGA2.ExposeI.SheafExtConnecting
import SGA.SGA2.ExposeI.ClosedAsLocallyClosed
import SGA.SGA2.ExposeI.OpenInclusionLeray
import SGA.SGA2.ExposeI.LocallyClosedWitnessChangeSpectral
import SGA.SGA2.ExposeI.RingedSpaceSupportHom
import SGA.SGA2.ExposeI.ExtRightDerivedMap
import SGA.SGA2.ExposeI.RepresentedFunctorSequence
import SGA.SGA2.ExposeI.Examples

/-!
# SGA 2, Exposé I — Global and local cohomological invariants relative to a closed subspace

English translation: `translation/SGA2/ExposeI/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

## Coverage (I.1–I.2)

* **I.1** `Γ_Z` closed — `GammaZ.lean`
* **I.1** sheaf `Γ̲_Z` — `UnderlineGammaZ.lean`
  `SupportedSheafSections.lean` identifies its actual sections with supported
  sections, naturally in both coefficients and opens, and proves left exactness.
* **I.1** locally closed + independence of open — `LocallyClosed.lean`
  (`gammaZSections_restrict_addEquiv`)
* **I.1 special cases** closed pushforward, open restriction, locally closed
  support, and closed `ℤ_{Z,X}` — `ExtensionByZero.lean`.
* **I.1.3–I.1.4, open case** actual exact extension by zero, its adjunction
  with restriction, and preservation of injectives by restriction
  — `OpenExtensionByZero.lean`. `ClosedSupportAdjunction.lean` proves the
  general closed and locally closed adjunctions, exact closed extension,
  preservation of injectives by extraordinary inverse image, and the natural
  comparison of closed pushforward with the original supported kernel.
* **I.1, (17), arbitrary coefficients** the original open counit and closed
  unit give the actual short exact extension sequence; exact locally closed
  extension transports it to arbitrary coefficients on the support space.
  Both endpoints are genuine single-witness extensions, with actual subset
  equality and coefficient-map compatibility — `LocallyClosedExtensionEndpoints.lean`.
  `LocallyClosedComposition.lean` proves the full arbitrary nested locally
  closed composition law (13), for extension and extraordinary inverse image,
  with the actual support-space homeomorphism and original adjunction maps.
* **I.1.6, closed case** the natural additive Hom representation of actual
  supported sections — `ClosedSupportHom.lean`.
  `ClosedSupportRestriction.lean` proves actual closed-support base change
  to every open and compatibility with the canonical integer presentation.
* **Internal Hom and sheaf Ext** `InternalHom.lean` constructs the genuine
  sheaf of local morphisms, proves left exactness, and derives it.
  `TopologicalInternalHom.lean` identifies sections with actual restricted Hom;
  `SheafExtLocalComparison.lean` proves sheaf Ext is the sheafification of local Ext.
  `ClosedSupportInternalHom.lean` proves the natural closed-support internal-Hom
  identity I.1.6 and its all-degree sheaf Ext consequence I.2.3 bis, including
  comparison with the unchanged supported-sheaf model.
  `LocallyClosedSupportInternalHom.lean` extends the actual ambient internal-Hom
  and all-degree sheaf Ext comparison to every locally closed support,
  with coefficient and open-restriction naturality proved.
* **I.1.6 / I.2.3, open case** actual open extension by zero represents
  sections on the open, and its Ext is ordinary cohomology of restriction,
  naturally in coefficients and compatibly with their boundaries
  — `OpenSupportCohomology.lean`.
* **I.1.8, degree zero** nested-support equality and global flasque extension
  — `ExactSequences.lean`, `Flasque.lean`
  `LocallyClosedNestedGamma.lean` proves the natural left exact sequence on
  the original section groups for every locally closed support, with short
  exactness on flasque coefficients.
* **I.1.9–I.1.10, constant support objects** the genuine closed/open short
  exact sequence of constant support sheaves — `ConstantSupportSequence.lean`.
  `NestedSupportLocallyClosed.lean` proves the integer-support sequence I.1.10
  for every locally closed support and every closed subset of its support space.
  `NestedSupportInternalHom.lean` identifies actual internal Hom of both
  open/closed-presentation object arrows with the original supported-sheaf
  arrows, as an isomorphism of the full short complexes.
* **I.1.9** the original ambient nested supported-sheaf sequence is left exact,
  and short exact on flasque coefficients, for arbitrary locally closed supports
  — `LocallyClosedNestedSheafSequence.lean`. All maps arise from actual section
  inclusion/restriction, through the proved original sheaf comparisons.
* **I.2.12 inputs** — injective abelian sheaves are flasque, and flasque
  sheaves have zero ordinary higher sheaf cohomology (`InjectiveFlasque.lean`,
  `FlasqueCohomology.lean`).
  `SupportedSectionExactness.lean` proves actual supported-section exactness
  for short exact coefficient sequences with flasque kernel.
* **I.2.1 / I.2.3 bis, closed supports** `H_Z^*` — `DerivedFunctors.lean` as
  `Ext(ℤ_{Z,X}, −)`; `SupportedCohomologyComparison.lean` proves the natural
  comparison with original right-derived supported sections in every degree.
* **I.2.1 original construction** `DerivedSupportedSections.lean`: actual
  right-derived supported sections, with a proved natural degree-zero comparison.
  `FlasqueResolution.lean` proves their positive-degree vanishing on flasque sheaves.
* **I.2.12, closed supported acyclicity** actual `H_Z` vanishes in positive
  degrees on flasque sheaves, also after restriction to every open.
  `FlasqueVanishingCriterion.lean` proves the converse: vanishing of `H_Z¹`
  for every closed support characterizes flasque sheaves.
* **I.2.1 / I.2.3 bis / I.2.12, locally closed witnesses** actual composite
  extension by zero represents supported sections, its Ext computes their
  original derived functors, and flasque coefficients are acyclic
  — `LocallyClosedCohomology.lean`. `LocallyClosedIndependence.lean` proves
  independence of arbitrary witnesses defining the same subset, for the
  actual support sheaf, section functor, original derived functors, and Ext.
* **I.2.1** algebraic — `LocalCohomology.lean`
* **I.2.2, all degrees, closed support** genuine excision, naturally in
  coefficients — `supportedExcisionEquiv` in `SupportedExcision.lean`.
* **I.2.11 model** `ℋ_Z^n` for all `n` — `sheafH_Z_n`, defined using
  kernel, cokernel, and derived pushforward.
  `SupportedSheafModel.lean` proves its natural comparison with the original
  derived kernel-sheaf functor in every degree, using the degree-one computation
  in `DerivedSupportedSheafOne.lean` and higher `SupportedSheafDimensionShift.lean`.
* **I.2.4 / sheaf-valued I.2.12, closed support** `DerivedSupportedSheaves.lean`
  constructs the original derived supported sheaves, proves their natural
  sheafification comparison with local supported cohomology, and proves
  positive-degree flasque acyclicity. The underlying short exact sequence
  of injective-resolution complexes is proved in `SupportedSheafSequence.lean`.
  `SupportedSheafModel.lean` transfers both results to the unchanged model.
* **I.2.4 / I.2.12, locally closed supports** `LocallyClosedSupportedSheaves.lean`
  constructs the ambient supported sheaf, its original derived functors and
  local-cohomology sheafification, flasque acyclicity, and all-degree witness
  independence. `OpenSupportedSections.lean` supplies the actual section comparison.
* **I.2.5** `OpenDerivedSupportedSheaves.lean` identifies original open-supported
  derived sheaves with the higher direct images of actual restriction.
* **I.2.7, closed support** `SupportedSheafRestriction.lean` proves natural
  open base change for the original support functor and all derived degrees.
  `SupportedSheafBoundary.lean` proves actual restriction vanishes off the
  support, and on its interior in positive degrees, for original supported
  sheaves, genuine sheaf Ext, and the unchanged model.
  `SupportedSheafStalkBoundary.lean` proves the corresponding literal stalk
  support inclusions in the closed set and its boundary.
  `LocallyClosedSheafBoundary.lean` proves the full locally closed stalk-support
  bounds: all degrees are supported in the closure and positive degrees in
  the boundary, for the original derived locally closed supported sheaves.
  `ClosedSupportCohomology.lean` identifies higher cohomology of supported
  sheaves with cohomology on the actual closed subspace, naturally in coefficients.
  `LocallyClosedSupportCohomology.lean` extends this comparison to the closure
  of a locally closed support, using ordinary closed pullback.
* **I.2.6** `SupportedSheafInjective.lean` and
  `LocalToGlobalResolution.lean` prove injective preservation and the supported
  resolution comparison with actual `H_Z`. `LocalToGlobalSpectralObject.lean`,
  `HomologicalSpectralObject.lean`, and `LocalToGlobalSpectralSequence.lean`
  construct the canonical truncation spectral sequence with actual pages and
  differentials. `DerivedTruncationHomology.lean` and `LocalToGlobalE2.lean`
  identify its actual E₂ terms with ordinary cohomology of original derived
  supported sheaves, including the E₂ universe comparison.
  `LocalToGlobalFirstQuadrant.lean` proves that all pages vanish outside the
  first quadrant. `HomComplexSingleComparison.lean` and
  `LocalToGlobalTotalCohomology.lean` identify the actual spectral-object total
  groups with original `H_Z`. `SpectralObjectConvergence.lean` and
  `LocalToGlobalConvergence.lean` prove the finite image filtration and actual
  stable-page associated-graded comparison, with uniform bound r ≥ n + 2.
  `LocalToGlobalSpectralFunctoriality.lean`, `HomComplexNaturality.lean`, and
  `LocalToGlobalTotalNaturality.lean` construct actual spectral-object maps and
  prove total naturality. `SpectralObjectCoefficientMaps.lean`,
  `SpectralSequenceCoefficientMaps.lean`, and `LocalToGlobalPageMaps.lean`
  give actual page morphisms respecting every differential and next-page
  homology isomorphism. `SpectralSequenceFirstPageExt.lean` proves uniqueness
  from the first page. `LocalToGlobalE2Naturality.lean` proves naturality of
  the original E₂ comparison. `LocalToGlobalCoefficientFunctor.lean` proves
  lift independence, the actual coefficient functor, and coherent natural
  resolution-change isomorphisms. `LocalToGlobalConvergenceNaturality.lean`
  proves naturality of the actual convergence filtration and original
  stable-page/graded-piece comparison, lift independence, and equality of
  the transported filtrations on original `H_Z` for all resolutions.
  The eight `LocallyClosedLocalToGlobal*.lean` modules extend the construction
  to arbitrary locally closed supports on the original ambient space: actual
  E₂ terms, original `H_locallyClosed` abutment, finite convergence,
  coefficient functoriality, and resolution-independent filtered naturality.
  The constructed sequence is the Grothendieck spectral sequence of the
  supported-sheaf functor; for open support its E₂ page is the Leray page
  of the inclusion. Spectral-level witness change is proved.
* **I.2.8 input / I.2.13 low degrees** Ext exactness for a supplied short
  exact sequence and actual mono/isomorphism criteria — `ExactSequences.lean`.
  `ExtRightDerivedMap.lean` proves that exact functors preserve Ext classes
  of actual resolution cocycles and the induced Hom-complex maps.
  `RepresentedFunctorSequence.lean` reconstructs a short exact sequence of
  representing objects from an exact sequence of represented additive functors.
* **I.2.8** the actual general locally closed nested-support sequence, with
  genuine extension-class connecting maps and coefficient naturality in all
  degrees — `NestedSupportCohomology.lean`, `NestedSupportLocallyClosed.lean`.
  The degree-zero maps for an open/closed presentation are actual supported
  section inclusion and restriction.
* **I.2.10** the original ambient derived nested supported-sheaf sequence is
  exact in every degree, naturally in coefficients; both arrows are actual
  derived maps and the boundary is constructed from the original injective
  resolution sequence — `LocallyClosedNestedSheafCohomology.lean`.
  Its zeroth-degree maps recover the original supported-sheaf maps under
  the original degree-zero isomorphisms.
* **I.2.9 / group-valued I.2.14** the actual closed/open relative long exact
  sequence and higher vanishing/restriction criteria — `RelativeCohomologySequence.lean`.
  `RelativeCohomologySections.lean` identifies its degree-zero maps with
  actual inclusion of supported sections and actual section restriction.
  Exposé III's `OrdinaryCohomologyRestriction.lean` proves this identity in
  every degree. Its `CohomologyRestrictionCriterion.lean` proves the main
  I.2.13 criterion using original supported sheaves and actual ordinary
  restriction to ambient intersections. `HigherRestrictionRedundancy.lean`
  proves the additional redundancy of highest-degree injectivity for every `N > 0`.

Exposé II handles topological↔algebraic comparison on affines.

Mathlib supplies: flasque sheaves, algebraic local cohomology, `Ext` /
`HasExt` for Grothendieck abelian sheaf categories, pushforward/pullback,
`Functor.rightDerived`.

Numbering follows Grothendieck (`I.1.1`, `I.2.1`, …). See `docs/formalization.md`.
-/
