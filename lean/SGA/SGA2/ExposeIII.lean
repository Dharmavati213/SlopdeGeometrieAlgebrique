/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.AssociatedPrimes
import SGA.SGA2.ExposeIII.DepthLocalization
import SGA.SGA2.ExposeIII.DepthSupport
import SGA.SGA2.ExposeIII.DepthBaseChange
import SGA.SGA2.ExposeIII.DepthLocalCohomology
import SGA.SGA2.ExposeIII.AffineDepth
import SGA.SGA2.ExposeIII.AffineStalkDepth
import SGA.SGA2.ExposeIII.AffineClopens
import SGA.SGA2.ExposeIII.AffineHartogs
import SGA.SGA2.ExposeIII.AffineConnectedComponents
import SGA.SGA2.ExposeIII.SheafHartogsGluing
import SGA.SGA2.ExposeIII.SchemeHartogs
import SGA.SGA2.ExposeIII.SchemeHartogsCriterion
import SGA.SGA2.ExposeIII.SchemeModuleStalks
import SGA.SGA2.ExposeIII.AffineQuasicoherentHartogs
import SGA.SGA2.ExposeIII.CoherentAffineCharts
import SGA.SGA2.ExposeIII.CoherentHartogs
import SGA.SGA2.ExposeIII.SupportedSheafVanishing
import SGA.SGA2.ExposeIII.HomeomorphismSupportedCohomology
import SGA.SGA2.ExposeIII.AffineChartSupportedCohomology
import SGA.SGA2.ExposeIII.AffineOpenCohomologyVanishing
import SGA.SGA2.ExposeIII.CoherentDepth
import SGA.SGA2.ExposeIII.CohomologyRestrictionCriterion
import SGA.SGA2.ExposeIII.RestrictionRedundancy
import SGA.SGA2.ExposeIII.HigherRestrictionRedundancy
import SGA.SGA2.ExposeIII.SchemeClopens
import SGA.SGA2.ExposeIII.SchemeConnectedComponents
import SGA.SGA2.ExposeIII.MaximalRegular
import SGA.SGA2.ExposeIII.InfiniteRegular
import SGA.SGA2.ExposeIII.Examples
import SGA.SGA2.ExposeIII.RegularLocalRegularSequence
import SGA.SGA2.ExposeIII.AntifilterConnectedness
import SGA.SGA2.ExposeIII.ConnectednessInCodimension
import SGA.SGA2.ExposeIII.HigherVanishingOnStructure
import SGA.SGA2.ExposeIII.SheafExtDepth
import SGA.SGA2.ExposeIII.ExamplesIII
import SGA.SGA2.ExposeIII.Equidimensionality
import SGA.SGA2.ExposeIII.AntifilterEquivalence
import SGA.SGA2.ExposeIII.ExamplesIII313
import SGA.SGA2.ExposeIII.EquidimensionalityCriterion

/-!
# SGA 2, Exposé III — Cohomological invariants and depth

English translation: `translation/SGA2/ExposeIII/` (repo root).

* `AssociatedPrimes`: III.1.1–III.1.3 and all five conditions of III.2.1;
* `RegularExt`: III.2.2(a), with no noetherian or finiteness hypotheses,
  and III.2.2(b) for finite modules over a noetherian ring;
* `Depth`: the Ext definition III.2.3, the equivalent depth criteria III.2.4,
  the quotient formula III.2.5, and the Ext description in III.2.8;
* `DepthLocalization`: the local infimum formula III.2.9 and its semilocal
  specialization III.2.10;
* `DepthBaseChange`: the flat inequality and faithfully flat equality III.2.11;
* `DepthLocalCohomology`: depth bounds are equivalent to vanishing of actual
  algebraic local cohomology below that bound; this is an algebraic input
  to the remaining geometric criteria of §3;
* `AffineDepth`: depth bounds are equivalent to vanishing of actual supported
  sheaf cohomology on a noetherian affine scheme, to the local-depth bounds
  along the support, and to Ext vanishing from finite test modules;
* `AffineStalkDepth`: the actual structure-sheaf and associated-module stalks
  are canonically identified with localizations, including scalar compatibility
  and equality of the original localization depth with literal stalk depth;
* `AffineHartogs`: actual restriction of associated-sheaf sections is injective
  at depth at least one and bijective at depth at least two; the positive-threshold
  local criteria of III.3.4 and affine connectedness across a depth-two support
  are proved using the genuine characteristic-section bridge in `AffineClopens`;
* `AffineConnectedComponents`: the actual inclusion-induced map on connected
  components is bijective under the affine local depth-two hypothesis (III.3.6);
* `SchemeHartogs`: on every locally noetherian scheme, literal structure-stalk
  depth at least two along a closed support implies bijective structure-sheaf
  restriction on every open. `SheafHartogsGluing` proves the local-to-global
  sheaf restriction argument;
  `SchemeHartogsCriterion` proves the converse, giving the actual structure-sheaf
  Hartogs equivalence in both directions;
* `SchemeModuleStalks`, `AffineQuasicoherentHartogs`, `CoherentAffineCharts`,
  and `CoherentHartogs`: full III.3.5 for actual coherent module sheaves on
  locally noetherian schemes, expressed using mathlib's local finite-presentation
  condition. Literal module-stalk depth at least two is equivalent to bijective
  section restriction on every open. Finite affine coefficients and all
  semilinear stalk comparisons are derived, not assumed;
* `SupportedSheafVanishing`: III.3.1(i) iff (iii) for arbitrary abelian
  sheaves, using actual spectral convergence and actual sheafification;
  `HomeomorphismSupportedCohomology`, `AffineChartSupportedCohomology`, and
  `CoherentDepth` prove III.3.3(i)/(iii)/(iv) in every nonnegative degree:
  literal module-stalk depth along the support is equivalent to vanishing
  of original derived supported sheaves, and to local supported-cohomology
  vanishing on every open. All affine-chart comparisons are proved;
* `OrdinaryCohomologyRestriction`, `OpenIntersectionCohomology`, and
  `CohomologyRestrictionCriterion` prove III.3.1(ii) and III.3.3(ii): in every
  positive threshold, actual ordinary restriction to the ambient intersection
  is bijective below the last degree and injective in the last degree.
  Its comparison with the original relative exact sequence is proved in all degrees;
* `RestrictionRedundancy` and `HigherRestrictionRedundancy` prove I.2.13 for
  every `N > 0` and III.3.2 at every threshold at least two, for arbitrary
  abelian sheaves. Highest-degree injectivity follows from all-open lower
  bijectivity, by actual complement-adapted injective effacement and coefficient
  dimension shifting. The corresponding coherent stalk-depth criterion follows;
* `SchemeClopens` and `SchemeConnectedComponents`: genuine global structure
  idempotents correspond to clopens, and depth at least two along a closed
  support implies bijectivity of the actual open-inclusion map on connected
  components for every locally noetherian scheme (III.3.6), without global
  quasi-compactness;
* `MaximalRegular`: extension to every finite length allowed by depth and
  maximal sequences at finite depth (III.2.6);
* `InfiniteRegular`: at infinite depth, any finite regular prefix extends
  to a single infinite regular sequence;
* `DepthSupport`: depth is finite exactly when the module support meets
  `V(I)` (III.2.7);
* `Examples`: infinite depth at the unit ideal, depth zero at the zero ideal,
  and the depth-one calculation for `ℤ` along `(2)`.
* `RegularLocalRegularSequence` and its imports: actual regular local rings
  are domains, every minimal generating list of the maximal ideal is regular,
  and regular parameters of the actual Krull dimension exist. Parameter
  quotient regularity and dimension drop are proved, not assumed.

SGA's regular sequences allow a zero final quotient, so they are expressed
using mathlib's `IsWeaklyRegular`. All depth formulae include infinite depth.
III.3.13 includes principal-curve vanishing and the non-UFD obstruction.
III.3.8's full component-chain equivalence holds on locally noetherian spaces.
III.3.7 gives actual finite component chains with the asserted codimension
bound, and III.3.9 derives equidimensionality from depth and the genuine
prime-chain condition. Remaining notes are recorded in `docs/formalization.md`.
-/
