/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.Points
import SGA.SGA1.ExposeXII.FiniteLimits
import SGA.SGA1.ExposeXII.SimpleRoot
import SGA.SGA1.ExposeXII.Etale
import SGA.SGA1.ExposeXII.Comparison
import SGA.SGA1.ExposeXII.JacobsonConstructible
import SGA.SGA1.ExposeXII.ProperMapLocal
import SGA.SGA1.ExposeXII.SchemePoints
import SGA.SGA1.ExposeXII.SchemeLimits
import SGA.SGA1.ExposeXII.Separated
import SGA.SGA1.ExposeXII.Analytic
import SGA.SGA1.ExposeXII.RiemannExistence
import SGA.SGA1.ExposeXII.Smooth
import SGA.SGA1.ExposeXII.FundamentalGroup
import SGA.SGA1.ExposeXII.ProjectiveSpace
import SGA.SGA1.ExposeXII.Proper
import SGA.SGA1.ExposeXII.HenselianQuotient
import SGA.SGA1.ExposeXII.AnalyticAffine
import SGA.SGA1.ExposeXII.LocalRings
import SGA.SGA1.ExposeXII.ReducedComparison
import SGA.SGA1.ExposeXII.Nullstellensatz
import SGA.SGA1.ExposeXII.ClosureComparison
import SGA.SGA1.ExposeXII.EntirePolynomial
import SGA.SGA1.ExposeXII.PolynomialLines
import SGA.SGA1.ExposeXII.RootFunctions
import SGA.SGA1.ExposeXII.RootLocus
import SGA.SGA1.ExposeXII.PrimitiveElement
import SGA.SGA1.ExposeXII.Connected
import SGA.SGA1.ExposeXII.AnalyticGluing
import SGA.SGA1.ExposeXII.AnalyticGluingMap
import SGA.SGA1.ExposeXII.AnalyticGluingPoints
import SGA.SGA1.ExposeXII.AnalyticGluingReduced
import SGA.SGA1.ExposeXII.BranchedCover
import SGA.SGA1.ExposeXII.FundamentalGroupQuotient
import SGA.SGA1.ExposeXII.GAGA
import SGA.SGA1.ExposeXII.GAGACompactRiemannSurface
import SGA.SGA1.ExposeXII.GAGAFiberSeparating
import SGA.SGA1.ExposeXII.LocalTopology
import SGA.SGA1.ExposeXII.LocalTopologyCones
import SGA.SGA1.ExposeXII.LocalTopologyCurves
import SGA.SGA1.ExposeXII.LocalTopologyLPC
import SGA.SGA1.ExposeXII.LocalTopologySLSC
import SGA.SGA1.ExposeXII.MorphismComparison
import SGA.SGA1.ExposeXII.MorphismComparisonGlobal
import SGA.SGA1.ExposeXII.MorphismComparisonIso
import SGA.SGA1.ExposeXII.MorphismComparisonOpenImmersion
import SGA.SGA1.ExposeXII.MorphismComparisonPoints
import SGA.SGA1.ExposeXII.MorphismComparisonScheme
import SGA.SGA1.ExposeXII.MorphismComparisonSmooth
import SGA.SGA1.ExposeXII.RiemannCurves
import SGA.SGA1.ExposeXII.RiemannCurvesCompactification
import SGA.SGA1.ExposeXII.RiemannCurvesPuncturedPlane
import SGA.SGA1.ExposeXII.RiemannCurvesPuncturedPlaneExistence
import SGA.SGA1.ExposeXII.RiemannCurvesPuncturedPlaneGroup
import SGA.SGA1.ExposeXII.RiemannCurvesSeparable
import SGA.SGA1.ExposeXII.RiemannCurvesSymmetric
import SGA.SGA1.ExposeXII.RiemannFull
import SGA.SGA1.ExposeXII.RiemannKummer
import SGA.SGA1.ExposeXII.RiemannLocal
import SGA.SGA1.ExposeXII.RiemannLocalAffine
import SGA.SGA1.ExposeXII.RiemannLocalChart
import SGA.SGA1.ExposeXII.RiemannReduction
import SGA.SGA1.ExposeXII.RiemannReductionFiniteEtale
import SGA.SGA1.ExposeXII.RiemannReductionUniverse
import SGA.SGA1.ExposeXII.RiemannSimplyConnected
import SGA.SGA1.ExposeXII.StatementCorollaries

import SGA.SGA1.ExposeXII.GAGAModules
import SGA.SGA1.ExposeXII.GAGAProjective
import SGA.SGA1.ExposeXII.GAGAProjectiveSpace
import SGA.SGA1.ExposeXII.RiemannCurvesExistence
import SGA.SGA1.ExposeXII.RiemannExtension
import SGA.SGA1.ExposeXII.RiemannExtensionAlgebra
import SGA.SGA1.ExposeXII.RiemannExtensionClosure
import SGA.SGA1.ExposeXII.RiemannExtensionCriterion
import SGA.SGA1.ExposeXII.RiemannExtensionLocal
import SGA.SGA1.ExposeXII.RiemannExtensionTopology
import SGA.SGA1.ExposeXII.RiemannHigher
import SGA.SGA1.ExposeXII.RiemannHigherAssembly
import SGA.SGA1.ExposeXII.RiemannHigherBase
import SGA.SGA1.ExposeXII.RiemannHigherDescent
import SGA.SGA1.ExposeXII.RiemannHigherDescentAffine
import SGA.SGA1.ExposeXII.RiemannHigherFibrePresentation
import SGA.SGA1.ExposeXII.RiemannHigherFibrewise
import SGA.SGA1.ExposeXII.RiemannHigherFrames
import SGA.SGA1.ExposeXII.RiemannHigherGeneric
import SGA.SGA1.ExposeXII.RiemannHigherGenericEtale
import SGA.SGA1.ExposeXII.RiemannHigherIsotopy
import SGA.SGA1.ExposeXII.RiemannHigherLine
import SGA.SGA1.ExposeXII.RiemannHigherParameter
import SGA.SGA1.ExposeXII.RiemannHigherPointedChart
import SGA.SGA1.ExposeXII.RiemannHigherPolyFamily
import SGA.SGA1.ExposeXII.RiemannHigherPolyPoints
import SGA.SGA1.ExposeXII.RiemannHigherPresentation
import SGA.SGA1.ExposeXII.RiemannHigherProductCovering
import SGA.SGA1.ExposeXII.RiemannHigherQuasiSection
import SGA.SGA1.ExposeXII.RiemannHigherRigidity
import SGA.SGA1.ExposeXII.RiemannHigherRootSpace
import SGA.SGA1.ExposeXII.RiemannHigherSmooth
import SGA.SGA1.ExposeXII.RiemannHigherTransport
import SGA.SGA1.ExposeXII.RiemannReductionNoether
import SGA.SGA1.ExposeXII.RiemannReductionProduct
/-!
# SGA 1, Exposé XII — Algebraic geometry and analytic geometry

English translation: `translation/SGA1/ExposeXII/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

Mathlib has no complex analytic spaces. Over any topological field `K` (for XII, `K = ℂ`) we
build the space `X(K)` of a `K`-scheme and, for `K` complete normed, the reduced analytic space
`(X^an)_red`; for affine `X` the (non-reduced) analytic space `X^an` of
`SGA.Foundations.Analytic` is related to it, and for separated `X` over `ℂ` the non-reduced `X^an`
is glued from the affine charts:

* §1 (`Points`, `FiniteLimits`, `SchemePoints`, `SchemeLimits`, `Analytic`, `AnalyticAffine`,
  `ReducedComparison`): the topology on `X(K)`, first for affine `X` (independent of the
  presentation), then glued from affine charts; functoriality, open and closed immersions, affine
  spaces and fibre products; the sheaf of analytic functions, the locally ringed space
  `analytification K X`, the canonical morphism `φ : X^an → X` and the functor `f ↦ f^an`
  (XII.1.1, XII.1.2, reduced versions); for affine `X`, the non-reduced `X^an` with underlying
  space `X(K)`, independent of the presentation, functorial, with its universal property, and the
  comparison morphism `(X^an)_red → X^an`;
* §1 for separated `X` (`AnalyticGluing`, `AnalyticGluingMap`, `AnalyticGluingPoints`,
  `AnalyticGluingReduced`): `X^an` glued from the `U^an`, `U` affine, the canonical morphism
  `φ : X^an → X` (XII.1.1: a comparison morphism, injective, with image the closed points), the
  morphism `f^an` and its functoriality (XII.1.2), the homeomorphism `X^an ≃ₜ X(ℂ)` compatible
  with `f^an` (`AnalyticGluing.pointsHomeomorph`), and, for affine `X`, `(X^an)_red` as the
  reduction of `X^an`. SGA's universal property of `X^an` is proved only for affine `X`, tested
  on local models, and the uniqueness of `f^an` is not proved;
* §§2–3 (`Comparison`, `SchemePoints`, `Separated`, `Etale`, `SimpleRoot`,
  `JacobsonConstructible`, `ProperMapLocal`, `Smooth`, `ProjectiveSpace`, `Proper`,
  `AnalyticAffine`, `HenselianQuotient`, `LocalRings`, `Nullstellensatz`, `ClosureComparison`,
  `Connected` with `RootLocus`, `PrimitiveElement`, `EntirePolynomial`, `PolynomialLines`,
  `RootFunctions`): the comparison statements that concern points and topology: surjectivity,
  injectivity, discreteness and dimension `0`, separatedness and Hausdorffness, immersions and
  embeddings; étale morphisms give local homeomorphisms (implicit function theorem), smooth
  schemes give spaces locally homeomorphic to `Kⁿ`, finite morphisms proper maps with finite
  fibres, finite étale morphisms finite coverings, proper morphisms proper maps (compactness of
  `ℙⁿ(K)` and Chow's lemma); the local rings of `X^an` (affine `X`): noetherian henselian with
  residue field `K`, the same jets and completions as those of `X`, the same dimension, regular
  together, normality and reducedness descending (XII.2.1); XII.2.2 and XII.2.3 (Rückert's
  Nullstellensatz; XII.2.2 is `SchemePoints.closureComparison`, and for affine `X` with `A : Type`
  `Points.closureComparisonStatement_zero`), XII.2.4 (connectedness, via Noether normalization,
  removable singularities and Liouville, without GAGA) and XII.2.6 (`π₀`);
* §3 for `f^an` (`MorphismComparison`, `MorphismComparisonScheme`, `MorphismComparisonGlobal`,
  `MorphismComparisonSmooth`, `MorphismComparisonPoints`, `MorphismComparisonIso`,
  `MorphismComparisonOpenImmersion`), for `X`, `Y` separated: XII.3.1 (i), (ii) (flat,
  unramified), (iii) (étale, with "`f^an` étale" read as flat and unramified at every point, not
  shown to be a local isomorphism; `AnalyticGluing.etale_iff_forall_analyticMap`) and (iv)
  (smooth, with "`f^an` smooth" read as flat with regular fibres), also for affine `X`, `Y`;
  XII.3.1 (ix) and (xi), the converse implications for `f` quasi-compact
  (`isIso_iff_isIso_analyticMap`, `isOpenImmersion_iff_isOpenImmersion_analyticMap`); the direct
  implications of XII.3.1 (vii) and of XII.3.2 (v) (topological part) and (vi) (`f^an` proper
  with finite fibres, `AnalyticGluing.isFiniteMap_analyticMap`); XII.3.2 (i), (ii) for `f`
  quasi-compact, i.e. of finite type as in SGA (`surjective_analyticMap_iff`,
  `denseRange_analyticMap_iff`);
* §4 (`GAGA`): XII.4.3–XII.4.6 as statements on the glued `X^an`, with `F^an` the pullback along
  `φ` (`CohomologyComparisonStatement`, `CoherentEquivalenceStatement`,
  `AnalyticFullyFaithfulStatement`, `FiniteAnalyticEquivalenceStatement`);
* §5, XII.5.2 (`RiemannExistence`, `FundamentalGroup`, `FundamentalGroupQuotient`,
  `LocalTopology`, `LocalTopologyLPC`, `LocalTopologySLSC`, `LocalTopologyCurves`,
  `LocalTopologyCones`, `BranchedCover`, `StatementCorollaries`): the functor `Ψ : Y ↦ Y(ℂ)` of
  XII.5.1 on points, for schemes and for algebras, its compatibility with the fibre functors of
  V.7, and the Riemann existence theorem XII.5.1 as a statement; without XII.5.1, the surjection
  `π̂₁(X(ℂ), x) ↠ π₁(X, x)` (`surjective_autWhiskerLeft_schemePointsFunctor`); `X(ℂ)` is locally
  path-connected and semilocally simply connected for every `X` (`locallyPathConnectedStatement`,
  `semilocallySimplyConnectedStatement`; branched coverings and semialgebraic geometry, no
  triangulation), hence the topological input `CoveringFundamentalGroupStatement`
  (`coveringFundamentalGroupStatement`), so XII.5.2 follows from XII.5.1 alone, with the
  isomorphism stated as `Nonempty` (`schemeFundamentalGroupComparison_of_riemannExistence`; affine
  form `fundamentalGroupComparison_of_riemannExistence`); strong local contractibility of `X(ℂ)`
  for smooth `X`, in dimension `≤ 1` and at the vertex of a quasi-homogeneous cone;
* §5, XII.5.1 (`RiemannFull`, `RiemannLocal`, `RiemannLocalAffine`, `RiemannLocalChart`,
  `RiemannReduction`, `RiemannReductionUniverse`, `RiemannReductionFiniteEtale`,
  `RiemannSimplyConnected`, `RiemannKummer`, `RiemannCurves`, `RiemannCurvesSymmetric`,
  `RiemannCurvesPuncturedPlane`, `RiemannCurvesSeparable`, `RiemannCurvesPuncturedPlaneExistence`,
  `RiemannCurvesPuncturedPlaneGroup`, `RiemannCurvesCompactification`, `GAGACompactRiemannSurface`,
  `GAGAFiberSeparating`): `Ψ` is fully faithful (step 1) of SGA's proof; for `X : Scheme.{0}`,
  `schemePointsFunctorFullyFaithful`); the scheme and affine forms of XII.5.1 are equivalent
  (`schemeRiemannExistence_iff`), the affine form does not depend on the universe
  (`riemannExistence_iff_zero`) and passes to finite étale coverings
  (`isEquivalence_pointsFunctor_of_finiteEtale`), and for connected `X` XII.5.1 is equivalent to
  the injectivity of `π̂₁(X(ℂ), x) ↠ π₁(X, x)`; XII.5.1 holds when `X(ℂ)` is simply connected
  (`isEquivalence_schemePointsFunctor_of_simplyConnectedSpace`, e.g. `𝔸ⁿ_ℂ`), for `𝔾_{m,ℂ}`
  (`riemannExistence_laurentPolynomial`), and for `ℂ` minus a finite set and its finite étale
  coverings (`PuncturedPlane.riemannExistence_coordRing`,
  `PuncturedPlane.riemannExistence_finiteEtale`).
  The last case goes by this project's route, not SGA's: on a compact Riemann surface every point
  is the only pole of a meromorphic function (`compactRiemannSurfaceMeromorphic`), and a finite
  covering of `ℂ ∖ S` is an open subset of a compact Riemann surface
  (`puncturedPlaneCompactification`); hence separating functions on such coverings
  (`fiberSeparatingFunction`, `separatingFunctionStatement`). As a consequence the étale `π₁` of
  `ℙ¹_ℂ` minus `n + 1` points is isomorphic to the profinite completion of a free group on `n`
  generators
  (`PuncturedPlane.etaleFundamentalGroup_mulEquiv_completion_freeGroup`; an abstract isomorphism,
  the generators are not identified with loops or inertia generators).

Open: XII.5.1 for all curves (`CurveRiemannExistenceStatement`) and in general
(`SchemeRiemannExistenceStatement`, `RiemannExistenceStatement`), hence XII.5.2
(`SchemeFundamentalGroupComparisonStatement`, `FundamentalGroupComparisonStatement`); strong local
contractibility of `X(ℂ)` for singular `X` of dimension `≥ 2` (`LocallyContractibleStatement`, not
needed for XII.5.2); the proofs of XII.4.3–XII.4.6 (they need, among others, Theorem B on
polydiscs, Oka's coherence theorem and Cartan–Serre finiteness; the first two are stated in
`SGA.Foundations.Analytic`); XII.4.1–XII.4.2 (not stated: no `Rᵖf_*` on both sides); XII.3.1
(iii) with "`f^an` étale" meaning a local isomorphism; XII.3.1 (v), (vi), (viii), (x) and the
converse of (vii) for `f^an`; XII.3.2 (iii), (iv) and the converses of (v), (vi) for `f^an`;
`(X^an)_red` at sheaf level for non-affine `X`; XII.2.2 for affine `X` in universes other than `0`
(`Points.ClosureComparisonStatement`; the scheme form is proved). Not formalized: `X^an` for
non-separated `X`; the universal property of `X^an` for non-affine `X` and the uniqueness of
`f^an`; XII.1.2 for analytic spaces (fibre products are compared on points only, `SchemeLimits`);
XII.1.3.1 (`F ↦ F^an` exact, faithful, conservative; only the functor
`AnalyticGluing.analytification` is defined); XII.2.5 and XII.5.3–XII.5.5 (normal analytic
spaces). `lean/SGA/Foundations/README.md` lists what each out-of-scope item still needs.
-/
