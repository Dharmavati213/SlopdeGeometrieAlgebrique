/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Ample
import SGA.Foundations.Analytic.AnalyticSpace
import SGA.Foundations.Analytic.Analytification
import SGA.Foundations.Analytic.Completion
import SGA.Foundations.Analytic.ConvergentPowerSeries
import SGA.Foundations.Analytic.Flatness
import SGA.Foundations.Analytic.GermEval
import SGA.Foundations.Analytic.Hadamard
import SGA.Foundations.Analytic.Henselian
import SGA.Foundations.Analytic.JetComparison
import SGA.Foundations.Analytic.LocalModel
import SGA.Foundations.Analytic.LocalModelHom
import SGA.Foundations.Analytic.LyingOver
import SGA.Foundations.Analytic.Noetherian
import SGA.Foundations.Analytic.Nullstellensatz
import SGA.Foundations.Analytic.OpenSubspace
import SGA.Foundations.Analytic.PowerSeriesExpansion
import SGA.Foundations.Analytic.Presentation
import SGA.Foundations.Analytic.PrincipalOpen
import SGA.Foundations.Analytic.SectionMorphism
import SGA.Foundations.Analytic.Sheaf
import SGA.Foundations.Analytic.Stalk
import SGA.Foundations.Analytic.Substitution
import SGA.Foundations.Analytic.UniversalProperty
import SGA.Foundations.Analytic.WeierstrassDivision
import SGA.Foundations.Cohomology.AdicSheafSystem
import SGA.Foundations.Cohomology.AffineHom
import SGA.Foundations.Cohomology.AffineOpenVanishing
import SGA.Foundations.Cohomology.AffineVanishing
import SGA.Foundations.Cohomology.AlgebraAlgebraization
import SGA.Foundations.Cohomology.ArtinRees
import SGA.Foundations.Cohomology.ArtinReesHom
import SGA.Foundations.Cohomology.BaseChangeAlgebra
import SGA.Foundations.Cohomology.BaseChangeCover
import SGA.Foundations.Cohomology.BaseChangeLocal
import SGA.Foundations.Cohomology.BaseChangeSections
import SGA.Foundations.Cohomology.Basic
import SGA.Foundations.Cohomology.Cartan
import SGA.Foundations.Cohomology.Cech
import SGA.Foundations.Cohomology.CechComparison
import SGA.Foundations.Cohomology.CechFinite
import SGA.Foundations.Cohomology.CechLocalization
import SGA.Foundations.Cohomology.CechMonomial
import SGA.Foundations.Cohomology.CechTransport
import SGA.Foundations.Cohomology.CechVanishing
import SGA.Foundations.Cohomology.ClosedFibre
import SGA.Foundations.Cohomology.ClosedImmersionSections
import SGA.Foundations.Cohomology.Coherent
import SGA.Foundations.Cohomology.CohomologicalDimension
import SGA.Foundations.Cohomology.CohomologyLemmas
import SGA.Foundations.Cohomology.Devissage
import SGA.Foundations.Cohomology.ExistenceFullyFaithful
import SGA.Foundations.Cohomology.ExistenceLocallyFree
import SGA.Foundations.Cohomology.Extension
import SGA.Foundations.Cohomology.FiniteEtaleAlgebraization
import SGA.Foundations.Cohomology.FiniteEtaleEquivalence
import SGA.Foundations.Cohomology.FiniteEtaleExistence
import SGA.Foundations.Cohomology.FiniteHomAlgebraization
import SGA.Foundations.Cohomology.FlatBaseChange
import SGA.Foundations.Cohomology.FormalFunctions
import SGA.Foundations.Cohomology.FormalPullback
import SGA.Foundations.Cohomology.GeometricConnectedness
import SGA.Foundations.Cohomology.Godement
import SGA.Foundations.Cohomology.GradedSheaf
import SGA.Foundations.Cohomology.HProjective
import SGA.Foundations.Cohomology.Helpers
import SGA.Foundations.Cohomology.HomTwist
import SGA.Foundations.Cohomology.IdealPowers
import SGA.Foundations.Cohomology.InvertibleSheaf
import SGA.Foundations.Cohomology.Leray
import SGA.Foundations.Cohomology.LerayNaturality
import SGA.Foundations.Cohomology.LerayTransfer
import SGA.Foundations.Cohomology.LocallyFreeAlgebraization
import SGA.Foundations.Cohomology.LongExactSequence
import SGA.Foundations.Cohomology.Modules
import SGA.Foundations.Cohomology.ProIsoAlgebraization
import SGA.Foundations.Cohomology.ProjectiveMorphism
import SGA.Foundations.Cohomology.ProjectiveSpace
import SGA.Foundations.Cohomology.ProjectiveSpaceTwist
import SGA.Foundations.Cohomology.ProperFiniteness
import SGA.Foundations.Cohomology.ProperProjectivity
import SGA.Foundations.Cohomology.Pushforward
import SGA.Foundations.Cohomology.PushforwardLeray
import SGA.Foundations.Cohomology.PushforwardProjective
import SGA.Foundations.Cohomology.QuasiCoherentAbelian
import SGA.Foundations.Cohomology.QuasiCoherentBiproduct
import SGA.Foundations.Cohomology.QuasiCoherentKernel
import SGA.Foundations.Cohomology.QuasiCoherentLocal
import SGA.Foundations.Cohomology.ReesBound
import SGA.Foundations.Cohomology.ReesCohomology
import SGA.Foundations.Cohomology.ReesMaps
import SGA.Foundations.Cohomology.ReesSheaf
import SGA.Foundations.Cohomology.RelativeArtinRees
import SGA.Foundations.Cohomology.RelativeSerre
import SGA.Foundations.Cohomology.RelativeSpec
import SGA.Foundations.Cohomology.RelativeSpecEtale
import SGA.Foundations.Cohomology.RelativeSpecFunctoriality
import SGA.Foundations.Cohomology.RelativeSpecUniversal
import SGA.Foundations.Cohomology.SeparatingSections
import SGA.Foundations.Cohomology.Serre
import SGA.Foundations.Cohomology.SerreFiniteness
import SGA.Foundations.Cohomology.SheafHomCoherent
import SGA.Foundations.Cohomology.Statements
import SGA.Foundations.Cohomology.SteinAlgebraization
import SGA.Foundations.Cohomology.SteinEtale
import SGA.Foundations.Cohomology.SteinFactorization
import SGA.Foundations.Cohomology.Thickening
import SGA.Foundations.Cohomology.ThickeningReduction
import SGA.Foundations.Cohomology.TrivialIdempotents
import SGA.Foundations.Cohomology.Twist
import SGA.Foundations.Cohomology.TwistBaseChange
import SGA.Foundations.Cohomology.TwistGeneration
import SGA.Foundations.Cohomology.TwistProjection
import SGA.Foundations.Cohomology.UniformVanishing
import SGA.Foundations.Cohomology.ZariskiConnectedness
import SGA.Foundations.CommAlg.AuslanderBuchsbaum
import SGA.Foundations.CommAlg.BasicOpenHartogs
import SGA.Foundations.CommAlg.Depth
import SGA.Foundations.CommAlg.Discriminant
import SGA.Foundations.CommAlg.Factorial
import SGA.Foundations.CommAlg.FlatDepth
import SGA.Foundations.CommAlg.Normal
import SGA.Foundations.CommAlg.PairSections
import SGA.Foundations.CommAlg.PuncturedSpectrum
import SGA.Foundations.CommAlg.Purity
import SGA.Foundations.CommAlg.PurityCompletion
import SGA.Foundations.CommAlg.PurityHull
import SGA.Foundations.CommAlg.PurityInduction
import SGA.Foundations.CommAlg.PurityLift
import SGA.Foundations.CommAlg.PurityQuasiFinite
import SGA.Foundations.CommAlg.PurityScheme
import SGA.Foundations.CommAlg.PurityStalk
import SGA.Foundations.CommAlg.RegularLocalRing
import SGA.Foundations.CommAlg.RegularPair
import SGA.Foundations.CompleteLocalQuasiFinite
import SGA.Foundations.CompletionDimension
import SGA.Foundations.Differentials.Affine
import SGA.Foundations.Differentials.AffineOpens
import SGA.Foundations.Differentials.BaseChange
import SGA.Foundations.Differentials.BaseChangeAffine
import SGA.Foundations.Differentials.Basic
import SGA.Foundations.Differentials.DerivationOn
import SGA.Foundations.Differentials.Exact
import SGA.Foundations.Differentials.Localization
import SGA.Foundations.Differentials.Presheaf
import SGA.Foundations.Differentials.QuasiCoherent
import SGA.Foundations.Differentials.Restrict
import SGA.Foundations.Differentials.Sections
import SGA.Foundations.Differentials.SheafHom
import SGA.Foundations.Differentials.Smooth
import SGA.Foundations.Differentials.Tangent
import SGA.Foundations.Differentials.Tilde
import SGA.Foundations.Differentials.Unramified
import SGA.Foundations.Dimension.Equidimensional
import SGA.Foundations.Dimension.FiberDimension
import SGA.Foundations.Dimension.FiniteType
import SGA.Foundations.Dimension.FlatFiber
import SGA.Foundations.Dimension.FlatLocal
import SGA.Foundations.Dimension.FlatScheme
import SGA.Foundations.Dimension.Integral
import SGA.Foundations.Dimension.LocalDimension
import SGA.Foundations.Dimension.QuasiFinite
import SGA.Foundations.Dimension.Scheme
import SGA.Foundations.Dimension.Semicontinuity
import SGA.Foundations.Dimension.Smooth
import SGA.Foundations.Etale.BaseChange
import SGA.Foundations.Etale.ChangeOfGroup
import SGA.Foundations.Etale.ConstantScheme
import SGA.Foundations.Etale.Functoriality
import SGA.Foundations.Etale.GroupObjectTorsor
import SGA.Foundations.Etale.HigherDirectImage
import SGA.Foundations.Etale.LocallyConstant
import SGA.Foundations.Etale.NonabelianExact
import SGA.Foundations.Etale.Picard
import SGA.Foundations.Etale.Points
import SGA.Foundations.Etale.Representable
import SGA.Foundations.Etale.RepresentableGluing
import SGA.Foundations.Etale.Restriction
import SGA.Foundations.Etale.StructureSheaf
import SGA.Foundations.Etale.Torsor
import SGA.Foundations.Etale.TorsorCech
import SGA.Foundations.Etale.TorsorDescent
import SGA.Foundations.Etale.TorsorEtale
import SGA.Foundations.Etale.TorsorPresheaf
import SGA.Foundations.Etale.TorsorProduct
import SGA.Foundations.Etale.TorsorPullback
import SGA.Foundations.Etale.TorsorPushforward
import SGA.Foundations.Etale.TorsorStack
import SGA.Foundations.Etale.TorsorTwist
import SGA.Foundations.EtaleSpreadingOut
import SGA.Foundations.EtaleStalk
import SGA.Foundations.EtaleStalkBaseChange
import SGA.Foundations.EtaleStalkPullback
import SGA.Foundations.EtaleStalkPushforward
import SGA.Foundations.EtaleStalkStructureSheaf
import SGA.Foundations.EtaleStalkTorsor
import SGA.Foundations.Fields.Differentials
import SGA.Foundations.Fields.GeometricallyReduced
import SGA.Foundations.Fields.GeometricallyReducedScheme
import SGA.Foundations.Fields.MacLane
import SGA.Foundations.Fields.Separable
import SGA.Foundations.Fields.SeparablyGenerated
import SGA.Foundations.Formal.AdicInverseLimit
import SGA.Foundations.Formal.AdicRing
import SGA.Foundations.Formal.AdicSystem
import SGA.Foundations.Formal.Completion
import SGA.Foundations.Formal.CompletionLocal
import SGA.Foundations.Formal.CompletionNoetherian
import SGA.Foundations.Formal.EtaleCovering
import SGA.Foundations.Formal.EtaleLift
import SGA.Foundations.Formal.FiniteEtale
import SGA.Foundations.Formal.FiniteEtaleSpec
import SGA.Foundations.Formal.FormalColimit
import SGA.Foundations.Formal.FormalScheme
import SGA.Foundations.Formal.NoetherianOfComplete
import SGA.Foundations.Formal.OpenImmersion
import SGA.Foundations.Formal.Spf
import SGA.Foundations.Formal.SpfBasicOpen
import SGA.Foundations.Formal.SpfCompletion
import SGA.Foundations.Formal.SpfInverseLimit
import SGA.Foundations.Formal.SpfMorphisms
import SGA.Foundations.Formal.TowerLimit
import SGA.Foundations.HenselianDegree
import SGA.Foundations.HenselianFinite
import SGA.Foundations.HenselianFiniteEtale
import SGA.Foundations.HenselianFiniteLocal
import SGA.Foundations.HenselianLifting
import SGA.Foundations.HenselianQuasiFinite
import SGA.Foundations.Henselization
import SGA.Foundations.HenselizationNoetherian
import SGA.Foundations.Limits.BaseChange
import SGA.Foundations.Limits.FiniteEtale
import SGA.Foundations.Limits.GeometricFiberCard
import SGA.Foundations.Limits.IntegralApproximation
import SGA.Foundations.Limits.SpecFibre
import SGA.Foundations.NoetherianApproximation
import SGA.Foundations.Pro.Basic
import SGA.Foundations.Pro.ContAction
import SGA.Foundations.Pro.Equivalence
import SGA.Foundations.Pro.Representable
import SGA.Foundations.Projective.AmpleDescent
import SGA.Foundations.Projective.AmpleFinite
import SGA.Foundations.Projective.AmpleLocal
import SGA.Foundations.Projective.AmpleProj
import SGA.Foundations.Projective.Chow
import SGA.Foundations.Projective.Dehomogenization
import SGA.Foundations.Projective.LineBundle
import SGA.Foundations.Projective.LineBundleIso
import SGA.Foundations.Projective.Morphisms
import SGA.Foundations.Projective.Norm
import SGA.Foundations.Projective.NormLineBundle
import SGA.Foundations.Projective.ProjBaseChange
import SGA.Foundations.Projective.ProjectiveSpace
import SGA.Foundations.Projective.ProjectiveSpaceHom
import SGA.Foundations.Projective.ProjectiveSpaceSpec
import SGA.Foundations.Projective.QuasiProjective
import SGA.Foundations.Projective.RelativeProj
import SGA.Foundations.Projective.SectionExtension
import SGA.Foundations.Projective.SectionRing
import SGA.Foundations.Projective.SectionRingMaps
import SGA.Foundations.Projective.SectionsBaseChange
import SGA.Foundations.Projective.Segre
import SGA.Foundations.Projective.ToProj
import SGA.Foundations.Projective.TwistingSheaf
import SGA.Foundations.QuasiAffine
import SGA.Foundations.QuasiCoherent.Cokernel
import SGA.Foundations.QuasiCoherent.Descent
import SGA.Foundations.QuasiCoherent.DescentChart
import SGA.Foundations.QuasiCoherent.DescentEffective
import SGA.Foundations.QuasiCoherent.DescentLocalIso
import SGA.Foundations.QuasiCoherent.DescentLocalizing
import SGA.Foundations.QuasiCoherent.DescentQuotient
import SGA.Foundations.QuasiCoherent.DescentSections
import SGA.Foundations.QuasiCoherent.Glue
import SGA.Foundations.QuasiCoherent.Local
import SGA.Foundations.QuasiCoherent.Pullback
import SGA.Foundations.QuasiCoherent.SchemeTheoreticImage
import SGA.Foundations.QuasiCoherent.Sections
import SGA.Foundations.QuasiCoherent.SpecSections
import SGA.Foundations.QuasiCoherent.Stalk
import SGA.Foundations.QuasiCoherent.StalkModule
import SGA.Foundations.QuasiCoherent.Tilde
import SGA.Foundations.Ramification.BaseLocalization
import SGA.Foundations.Ramification.Henselian
import SGA.Foundations.Ramification.Inertia
import SGA.Foundations.Ramification.IntegralClosure
import SGA.Foundations.Ramification.Pi
import SGA.Foundations.Ramification.Tame
import SGA.Foundations.Ramification.TameInertia
import SGA.Foundations.Ramification.Transport
import SGA.Foundations.SpecStalkLimit
import SGA.Foundations.StrictHenselization
import SGA.Foundations.StrictLocalization
import SGA.Foundations.StrictLocalizationLift
import SGA.Foundations.StrictLocalizationLimit
import SGA.Foundations.StrictlyHenselianFinite
import SGA.Foundations.StrictlyHenselianFiniteScheme
import SGA.Foundations.StrictlyHenselianLift
import SGA.Foundations.Topology.CoveringGalois
import SGA.Foundations.Topology.CoveringOfFunctor
import SGA.Foundations.Topology.FiniteCovering
import SGA.Foundations.Topology.GaloisCategoryEquivalence
import SGA.Foundations.Topology.LocallyContractible
import SGA.Foundations.Topology.ProfiniteCompletionGalois
import SGA.Foundations.Topology.SemilocallySimplyConnected
import SGA.Foundations.WeilRestriction

/-!
# Foundations for the SGA formalization

Prerequisites of SGA 1 that mathlib does not have, written in mathlib style (mathlib namespaces
and naming, references to EGA and the Stacks Project in the module docstrings). None of them
restates a mathlib result.

* `QuasiAffine`, `Ample`, `Projective`: quasi-affine, ample and quasi-projective morphisms,
  relative `Proj`, Segre embeddings, Chow's lemma, norms of line bundles (EGA II);
* `CommAlg`, `Dimension`, `CompletionDimension`, `Fields`: regular local rings,
  Auslander–Buchsbaum, factoriality, Zariski–Nagata purity, dimension theory of schemes,
  separability of field extensions (EGA 0_IV, EGA IV 4–7);
* `Henselization`, `StrictHenselization`, `HenselizationNoetherian`, `HenselianLifting`,
  `HenselianFiniteEtale`, `StrictLocalization`, `StrictLocalizationLift`, `EtaleStalk`,
  `EtaleStalkStructureSheaf`, `EtaleStalkPushforward`, `SpecStalkLimit`: henselian rings,
  (strict) henselization, strict localization and étale stalks (EGA IV 18, Stacks 04GE, 04HX);
* `Differentials`: the sheaf `Ω_{X/Y}` and its properties (EGA IV 16–17);
* `QuasiCoherent`, `Cohomology`: quasi-coherent sheaves, Čech and derived cohomology of
  quasi-coherent sheaves, Serre vanishing, the finiteness, formal-function, connectedness and
  base-change theorems for proper morphisms and the Grothendieck existence theorem (EGA III);
* `Formal`: adic completion, formal schemes and `Spf` (EGA I 10);
* `Etale`: étale sheaves, torsors, non-abelian `H¹`, the stack of torsors, `Pic`, and locally
  constant sheaves versus finite étale coverings (SGA 4 VII–IX);
* `Pro`: pro-objects and pro-representable functors (SGA 4 I 8);
* `Limits`, `NoetherianApproximation`, `EtaleSpreadingOut`, `WeilRestriction`: limits of schemes
  and noetherian approximation (EGA IV 8, 17.7);
* `Ramification`, `CompleteLocalQuasiFinite`: ramification and tame inertia of valuations,
  quasi-finite algebras over complete local rings;
* `Topology`: topological coverings form a Galois category;
* `Analytic`: convergent power series, the Weierstrass theorems, Rückert's Nullstellensatz,
  complex analytic spaces and analytification (Grauert–Remmert).
-/
