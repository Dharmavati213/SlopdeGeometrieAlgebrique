/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.AdditiveFunctorModules
import SGA.SGA2.ExposeIV.LinearFunctorModuleLift
import SGA.SGA2.ExposeIV.FiniteModuleEvaluation
import SGA.SGA2.ExposeIV.FiniteFreeEvaluation
import SGA.SGA2.ExposeIV.FiniteModuleRepresentation
import SGA.SGA2.ExposeIV.FiniteModuleFunctorEquivalence
import SGA.SGA2.ExposeIV.PreorderLimitRepresentation
import SGA.SGA2.ExposeIV.InjectivityCriterion
import SGA.SGA2.ExposeIV.SupportedHomDetection
import SGA.SGA2.ExposeIV.SupportedFiniteModules
import SGA.SGA2.ExposeIV.SupportedQuotientStages
import SGA.SGA2.ExposeIV.SupportedFunctorDiagram
import SGA.SGA2.ExposeIV.SupportedStageEvaluation
import SGA.SGA2.ExposeIV.SupportedStageRepresentation
import SGA.SGA2.ExposeIV.SupportedFunctorColimit
import SGA.SGA2.ExposeIV.SupportedFunctorEvaluation
import SGA.SGA2.ExposeIV.SupportedFunctorRepresentation
import SGA.SGA2.ExposeIV.SupportedRestrictedHom
import SGA.SGA2.ExposeIV.SupportedFunctorEquivalence
import SGA.SGA2.ExposeIV.SupportedModuleTorsion
import SGA.SGA2.ExposeIV.IntegerCohomologicalSequence
import SGA.SGA2.ExposeIV.SupportedFunctorVanishing
import SGA.SGA2.ExposeIV.SupportedDeltaVanishing
import SGA.SGA2.ExposeIV.SupportedFunctorExactness
import SGA.SGA2.ExposeIV.SupportedArtinianDuality
import SGA.SGA2.ExposeIV.SupportedFunctorLengthExactness
import SGA.SGA2.ExposeIV.ArtinianLocalIdealDuality
import SGA.SGA2.ExposeIV.LocalSocleDuality
import SGA.SGA2.ExposeIV.QuotientAnnihilatorDuality
import SGA.SGA2.ExposeIV.AnnihilatorFiltrationColimit
import SGA.SGA2.ExposeIV.AdicTensorSupported
import SGA.SGA2.ExposeIV.SupportedDualizingTransfers
import SGA.SGA2.ExposeIV.LocalFiniteLengthCategory
import SGA.SGA2.ExposeIV.MacaulayDualizingModule
import SGA.SGA2.ExposeIV.LocalCompletionEquivalence
import SGA.SGA2.ExposeIV.CompletionSubmodules
import SGA.SGA2.ExposeIV.CompletionExactness
import SGA.SGA2.ExposeIV.SupportedDualityTransport
import SGA.SGA2.ExposeIV.FiniteSupportedCompletionEquivalence
import SGA.SGA2.ExposeIV.CompletionDualizingTransfer
import SGA.SGA2.ExposeIV.NonlocalDualizingLocallyArtinian
import SGA.SGA2.ExposeIV.MatlisCompleteDuality
import SGA.SGA2.ExposeIV.MatlisArtinianCompletion
import SGA.SGA2.ExposeIV.MatlisCompletedRingDuality
import SGA.SGA2.ExposeIV.MatlisArtinianModules
import SGA.SGA2.ExposeIV.EssentialSocles
import SGA.SGA2.ExposeIV.MatlisCompletedHomComparison
import SGA.SGA2.ExposeIV.MatlisDuality
import SGA.SGA2.ExposeIV.MatlisDualityTransport
import SGA.SGA2.ExposeIV.MatlisFiniteLengthIntersection
import SGA.SGA2.ExposeIV.CompleteScalarAction
import SGA.SGA2.ExposeIV.RegularLocalExtVanishing
import SGA.SGA2.ExposeIV.RegularLocalExtFunctor
import SGA.SGA2.ExposeIV.RegularLocalTopExt
import SGA.SGA2.ExposeIV.RegularLocalExtDuality
import SGA.SGA2.ExposeIV.RegularLocalCohomologyDuality
import SGA.SGA2.ExposeIV.RegularMacaulayComparison
import SGA.SGA2.ExposeIV.ModuleExtDerivedCoefficientNaturality
import SGA.SGA2.ExposeIV.RegularLocalDepth
import SGA.SGA2.ExposeIV.CofiniteIdeals
import SGA.SGA2.ExposeIV.FiniteLengthRestrictedHom
import SGA.SGA2.ExposeIV.CofiniteFunctorEquivalence
import SGA.SGA2.ExposeIV.CofiniteFunctorExactness
import SGA.SGA2.ExposeIV.NonlocalDualizingRepresentation
import SGA.SGA2.ExposeIV.MacaulayContinuousDual
import SGA.SGA2.ExposeIV.PowerSeriesPowerQuotientBasis
import SGA.SGA2.ExposeIV.PowerSeriesResiduePairing
import SGA.SGA2.ExposeIV.PowerSeriesResidueDuality
import SGA.SGA2.ExposeIV.MatlisFiniteLengthDetection

/-!
# SGA 2, Exposé IV: dualizing modules and functors

This partial formalization proves the canonical module structure of an
additive functor, IV.1.1 with its specified evaluation map, and the resulting
equivalence between arbitrary modules and additive left-exact contravariant
functors on finite modules. It also proves IV.2.1 for the original functor:
exactness is equivalent to injectivity of its actual representing colimit,
using Artin–Rees and Baer's criterion. IV.2.2 is also proved.

The Hom-detection argument of IV.1.4 covers arbitrary supported target
modules; it does not assume those targets are finite. IV.1.3 is proved with
the actual colimit of `T(R/Jⁿ)`, canonical stage evaluation and its proved
choice independence. The actual restricted Hom functor gives the equivalence
of supported modules and additive left-exact functors on finite supported modules.
IV.1.4 proves the three vanishing conditions for arbitrary integer-indexed
bounded-below exact delta functors, deriving left exactness from their actual
connecting sequences. Arbitrary support in `V(J)` is equivalent to ideal-power
torsion, without assuming the supported module finite.

IV.1.2 is proved for the original additive functor on all modules: canonical
evaluation with target `T(R)` is invertible precisely when the functor preserves
arbitrary projective limits indexed by preorders, not necessarily filtered.
The actual module is proved to be the colimit of its finite submodules.
IV.3.1 is proved as the full four-condition equivalence for the original
additive abelian-group-valued functor. The canonical action, actual finite-valued
factorization, natural map into actual `T(T(M))`, and all comparison maps are
constructed. Left exactness and finite values occur inside the first condition,
not as extra hypotheses. IV.3.2 proves length preservation alone implies
exactness under the standing left-exactness hypothesis of IV §3; finite values
are derived. The opening of §5 gives the actual original functor's
anti-equivalence, the actual orthogonal order-reversing submodule bijection,
both length/colength identities, and the Artinian-local correspondence of
ideals with actual coefficient submodules via annihilation. Over a local ring,
actual single generation is equivalent to the original dual's socle having
length at most one, including the zero module.

IV.4.3–4.4 prove actual finite local coinduction and the quotient-annihilator
construction, retaining support and canonical Hom biduality. IV.4.5's actual
map `M → M ⊗ Â` is invertible for arbitrary locally Artinian modules, not only
finite ones; this is not the adic completion of `M`. Original representing
colimits are locally Artinian, and their actual ideal-power annihilators have
finite length under duality and form a categorical colimit. Actual tensor
extension and restriction give inverse equivalences on supported modules
and on the literal locally Artinian categories. No extra noetherianity
hypothesis on the completed ring is imposed.
IV.4.6 transfers the actual supported-dualizing property in both directions
through original restriction/tensor extension. The Hom comparison retains
actual values and intertwines the specified canonical bidual evaluation.
IV.4.7 proves existence, injective-envelope characterization, and uniqueness
under the explicit supported representing-module convention. The envelopes
are constructed using enough injectives and two Zorn arguments. No uniqueness
claim is made for arbitrary Hom targets with invisible off-support summands.

IV.4.2 constructs an exact linear duality on the whole finite-length module
category using the actual injective envelope of the sum of all residue fields.
Its original canonical evaluation is a natural isomorphism, and each actual
maximal-ideal annihilator has length one. The coefficient is locally Artinian,
proved via associated primes of its actual essential semisimple submodule.
Every additive left-exact functor on the entire finite-length category is
now represented by its actual cofinite-ideal colimit, with canonical scalar
action and evaluation. Original Hom gives an equivalence with locally
Artinian modules over a noetherian ring, without assuming a local base.
Exactness of the original functor is equivalent to injectivity of this
actual colimit among all modules, by a genuine cofinite Artin–Rees/Baer proof.
For every original linear involutive finite-length functor, this coefficient
is injective and locally Artinian, and each actual maximal-ideal annihilator
is one copy of its residue field. These assertions concern the actual
cofinite representative; arbitrary raw Hom targets may have invisible
summands. The supplied natural involution is not relabelled canonical evaluation.
The local finite-length category
is explicitly identified with the original finite supported category.
IV.5.1 is proved over a complete noetherian local base: the actual Hom
functors give inverse equivalences between finite modules and locally Artinian
modules with finite socle, with original canonical bidual evaluations.
For an arbitrary noetherian local base, the actual dual of a locally Artinian
finite-socle module is complete with finite-length power quotients. The actual
bidual of every finite module is its adic completion, compatibly with the
original evaluation and completion maps. Topological Nakayama and Hom
cogeneration are proved, rather than included as extra hypotheses.
The actual completion/restriction equivalence also preserves finite socles,
giving the full original `CA` completion equivalence with its tensor unit
and multiplication counit, without assuming noetherianity of the completion.
Noetherianity of actual adic completions is now proved for every ideal in a
noetherian ring, by a genuine surjective map from a finite-variable power
series ring. Thus the original `CA` category is also anti-equivalent to finite
modules over the actual completed ring via scalar change and completed-ring Hom.
The latter functor is naturally identified with original-ring Hom after
restriction, with pointwise tensor-unit formula and inverse actual tensor map.
The original `CA` property is also equivalent to genuine Artinianity over
every noetherian local base. All-module Hom cogeneration gives the orthogonal
submodule embedding, and the actual completion action preserves the entire
supported submodule lattice and its descending-chain condition.
Every essential embedding preserves the actual socle and its finiteness;
this applies to the constructed injective envelopes without finiteness of
the whole envelope.
For IV.5.3–5.4, actual regular local rings have residue-field projective
dimension equal to Krull dimension, and original Ext of any finite-length
first argument into the ring vanishes in every other degree. The top
module-valued residue Ext is computed by the original regular Koszul
resolution and the actual top coefficient quotient, with an additive
comparison to derived-category Ext. This comparison is proved linear for
the original Ext actions. The genuine derived-category top Ext functor is
dualizing on the original finite supported category and canonically represented
by its actual supported dualizing quotient-Ext colimit. The final comparison
identifies this colimit with original algebraic local cohomology as a module,
respecting the original quotient transitions and colimit stage maps. Thus
the actual top local cohomology module is supported dualizing and represents
the original top Ext functor naturally. The affine supported-sheaf-cohomology
interpretation is also proved as an additive-group isomorphism.
The arbitrary-module global-dimension assertion in IV.5.3 is proved in
`ExposeV.GlobalProjectiveDimension`: support-dimension induction extends the
finite-length bound to finite modules, and Baer's criterion with actual
injective dimension shifting gives the bound for arbitrary modules. The
original residue field realizes equality with Krull dimension.
IV.5.2 proves Macaulay's literal coefficient-field Hom duality and its actual
quotient-dual colimit representation, assuming only that the residue field
is finite-dimensional over the coefficient field, not that the ring is.
The original quotient-dual colimit is canonically the continuous linear dual
of the original adic ring, without assuming completeness. In a literal
finite-variable power series ring, coordinate-power quotients have their
actual monomial basis and a perfect product-residue pairing.
These pairings now glue through the original product transitions to give an
explicit isomorphism from actual maximal-ideal top local cohomology to the
continuous dual and the original Macaulay module. The coefficient-field
linear residue form has the original monomial formula and its product pairing
is nondegenerate. A Cohen presentation for a general complete regular local
ring, completed differentials, and intrinsic parameter independence remain open.
IV.5.5's initial noncanonical isomorphism between the actual local cohomology
and Macaulay modules is proved; the explicit intrinsic residue pairing is not.
The literal `DA` category is equivalent to its completed-ring version by
actual module-adic completion and restriction. Combining this with the
proved original Hom comparison gives IV.5.1 over an arbitrary noetherian
local ring: the forward functor is exactly original-ring Hom; the inverse
is actual completed-ring Hom through these canonical scalar comparisons.
The later structural and explicit residue-pairing results remain incomplete.
-/
