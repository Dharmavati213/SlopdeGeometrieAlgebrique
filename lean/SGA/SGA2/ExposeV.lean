/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.ExtPairing
import SGA.SGA2.ExposeV.InjectiveHomComplexExt
import SGA.SGA2.ExposeV.InjectiveHomComplexProduct
import SGA.SGA2.ExposeV.ProjectiveExtConnectingCocycle
import SGA.SGA2.ExposeV.LocalCohomologyBoundaryComparison
import SGA.SGA2.ExposeV.HomComplexContravariantNaturality
import SGA.SGA2.ExposeV.HomComplexPairingNaturality
import SGA.SGA2.ExposeV.InjectiveHomModuleExtBoundary
import SGA.SGA2.ExposeV.InjectiveHorseshoeBoundaryNaturality
import SGA.SGA2.ExposeV.InjectiveResolutionSequenceNaturality
import SGA.SGA2.ExposeV.RingedModuleAdditiveCohomology
import SGA.SGA2.ExposeV.RingedModuleAdditiveNaturality
import SGA.SGA2.ExposeV.RingedModulePushforwardSpectralSequence
import SGA.SGA2.ExposeV.RingedModuleSpectralFiltration
import SGA.SGA2.ExposeV.RingedModuleSpectralAbutment
import SGA.SGA2.ExposeV.RingedModuleSpectralE2Linear
import SGA.SGA2.ExposeV.RingedModuleSpectralE2Naturality
import SGA.SGA2.ExposeV.RingedModuleSpectralAbutmentNaturality
import SGA.SGA2.ExposeV.ModuleExtPairing
import SGA.SGA2.ExposeV.LocalDualityMap
import SGA.SGA2.ExposeV.RegularLocalVanishing
import SGA.SGA2.ExposeV.LocalDualityUnit
import SGA.SGA2.ExposeV.LocalDualityRing
import SGA.SGA2.ExposeV.LocalDualityTopFinite
import SGA.SGA2.ExposeV.LocalDuality
import SGA.SGA2.ExposeV.LocalCohomologyFiniteness
import SGA.SGA2.ExposeV.LocalRingUpperVanishing
import SGA.SGA2.ExposeV.ModuleDimensionVanishing
import SGA.SGA2.ExposeV.LocalRingFiniteness
import SGA.SGA2.ExposeV.CompletedDualDimension
import SGA.SGA2.ExposeV.CompleteTopLocalCohomology
import SGA.SGA2.ExposeV.LocalRingTopNonvanishing
import SGA.SGA2.ExposeV.TopLocalCohomologyAssociatedPrimes
import SGA.SGA2.ExposeV.SupportedFunctorComponents
import SGA.SGA2.ExposeV.AffineComplementCodimension
import SGA.SGA2.ExposeV.LocalCohomologyFiniteLength
import SGA.SGA2.ExposeV.SurjectiveDualityChange
import SGA.SGA2.ExposeV.PuncturedDepthCriterion
import SGA.SGA2.ExposeV.GlobalProjectiveDimension
import SGA.SGA2.ExposeV.HomologicalRegularityCriterion
import SGA.SGA2.ExposeV.LocalCohomologyFiniteLengthCriterion

/-!
# SGA 2, Exposé V: canonical local duality

The literal displayed Hom-complex differential of V.1 is constructed on the
original graded families, with square-zero, actual Leibniz and homotopy
identities. Multiplication by `(-1)^(n(n+1)/2)` gives an explicit chain
isomorphism to Mathlib's convention. Actual precomposition by a quasi-isomorphism
preserves cohomology into a K-injective target. For any two given injective
resolutions, the sign-normalized augmentation into ordinary Hom is therefore
a quasi-isomorphism, and its actual homology map computes Ext as in V.1.3.
The component formula displays the required sign on the original augmentation;
the source's unsigned ordinary-Hom augmentation claim is not asserted.
The actual graded composition descends to a biadditive cohomology pairing,
with its original representative formula and associativity. The previously
constructed double-resolution Ext equivalence carries the standard Hom-complex
product to Yoneda composition. The source complex has its own verified kernel
and quotient data with unscaled cocycles. Its original product acquires exactly
`(-1)^(ij)` under the sign-normalized Ext comparison, as proved on actual homology.
The lift-and-differentiate boundary is now compared on original cocycles:
the actual mapping-cone lift projects to the original cocycle and composes
with the cone's third arrow to its original boundary. This gives the derived
connecting morphism of the original short exact sequence. In the literal source
convention the target-degree sign is explicit. For the unsigned projective
Hom representatives used by module-valued Ext, composition with the actual
extension class is `(-1)^(n+1)` times the lifted boundary's `extMk` class.
Projectivity and exactness provide these original lifts for every Ext class.
The existing linear comparison now sends actual module-cohomology representatives
to those same `extMk` classes in every degree, including zero. Thus the original
module-valued Yoneda coefficient boundary is exactly `(-1)^(n+1)` times the
independently constructed coefficient boundary. The same equality holds on the
unchanged Ext diagrams, filtered colimits, and ideal-power local-cohomology
objects. The original contravariant Hom sequence into a degreewise-injective
complex is now short exact, and its actual long exact sequence is natural.
For a K-injective target, its boundary is compared to precomposition by the
original derived connecting arrow in every integer degree: the standard
convention contributes `(-1)^(n+1)`, while the literal source convention has
no extra sign under its fixed unscaled quotient equivalence. The latter
equivalence is also natural for the original precomposition maps.
The covariant Hom sequence is now short exact for any source complex when
the first coefficient complex is degreewise injective, using actual degreewise
splittings derived from injectivity. Both differentials give natural long
exact sequences and original lift-and-differentiate representatives. With
K-injective endpoints, the standard boundary is the derived connecting arrow;
the literal source boundary contributes `(-1)^(n+1)` under the same unscaled
quotient comparison, now also proved natural in coefficients.
The original pairing is natural in the middle complex and compatible with
the two independently constructed Hom boundaries without boundedness or
K-injectivity: its factor is `(-1)^(j+1)` in the standard convention and
`(-1)^(i+1)` for the literal source differential. The composite of original
lifts is an explicit coboundary witness. An unsigned identity for these
unchanged source conventions is not asserted.
For a supplied augmented short exact sequence of chosen injective resolutions,
the augmentation squares now identify its actual derived connecting arrow
with the original extension class. The previously specified double-resolution
Ext equivalences, including the normalized source equivalence, carry the
actual covariant Hom boundary to the original Yoneda boundary and the
contravariant one to it with factor `(-1)^(n+1)`. These comparisons hold in
every natural degree, including zero, and are also proved on the original
module-valued Ext objects through the unchanged canonical linear comparison
(as additive-group identifications). The injective horseshoe now constructs
such an augmented exact resolution sequence for every short exact sequence
in an abelian category with enough injectives. Actual categorical cokernels
give the successive syzygies, and the original horizontal maps extend to
degreewise split sequences with strictly commuting augmentation squares.
The same split rows are injective as objects of the short-complex category.
Thus the unchanged horseshoe is an injective resolution of the whole row,
with simultaneous comparison maps and homotopies preserving both horizontal
arrows. Its integer-indexed sequence comparisons strictly preserve the original
augmentations. Identity, composition, and uniqueness up to homotopy give a
functor on short exact sequences. Arbitrary injective row-resolution changes
satisfy naturality and the cocycle identity in the homotopy category.
Both original Hom boundaries are natural under the constructed comparisons,
for both differential conventions and all integer degrees. Arbitrary separately
specified resolution sequences now give the same kind of simultaneous row
resolution: full faithfulness recovers their original nonnegative maps,
and exactness and augmentations are retained. They have actual augmented
comparison maps with coherent row homotopies and natural cocycle-compatible
model changes. The fixed standard and normalized-source Hom/Ext equivalences
respect precomposition and postcomposition in every natural degree, including
zero. Model changes over identities act as the identity under these unchanged
equivalences, also on the original module-valued Ext objects. Both original
Hom boundaries are natural for these arbitrary-model comparison maps.

The actual derived-category Yoneda pairing is linear, natural, and compatible
with both original Ext long-exact-sequence boundaries. Its canonical linear
comparison with the module-valued Ext used by local cohomology transports
the pairing and its naturality in all three variables. The original quotient
Ext stages give a canonical natural local-duality map into
`Hom_R(Ext^j(M,P), H^n_J(P))`, for `i+j=n` over any commutative ring.
Evaluation at the original identity Ext class retracts the top-degree map
with equal coefficients. The canonical rank-one ring case is an actual
isomorphism for every ideal and degree, with no regularity assumption.
Additivity extends this to finite free modules. The genuine finite-presentation
argument and proved right exactness of both original functors then give
V.2.1 in top degree for every finite module over a regular local ring, as a
natural isomorphism of the original finite-module functors. The canonical
linear Ext comparison also transports the exact Yoneda sequences onto the
unchanged original Ext objects. Their filtered colimits give exact sequences
on actual local cohomology, and stagewise Yoneda associativity intertwines
their boundaries with the canonical local-duality map. Descending induction
through actual finite free covers proves V.2.1 in every complementary degree.
The canonical transpose identifies dual local cohomology with the actual
completion of complementary Ext; the transpose becomes the original completion
map. Over a complete regular base this gives V, formula (22), naturally on finite modules.
For every noetherian local base, all local-cohomology values of finite modules
are Artinian, with finite socle and finite-length power annihilators. Their
actual duals are complete with finite-length power quotients, and finite over
the original ring when that ring is complete. Their original completions are
finite over the actual completed ring, even over a noncomplete base. This
proves V.3.1(ii)'s finite-generation assertion without Cohen reduction.
The proof preserves finite original residue Ext through actual injective
envelopes and their actual cokernels, and uses the genuine coefficient exact
sequence. It also proves Artinianity for arbitrary modules with finite residue
Ext in every degree, without assuming the whole module finite.

V.3.1(ii)'s dimension bound is also proved over every noetherian local base.
The actual torsion quotient preserves positive local cohomology and admits
a regular element. Original scalar maps remain scalar maps on local cohomology;
dualizing the genuine regular-element sequence bounds the principal quotient
of the higher dual by the lower dual. Since these duals are already complete,
their exact sequence stays exact under actual completion, with its existing
completed-ring actions. The completed-ring dimension inequality gives the
bound by induction on degree. Over a complete base the original dual itself
has dimension at most the cohomological degree.

Over complete noetherian local rings, V.3.1(iii)'s top-dual dimension equality
and top-degree nonvanishing are now proved. Removing actual torsion preserves
positive support dimension. A simultaneous regular element on the coefficient
torsion quotient and preceding dual's torsion quotient confines the dual
sequence's error to the closed point. Upper vanishing makes that element
regular on the top dual; induction on the actual coefficient dimension
gives the equality. The zero-dimensional base retains the original torsion
inclusion and canonical Hom duality. No regularity of the base is assumed.

Top-degree nonvanishing in V.3.1(iii) also holds over every noncomplete
noetherian local base. Prime avoidance of contracted associated primes
chooses an original scalar regular on the coefficient torsion quotient and
the preceding completed dual's torsion quotient. The actual completion maps
preserve the genuine dual exact sequences and original scalar injectivity.
Induction proves that the completed top dual has exactly the original
coefficient support dimension, forcing original top local cohomology to be
nonzero. No Cohen presentation or base-change comparison is assumed.

V.3.1(iii)'s associated-prime formula is now proved for the original top
Hom dual, even without completeness of the base. Original local cohomology
is right exact on finite modules supported on a fixed closed set of bounded
dimension. Nonvanishing and actual chains of primes identify the dual's
vanishing with missing the top component generic points. V.3.3, proved
for actual irreducible component families as well as minimal-prime indices,
computes the associated primes
of IV's actual representing colimit using the original cyclic tests `R/p`.
The canonical module lift agrees with the original dual's scalar action;
III.1.3 then computes the associated primes of the unchanged top dual.

V.3.4 is proved for every actual irreducible component of any closed subset
with affine complement in a noetherian affine spectrum. Actual affine-chart
and sheaf comparisons give positive cohomology vanishing on the complement.
The original relative sequence and algebraic comparison imply local cohomology
vanishes above degree one. Localizing at a component generic point identifies
the inverse image of that complement with the actual punctured local spectrum.
Original top nonvanishing bounds its dimension by one. The component's actual
codimension, the infimum of its original structure-stalk dimensions, is thus
at most one; no principal-support hypothesis is imposed.

V.3.5 is proved for finite modules over quotients of regular local rings. Original
Hom duality detects finite length on arbitrary modules without completeness.
Original local cohomology over a regular local ring has the same extended
length as complementary Ext. Finite projective resolutions and the actual
Hom localization comparison identify localized Ext with Ext over the localized
ring, linearly over that ring. Thus finite length of local cohomology is
equivalent to vanishing of actual complementary Ext at every nonclosed point.
The quotient reduction is proved on both original conditions: actual local
ring maps and localized coefficients, prime-quotient dimensions, and all
nonclosed points are accounted for. Points outside the image contribute zero.
Shifted vanishing through a threshold is equivalent to the original localized
depth inequality, proving V.3.6 under the same source hypotheses. Negative
shifted degrees impose no condition; zero modules retain infinite depth.
The dimension formula is proved using the top-dual associated-prime formula:
complementary Ext of the original prime quotient is nonzero at that prime,
so the localized residue Ext identifies the complementary degree with the
local ring's dimension. Both regularity and the dimension formula are proved,
and neither V.3.5 nor V.3.6 assumes an extra local criterion.

The homological input for prime-localization regularity is proved: every
finite module over a regular local ring has projective dimension bounded
by the original ring dimension. The actual localization of `R/p` is the
actual residue field of `R_p`, with its original element map, so residue
fields at all primes inherit the bound. Baer's criterion and genuine
injective dimension shifting extend cyclic bounds to arbitrary modules.
This also proves IV.5.3's global-dimension equality and upper Ext vanishing
with both arguments arbitrary. Every prime localization has finite global
dimension. The converse homological regularity criterion is now proved:
finite residue-field projective dimension forces regularity. An associated
maximal ideal would force the ring to be a field; otherwise prime avoidance
chooses a regular element outside its square. Actual quotient-ring linear
splittings lower the residue-field bound, and lifting minimal generators
completes the induction. Thus every prime localization is genuinely regular,
and its global dimension equals its own Krull dimension.

The algebraic change-of-rings steps in V, formulas (19)--(21), are proved.
The actual inverse Koszul systems commute with arbitrary tensor extension,
including non-flat quotient maps. The original Hom adjunction, exact scalar
restriction, and original colimits give local-cohomology scalar restriction
for every ideal over noetherian rings and every coefficient module. Surjective
local-ring maps identify the actual maximal-ideal cohomology modules and
preserve their extended length. Actual coinduction of a supported dualizing
module and one coefficient isomorphism give the Hom-dual comparison, naturally
in all modules. Original annihilator quotients are isomorphic, and finite
generation and support dimension are unchanged.

V.3.1(i)'s module-dimension upper vanishing is proved over every noetherian
local ring. Parameters are constructed in the actual annihilator quotient
and lifted; finite annihilator generators are prepended. Above the module
dimension, the original consecutive-power Hom--Koszul transition is zero.
The unchanged Koszul colimit and radical comparisons give the assertion for
original local cohomology, without regularity, completeness, or Cohen reduction.
Dimension-length parameters also give the ring-dimension bound for arbitrary
coefficient modules over every noetherian local ring.

For actual regular local rings, local cohomology of every module vanishes
above the dimension; with ring coefficients it is concentrated in the
dimension and nonzero there. Thus the above-dimension vanishing case is also
proved. The transported covariant Yoneda boundaries now have the proved signed
comparison with the original module-valued coefficient and local-cohomology
boundaries in all degrees. Both actual Hom sequences now have exactness,
naturality, their signed pairing compatibility, and their derived-boundary
comparisons (with K-injective target complexes). The double-resolution and
original module-valued Ext boundary comparisons are proved for supplied
augmented exact resolution sequences. The horseshoe now constructs such
sequences and simultaneous comparison maps, with functoriality and coherent
row-resolution change in the homotopy category. The same construction now
handles arbitrary separately specified resolution-sequence models, and its
actual model-change maps preserve the fixed Hom/Ext equivalences and both
original Hom boundaries.
For V.3.2, the actual supported-section functors on arbitrary ringed spaces now
retain their module structures. Injective module sheaves are flasque; forgetting
to additive sheaves is exact; supported sections preserve short exact sequences
with flasque kernel. Their actual module-valued right-derived functors vanish
in positive degrees on flasque modules, including direct images of injective
modules under arbitrary morphisms of ringed spaces. The right-derived
supported-section/direct-image composite is naturally supported cohomology on
the source, restricted along the actual global ring map in every degree.
Bounded-below flasque mapping cones prove the needed quasi-isomorphism
comparison with additive-injective resolutions. In every degree, forgetting
the resulting module cohomology recovers the original additive-sheaf `H_Z`.
These last comparisons are now natural in the original coefficient maps,
by augmentation-compatible chain homotopies between resolution comparisons.
Global scalars act naturally on the underlying additive complexes and their
derived objects. Canonical truncations of the actual module direct-image
resolution now give a genuine module-valued spectral sequence. Forgetting the
retained action canonically recovers the entire original additive sequence,
including its differentials and next-page homology isomorphisms. Its actual E₂
groups are the original supported cohomology of the original higher module
direct images. First-quadrant bounds and a finite exhaustive module filtration
of the canonical total object are proved: pages with `r ≥ n + 2` in total
degree `n` are its genuine associated-graded module quotients. The actual total
module now identifies module-linearly with original source supported cohomology
restricted along the prescribed global ring map. The finite exhaustive
filtration is transported to that original cohomology module. This uses the
canonical derived-Hom comparison on bounded-below flasque complexes, natural
in all additive cochain maps, not preservation of injectivity under direct
image. The original E₂ comparison is now module-linear: its canonical page,
truncation/shift and supported-cohomology factors all retain the original scalar
maps, and its underlying additive equivalence is exactly the preexisting one.
Actual coefficient maps now make this module spectral sequence a functor.
Resolution homotopies give lift-independence, functor laws and canonical natural
change-of-resolution isomorphisms with their cocycle law. The original E₂ and
abutment identifications commute with the original higher-direct-image and source
cohomology coefficient maps. These maps preserve the original source finite
filtration, which is independent of resolution; stable-page comparisons commute
with the genuine associated-graded maps. The source's Cohen presentation is not
formalized and is not assumed in the proved general-local bounds or algebraic
scalar change.
-/
