# Formalization notes

The Lean library in `lean/` follows Grothendieck's numbering of SGA 1 and SGA 2.
Mathlib already has the language of the exposés; we import it and add
the statements that are still missing.

## Exposé I — Étale morphisms

Entry point: `lean/SGA/SGA1/ExposeI.lean`.

SGA works with locally noetherian schemes after no. I.2 and defines
étale as flat + unramified of finite type. Mathlib's `Etale` is
formally étale of finite presentation. On a locally noetherian base
these agree (`etale_of_flat_unramified_locallyNoetherian`).
Universally injective is SGA's radicial.

| SGA 1 I | Mathlib |
| --- | --- |
| I.1 `Ω¹_{X/Y}` | `Ω[S⁄R]`, `FormallyUnramified` |
| I.2 quasi-finite | `Algebra.QuasiFinite`, `LocallyQuasiFinite`, `QuasiFiniteAt` |
| I.3 net / unramified | `FormallyUnramified`, `Algebra.Unramified` |
| I.3.1 residue / `mS = n` | `FormallyUnramified.iff_map_maximalIdeal_eq` |
| I.3.4 graph | `pullback_lift_diagonal_isPullback` |
| I.4 étale | `Etale`, `Algebra.Etale` |
| I.4.9 covering | `IsFinite` + `Etale`, `CommAlgCat.FiniteEtale` |
| I.5.1 étale + radicial | `IsOpenImmersion.of_flat_of_mono` |
| I.5.5 uniqueness | `FormallyUnramified.hom_ext` |
| I.7 standard étale | `StandardEtalePair`, `IsStandardEtale` |
| I.7.6–I.7.8 | `IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`, `IsEtaleAt.exists_isStandardEtale` |
| I.9.5 integral closure | `TensorProduct.toIntegralClosure_bijective_of_smooth` |
| I.10 normalisation | `Scheme.Hom.toNormalization` |

## Exposé VI — Fibered categories and descent

These are the names to import, not to redo.

| SGA 1 VI | Mathlib |
| --- | --- |
| VI.2 category over another | `BasedCategory`, `BasedFunctor`, `BasedNatTrans` |
| VI.4 fiber-category | `CategoryTheory.Functor.Fiber`, `HasFibers` |
| VI.5.1 cartesian morphism | `Functor.IsCartesian` |
| strongly cartesian | `Functor.IsStronglyCartesian` (Stacks 02XK) |
| VI.6.1 prefibered / fibered | `Functor.IsPreFibered`, `Functor.IsFibered` |
| VI.8 cloven / Grothendieck construction | `∫ᶜ`, `Pseudofunctor.CoGrothendieck.forget` |
| VI.9 split (1-functor) | `Functor.toPseudofunctor'` then `∫ᶜ` |
| VI.10 cocartesian | `Functor.IsCocartesian` |
| descent data, (pre)stack | `Pseudofunctor.DescentData`, `IsPrestack`, `IsStack` |

Entry point: `lean/SGA/SGA1/ExposeVI.lean`.

## Corrections relative to the English draft

- Both quasi-inverse identities are required for an equivalence of
  categories (VI.1). A one-sided `GF ≅ id` is not enough; see
  `Examples.selectFalse_not_isEquivalence`.
- The remark after VI.6.1 needs prefiberedness in (i). All morphisms
  cartesian does not imply lifts exist; see
  `Examples.oneToTwo_not_prefibered`.
- Ordinary equivalence is weaker than equivalence over the base
  (VI.4.2); see `Examples.oneToTwo_not_basedEquivalence`.

## Remaining gaps in Exposé I

- I.2.1(iii): quasi-finite local homomorphisms via finiteness of completions.
- I.3.7 / I.4.4: unramified (resp. étale) iff the map of completions is a
  quotient (resp. an isomorphism), when the residue extension is trivial.
- I.4.10: discriminant / trace pairing criterion for étale coverings.
- I.5.3–I.5.4 in full: a section of a connected unramified scheme is an
  isomorphism onto a connected component; two morphisms that agree
  geometrically at a point are equal. Open-and-closed immersions of the
  section are in `Fundamental.lean`; identification with a component uses
  locally noetherian connectedness.
- I.5.5 existence / I.8.3 essential surjectivity: étale schemes lift
  uniquely along nilpotent closed immersions; existence of the lift of
  the scheme (not just of morphisms) remains.
- I.6.1 over a complete local ring (the artinian case of I.6.2 is proved).
- I.8.4: étale coverings of a locally noetherian formal scheme.
- I.9.1 in general (regularity of local étale algebras); the identification
  `m_A S = m_S` is recorded.
- I.9.5(ii) and I.9.11: unramified + injective over a normal local ring
  is étale; dominant unramified over a normal base is étale.
- I.10.3, I.10.7–I.10.12: the equivalence with unramified extensions of
  the function field, and the counting of geometric fibre points.
- I.11: the examples, and étale descent along a universal homeomorphism
  (IX.4.10).

## Remaining gaps in Exposé VI

- VI.6.3–6.8, VI.6.10 (fiber products of cartesian arrows, fiberwise
  criterion for cartesian functors).
- VI.7.2 converse, VI.7.3–7.4 (normalized cleavages, associativity of
  `c_{f,g}`).
- VI.10.1 (prefibered + precofibered ⇒ fibered iff cofibered).
- VI.11(a)–(d), (f)–(g) beyond the discrete-base case.
- VI.12.1 as an isomorphism of functor categories (only the constraint
  data of a total functor is recorded).

## SGA 2, Exposé I — Local cohomological invariants

Entry point: `lean/SGA/SGA2/ExposeI.lean`.

Exposé I is topological (abelian sheaves on a space `X`, functors `Γ_Z`
and their derived functors `H_Z^*`). Mathlib supplies flasque sheaves,
pushforward/pullback, `Ext` on Grothendieck abelian sheaf categories, and
the *algebraic* local cohomology of modules. This repo defines topological
`H_Z^*` for closed supports as `Ext(ℤ_{Z,X}, −)` following I.2.3 bis.

| SGA 2 I | Mathlib / this repo |
| --- | --- |
| I.1 `Γ_Z` (closed `Z`) | `gammaZ`, `gammaZSections` (`GammaZ.lean`) |
| I.1 (8) `Γ̲_Z` sheaf | `underlineGammaZ` = `ker(F → j_* j^* F)` (`UnderlineGammaZ.lean`) |
| I.1 (8), actual section comparison | `underlineGammaZSectionsEquiv`, `underlineGammaZPresheafFunctorIso`: original kernel-sheaf sections are supported sections, naturally in coefficients and opens; the original functor is additive and left exact |
| I.1 (3) locally closed | `LocallyClosedIn`, `LocallyClosedIn.gamma` |
| I.1 independence of open | `gammaZSections_restrict_addEquiv` |
| I.1 special cases | closed pushforward, open restriction, `underlineGamma_locallyClosed`; `zZX_closed` |
| I.1.3–I.1.4, open case | `iBang_open`, `openExtensionByZeroAdjunction`: genuine exact open extension by zero, left adjoint to restriction; `restrictToOpen_injective` |
| I.1.3–I.1.4, closed and locally closed | `closedSupportAdjunction`, `locallyClosedSupportAdjunction`: genuine arbitrary-coefficient adjunctions; exact fully faithful closed extension and injective-preserving extraordinary inverse image; `closedSupportPushforwardIso` and `closedSupportPullbackIso` compare with the original kernel, including actual counit compatibility |
| I.1.6, closed case | `closedSupportHomEquiv`: actual `Hom(zZX_closed Z, F)` is naturally the additive group of supported sections |
| Internal Hom and sheaf Ext | `abelianSheafHom`, `internalHomSectionsRestrictEquiv`, `internalSheafExtSheafificationIso`: genuine sheaf of local morphisms, left exactness, actual restriction-Hom comparison, and right-derived sheaf Ext as sheafification of local Ext |
| Closed support under arbitrary open restriction | `closedSupportRestrictionIso`: actual pullback of the closed integer support sheaf is the support sheaf of the restricted closed set, compatibly with its full integer-presheaf presentation |
| I.1.6 / I.2.3 bis, closed support, sheaf-valued | `closedSupportInternalHomFunctorIso`, `closedSupportInternalSheafExtIso`, `closedSupportInternalSheafExtIsoModel`: actual internal Hom and its derived sheaf Ext identify naturally with the original supported-sheaf functor and unchanged model |
| I.1.6 / I.2.3, open case | `openSupportHomEquiv`, `openSupportExtEquiv`: actual open extension by zero represents sections on the open and its Ext is ordinary cohomology of restriction, naturally in coefficients and compatibly with coefficient boundaries |
| I.1.8 degree 0 | `exact_gammaZ_of_le`, `I_1_8_package`; global flasque extension |
| I.1.9–I.1.10, constant support objects | `constantSupportSequence_shortExact`: actual `0 → ℤ_{X\\Z,X} → ℤ_X → ℤ_{Z,X} → 0`; open inclusion agrees with restriction under the genuine adjunction |
| I.1, (13)/(17), arbitrary coefficients | `locallyClosedSingleExtensionSequence_shortExact`, `locallyClosedSingleExtensionSequenceFunctorIso`: genuine single-witness extension endpoints for every coefficient sheaf, with original counit/unit arrows and literal coefficient-map compatibility; the required closed/open composition cases are proved |
| I.1.10, general integer-support sequence | `locallyClosedNestedObjectSequence_shortExact`, `nestedClosedSubspaceObjectSequence_shortExact`: actual `0 → ℤ_{Z″,X} → ℤ_{Z,X} → ℤ_{Z′,X} → 0` for arbitrary locally closed `Z` and closed `Z′` in its literal support space; the witnesses represent the original closed subset and its set difference |
| I.1.10, internal-Hom arrows | `nestedSupportObjectRestriction_internalHom`, `nestedSupportObjectInclusion_internalHom`, `nestedSupportInternalHomSequenceIso`: internal Hom of both actual support-object arrows gives the original I.1.9 sheaf arrows in any open/closed presentation, with a genuine isomorphism of short complexes |
| I.1.9, general supported-sheaf sequence | `locallyClosedNestedSheafSequence_exact`, `locallyClosedNestedSheafInclusion_mono`, `locallyClosedNestedSheafSequence_shortExact`: actual ambient supported functors, actual section inclusion and restriction, left exactness for every coefficient, and short exactness for flasque coefficients |
| I.1.8, general original section groups | `locallyClosedNestedGammaSequence_exact_and_mono`, `locallyClosedNestedGammaSequence_shortExact`: the original locally closed section functors, with actual inclusion/restriction, form a natural left exact sequence, short exact on flasque coefficients |
| I.1.6 / I.2.3 bis, locally closed internal Hom and sheaf Ext | `locallyClosedSupportInternalHomFunctorIso`, `locallyClosedSupportInternalSheafExtIso`: the original ambient locally closed supported functor is actual internal Hom from the original integer-support object, and the all-degree original derived functors are its sheaf Ext; both coefficient and ambient-open naturality are proved |
| I.2.1 / I.2.3 bis `H_Z^n` | `H_Z Z F n` := `Ext (zZX_closed Z) F n` |
| I.2.1 original derived functor | `derivedGammaZSections`: right-derived actual supported sections, with proved left exactness and natural degree-zero comparison |
| I.2.1 / I.2.3 bis comparison, closed supports | `derivedGammaZSectionsIsoH_Z`: natural isomorphism from original right-derived supported sections to existing Ext-defined `H_Z` in every degree; generic derived-Hom/Ext comparison in `ExtRightDerived.lean` |
| I.2.2 degree-zero excision | `I_2_2_degree_zero`, `I_2_2_excision_degree_zero` |
| I.2.2, all degrees for closed supports | `supportedExcisionEquiv`: actual `H_Z` is unchanged by restricting to an open neighbourhood containing `Z`, naturally in coefficients; `closedSupportExcisionIso` compares the genuine support sheaves |
| I.2.1 / I.2.3 bis / I.2.12, chosen locally closed witnesses | `zZX_locallyClosed`, `derivedGammaLocallyClosedIsoExt`, `locallyClosedSupportExtEquiv`: genuine composite extension by zero represents the existing supported sections; its Ext computes their original derived functors and agrees with closed-support cohomology on the neighbourhood; flasque coefficients are acyclic |
| I.2.11 model for `ℋ_Z^n` | `sheafH_Z_n` defined by ker / coker / `rightDerived` |
| I.2.2, arbitrary locally closed witnesses | `locallyClosedSupportIsoOfSameSet`, `derivedGammaLocallyClosedIndependenceIso`, `locallyClosedCohomologyEquivOfSameSet`: the genuine support sheaf and all-degree cohomology are independent of the chosen witness, naturally in coefficients |
| I.2.4, closed support | `supportedCohomologySheafificationIso`: the original derived kernel-sheaf functor is naturally the sheafification of local supported cohomology; `supportedCohomologyPresheafSectionsEquiv` identifies its values with actual `H_Z` on each restricted open |
| I.2.4, locally closed support | `underlineGammaLocallyClosedFunctor`, `locallyClosedCohomologySheafificationIso`, `derivedUnderlineGammaLocallyClosedIndependenceIso`: actual ambient locally closed supported sheaves, their original derived functors, local-cohomology sheafification, and arbitrary witness independence in all degrees |
| I.2.5, open support | `derivedUnderlineGammaOfOpenIso`: original open-supported derived sheaves identify naturally with actual open restriction followed by higher direct image, with no assumed exactness of direct image |
| I.2.11, all degrees | `derivedUnderlineGammaZIsoModel`: the unchanged kernel/cokernel/derived-pushforward model is naturally the original derived kernel-sheaf functor; `sheafH_Z_nSheafificationIso` proves its sheafification interpretation |
| I.2.12, sheaf-valued closed support | `derivedUnderlineGammaZ_isZero_of_isFlasque`, `sheafH_Z_n_isZero_of_isFlasque`: original higher supported sheaves and the unchanged model vanish on flasque coefficients |
| I.2.12, sheaf-valued locally closed support | `derivedUnderlineGammaLocallyClosed_isZero_of_isFlasque`: all positive original ambient supported sheaves vanish on flasque coefficients |
| I.2.6 resolution inputs | `SupportedSheafInjective.lean`, `LocalToGlobalResolution.lean`: original supported sheaves preserve injectives and the supported resolution computes actual `H_Z` |
| I.2.6 closed-support spectral sequence construction | `supportedTruncationSpectralSequence`: canonical truncations and actual derived Hom give genuine pages, differentials, and next-page homology isomorphisms |
| I.2.6 E₂ identification | `supportedTruncationSpectralSequenceE2Equiv`: actual E₂ terms of that sequence are ordinary cohomology of original derived supported sheaves, including the E₂ universe comparison |
| I.2.6 first quadrant | `supportedLocalToGlobalAbelianSpectralObject_isFirstQuadrant`: the actual spectral object is first quadrant, and all pages Eᵣ, r ≥ 2, vanish outside it |
| I.2.6 total groups | `supportedSpectralObjectTotalEquivH_Z`: actual total-interval cohomology of the constructed spectral object identifies additively with original `H_Z`, using K-injectivity and the actual global-sections complex; finite convergence is proved separately below |
| I.2.6 convergence | `supportedCohomologyFiniteFiltration`, `supportedLocalToGlobalStablePageIsoGraded`: actual total cohomology, additively identified with original `H_Z`, has a finite image filtration from zero to the whole group; actual pages r ≥ n + 2 in total degree n are its associated-graded cokernels |
| I.2.6 spectral-object and total naturality | `supportedAbelianSpectralObjectMap`, `supportedSpectralObjectTotalEquivH_Z_naturality`: actual compatible resolution maps give spectral-object maps preserving every connecting map, and the existing total comparison intertwines these with `H_Z_map` |
| I.2.6, closed-support page morphisms | `supportedTruncationSpectralSequenceMap`, `_d`, `_next`: actual resolution maps induce actual spectral-sequence morphisms respecting all differentials and original next-page homology isomorphisms; `spectralSequence_hom_ext_firstPage` proves uniqueness from the first page |
| I.2.6, closed-support E₂ naturality | `supportedTruncationSpectralSequenceE2Equiv_naturality`: the original E₂ comparison intertwines actual coefficient maps, via naturality of the actual single-degree truncation and first-page comparisons |
| I.2.6, closed-support coefficient functor | `supportedTruncationSpectralSequenceFunctor`: actual coefficient maps are independent of compatible resolution lifts, satisfy identity and composition, and commute with canonical resolution-change isomorphisms satisfying the cocycle identity |
| I.2.6, closed-support filtered naturality | `supportedLocalToGlobalStablePageIsoGraded_coefficient_naturality`, `H_Z_map_mem_supportedCohomologyFiltration`, `supportedCohomologyFiltrationOnH_Z_independent`: original stable-page/graded-piece comparisons and the actual finite filtration are natural; total, filtration and graded maps are lift-independent, and the transported filtration on original `H_Z` is independent of the resolution |
| I.2.6, general locally closed support | `LocallyClosedLocalToGlobalResolution.lean`, `LocallyClosedLocalToGlobalSpectralSequence.lean`, `LocallyClosedLocalToGlobalConvergence.lean`: the original ambient support functor gives an actual spectral sequence with E₂ ordinary cohomology on `X` of the original derived locally closed sheaves, original `H_locallyClosed` abutment, first-quadrant vanishing, and actual finite convergence |
| I.2.6, locally closed functoriality | `LocallyClosedLocalToGlobalMaps.lean`, `LocallyClosedLocalToGlobalCoefficientFunctor.lean`, `LocallyClosedLocalToGlobalE2Naturality.lean`, `LocallyClosedLocalToGlobalTotalNaturality.lean`, `LocallyClosedLocalToGlobalConvergenceNaturality.lean`: coefficient functor, original E₂/total/stable-page/filtered naturality, lift independence, and resolution-independent filtration on original support Ext |
| I.2.7, locally closed boundary | `derivedUnderlineGammaLocallyClosed_stalkSupport_subset_closure`, `_subset_frontier`: original derived locally closed sheaves have actual stalk support inside the closure, and inside the boundary in positive degrees; the stronger open-restriction vanishing statements are also proved |
| I.2.7, locally closed cohomology | `derivedLocallyClosedSupportCohomologyEquiv`, `_naturality`: higher cohomology of the original derived supported sheaves is cohomology of their ordinary pullbacks to the actual closure; the comparison is natural in coefficients |
| I.2.7, closed support | `derivedSupportedSheafRestrictionIso`: original derived supported sheaves commute naturally with actual open restriction in every degree; `SupportedSheafBoundary.lean` proves vanishing off the support and positive-degree vanishing on its interior, including sheaf Ext and the unchanged model |
| I.2.7, literal stalk support | `derivedUnderlineGammaZ_stalkSupport_subset_frontier` and its model/sheaf-Ext analogues: positive original supported sheaves have actual stalk support in the boundary; all-degree support is contained in the closed set |
| I.2.7, closed-space cohomology | `closedPushforwardCohomologyEquiv`, `derivedSupportedSheafClosedCohomologyEquiv`: closed direct image preserves actual ordinary cohomology; cohomology of original derived supported sheaves is computed on the closed subspace using ordinary closed pullback, naturally in coefficients |
| Homological input for I.2.8 | `ext_contravariant_exact`, assuming a supplied short exact sequence |
| I.2.8 | `locallyClosedNestedCohomologySequence_exact`, `nestedClosedSubspaceCohomologySequence_exact`: the original ambient nested-support Ext sequence is exact in every degree, naturally in coefficients, with the extension class of the proved actual support-object sequence; open/closed degree-zero maps are actual section inclusion and restriction |
| I.2.10 | `locallyClosedNestedDerivedSheafSequence_exact`, `nestedClosedSubspaceDerivedSheafSequence_exact`: original ambient derived supported sheaves, their actual derived maps, and the genuine resolution connecting boundary form a natural long exact sequence in every degree; the initial map is monic and degree-zero maps recover the original supported-sheaf maps |
| I.2.9, closed/open relative sequence | `relativeCohomologySequence_exact`: actual `H_Z → H(X) → H(X\\Z) → H_Z[1]` is exact in all degrees, from the proved constant-support sequence and open Ext comparison; begins injectively in degree zero |
| I.2.9, section compatibility | `relativeRestriction_zero_sections`, `relativeSupportMap_zero_sections`: the degree-zero maps are actual restriction and inclusion of supported sections under the standard cohomology equivalences |
| Group-valued I.2.14 / III.3.1 input | `supported_vanishing_iff_relativeRestriction`: supported vanishing through degree `n` is equivalent to bijective relative restriction below `n` and injective restriction in degree `n`; `relativeBoundaryEquiv` identifies adjacent groups when ordinary cohomology vanishes |
| Inputs for I.2.12 | `isFlasque_of_injective`: every injective abelian sheaf is flasque; `H_pos_subsingleton_of_isFlasque`, `H_pos_restrict_subsingleton_of_isFlasque`: flasque sheaves have zero actual ordinary higher sheaf cohomology, also on every open subspace |
| Supported-section exactness | `gammaZSectionsFunctor_map_shortExact`: a short exact coefficient sequence with flasque kernel gives a short exact sequence of actual supported sections on every open |
| I.2.12 original supported acyclicity | `derivedGammaZSections_isZero_of_isFlasque`: actual right-derived supported sections vanish in positive degrees on flasque sheaves, proved using exactness of the supported-section resolution |
| I.2.12, closed supported acyclicity | `H_Z_pos_subsingleton_of_isFlasque`, `H_Z_pos_restrict_subsingleton_of_isFlasque`: the actual Ext-defined supported cohomology vanishes in positive degrees on flasque sheaves, also on every open subspace |
| I.2.12, converse | `isFlasque_iff_H_Z_one_subsingleton`, `isFlasque_iff_H_Z_pos_subsingleton`: flasqueness is exactly vanishing for all closed supports in degree one, equivalently every positive degree; the proof uses actual section restriction |
| I.2.13 degree 0 and 0–1 | kernel vanishing iff the unit is mono; kernel and cokernel vanishing iff it is an isomorphism |
| I.2.1 algebraic `H_J^i(M)` | `localCohomology` (`LocalCohomology.lean`) |
| III depth / Rees | `ModuleCat.exists_isRegular_tfae` |

### Remaining gaps in SGA 2 Exposé I

The modules compile without placeholders, but Exposé I remains partial.
The group-valued derived/Ext comparison and the sheafification comparison for
original derived supported sheaves are proved for closed supports; ambient
locally closed supported sheaves now have original derived functors,
sheafification, witness independence, and flasque acyclicity. In particular:

The internal-Hom/sheaf-Ext modules prove coefficient naturality in every
degree. They do not yet package first-variable bifunctoriality, connecting-map
compatibility, or compatibility of the local Ext evaluation equivalences with
the usual Ext restriction maps for nested opens. The underlying internal-Hom
presheaf and the closed-support sheaf comparison do have actual open-restriction
compatibility.

- I.1.1–I.1.7: the remaining internal Hom identities and the ringed-space versions.
  Genuine abelian internal Hom, its restriction-Hom comparison, and sheaf Ext
  as sheafification of local Ext are constructed. The closed-support internal-Hom
  identity and all-degree sheaf Ext comparison are also proved in the general
  locally closed setting, for the original ambient functors. Ringed-space
  analogues and the remaining internal-Hom identities remain.
  The general closed and locally closed `i_! ⊣ i^!` adjunctions and
  preservation of injectives by extraordinary inverse image are now proved,
  alongside exact open/closed extension and the closed Hom representation.
- I.2.6: a separate identification with a named general Leray construction
  and spectral-level change of locally closed witness remain.
  For closed supports, the actual sequence, E₂ identification and naturality, first-quadrant
  vanishing, total comparison to original `H_Z`, and finite convergence
  filtration are proved. Spectral-object coefficient maps preserve connecting
  maps, the total comparison is natural in compatible resolution maps, and
  actual spectral-sequence morphisms respect every differential and original
  next-page homology isomorphism. First-page equality determines morphisms.
  The actual coefficient functor is independent of compatible resolution lifts,
  with coherent natural resolution-change isomorphisms.
  The original stable-page/graded-piece comparison and actual convergence
  filtration are natural. Total, filtration and graded maps are lift-independent,
  and the filtration transported to original `H_Z` is resolution-independent.
  All these constructions now also exist for arbitrary locally closed supports,
  using the original ambient functor and cohomology on `X`, not merely
  replacing `X` by an open witness. The open-support case is included.
  I.2.7's locally closed boundary and closure bounds are now proved for literal
  stalks of the original derived locally closed sheaves. Their higher cohomology
  is naturally computed on the actual closure using ordinary closed pullback.
  Closed-support cohomology is also computed on the actual closed subspace, and the closed-support
  vanishing bounds apply to sheaf Ext and the unchanged kernel/cokernel model.

I.1.8–I.1.9's original group- and sheaf-valued nested sequences are proved in
general locally closed support, including flasque surjectivity. I.1.10's
integer-support short exact sequence is proved. I.2.8 and I.2.10's actual
nested group- and sheaf-valued long exact sequences are proved in all degrees,
with actual connecting maps and coefficient naturality. No support-object
short exact sequence or derived exactness is assumed. I.2.9's relative
sequence is also proved.
For every open/closed presentation, applying actual internal Hom to both
integer-support arrows recovers the actual original supported-sheaf arrows.
The arbitrary-coefficient extension sequence (17) is now proved using the
original open counit and closed unit, followed by exact locally closed
extension. Both endpoints are now actual single-witness extensions, with
literal subset equality, original arrow compatibility, and coefficient-map
naturality. Full arbitrary nested locally closed composition (13) is proved
for extension and extraordinary inverse image, with the actual support-space
homeomorphism and original unit/counit comparisons. No separate comparison of the group- and sheaf-sequence
connecting maps is claimed.

I.2.13's extra redundancy clause is proved for every `N > 0` by
`HigherRestrictionRedundancy.lean`, using actual complement-adapted injective
effacement and coefficient dimension shifting for arbitrary abelian sheaves.
The main higher-degree criterion is proved in Exposé III's
`derivedSupported_vanishes_iff_intersectionRestriction`; I.2.14's actual
group-valued criterion is `supported_vanishing_iff_ordinaryRestriction`.
Original closed and locally closed supported sheaves are proved acyclic on
flasque coefficients. The group-valued relative criterion and ordinary and
closed-supported flasque acyclicity are proved for both original right-derived
supported sections and the Ext-defined `H_Z`; the flasque converse is also proved.

## SGA 2, Exposé II — Algebraic and affine comparisons

Entry point: `lean/SGA/SGA2/ExposeII.lean`.
Source: `translation/SGA2/ExposeII/en-body.tex`.

| SGA 2 II | Proved content |
| --- | --- |
| (4.2), localization kernel | `localizationFamilyMap_ker`: ideal-power torsion is the kernel of the product of finitely many principal localization maps |
| II.4 affine input, noetherian rings | `affineTildeAb_H_pos_subsingleton`: actual ordinary higher sheaf cohomology of every associated module sheaf vanishes; no module finiteness assumption |
| II.(4.2)–(4.3), noetherian rings | `affineRelativeLowDegree_exact`, `affineSupportedCohomologyEquivOpen`: actual four-term low-degree cohomology sequence and higher supported/open-complement comparison, for arbitrary coefficient modules |
| Associated-sheaf exactness | `affineTildeAb_shortExact`, `affineTildeAb_globalSectionsEquiv`: the actual abelian associated-sheaf functor is exact and global sections recover the module, over arbitrary commutative rings |
| (4.2), actual affine supported sections | `powerTorsionEquivAffineSupportedSections`, `powerTorsionEquivGammaZ`: the kernel of actual associated-sheaf restriction outside `V(I)` agrees with torsion and exactly Exposé I's `gammaZ` |
| (5.1), degree zero | `stableKoszulCohomologyZeroIsoGammaZ`: stable Koszul degree zero agrees with the supported-section group |
| (4.2)/(5.1), principal degree-one calculation | `stableKoszulSingletonOneIsoRestrictionCokernel`: stable singleton Koszul H¹ is the cokernel of actual restriction from `Spec R` to `D(f)`; higher singleton cohomology vanishes |
| (7.3)–(7.4), reindexing | `generatorPowerIdeal_cofinal`, `generatorPowersLocalCohomologyIso`: finite generator powers and ordinary ideal powers give naturally isomorphic Ext colimits in each degree |
| (7.5), module algebra | `powerTorsion`, `quotientHomEquivTorsionBySet`: torsion is the union of annihilators, and evaluation at 1 identifies quotient Hom with annihilators |
| (7.5), categorical Hom colimits | `quotientHomColimitIso`, `generatorHomColimitIso`: both actual Hom systems have the torsion functor as colimit |
| (7.5), Koszul degree zero | `koszulHomologyZeroIsoQuotient`, `koszulCohomologyZeroIsoAnnihilator`, `stableKoszulCohomologyZeroIsoPowerTorsion`: the genuine finite Koszul complexes give the quotient, annihilator, and torsion comparisons |
| (7.3), affine degree zero | `localCohomologyZeroIsoAffineSupportedFunctor`, `localCohomologyZeroIsoGammaZ`: the Ext-colimit comparison reaches actual sheaf supported sections, naturally in coefficients at the module-valued level |
| (7.3), noetherian affine comparison, all degrees | `affineLocalCohomologyNatIso`, `affineLocalCohomologyAddEquiv`: actual algebraic local cohomology agrees with actual Ext-defined `H_Z` of the associated sheaf, naturally in every coefficient module; `affineLocalCohomologyNatIso_δ` proves compatibility with all coefficient boundaries |
| (7.6), canonical map | `koszulExtComparison`, `stableKoszulExtComparison`: lift the actual projective Koszul augmentation into a quotient resolution, dualize, and take cohomology and colimits; the maps are independent of the lift |
| Regular-sequence finite-stage comparison | `koszulProjectiveResolution`, `koszulExtComparisonIsoOfIsRegular`: the original augmentation is a quasi-isomorphism and the actual Koszul complex resolves the quotient for regular sequences over noetherian local rings; the original comparison is an isomorphism in all degrees, naturally in coefficients |
| (7.6), coefficient boundaries | `stableKoszulExtComparisonConnectingHom`: the constructed map commutes with actual connecting maps; finite and stable coefficient connecting maps and their exactness are proved |
| (7.3)–(7.6), cofinal boundaries | `localCohomologyIsoOfFinal_δ`, `localCohomologyToStableKoszul_δ`: cofinal reindexing and the canonical ordinary ideal-power Ext-to-Koszul comparison commute with coefficient boundaries, without a noetherian hypothesis |
| II.8 | `II_8`, `stableKoszulExtComparisonIso`: over a noetherian ring, the canonical generator-power Ext comparison is an isomorphism in every degree, naturally in coefficients |
| II.8, ordinary ideal powers | `localCohomologyIsoStableKoszul`: mathlib's algebraic local cohomology is naturally isomorphic to stable Koszul cohomology over a noetherian ring |
| II.9(b) ⇔ (c), each degree | `II_9_b_iff_c`: vanishing of actual stable Koszul cohomology on all injective coefficients detects essential vanishing of the corresponding Koszul homology system |
| II.9(a) ⇔ (b) ⇔ (c), all degrees | `II_9_a_iff_b`, `II_9_a_iff_c`: invertibility of the actual comparison in every degree is equivalent to positive-degree injective vanishing and essential vanishing of every positive homology system |
| II.10, noetherian-ring case | `affineTildeSheaf_isFlasque_of_injective`, `affineTildeAbSheaf_isFlasque_of_injective`: associated sheaves of injective modules are flasque; every section on any open extends globally |
| II.10, algebraic input | `powerTorsion_injective_of_injective`: supported torsion in an injective module is injective, using Artin–Rees and Baer's criterion |
| II.11 | `II_11`: for every finite list and noetherian coefficient module, every positive Koszul homology inverse system is essentially zero; the ring need not be noetherian |
| II.11, exact sequence | `scalarCofiberHomologyShortComplex_shortExact`: the genuine cofiber homology sits between the scalar cokernel and annihilator; its transition naturality supports induction on generators |

The Koszul complexes in `KoszulComplex.lean` are recursively defined homotopy
cofibers, with explicit chain maps for powers of the generators. Their terms
are noetherian for noetherian coefficients and projective for projective
coefficients. `KoszulCofiber.lean` proves the exact sequence from cycles and
boundaries. `KoszulProZero.lean` completes the induction in II.11 using the
varying-coefficient annihilator argument. `PrincipalKoszul.lean` also provides
explicit two-term calculations.

`InjectiveHomology.lean` proves the natural Hom–homology comparison for
injective coefficients. `InjectiveDetection.lean` proves the converse
vanishing criterion by embedding a term in an injective module and detecting
eventual equality in filtered colimits. `KoszulCoefficientSequence.lean`,
`ExtCoefficientSequence.lean`, and `ExtColimitSequence.lean` construct the
coefficient boundaries and prove exactness. `CohomologicalComparison.lean`
proves the general dimension-shifting isomorphism criterion; its hypotheses
are discharged for the actual map in `KoszulComparisonIsomorphism.lean`.

The formal II.9(a) equivalences quantify **all degrees simultaneously**.
The comparison argument uses vanishing in every positive degree; it does not
claim that vanishing in one isolated degree alone makes the full comparison
invertible. The equivalence II.9(b) ⇔ (c) is also proved degree by degree.

`AffineSupport.lean` uses mathlib's actual associated sheaf and its
restriction maps. Its degree-zero results require only a finitely generated
support ideal. `LocalizationCokernelColimit.lean` and
`PrincipalCechComparison.lean` identify principal degree-one stable Koszul
cohomology with the actual restriction cokernel over any commutative ring.
Over noetherian rings, `AffineCohomologyComparison.lean` now compares actual
algebraic local cohomology with the independently defined supported sheaf
cohomology of Exposé I in every degree.

Here `localCohomology` means mathlib's **algebraic Ext-colimit definition**.
Its comparisons with stable Koszul cohomology and actual group-valued
supported sheaf cohomology are proved over noetherian rings. The latter
comparison is a natural isomorphism respecting every coefficient boundary.
General-scheme and sheaf-valued comparisons remain open.

`Examples.lean` checks a nonzero principal homology module in an essentially
zero system, an explicit zero transition, and empty generating families.
Radical invariance of torsion is proved for finitely generated ideals.

### Remaining gaps in SGA 2 Exposé II

- II.1–II.4: quasi-coherence of higher supported cohomology sheaves, affine
  sheaf-cohomology vanishing over arbitrary rings, and the spectral-sequence
  comparison. Ordinary affine vanishing, the actual low-degree relative
  sequence and higher open-complement formulas are proved over noetherian rings;
  the actual degree-zero restriction-kernel comparison with torsion is also proved.
- II.5: compare stable Koszul cohomology with the independently defined
  higher topological supported cohomology for arbitrary finite families.
  Degree-zero supported sections and the principal restriction-cokernel
  calculation are proved.
- II.6–II.7: construct the global and sheaf Ext comparisons, their spectral
  sequences and compatibility, and the local-to-global argument. II.8's
  algebraic comparison and the actual noetherian affine group-valued comparison
  are proved, but do not supply these general-scheme geometric steps.
- II.10: prove the equivalence between Koszul vanishing and injective
  associated-sheaf flasqueness assuming only a topologically noetherian
  spectrum. Flasqueness over a noetherian ring is proved, with actual global
  extension from every open, in `InjectiveFlasque.lean`.

Exposé II remains partial.

## SGA 2, Exposé III — Cohomological invariants and depth

Entry point: `lean/SGA/SGA2/ExposeIII.lean`.

| SGA 2 III | Proved content |
| --- | --- |
| III.1 definitions | `sgaAssociatedPrimeSpectrum`: exact nonzero-element annihilators over arbitrary rings, with a proved noetherian comparison to mathlib's radical-annihilator convention |
| III.1.1 | Finiteness of associated primes, their union as the zero divisors, and the radical annihilator as the intersection of minimal associated primes |
| III.1.2 | Support membership is equivalent to containing an associated prime, the annihilator, or its radical |
| III.1.3 | `associatedPrimeSpectrum_linearMap`: `Ass Hom(N,M) = Supp N ∩ Ass M` |
| III.2.1 | `lemma_2_1`: all five conditions, including the localization criterion |
| III.2.2 | `III_2_2_a`, `III_2_2_b`: regular sequences and Ext vanishing with the hypotheses in the source |
| III.2.3–III.2.4 | `depth`, `le_depth_iff`, `le_depth_iff_exists_regular`, `le_depth_iff_exists_test_module`: the actual Ext-based definition and depth criteria |
| III.2.5 | `III_2_5`: `depth_I M = depth_I(M/fM) + 1` for a regular `f ∈ I`, including infinite depth |
| III.2.6, finite depth | `III_2_6`: any regular sequence extends to a maximal one of length equal to depth; `exists_regular_extension` also permits any intermediate finite length |
| III.2.6, infinite depth | `exists_infinite_regular_extension`: any finite regular prefix extends to one infinite sequence whose every finite prefix is regular |
| III.2.7 | `III_2_7`: depth is finite exactly when the support of the module meets `V(I)` |
| III.2.8 | `depth_eq_extDepth`: depth is the first nonzero Ext degree for any finite test module with the prescribed support; includes the residue-module case |
| III.2.9–III.2.10 | `III_2_9`, `III_2_10`: infimum of local depths over `V(I)`, and over maximal ideals for a semilocal ring |
| III.2.11 | `III_2_11_flat`, `III_2_11_faithfullyFlat`: flat base change cannot decrease depth, and faithful flatness gives equality |
| Algebraic input to III.§3 | `le_depth_iff_localCohomology_vanishes`, `depth_eq_iInf_localCohomology`: depth is detected by actual algebraic local cohomology, including infinite depth; the two Ext conventions are linked by a proved vanishing equivalence |
| Affine group-valued bridge for III.§3 | `le_depth_iff_affine_H_Z_vanishes`, `depth_eq_iInf_affine_H_Z`: depth is the first nonzero actual supported sheaf-cohomology degree; `affine_H_Z_vanishes_iff_localDepth` and the test-module/quotient criteria connect it to localized depths and genuine Ext |
| Literal affine stalk depth | `affineStalkRingEquiv`, `affineModuleStalkSemilinearEquiv`, `localDepth_eq_actual_stalk_depth`: the genuine structure and associated-module stalks identify with localizations compatibly with scalars, so original local depth is actual stalk depth |
| III.3.1(i) iff (iii) | `derivedSupported_vanishes_iff_local_H_Z`: for arbitrary actual abelian sheaves, lower vanishing of original derived supported sheaves is equivalent to lower vanishing of actual supported cohomology on every open; the proof uses actual spectral convergence and sheafification |
| III.3.3(i)/(iii)/(iv), all nonnegative thresholds | `coherent_depth_iff_derivedSupported_vanishes`, `coherent_depth_iff_local_H_Z_vanishes`: literal actual module-stalk depth along the support is equivalent to original derived supported-sheaf vanishing and local supported-cohomology vanishing, for coherent modules on arbitrary locally noetherian schemes; actual affine-chart cohomology transport and all finiteness conditions are proved |
| III.3.1(ii) / III.3.3(ii), all positive thresholds | `derivedSupported_vanishes_iff_intersectionRestriction`, `coherent_depth_iff_intersectionRestriction`: actual ordinary cohomology restriction from `V` to `V ∩ (X ∖ Z)` is bijective below the last degree and injective in the last degree; `relativeRestriction_eq_ordinary` proves the all-degree map comparison, and the actual nested-open/intersection sheaf and cohomology transport are proved |
| III.3.2, threshold two / I.2.13, `N = 1` | `derivedSupported_vanishes_two_iff_intersectionRestriction_zero`, `intersectionRestriction_one_injective_of_zero_bijective`: for arbitrary abelian sheaves, all-open actual degree-zero restriction bijectivity suffices; original supported sheaves vanish in degrees zero and one, and the discarded degree-one injectivity follows |
| III.3.2, every threshold at least two / I.2.13, every `N > 0` | `derivedSupported_vanishes_iff_intersectionRestriction_bijective`, `intersectionRestriction_highest_injective_of_lower_bijective`: lower actual ordinary restriction bijectivity on every open suffices; highest-degree injectivity follows, without assuming a separate local-effacement comparison |
| III.3.2–III.3.3, coherent form | `coherent_depth_iff_intersectionRestriction_bijective`: literal coherent module-stalk depth at least `n + 2` along the support iff actual ordinary restriction is bijective in degrees below `n + 1` on every open |
| III.3.4, positive thresholds | `example_3_4`: local depth, actual supported cohomology, relative restriction, and residue-field Ext criteria |
| III.3.5, affine Hartogs | `two_le_depth_iff_affineRestriction_bijective`, `affineRestriction_bijective_of_localDepth`: actual associated-sheaf section restriction is bijective at depth at least two, and injective at depth at least one |
| III.3.5, general locally noetherian schemes, structure sheaf | `structureStalkDepth_two_le_iff_restriction_bijective`, `structureGlobalHartogsRingEquiv`: literal local structure-ring depth at least two along the closed support is equivalent to bijective actual restriction on every open, via proved affine-open compatibility and sheaf gluing |
| III.3.5, coherent coefficients | `coherent_hartogs_iff`, `coherentHartogsEquiv`: for actual `M : X.Modules` with mathlib's local `M.IsFinitePresentation`, literal module-stalk depth at least two along the closed support is equivalent to actual bijective restriction on every open; finite affine coefficient charts, actual stalk modules, and semilinear restriction/stalk depth comparisons are proved |
| III.3.6, affine connectedness equivalence | `affine_connected_iff_of_localDepth`: removing the depth-two closed support preserves connectedness; proved using actual structure-sheaf restriction and clopen characteristic sections, with no assumed idempotent/section comparison |
| III.3.6, affine connected components | `affineConnectedComponents_bijective_of_localDepth`: the actual inclusion-induced map on connected components is bijective; `affineConnectedComponentsEquiv` has this map as its forward function |
| III.3.6, general locally noetherian schemes | `schemeConnectedComponents_bijective_of_stalkDepth`, `schemeConnectedComponentsEquiv`: actual complement inclusion induces a bijection on connected components under literal structure-stalk depth at least two; proved using genuine global-idempotent/clopen correspondence, with no global quasi-compactness hypothesis |

The source's regularity convention only requires injectivity of each
successive scalar multiplication. This is mathlib's `IsWeaklyRegular`.
It permits a zero final quotient. Consequently III.2.2 does not add the
condition `IM ≠ M` used in mathlib's existing Rees theorem. Part (a) also
does not add noetherian or finite-module hypotheses.

There is a necessary qualification to the unqualified wording of III.2.6:
finite maximal sequences exist at **finite depth**. At infinite depth,
`exists_regular_extension_of_depth_top` proves that every finite regular
sequence can be extended; `exists_infinite_regular_extension` constructs
one compatible infinite extension. The unit ideal provides a concrete example:
its depth is infinite and arbitrarily long lists of `1` are regular in
SGA's convention. `Examples.lean` also proves depth zero at the zero ideal
on a nonzero finite module, and depth one for `ℤ` along `(2)`. The English
translation has not been silently altered.

Remaining gaps in III.3.1–III.3.13 include the module-valued internal
sheaf Ext criteria (v)/(vi) and further connectedness results. The all-degree
coherent depth criterion now uses original supported sheaves on general locally
noetherian schemes, with literal actual module-stalk depth. The affine
group-valued depth/supported-cohomology bridge, actual Hartogs restriction, and
full affine connected-components bijection are proved. Literal affine stalk
compatibility, structure-sheaf Hartogs, and the full III.3.6 connected-components
bijection on every locally noetherian scheme are also proved. The full III.3.5
Hartogs equivalence now covers actual coherent module sheaves. Mathlib has no
named `IsCoherent` class here: the theorem uses its local finite-presentation
condition, which is the coherent condition on a locally noetherian scheme.
Higher-threshold redundancy is proved using the actual embedding into the
direct image of an injective on the complement, followed by coefficient
dimension shifting. It does not require a separate sheafification comparison
for positive ordinary cohomology; that comparison itself is not claimed here.
Sections 1–2 are
covered with the explicit finite-depth qualification for maximal finite
sequences in III.2.6.

## SGA 2 IV — Dualizing modules and functors

English: `translation/SGA2/ExposeIV/`. Lean: `lean/SGA/SGA2/ExposeIV/`.
This exposé is partial and imported by the root library.

| Source | Formalized result |
| --- | --- |
| IV.1 opening | `additiveFunctorModule`, `additiveFunctorModuleLift`: the original additive functor induces the scalar action through scalar endomorphisms; all its maps are linear for that action, and forgetting recovers the original functor |
| IV.1.1 | `additiveFiniteModuleEvaluation_isIso_iff`, `additiveFiniteModuleRepresentationIso`: the actual canonical evaluation map is an isomorphism precisely when the original abelian-group-valued additive contravariant functor is left exact; no pre-existing scalar action or representing module is assumed |
| IV.1 categorical equivalence | `finiteModuleFunctorEquivalence`: arbitrary modules are equivalent to additive left-exact contravariant functors on finite modules; the forward functor is actual restricted Hom, with full faithfulness proved by evaluation at the ring |
| IV.1.2 | `additiveModuleEvaluation_isIso_iff_preorderLimits`, `additiveModule_representable_iff_preorderLimits`: the original additive functor on all modules is canonically represented by its actual `T(R)` iff it preserves arbitrary preorder-indexed projective limits, without filteredness; actual finite-submodule colimits and the precise preorder-to-all-limits bridge are proved |
| IV.1.3 foundations | `SupportedFGModuleCat`, `supportedQuotientStage`, `supportedQuotientStage_covers`, `supportedFunctorDiagram`: the actual support-defined finite module category is abelian, genuine quotient-ring restriction gives fully faithful exact stages covering all objects, and `T(R/Jⁿ)` has its canonical linear quotient-induced transitions and proved annihilator bounds; transitions are injective for left-exact `T` |
| IV.1.3 representation | `additiveSupportedFunctorEvaluation_isIso_iff`, `additiveSupportedFunctorRepresentationIso`: the original canonical evaluation into the actual colimit of `T(R/Jⁿ)` is an isomorphism iff `T` is left exact; all scalar, transition, choice-independence, naturality and finite-source factorization steps are proved |
| IV.1.3 categorical equivalence | `supportedModuleFunctorEquivalence`: actual restricted Hom gives an equivalence of arbitrary modules supported in `V(J)` with additive left-exact functors on finite supported modules; full faithfulness is proved via actual finite cyclic submodules, and essential surjectivity uses the original colimit |
| IV.1.4 Hom detection input | `subsingleton_linearMap_iff_of_support_eq_zeroLocus`: a finite full-support test module detects zero arbitrary supported targets, without requiring the target to be finite; actual represented-functor vanishing detection is also proved |
| IV.1.4 | `supportedDeltaFunctor_vanishing_tfae`: all three lower-vanishing conditions for arbitrary integer-indexed bounded-below exact delta functors; `IntegerCohomologicalSequence` records actual natural connecting maps and all exactness pieces, and the needed left exactness is derived from preceding-degree vanishing |
| IV.2.1 | `finiteSupportedHomExact_iff_injective`: for an actual ideal-power-torsion module, exactness of contravariant Hom on finite supported modules is equivalent to categorical injectivity; the proof reduces to Baer using Artin–Rees |
| IV.2.1 support formulation | `powerTorsion_eq_top_iff_support_subset_zeroLocus`, `finiteSupportedHomExact_iff_injective_of_support`: actual support in `V(J)` agrees with elementwise ideal-power torsion, without assuming the module finite, giving the original support-hypothesis Hom criterion |
| IV.2.1 original functor | `supportedFunctorExact_iff_injective_colimit`, `supportedFunctor_preservesHomology_iff_injective_colimit`: for the original additive left-exact `T`, preservation of all genuine short exact sequences is equivalent to injectivity of its actual colimit in the category of all modules |
| IV.2.2 | Ideal-power torsion in an injective module is injective, reusing the proved Exposé II theorem |
| IV.3.1, Hom-duality implication | `moduleBidualEvaluation_isIso_of_artinian_support`, `moduleHomDual_finite_of_artinian_support`, `moduleHomDual_length_of_artinian_support`: arbitrary injective `H` with residue-field Hom tests gives original canonical Hom biduality, finite Hom values, and length preservation on every finite supported module; the actual finite-length property follows from noetherian `R` and Artinian `R/J`, not from an extra hypothesis |
| IV.3.1, original functor | `supportedFunctor_duality_tfae`: all four conditions for the original additive abelian-group-valued `T`, with left exactness and finite values inside condition (i), actual canonical `M → T(T(M))`, actual residue values, actual injective representations, and length preservation |
| IV.3.1, canonical comparisons | `supportedFunctorBidualEvaluationNatTrans`, `supportedFunctorValueIsoOfRepresentation`: actual twice-iterated functor evaluation is natural; any original abelian-group-valued representation automatically respects the canonical scalar actions |
| IV.3.2 | `supportedFunctor_exact_and_length_iff_length`, `supportedFunctor_duality_iff_length`: under IV §3's standing left-exactness hypothesis, length preservation alone implies exactness and canonical duality; finite values are derived |
| IV.4.3 | `finite_local_coinduction_supported_duality`: original `Hom_A(B,I)` with its actual `B`-action preserves all three supported-dualizing conditions; genuine Hom adjunction and canonical bidual-evaluation comparison are proved, with no extra local-homomorphism hypothesis |
| IV.4.4, proper quotients | `quotientCoinductionAnnihilatorIso`, `quotientAnnihilator_supported_duality`: evaluation at one identifies the actual coinduced module with the ideal annihilator equipped with the standard quotient action, and transfers supported duality |
| IV.4.2, existence | `nonlocalDualizingFunctor`, `nonlocalDualizingEvaluationIso`, `nonlocalDualizingAntiEquivalence`: actual exact linear Hom duality on the entire finite-length category, constructed using the injective envelope of the sum of all residue fields; actual maximal-ideal annihilators have length one |
| IV.4.2, local comparison | `localFiniteLengthEquivalence`: identity-on-modules equivalence with the original finite closed-point-supported category and literal compatibility with original Hom maps |
| IV.4.2, local Artinianness | `allResidueFieldEnvelope_locallyArtinian`: the actual nonlocal coefficient is locally Artinian, proved using associated primes under essential embeddings |
| IV.4.2, cofinite index | `quotient_annihilator_isFiniteLength`, `cofiniteRingQuotientDiagram`: actual annihilator quotients of finite-length modules have finite length; cofinite ideals form a reverse-inclusion filtered category with original quotient maps, over any commutative ring |
| IV.4.2, uniqueness foundation | `locallyArtinianRestrictedHomFullyFaithful`, `locallyArtinianIsoOfFiniteLengthHom`: actual Hom on finite-length tests is fully faithful on locally Artinian modules over a noetherian ring, recovering specified natural transformations and isomorphisms |
| IV.4.2, original nonlocal representation | `additiveCofiniteFunctorEvaluation_isIso_iff`, `additiveCofiniteFunctorRepresentationIso`: canonical evaluation into the actual cofinite-ideal colimit is invertible exactly for additive left-exact functors on the whole finite-length category; all original actions, point maps, quotient transitions, and stage comparisons are proved, over any commutative ring |
| IV.4.2, nonlocal Hom equivalence | `locallyArtinianFiniteLengthFunctorEquivalence`: original Hom identifies locally Artinian modules over a noetherian ring with additive left-exact finite-length functors; the constructed original colimit supplies essential surjectivity |
| IV.4.2, nonlocal injectivity | `finiteLengthHomExact_iff_injective`, `cofiniteFunctorExact_iff_injective_colimit`: original finite-length Hom exactness detects injectivity of arbitrary locally Artinian coefficients; exactness of any original additive left-exact functor is equivalent to injectivity of its actual colimit, via proved cofinite Artin–Rees/Baer reduction |
| IV.4.2, arbitrary original dualizing functor | `nonlocalInvolutiveRepresentationIso`, `nonlocalInvolutiveCoefficient_injective`, `nonlocalInvolutiveAnnihilator_length`: a linear finite-length functor with a natural involution has its original cofinite-colimit representation, locally Artinian injective coefficient, and actual maximal-ideal annihilators isomorphic to their residue fields; no residue tests or length preservation are assumed |
| IV.5.1, actual bidual completion | `finiteBidualCompletionIso`, `finiteBidualCompletionIso_evaluation`: double Hom of an arbitrary finite module is its actual adic completion, and original evaluation becomes the original completion map |
| IV.5.1, dual completeness | `homDualCompletionIso_hom`, `SupportedDualizingModule.supported_dual_isAdicComplete`, `matlisHomToComplete`: original Hom from locally Artinian finite-socle modules lands in the literal complete category with finite-length power quotients |
| IV.5.1, complete-base formulation | `matlisCompleteAntiEquivalence`, `matlisCompleteCategoryAntiEquivalence`: actual linear Hom functors in both directions, with canonical natural evaluations, give inverse equivalences over a complete noetherian local base |
| IV.5.1, `CA` completion transport | `matlisArtinianCompletionEquivalence`, `completionSocleRestrictionEquiv`: actual tensor/restriction identify finite-socle locally Artinian categories, with original maps, without assuming completed-ring noetherianity |
| Noetherian completion / IV.5.1 | `adicCompletion_isNoetherianRing`, `matlisCompletedRingAntiEquivalence`: actual adic completions of noetherian rings are noetherian for arbitrary ideals; actual `CA(R)` is opposite-equivalent to finite modules over the completion via original scalar change and completed-ring Hom |
| IV.5.1, original Hom comparison | `matlisCompletedRingHomIso`: the equivalence's actual forward functor, followed by restriction, is naturally original-ring Hom, with explicit tensor-unit formula, inverse actual tensor extension, and coefficient naturality |
| IV.5.1, full general-base proposition | `matlisAntiEquivalence`: literal `CA(R)ᵒᵖ ≌ DA(R)`, with forward exactly original-ring Hom and inverse actual completed-ring Hom through the original completion/restriction comparisons; no completeness assumption on `R` |
| IV.5.1, transport clause | `matlisCompleteCompletionEquivalence`, `matlisDualityForwardCompletionIso`, `matlisDualityInverseCompletionIso`: actual module completion and restriction identify `DA`, and both Hom transport squares commute naturally in the original categories |
| IV.5.1, finite-length intersection | `matlisFiniteLengthIntersectionEquivalence`, `finiteLength_matlisHomToComplete`: finite modules intersect `CA` exactly in the original finite-length category; actual Hom restrictions and canonical evaluations agree with finite-length duality |
| IV.5.1, finiteness and cogeneration | `finite_of_isHausdorff_of_finite_reduction`, `SupportedDualizingModule.moduleBidualEvaluation_isIso_of_dual`: topological Nakayama and original all-module Hom cogeneration are proved; actual finite socle has finite-length power annihilators |
| IV.5.1, full Artinian characterization | `matlisArtinianModuleProperty_iff_isArtinian`: the literal locally-Artinian finite-socle category consists exactly of all Artinian modules over every noetherian local base; original Hom orthogonals embed the submodule lattice into the dual's opposite lattice, and completion preserves the whole supported submodule lattice |
| Essential-extension socles | `EssentialIn.localSocle_le`, `EssentialModuleMap.localSocleMap_surjective`, `EssentialModuleMap.localSocle_finite`: every essential submodule contains the actual socle; the unchanged embedding induces a bijection on socles and preserves finite socle, including for the constructed injective envelopes |
| IV.5.3–5.4, regular-local foundations | `regularLocal_isDomain`, `regularLocal_exists_regular_parameters`: genuine regular local rings are domains and have regular systems of parameters of their actual Krull dimension; every minimal generating list is regular |
| IV.5.3–5.4, off-degree vanishing | `regularLocal_residueField_projectiveDimension`, `regularLocal_moduleExt_ring_isZero_of_finiteLength`: residue projective dimension equals Krull dimension, finite-length projective dimension is bounded by it, and original module-valued Ext into the ring vanishes in every other degree |
| IV.5.3, depth and arbitrary lower vanishing | `regularLocal_depth_eq`, `regularLocal_ext_ring_subsingleton_of_maximalIdeal_pow_annihilator`: literal depth equals Krull dimension, and lower Ext vanishes for arbitrary modules killed by a maximal-ideal power, in both Ext models |
| Finite-module projective-dimension bound | `finite_hasProjectiveDimensionLE_of_residueField`, `regularLocal_finite_hasProjectiveDimensionLE`: support-dimension induction removes actual closed-point torsion and quotients by an actual regular element; a residue-field bound extends to every finite module over a noetherian local ring |
| Baer and higher cyclic Ext tests | `injective_of_cyclic_ext_one`, `hasInjectiveDimensionLE_of_cyclic_ext`, `hasProjectiveDimensionLE_of_cyclic_bound`: actual cyclic Ext tests and genuine injective dimension shifting control arbitrary modules, without noetherianity in the cyclic-to-arbitrary step |
| IV.5.3, full global-dimension bound | `moduleGlobalDimension_eq_residueField`, `regularLocal_moduleGlobalDimension_eq`, `regularLocal_ext_subsingleton_of_gt`, `regularLocal_moduleExt_isZero_of_gt`: global projective dimension equals the residue-field dimension over every noetherian local ring (including infinite dimension), hence equals Krull dimension over a regular local ring; upper Ext vanishing has both arguments arbitrary |
| Ext comparison naturality | `moduleExtLinearIsoAbelianExt_naturality_first`, `moduleExtLinearIsoAbelianExt_naturality_coefficient`: the unchanged canonical linear comparison respects original maps in both variables in every degree, over any commutative ring |
| IV.5.4, exactness and actual representation | `regularLocalTopExtFunctor_exact`, `regularLocalTopExtRepresentationIso`, `regularLocalTopExtModule_injective`: the genuine derived-category top Ext functor is exact and canonically represented by its actual injective quotient-Ext colimit; no top residue value is assumed |
| IV.5.3, top residue value | `koszulTopCohomologyIsoQuotient`, `regularLocal_topResidueModuleExtIso`: actual top Hom–Koszul cohomology is the coefficient quotient, and original module-valued `Extⁿ_R(k,R)` is the actual residue module; `moduleExtAddEquivAbelianExt` also compares the two genuine Ext models as additive groups |
| IV.5.4, original functor duality | `moduleExtLinearIsoAbelianExt`, `regularLocalTopExtFunctor_duality`, `regularLocalTopExtModule_dualizing`: the genuine linear Ext comparison proves residue tests for the original canonical scalar action; top Ext and its actual representing quotient-Ext colimit are dualizing |
| IV.5.4, local cohomology identification | `regularLocalTopExtModuleIsoLocalCohomology`, `regularLocal_localCohomology_dualizing`, `regularLocalTopExtLocalCohomologyRepresentationIso`: genuine first-variable Ext naturality compares the original quotient diagrams and colimits, including stage maps; actual top local cohomology is supported dualizing and represents original top Ext |
| IV.5.4, geometric footnote | `regularLocalTopExtModuleIsoSupportedCohomology`: the actual representing module's underlying additive group is original affine supported-sheaf cohomology; no separately defined geometric scalar action is compared |
| IV.5.5, initial existence assertion | `regularLocal_localCohomology_nonempty_iso_macaulay`: the actual local cohomology and Macaulay modules are noncanonically isomorphic; explicit residue-pairing and parameter-independence clauses remain open |
| IV.5.5, power transitions | `koszulTopCohomologyRing_transition_add_apply`, `koszulTopCohomologyRing_transition_monomial`: the original top Koszul cohomology diagram becomes the stated product-multiplication transition on actual power-ideal quotients; monomial classes have all exponents shifted by the same amount, with no monomial-basis assertion |
| IV.5.5, explicit quotient colimit | `koszulTopQuotientDiagram`, `koszulTopQuotientColimitIsoLocalCohomology`: direct product-multiplication maps on the actual power-ideal quotients form a diagram whose colimit is original local cohomology in top Koszul degree over a noetherian ring, with original stage-map compatibility; arbitrary lists and coefficients are allowed |
| IV.5.2, continuous dual | `continuous_linearForm_adic_iff`, `macaulayModuleIsoContinuousDual`: continuity to the discrete coefficient field is exactly vanishing on an ideal power; original quotient-dual colimit is canonically the continuous dual of the original adic ring, without completeness |
| IV.5.5, actual power-series basis | `powerSeriesPowerQuotientBasis_apply_prod`, `powerSeriesPowerQuotient_finrank`: actual coordinate-power quotients have their bounded-monomial basis and dimension `r^d`, including zero-variable and zero-power cases |
| IV.5.5, finite-stage residue | `powerSeriesPowerQuotientResidue_mul_complement`, `powerSeriesPowerQuotientResidueEquiv`: actual product-residue pairing on positive coordinate-power quotients is perfect; complementary monomials recover every coefficient |
| IV.5.5, explicit power-series comparison | `powerSeriesLocalCohomologyIsoMacaulay`, `powerSeriesLocalCohomologyIsoContinuousDual_stage_apply`: original product transitions preserve the residue functionals; the actual quotient colimit gives an explicit ring-linear local-cohomology/Macaulay isomorphism, with literal product-coefficient formula at every original stage |
| IV.5.5, glued residue form | `powerSeriesLocalCohomologyResidue_basis`, `powerSeriesLocalCohomologyResidue_nondegenerate`, `powerSeriesTopLocalCohomology_supportedDualizing`: the original local-cohomology residue form is coefficient-field linear, has the stated monomial formula and nondegenerate product pairing, and its coefficient is supported dualizing; no Cohen presentation or completed differential module is assumed to have been constructed |
| V.1, literal Hom-complex signs | `sourceHomδ_v`, `sourceHomδ_comp`, `sourceHomComplexIso`, `sourceHomSign_smul_comp`: the original displayed differential is square-zero; actual Leibniz, cocycle/coboundary and homotopy formulas are proved. The explicit chain isomorphism multiplies degree `n` by `(-1)^(n(n+1)/2)`, with composition correction `(-1)^(ij)` |
| V.1.3, actual double-resolution comparison | `homComplexPrecomp_quasiIso`, `sourceInjectiveHomAugmentation_f`, `sourceInjectiveHomologyExtAddEquiv`: precomposition preserves cohomology into K-injective targets; the sign-normalized augmentation from the actual source Hom complex of two specified injective resolutions is a quasi-isomorphism, and its actual homology map computes Ext |
| V.1, original cohomology composition | `homClassComp_mk`, `homClassComp_assoc`, `homologyComp`: original graded composition gives a biadditive cohomology pairing with its actual representative formula and associativity, not just a separately transported operation |
| V.1, original source quotient and pairing | `sourceHomLeftHomologyData`, `sourceHomologyComp_mk`, `sourceHomologyAddEquiv_comp`: the source's actual kernel and quotient use unscaled cocycles and classes; their original composition acquires exactly `(-1)^(ij)` under the explicit normalization |
| V.1, Hom-complex/Yoneda product comparison | `injectiveHomologyExtAddEquiv_comp`, `sourceInjectiveHomologyExtAddEquiv_comp`: the previously specified double-resolution Ext equivalences carry the actual standard product to Yoneda composition and the literal source product to the precisely signed Yoneda composition; the proof retains the original augmentations |
| V.1, actual connecting cocycle | `connectingConeCocycle_postcomp`, `homCocycle_connecting_eq_derived`, `sourceHomCocycle_connecting_eq_derived`: original lift-and-differentiate is the derived connecting morphism through an actual mapping-cone cocycle; the literal source convention has its precise target-degree sign |
| V.1, projective-resolution Ext boundary | `projectiveExtCocycle_comp_extClass`, `projectiveExtMk_comp_extClass`, `exists_projectiveExtBoundaryFormula`: Yoneda composition with the actual extension class equals `(-1)^(n+1)` times the unchanged unsigned lift-and-differentiate representative; actual lifts and factorizations exist for every Ext class, and the original boundary is proved to be a cocycle |
| V.1, original coefficient boundaries in all degrees | `moduleCohomologyMk_δ`, `moduleExtLinearEquivAbelianExt_isoExt_inv_mk`, `moduleExtYonedaCovariantBoundary_eq_signed_extCoefficientδ`: original module-cohomology representatives map to their unchanged `extMk` classes, including degree zero through the existing Ext-to-Hom isomorphism; the actual Yoneda coefficient boundary is `(-1)^(n+1)` times the independently constructed Hom boundary |
| V.1, original local-cohomology boundary comparison | `extColimitYonedaBoundary_eq_signed_extColimitδ`, `localCohomologyYonedaBoundary_eq_signed_localCohomologyδ`: the same signed equality holds for the existing maps on the unchanged Ext diagrams, filtered colimits, and ideal-power local-cohomology objects in every degree |
| V.1, actual contravariant Hom exactness and naturality | `homComplexContravariantSequence_shortExact`, `sourceHomContravariantSequence_shortExact`, `homComplexContravariant_exact₁`–`exact₃`, `sourceHomContravariant_exact₁`–`exact₃`, `sourceHomContravariantδ_naturality`: the original reversed Hom sequences into any degreewise-injective complex give natural long exact sequences in every integer degree, for both differentials |
| V.1, actual contravariant derived-boundary comparison | `homComplexContravariantδ_mk`, `homComplexContravariantδ_compare`, `sourceHomContravariantδ_compare`: original lift-and-differentiate representatives identify the actual boundary with precomposition by the original derived connecting arrow into a degreewise-injective K-injective target; the standard convention contributes exactly `(-1)^(n+1)`, and the literal source differential has no extra sign under its fixed unscaled, precomposition-natural quotient equivalence |
| V.1, actual pairing and boundaries | `extPairing_sequence_connecting`, `moduleExtPairing_naturality_middle`: actual derived Yoneda composition agrees with both original Ext connecting maps; canonical transport to original module-valued Ext is natural in all three variables |
| V.1, covariant Hom exactness and naturality | `homComplexCovariantSequence_shortExact`, `sourceHomCovariantSequence_shortExact`, `homComplexCovariant_exact₁`–`exact₃`, `sourceHomCovariantδ_naturality`: for arbitrary source complex, a coefficient short exact sequence with degreewise-injective first term induces actual natural long exact Hom sequences, for both differentials and all integer degrees; injectivity supplies the degreewise splittings |
| V.1, actual covariant derived-boundary comparison | `homComplexCovariantδ_compare`, `sourceHomCovariantδ_compare`: with K-injective endpoint coefficients, the original standard boundary is postcomposition with the original derived connecting arrow; the literal-source boundary contributes exactly `(-1)^(n+1)` under the fixed unscaled quotient equivalence, also natural for original coefficient maps |
| V.1, original Hom pairing and both connecting maps | `homologyComp_connecting`, `sourceHomologyComp_connecting`, `sourceHomologyComp_naturality_middle`: the actual Hom pairing is natural in the middle complex and intertwines the two original Hom boundaries with factors `(-1)^(j+1)` (standard) and `(-1)^(i+1)` (displayed source); the original composite of lifts is an explicit coboundary, with no boundedness or K-injectivity requirement |
| V.1, augmented chosen-resolution boundary comparison | `InjectiveResolutionSequence.extClass_augmentation`, `injectiveHomologyExtAddEquiv_contravariantδ`, `injectiveHomologyExtAddEquiv_covariantδ`: for a supplied augmented short exact sequence of chosen injective resolutions, the original augmentation squares identify its connecting arrow with the original extension class; the existing standard and normalized-source Ext equivalences respect the actual Hom boundaries with factor `(-1)^(n+1)` contravariantly and no factor covariantly, including degree zero |
| V.1, injective horseshoe existence | `InjectiveResolutionSequence.ofShortExact`, `nonempty_injectiveResolutionSequence`: enough injectives suffices to construct an actual augmented short exact sequence of injective resolutions; the snake lemma proves the successive categorical cokernel rows short exact, the projected augmentations are quasi-isomorphisms, and the original horizontal maps form a degreewise split integer-indexed sequence |
| V.1, simultaneous horseshoe comparison | `injective_splitRow`, `InjectiveHorseshoe.rowResolution`, `compareHomotopy`, `sequenceCompare_augmentation`: the unchanged horseshoe is an injective resolution of the whole short complex; simultaneous lifts and homotopies preserve the horizontal arrows, and the actual integer-indexed comparison strictly preserves all original augmentations |
| V.1, coherent row-resolution functor | `InjectiveHorseshoe.homotopyFunctor`, `homotopyFunctor_map_eq`, `InjectiveRowResolution.change_trans`, `change_naturality`: identity, composition, and independence of simultaneous lifts hold in the homotopy category; changes between arbitrary injective resolutions of the whole row satisfy naturality and the cocycle law |
| V.1, constructed-map Hom boundary naturality | `InjectiveHorseshoe.covariantδ_compare_naturality`, `contravariantδ_compare_naturality` and their literal-source counterparts: both original boundaries commute with the actual constructed augmented sequence maps in all integer degrees, without assuming a compatible resolution map |
| V.1, arbitrary supplied resolution models | `injectiveResolutionNatHom`, `InjectiveResolutionSequence.rowResolution`: full faithfulness recovers the actual original nonnegative maps with their augmentation squares; short exactness is retained and the transposed supplied sequence is an injective resolution of the entire short complex |
| V.1, arbitrary-model coherent maps | `InjectiveResolutionSequence.compare`, `compare_augmentation`, `rowCompareHomotopy`, `change_trans`, `change_naturality`: arbitrary supplied resolution models admit actual augmented sequence comparisons, simultaneous coherent homotopies, and natural model-change isomorphisms satisfying the cocycle law |
| V.1, fixed Hom/Ext model independence | `injectiveHomologyExtAddEquiv_precomp`, `injectiveHomologyExtAddEquiv_postcomp` and their normalized-source variants: the unchanged double-resolution equivalences respect the actual maps in both variables; model change over identities preserves the fixed Ext value, also under the original module-valued equivalences |
| V.1, arbitrary-model boundary naturality | `InjectiveResolutionSequence.covariantδ_compare_naturality`, `contravariantδ_compare_naturality` and their literal-source counterparts: both original Hom boundaries commute with the actual arbitrary-model comparison maps in every integer degree |
| V.1, original module-valued boundary specialization | `injectiveHomologyModuleExtAddEquiv_contravariantδ`, `sourceInjectiveHomologyModuleExtAddEquiv_covariantδ` and their opposite-convention counterparts: the unchanged canonical linear Ext comparison gives additive-group identifications carrying the actual Hom boundaries to the previously defined module-valued Yoneda boundaries with the same signs; an augmented exact resolution sequence is supplied, not constructed |
| V.2, canonical natural map | `localDualityNatTrans`, `localDualityMap_stage`: original quotient-Ext stages define the actual natural map into `Hom_R(Ext^j(M,P), H^n_J(P))` for `i+j=n`, over any commutative ring; invertibility is not asserted |
| V.2, regular-local inputs | `regularLocal_localCohomology_isZero_of_gt`, `regularLocal_localCohomology_ring_isZero_of_ne`, `regularLocal_topLocalCohomology_not_isZero`: actual local cohomology vanishes above the dimension for any module; ring coefficients are concentrated and nonzero in that dimension |
| V.2, identity and rank-one normalization | `localDualityMap_identity_evaluation`, `localDualityMap_ring_top_isIso`: evaluation at the original identity Ext class retracts the canonical top-degree map with equal coefficients; for the rank-one ring module the canonical map is an isomorphism over every commutative ring |
| V.2.1, top degree for every finite module | `regularLocal_localDualityMap_top_isIso`, `regularLocal_localDualityTopNatIso`: the original canonical map is a natural isomorphism in the actual Krull dimension over a regular local ring; proved by additivity, actual finite free covers and their noetherian kernels, and right exactness of both unchanged functors |
| V.2.1, all complementary degrees | `regularLocal_localDualityMap_isIso`, `regularLocal_localDualityNatIso`: the unchanged canonical map is a natural isomorphism for every finite module and every `i+j=n`; descending induction uses exact transported Yoneda sequences on the original Ext/local-cohomology objects, their proved stagewise pairing compatibility, and actual finite-free vanishing. Above-dimension local-cohomology vanishing is already proved |
| V.3, formula (22), original dual comparison | `regularLocal_localCohomologyDualCompletionIso`, `regularLocal_localCohomologyDualCompletionIso_transpose`: over any regular local base, actual dual local cohomology is completed complementary Ext, with canonical transpose equal to the original completion map under this comparison |
| V.3, formula (22), complete regular base | `regularLocal_localDualityTransposeMap_isIso`, `regularLocal_localCohomologyDualIsoExt`, `regularLocal_localDualityTransposeNatIso`: the original transpose is invertible, naturally on finite modules, identifying the actual dual with original complementary Ext |
| V.3, regular-local finiteness | `regularLocal_localCohomology_isArtinian`, `regularLocal_localCohomology_socle_finite`, `regularLocal_localCohomology_annihilator_isFiniteLength`: all actual local-cohomology values of finite modules are Artinian with finite socle and finite-length power annihilators, even over a noncomplete regular base |
| V.3.1(ii), regular-base finite generation | `regularLocal_localCohomology_dual_completeProperty_of_dualizing`, `regularLocal_completedLocalCohomologyDual_finite_of_dualizing`: for every supported dualizing coefficient, actual duals satisfy the original complete-category conditions; their original completions are finite over the actual completed ring without completeness of the regular base; generalized to arbitrary noetherian local bases below |
| V.3.1(i), actual module parameters | `exists_localParameters`, `exists_localParameters_modulo`, `exists_moduleParameters`: converse Krull height produces genuine dimension-length parameters over every noetherian local ring; lifting parameters of the actual annihilator quotient gives a list of length equal to the module's support dimension |
| V.3.1(i), original transition calculation | `koszulTransition_comp_eq_zero_of_annihilating_prefix`, `stableKoszulCohomology_isZero_of_annihilating_prefix`: for annihilator generators followed by `d` parameters, the unchanged consecutive-power Hom--Koszul transition is zero in every degree above `d`, so its original cohomology colimit vanishes |
| V.3.1(i), sharp upper vanishing | `localRing_localCohomology_isZero_of_gt_moduleDim`: over every noetherian local base, original algebraic local cohomology of a finite module vanishes above its actual support dimension; the proof uses actual annihilator parameters, zero transitions, and original radical/Koszul comparisons, with no regularity or completeness hypotheses |
| General local-ring upper vanishing | `localRing_localCohomology_isZero_of_gt`: original local cohomology vanishes above the ring dimension for arbitrary coefficient modules over every noetherian local ring, using actual parameters and radical invariance |
| Actual residue Ext through injective envelopes | `FiniteResidueExt.injectiveEnvelope`, `FiniteResidueExt.cokernel_injectiveEnvelope`: finite original residue Ext is preserved through actual constructed injective envelopes and their categorical cokernels, using the unchanged degree-zero socle and genuine coefficient exact sequence |
| General-local Artinianity | `FiniteResidueExt.localCohomology_isArtinian`, `localRing_localCohomology_isArtinian`: all original local-cohomology values of modules with finite residue Ext are Artinian over every noetherian local ring, in particular for all finite modules; dimension shifting uses actual envelopes and original coefficient sequences |
| V.3.1(ii), general-local finite generation | `localRing_completedLocalCohomologyDual_finite`, `localRing_localCohomology_dual_finite`: for any actual supported dualizing coefficient, the completed original Hom dual is finite over the actual completed ring, and the original dual is finite over a complete base; no regularity or Cohen presentation is assumed |
| Original torsion quotient and scalar maps | `powerTorsion_quotient_eq_bot`, `exists_regular_on_powerTorsion_quotient`, `localCohomology_powerTorsion_mkQ_isIso`: the actual finite torsion quotient admits a regular element and its original projection preserves positive local cohomology; `localCohomology_linear` identifies original coefficient scalar maps with scalar maps on local cohomology |
| V.3.1(ii), general-local dimension bound | `localRing_completedLocalCohomologyDual_supportDim_le`: the original completed Hom dual in degree `i` has actual support dimension at most `i` over the completed ring, without completeness or regularity of the base; `completeLocal_localCohomology_dual_supportDim_le` gives the bound on the original dual over a complete base. The genuine dual regular-element sequence and original completion maps give induction on degree, without Cohen reduction |
| V.3.1(iii), complete-base top-dual dimension and nonvanishing | `completeLocal_topLocalCohomology_dual_supportDim_eq`, `completeLocal_topLocalCohomology_nontrivial`: over every complete noetherian local ring, the original top dual has exactly the finite coefficient module's support dimension, and original top local cohomology is nonzero. Simultaneous regular elements, actual support control modulo the closed point, and the genuine dual regular-element sequence give induction without regularity of the ring. The zero-dimensional base holds without completeness |
| V.3.1(iii), general-local top nonvanishing | `localRing_topLocalCohomology_nontrivial`, `localRing_completedTopLocalCohomologyDual_supportDim_eq`: original top local cohomology is nonzero over every noetherian local ring, and its original completed Hom dual has exactly the original coefficient support dimension over the actual completed ring. Original-ring parameters avoid contracted associated primes of the preceding completed dual, and the genuine completed scalar sequences give induction without a Cohen presentation or an assumed base-change comparison |
| V.3.2, module-valued ringed-space foundations | `moduleGammaZSectionsFunctor`, `moduleGammaZSectionsForgetIso`, `moduleToSheaf_map_shortExact`: supported sections are actual modules over the structure ring on each open; their additive groups recover Exposé I's section functor, and forgetting the sheaf's module structure is exact |
| V.3.2, general acyclicity input | `moduleIsFlasque_of_injective`, `derivedModuleGammaZSections_isZero_of_isFlasque`, `derivedModuleGammaZSections_isZero_pushforward_injective`: injective module sheaves are flasque, and the actual higher module-valued supported cohomology vanishes on flasque sheaves and on direct images of injectives under arbitrary ringed-space morphisms, without flatness |
| V.3.2, scalar-compatible composite comparison | `ringedModulePushforwardSupportedGlobalIso`, `ringedModuleSupportedGlobalRightDerivedIso`: actual supported sections and the right-derived direct-image/section composite agree naturally with source supported cohomology restricted along the actual map on global structure rings |
| V.3.2, original additive cohomology, naturally | `gammaZSections_quasiIso_of_boundedBelow_flasque`, `derivedModuleGammaZSectionsForgetIso`, `derivedModuleGammaZSectionsIsoH_Z`: mapping cones compare the actual module and additive resolutions in all degrees; augmentation-compatible chain homotopies prove that the unchanged objectwise comparisons commute with the original coefficient maps, without preservation of injectivity by forgetting scalars |
| V.3.2, retained scalar action | `moduleUnderlyingComplexGlobalScalarRingHom`, `moduleUnderlyingDerivedGlobalScalarRingHom`: actual global structure-ring actions on underlying additive complexes and derived objects satisfy all ring laws and commute with coefficient cochain maps |
| V.3.2, additive spectral sequence and E₂ | `ringedModulePushforwardAdditiveSpectralSequence`, `ringedModulePushforwardAdditiveSpectralSequenceE2Equiv`, `ringedModulePushforwardE2ModuleAddEquiv`: actual truncations of the original module direct-image resolution give genuine pages and differentials with E₂ the original supported cohomology of original higher module direct images |
| V.3.2, genuine module-valued spectral sequence | `spectralObjectModuleLift`, `ringedModulePushforwardModuleSpectralSequence`, `ringedModulePushforwardModuleSpectralSequenceForgetIso`: the original scalar action lifts the actual spectral object and its exactness to modules; canonical forgetful comparisons preserve all differentials and the original next-page homology isomorphisms |
| V.3.2, original module-linear E₂ identification | `ringedModulePushforwardModuleE2LinearEquiv`, `ringedModulePushforwardModuleE2LinearEquiv_toAddEquiv`: the actual E₂ page identifies module-linearly with original module-supported cohomology of the original higher module direct image; every original comparison factor intertwines the retained scalar endomorphisms, and the underlying additive equivalence is exactly the preexisting one, without commutativity or flatness assumptions |
| V.3.2, first quadrant and canonical finite module filtration | `ringedModulePushforwardModuleSpectralObject_isFirstQuadrant`, `ringedModulePushforwardSpectralFiniteFiltration`, `ringedModulePushforwardModuleStablePageIsoGraded`: the actual module pages vanish outside the first quadrant and, for `r ≥ n + 2`, are the associated graded of the canonical total object's finite exhaustive submodule filtration |
| V.3.2, actual module-linear abutment | `flasqueGammaComplexDerivedHomEquiv`, `ringedModulePushforwardSpectralAbutmentLinearEquiv`, `ringedModulePushforwardSourceFiniteFiltration`: the unchanged localization map computes supported derived Hom on bounded-below flasque complexes and respects all additive cochain maps; the actual filtered total module is original source supported cohomology with the prescribed scalar restriction, and the finite exhaustive filtration is transported to that source module |
| V.3.2, coefficient functoriality and original comparisons | `ringedModulePushforwardModuleSpectralSequenceFunctor`, `ringedModulePushforwardModuleSpectralSequenceCoefficientMap_E2`, `ringedModulePushforwardSpectralTotalCoefficientMap_abutment`: actual resolution maps induce module-linear maps of the entire spectral sequence; resolution homotopies prove lift-independence and the functor laws; the unchanged E₂ and abutment identifications retain the original higher-direct-image and source supported-cohomology coefficient maps |
| V.3.2, natural and resolution-independent filtration | `ringedModulePushforwardModuleSpectralSequenceResolutionIso_naturality`, `ringedModulePushforwardModuleStablePageIsoGraded_naturality`, `ringedModulePushforwardSourceFiniteFiltration_map_le`, `ringedModulePushforwardSourceFiniteFiltration_eq`: canonical resolution changes are natural and satisfy the cocycle law; stable-page comparisons retain the genuine associated-graded maps; original source coefficient maps preserve the actual finite filtration, which is independent of resolution |
| V.3.3, component-generic-point criterion | `supportedFunctorColimit_associatedPrimeSpectrum_eq`, `supportedFunctorColimit_associatedPrimeSpectrum_eq_of_components`: IV's actual representing colimit has exactly the selected component generic points as associated primes when the original left-exact functor vanishes precisely on modules containing none of those components; original `R/p` tests prove the criterion, with components indexed by minimal primes of the support ideal |
| V.3.3, actual topological components | `supportedFunctorColimit_associatedPrimes_of_irreducibleComponents`: the original irreducible components of `V(J)` are accepted directly; their genuine generic points are constructed and the actual representing colimit has exactly their range as associated primes. No list of minimal primes or generic points is supplied as an assumption |
| V.3.1(iii), supported top-dual functor | `supportedLocalCohomologyFunctor_preservesFiniteColimits`, `supportedTopLocalCohomologyDual_isZero_iff`: original top local cohomology is right exact on the actual bounded supported category, and its actual Hom dual vanishes exactly when the coefficient support misses the top component generic points; actual chains of primes supply the dimension criterion |
| V.3.1(iii), associated-prime formula | `localRing_topLocalCohomologyDual_associatedPrimeSpectrum`: the original top Hom dual has precisely the dimension-`n` associated primes of the original finite coefficient module. V.3.3 and III.1.3 apply to the genuine supported representation; `additiveFunctorModuleLiftIsoOfLinear` retains the original scalar action. The formula holds even without completeness; finiteness over the original ring still uses completeness |
| Actual affine-open vanishing | `homeomorphismCohomologyFunctorIso`, `affineChartCohomologyEquiv`, `affineOpen_H_pos_subsingleton`: genuine direct image under homeomorphisms and canonical affine charts transport original ordinary cohomology; every actual quasi-coherent module is acyclic in positive degrees on an affine open of a locally noetherian scheme |
| V.3.4, local argument | `localCohomology_isZero_of_affineComplement`, `localRing_ringKrullDim_le_one_of_affinePuncturedSpectrum`: actual affine-complement vanishing and the original relative sequence give local-cohomology vanishing above one; original top nonvanishing then bounds the dimension of a noetherian local ring with affine punctured spectrum by one |
| V.3.4, component codimension | `irreducibleComponent_codimension_le_one_of_affineComplement`: every actual irreducible component of an arbitrary closed subset with affine complement in a noetherian affine spectrum has codimension at most one. Localization identifies the actual complement with the punctured local spectrum; codimension is the literal infimum of original structure-stalk dimensions. There is no principal-support hypothesis |
| V.3.5, finite-length duality | `SupportedDualizingModule.moduleHomDual_finiteLength_iff`, `.moduleHomDual_length`: actual Hom duality detects finite length and preserves extended length on arbitrary modules over a noetherian local ring, without completeness; the original bidual evaluation is invertible when the dual has finite length |
| Actual Ext localization | `finiteProjectiveResolution`, `localizedLinearYonedaObjIso`, `moduleExtLocalizationIso`, `moduleExtLocalizationRingIso`: degreewise finite genuine projective resolutions and termwise Hom localization give localized-ring-linear comparisons for original Ext, with finite first argument and arbitrary second argument, including actual ring coefficients |
| V.3.5, through localized Ext | `regularLocal_localCohomology_length_eq_ext`, `regularLocal_localCohomology_finiteLength_iff_ext_atPrime`: over a regular local ring, original local cohomology has the same extended length as complementary Ext; finite length is equivalent to vanishing of actual complementary Ext over every nonclosed prime localization |
| Koszul systems under arbitrary ring maps | `koszulSystemBaseChangeIso`, `koszulHomComplexSystemScalarChangeIso`: actual tensor extension identifies the original inverse Koszul systems, including every power transition; the source-ring-linear Hom adjunction identifies their actual Hom cochain systems, without flatness |
| Original local-cohomology scalar change | `localCohomologyScalarChangeIso`: for any map of noetherian commutative rings, scalar restriction of local cohomology at the image ideal is source-ring local cohomology of the restricted coefficient, for all ideals, degrees, and arbitrary coefficients |
| V, formula (19) and finite length | `localRing_localCohomologyScalarChangeIso`, `localRing_localCohomology_length_eq_of_surjective`, `localRing_localCohomology_finiteLength_iff_of_surjective`: surjective local-ring change preserves actual maximal-ideal local cohomology, extended length, and finite length; no flatness is assumed |
| V, formula (20), actual Hom duals | `surjectiveHomDualScalarChangeIso`, `surjectiveLocalCohomologyDualIso`: actual coinduction is dualizing over the target; one choice of coefficient isomorphism gives a natural source-ring-linear comparison of the specified Hom duals on all modules, and a comparison of duals of actual local cohomology |
| V, formula (21) and module dimension | `restrictScalarsAnnihilatorQuotientEquiv`, `restrictScalars_finite_iff_of_surjective`, `restrictScalars_supportDim_of_surjective`: the induced map identifies the original annihilator quotients; finite generation and actual finite-module support dimension are unchanged |
| V.3.5, original prime-localization transport | `localRingHom_surjective`, `localizedRestrictScalarsIso`, `localizedRestrictScalarsIso_hom_mk`, `ringKrullDim_quotient_comap_of_surjective`: the actual local ring map is surjective, the original localized coefficients agree with their original element maps, and the dimensions of corresponding prime quotients agree |
| V.3.5, quotient reduction of both conditions | `localCohomologyAtPrimeScalarChangeIso`, `puncturedLocalCohomologyVanishing_iff_of_surjective`, `localCohomologyFiniteLengthCriterion_iff_of_surjective`: actual local cohomology at corresponding points agrees after scalar restriction; both finite length and shifted punctured vanishing are quotient-invariant. Points outside the image vanish and negative degrees impose no condition |
| V.3.6, depth deduction | `puncturedLocalCohomologyVanishing_le_iff_depth`, `localCohomology_finiteLength_le_iff_depth_of_criterion`, `puncturedDepthBound_iff_of_surjective`: shifted vanishing through a threshold is equivalent to the actual localized depth bound, including infinite depth; the deduction from V.3.5 and quotient invariance hold over every noetherian local ring |
| V.3.5, homological prime-localization input | `localizedPrimeQuotientResidueFieldIso`, `localizedPrimeQuotientResidueFieldIso_hom_mk`, `regularLocal_atPrime_moduleGlobalDimension_le`: the original localization of `R/p` is the actual residue field of `R_p`, with the original element map; every prime localization has global dimension bounded by the original regular ring's Krull dimension, without assuming regularity of the localized ring |
| Homological regularity criterion | `isRegularLocalRing_of_residueField_bound`, `isRegularLocalRing_iff_residueField_projectiveDimension_ne_top`: a noetherian local ring is regular exactly when its actual residue field has finite projective dimension. Regular-element reduction preserves bounds over the quotient ring, a cotangent functional gives the actual residue-field retract of `m/xm`, and lifting minimal generators completes induction |
| V.3.5, regularity of prime localizations | `regularLocal_atPrime_isRegularLocalRing`, `regularLocal_isRegularRing`, `regularLocal_atPrime_moduleGlobalDimension_eq_ringKrullDim`: every actual prime localization of a regular local ring is regular, and its global dimension equals its own Krull dimension; no converse criterion or localization-regularity hypothesis is supplied |
| V.3.5, regular-local dimension formula | `regularLocal_top_associated_mem_ext_support`, `regularLocal_atPrime_dimension_add_quotient`: the top-dual associated-prime formula forces complementary Ext to be supported at the original top primes; localization and residue Ext concentration give `dim R_p + dim(R/p) = dim R`, without assuming catenarity |
| V.3.5, full criterion | `regularLocal_localCohomology_finiteLength_iff_punctured`, `localCohomology_finiteLength_iff_punctured_of_surjective`: for finite modules over quotients of regular local rings, original local cohomology has finite length exactly when the original shifted local cohomology vanishes at all nonclosed points. Both localization regularity and the dimension formula are proved; negative shifted degrees and upper vanishing are handled explicitly |
| V.3.6, full criterion | `regularLocal_localCohomology_finiteLength_le_iff_depth`, `localCohomology_finiteLength_le_iff_depth_of_surjective`: finite length through degree `n` is equivalent to the actual punctured depth bound for finite modules over quotients of regular local rings; no additional finite-length criterion is assumed, and zero modules retain infinite depth |
| General-local socle and annihilators | `localRing_localCohomology_socle_finite`, `localRing_localCohomology_annihilator_isFiniteLength`, `localRing_localCohomology_dual_completeProperty`: actual socles are finite, actual power annihilators have finite length, and actual Hom duals satisfy the original complete-category conditions over every noetherian local ring |
| IV.4.5 | `localArtinianTensorCompletionEquiv`, `supportedCompletionEquivalence`, `localArtinianCompletionEquivalence`: the actual tensor map is invertible on arbitrary locally Artinian modules, and original tensor/restriction give inverse equivalences on the actual supported and locally Artinian categories; no extra noetherianity hypothesis on the completed ring |
| IV.4.5, submodules and finiteness | `completion_submodule_smul_mem`, `completion_restrictScalars_finite`: every original-ring submodule of a supported completed-ring module is stable under its existing completed action; restriction preserves finite generation |
| IV.4.5, finite category | `finiteSupportedCompletionEquivalence`: original tensor/restriction give an equivalence on finite supported modules, retaining the actual unit/counit and commuting with the full supported equivalence |
| IV.4.6, supported convention | `completion_supportedDualizingModule_iff`, `SupportedDualizingModule.completion`: actual restriction and tensor extension preserve supported duality, with actual linear Hom restriction, canonical bidual-evaluation compatibility, and underlying-group identification; no extra noetherianity hypothesis on the completion |
| IV.4.9, canonical representing module | `supportedFunctorColimit_locallyArtinian`, `supportedFunctorColimit_annihilator_isFiniteLength`, `supportedFunctorAnnihilatorFiltrationIsColimit`: literal local Artinianness, finite-length actual annihilator stages under duality, and the original module as their categorical colimit with literal inclusions |
| IV.4.7, explicit supported convention | `nonempty_moduleInjectiveEnvelope`, `supportedDualizingModule_iff_injective_essential_residue`, `exists_supportedDualizingModule`, `SupportedDualizingModule.nonempty_iso`: actual envelopes constructed by Zorn, full supported characterization, existence, and noncanonical uniqueness |
| IV.4.1 / IV.4.3–4.4 / IV.4.9, supported convention | `supportedDualizingModule_iff_support_functorDuality` ties the definition to original abelian-group-valued Hom duality plus actual support; `SupportedDualizingModule.finite_coinduction`, `.quotient_annihilator`, and `.locallyArtinian` give the named transfers and local Artinian property |
| IV.5 opening, anti-equivalence | `supportedFunctorAntiEquivalence`: the actual original dual functor and its right opposite, with original inverse-evaluation counit and both coherent triangle identities; standard adjointification changes neither functor nor counit |
| IV.5 opening, orthogonality | `supportedHomOrthogonalOrderIso`, `supportedFunctorOrthogonalOrderIso`, `mem_supportedFunctorOrthogonalOrderIso`: the actual vanishing orthogonal and coorthogonal are inverse order-reversing submodule bijections; original-functor membership is literal canonical evaluation vanishing |
| IV.5 opening, length/colength | `supportedFunctorOrthogonal_length_eq_colength`, `supportedFunctorOrthogonal_colength_eq_length`: the original orthogonal bijection exchanges actual submodule length and quotient length, including infinite lengths |
| IV.5 opening, Artinian-local ideals | `artinianLocalHomIdealOrderIso`, `mem_artinianLocalHomIdealOrderIso`: the actual injective residue-tested coefficient has an order-reversing ideal/submodule bijection, whose image of an ideal is literally its annihilator in that coefficient |
| IV.5 opening, cyclic/socle criterion | `supportedFunctor_monogenic_iff_socle_length_le_one`: literal single generation is equivalent to the original dual's socle having length at most one, including zero; `localSocle_eq_sSup_simple` identifies the maximal-ideal annihilator with the sum of simple submodules |
| IV.5.2, Macaulay example | `macaulayFunctor_duality`, `macaulayModule_supportedDualizing`, `macaulayFunctorRepresentationIso`: literal `Hom_K(-,K)` with its source-induced ring action, actual quotient-dual colimit and canonical representation; only the residue field is required finite over `K`; `coefficientField_finrank_eq_residueDegree_mul_length` gives the dimension–length formula |

The IV.1.1 proof constructs the source's evaluation from maps `R → M`.
Finite free modules are handled by coordinate reconstruction; over a noetherian
ring the kernel of a finite free cover is finite, and left exactness descends
the reconstructed value. The representing module is the canonical module
on the functor's actual value at `R`, with no finiteness assumption on that value.

IV.1.2 extends the same actual evaluation to all modules. The genuine cocone
of finite submodule inclusions is colimiting, so IV.1.1 and preservation of
its opposite limit prove invertibility on arbitrary modules. The source's
preorder-only condition is sufficient: thin skeletons of discrete and cospan
categories give actual preorder presentations of products and pullbacks,
which force preservation of all small limits. All indexing sets and modules
use the stated universe; no filteredness is silently imposed.

IV.1.3 uses the actual quotient-induced diagram and its actual colimit.
The colimit support is proved without left exactness. Under left exactness,
its stage maps are injective, so the finite image of any map from a finite
module lies in one stage. The original stagewise evaluation then proves the
specified global evaluation bijective. IV.1.4 applies this result by integer
induction from the supplied lower bound, deriving each required left-exact
degree from the original connecting sequence.

The IV.3.1 Hom-model implication uses genuine double Hom evaluation
`x ↦ (f ↦ f x)`. Residue-field tests give the canonical simple-module
evaluation isomorphism by nonvanishing and Schur's lemma; the actual short
five lemma and finite-length induction extend this to all finite supported
modules. Their finite length is derived from an annihilating ideal power
and the Artinian power quotient. Neither finiteness of `H` nor duality on
all modules is assumed. Full transport to the original `T` and the four-way
equivalence are now proved: canonical biduality forces dual restriction maps
to be surjective by applying reflexivity to their actual cokernels. Residue
tests follow from their actual annihilators and simplicity. For IV.3.2,
left exactness of Hom and finite-length additivity force surjectivity; the
canonical representation transfers this to the original left-exact functor.
The original functor's scalar action, actual finite-valued factorization,
and natural map into actual `T(T(M))` are constructed, not assumed as extra
comparison data. IV §5's opening anti-equivalence and orthogonality results
are proved for the original functor. Canonical reflexivity of actual supported
quotients supplies separation of elements and both double-orthogonal identities;
the resulting actual lattice anti-isomorphism exchanges length and colength.
Over a local ring, Nakayama identifies actual single generation with residue
quotient length at most one. The orthogonal of the maximal-ideal multiple is
the actual dual socle, giving the cyclic/socle criterion for the original `T`.
Finite coinduction and quotient annihilators preserve the actual support,
not just the Hom tests. The tensor assertion of IV.4.5 holds for arbitrary
locally Artinian modules: finite nilpotent cyclic submodules and flatness of
the completed ring prove that the original scalar-extension map is bijective.
The result concerns tensoring with the completed ring, not taking the adic
completion of the coefficient module.
Finite length of all ideal-power annihilators is proved under duality only;
it is not assumed for arbitrary locally Artinian modules in the tensor proof.

IV.4.7 is proved with the supported representing-module convention explicit.
Raw Hom duality on finite closed-point-supported modules alone does not imply
that the coefficient has this support: off-support summands can be invisible.
The proof does not claim unqualified uniqueness for such arbitrary Hom targets.
With actual support, canonical Hom duality is equivalent to being an injective
essential extension of the residue field. Envelopes are constructed from
enough injectives using two Zorn arguments; support of an injective essential
residue extension is then derived using the injectivity of ideal-power torsion.
IV.4.2 now has a constructed exact linear finite-length duality, its canonical
evaluation isomorphism, length-one maximal-ideal annihilators, and local
Artinianness of its actual nonlocal coefficient. General nonlocal representation
is now proved: every additive left-exact finite-length functor is canonically
represented by its actual cofinite-ideal colimit. Over a noetherian ring,
original Hom gives an equivalence with locally Artinian modules. Exactness
of the original functor is equivalent to injectivity of its actual colimit,
by cofinite Artin–Rees/Baer reduction. For any original linear finite-length
functor with a natural involution, its actual representing coefficient is
injective and locally Artinian, and every maximal-ideal annihilator is the
corresponding residue module, of length one. No separate socle-decomposition
theorem is asserted, and the supplied involution is not identified with
canonical bidual evaluation. Local Artinianness and coefficient uniqueness
concern the constructed representative or already-locally-Artinian modules,
not arbitrary raw Hom targets with invisible summands.
IV.4.5's categorical completion equivalences are
proved using actual scalar change; the completed ring's finitely generated
maximal ideal suffices, without assuming a separate noetherianity theorem.
IV.5.2 has the actual Macaulay quotient-dual colimit and its canonical
identification with the continuous coefficient-field linear dual of the
original adic ring. Continuity is proved equivalent to vanishing on an
ideal power, and the comparison uses original quotient maps; completeness
of the ring is not assumed. IV.4.6 transfers the actual
supported-dualizing definition in both directions through completion, using
the actual Hom comparison and original canonical evaluation. The structural
remarks of IV.4.8 and later dualizing-module results remain incomplete.
IV.5.1 is proved over a complete noetherian local base with the actual Hom
functors and canonical evaluations. Over a general noetherian local base,
finite biduals are actual completions and the original `CA` dual lands in
literal `DA`. Completion transport of the actual `CA` category is proved;
noetherianity of actual adic completions is proved for every ideal, and the
resulting actual scalar-change/Hom equivalence with finite completed-ring
modules is constructed and naturally compared with original-ring Hom.
Actual module completion and scalar restriction identify the original `DA`
categories. `matlisAntiEquivalence` proves IV.5.1 over a general noetherian
local base with forward exactly original-ring Hom; both natural completion
transport squares are proved. The explicit supported representing-module
convention remains in force. The final packaged equivalence unit is not
claimed to be definitionally the canonical evaluation.
The regular-local domain and regular-parameter foundations for IV.5.3–5.4
are proved from the actual regular-local class, as are the actual residue
projective dimension and off-degree Ext vanishing for all finite-length
first arguments. The top Ext functor is exact and canonically represented
by its actual injective colimit. The original regular Koszul augmentation is
a proved resolution and its actual finite-stage Ext comparison is invertible.
The concrete top module-valued residue Ext is computed as an actual linear
isomorphism. The canonical comparison to derived-category Ext is proved
linear, exactly upgrading the existing additive comparison, and natural in
both variables. Literal maximal-ideal depth equals Krull dimension, and
lower Ext vanishing also holds for arbitrary modules annihilated by a
maximal-ideal power. Hence IV.5.4's original top-degree functor is dualizing,
and its actual representing colimit is original algebraic local cohomology,
with the actual quotient transitions and colimit stage maps respected.
Original affine supported-sheaf cohomology is compared as an additive group;
compatibility with a separately defined geometric scalar action is not claimed.
IV.5.3's global dimension equality and upper vanishing for arbitrary modules
are now proved. Induction on actual support dimension extends the finite-length
bound to all finite modules. Baer's criterion and actual injective dimension
shifting extend cyclic tests to all modules. The supremum of the original
projective dimensions equals the residue-field dimension over any noetherian
local ring, even when infinite; for regular local rings it equals Krull
dimension. Both arguments of upper Ext vanishing may be arbitrary.
IV.5.5's initial noncanonical local-cohomology/Macaulay
isomorphism is proved, as are the original product power transitions and
monomial-class shifts on actual quotient modules. The direct power-ideal
quotient diagram has original top local cohomology as its colimit, with
original stage maps preserved. For literal finite-variable power series
rings, coordinate-power quotients have the actual bounded-monomial basis
and dimension `r^d`, including the zero-variable and zero-power cases. For
positive powers, top-coefficient extraction of products is a perfect pairing
on the original quotient, with complementary monomials recovering every
coefficient. The finite forms now glue through the original product transitions
and the proved positive-index cofinality. This gives the explicit ring-linear
isomorphism from original maximal-ideal top local cohomology to the actual
continuous dual and Macaulay module. Its coefficient-field linear residue
form has the stated monomial formula and a nondegenerate product pairing.
The comparison is proved equal to its explicit colimit construction, not
obtained by abstract uniqueness. Constructing a coefficient field and Cohen
presentation for arbitrary complete regular local rings, completed
differentials, parameter independence, and field compatibility remain open.
IV.2.1 is proved for the original functor, using an actual
lift of finite supported short exact sequences and the canonical representation.
Exposé V has a partial formalization: the actual linear Yoneda pairing is
natural in all variables and compatible with both original derived Ext
long-exact-sequence boundaries. Its canonical transport to the original
module-valued Ext gives `localDualityNatTrans`, with original quotient-stage
compatibility, over every commutative ring. For regular local rings, actual
local cohomology vanishes above the dimension for arbitrary modules, and
ring-coefficient local cohomology is concentrated and nonzero in the actual
dimension. The original identity Ext class gives a retraction of the
top-degree canonical map with equal coefficients. Additivity and the genuine
finite-presentation argument extend the rank-one isomorphism to every finite
module in top degree, naturally on the original finite-module category.
Right exactness is proved from the original Ext-colimit coefficient sequence
and upper vanishing on the source, and from canonical degree-zero Ext--Hom
comparison and the actual injective dualizing module on the target.
The canonical linear Ext comparison transports the exact Yoneda sequences
onto the unchanged module-valued Ext objects, with their original
degree-preserving arrows. Filtered colimits give exact sequences on actual
local cohomology. Their boundary compatibility with the unchanged canonical
map is proved at each original quotient stage by Yoneda associativity.
Descending induction through finite free covers and their finite kernels
now proves V.2.1 in every complementary degree, naturally on finite modules;
above-dimension vanishing is already proved. The source's literal Hom complex
is now constructed, and an explicit degreewise sign gives its chain
isomorphism to Mathlib's convention. The actual sign-normalized augmentation
from two specified injective resolutions is a quasi-isomorphism and computes
Ext through its homology map; the incompatible unsigned formula in the source
is not asserted. The original cohomology product is now identified with Yoneda
composition under the same previously specified Ext comparison. Actual unscaled
source kernel and quotient data prove that the source product acquires exactly
`(-1)^(ij)` under normalization. Actual mapping-cone lifts now identify the
original lifted-cocycle boundary with the derived connecting morphism. For
unchanged unsigned projective-resolution representatives, the Yoneda boundary
is precisely `(-1)^(n+1)` times the lifted boundary's `extMk` class; projectivity
and exactness supply the lifts for every Ext class. The existing linear comparison
now sends actual module-cohomology representatives to these same `extMk` classes
in all degrees, including zero through the original Ext-to-Hom isomorphism.
Consequently the independently constructed module-valued coefficient boundary
and the transported Yoneda boundary differ by exactly `(-1)^(n+1)`, as do their
original filtered Ext-colimit and ideal-power local-cohomology boundaries.
The original contravariant Hom sequences into degreewise-injective complexes
now have exactness and naturality in every integer degree. For K-injective
targets, actual cocycle representatives identify their connecting maps with
the original derived connecting arrow: the standard convention contributes
`(-1)^(n+1)`, while the literal source differential needs no extra sign under
its fixed unscaled quotient equivalence. The covariant Hom sequence now also
has exactness and naturality for arbitrary source complex and degreewise-injective
first coefficient complex. With K-injective endpoints, its standard boundary
is the original derived connecting arrow, while the literal-source boundary
has exactly `(-1)^(n+1)`. The original pairing is natural in the middle complex;
an explicit composite of lifts proves its boundary identity with factors
`(-1)^(j+1)` (standard) and `(-1)^(i+1)` (source), without boundedness or
K-injectivity. The source's unsigned connecting-pairing formula is not asserted
for these unchanged conventions. For a supplied augmented short exact sequence
of chosen injective resolutions, its original augmentation squares now prove
compatibility with the original extension class. The existing standard and
normalized source Ext equivalences compare the actual Hom boundaries with
Yoneda boundaries in every natural degree: factor `(-1)^(n+1)` contravariantly,
no factor covariantly. The unchanged canonical linear comparison gives the
same result for original module-valued Ext, as additive-group identifications.
The injective horseshoe now constructs augmented exact resolution sequences
in every abelian category with enough injectives, by iterating actual
categorical cokernels of embeddings into split injective rows. The original
horizontal maps and augmentation squares are retained, and the resulting
integer-indexed sequence is split in each degree. These split rows are also
injective objects of the short-complex category. The same horseshoe therefore
has simultaneous comparison maps and homotopies preserving both horizontal
arrows; its actual integer-indexed comparisons strictly preserve the original
augmentations. They form a functor after passing to homotopy, independent of
the chosen simultaneous lift. Arbitrary injective row-resolution changes
satisfy naturality and the cocycle identity. Both original Hom boundaries
are natural under the constructed maps, in both differential conventions.
Arbitrary separately specified resolution-sequence data now gives an injective
resolution of the entire row, with full faithfulness recovering the unchanged
nonnegative maps and augmentation squares. These models admit actual augmented
comparisons, simultaneous coherent homotopies, and natural model changes
satisfying the cocycle identity. The fixed standard and normalized-source Ext
equivalences respect actual precomposition and postcomposition in all natural
degrees. Changes over identities preserve the Ext value, including the original
module-valued Ext comparison. Both original Hom boundaries are natural for
the arbitrary-model comparisons. These results are not assumed in
local-duality invertibility.
The canonical transpose now identifies
actual dual local cohomology with completed complementary Ext and becomes
the original completion map. Over a complete regular base this proves V, formula (22),
naturally on finite modules. Local cohomology of finite modules over every
noetherian local base is Artinian, with finite actual socle and finite-length
power annihilators; its actual Hom duals satisfy the literal complete-category
conditions and are finite over a complete base. Their original completions
are finite over the actual completed ring even without completeness of the
base. This general-local finite-generation assertion is proved through finite
original residue Ext: actual essential injective envelopes preserve finite
socles, the original coefficient sequence preserves residue-Ext finiteness in
their cokernels, and the genuine local-cohomology sequence gives Artinianity
by induction. The dimension bound in V.3.1(ii) now also holds over arbitrary
noetherian local bases. The original torsion-quotient map preserves positive
local cohomology, and original coefficient scalar maps induce the same scalars
on local cohomology. Dualizing the genuine regular-element sequence bounds
the principal quotient of the higher dual by the lower dual. Those duals are
already complete; their actual completion maps preserve the exact sequence
over the completed ring, giving the dimension bound by induction on degree.
No Cohen presentation is assumed. V.3.1(i)'s sharp upper bound
by the module support dimension is
proved for arbitrary noetherian local rings: genuine parameters modulo the
annihilator, lifted and preceded by annihilator generators, make the original
consecutive-power Hom--Koszul transitions zero above that dimension. The
actual radical and Koszul-colimit comparisons give original local-cohomology
vanishing. The ring-dimension bound also holds for arbitrary coefficient
modules. These are upper-vanishing statements for the natural-number-indexed
algebraic functors, not a separate negative-degree convention. Over every
complete noetherian local ring, V.3.1(iii)'s top-dual dimension equality and
top nonvanishing are now proved. A simultaneous regular element on the
coefficient and preceding dual torsion quotients confines the genuine dual
sequence's error to the closed point; upper vanishing makes the parameter
regular on the top dual, giving dimension equality by induction. The
zero-dimensional base holds without completeness. Top nonvanishing now also
holds over noncomplete noetherian local rings. Prime avoidance of contracted
associated primes chooses original-ring parameters regular on the coefficient
and preceding completed-dual torsion quotients. The actual completed dual
sequences preserve scalar injectivity and control the closed-point support
error. Induction proves that the completed top dual has exactly the original
coefficient support dimension, forcing original top nonvanishing without an
assumed local-cohomology base-change comparison. The associated-prime formula
is now proved for the unchanged top dual, even without completeness of the
base. The top functor is right exact on actual finite supported modules.
Chains in the original spectrum identify the maximal-dimensional components;
the original top dual vanishes exactly when its coefficient support misses
all those generic points. The minimal-prime-indexed form of V.3.3 identifies
the associated primes of IV's actual representing colimit via the original
cyclic tests. The criterion also accepts the actual irreducible components
of the closed subspace and constructs their genuine generic points.
The canonical module lift agrees with the dual's original
scalar action, and III.1.3 gives the formula on the original functor values.
V.3.4 is proved for arbitrary closed subsets with affine complement: every
original irreducible component has codimension at most one, with codimension
defined as the infimum of its original structure-stalk dimensions. Genuine
affine-chart comparisons prove quasi-coherent vanishing on actual affine opens.
The original relative sequence gives local-cohomology vanishing above one.
Localizing the actual complement at a component generic point gives the
punctured local spectrum, and original top nonvanishing bounds its dimension.
V.3.5 is proved for finite modules over quotients of regular local rings. The
original Hom dual detects finite length without completeness of the base.
Degreewise finite projective resolutions exist in the category of all modules;
the actual Hom localization maps commute with their differentials. Original
Ext therefore localizes to original Ext over the localized ring, linearly over
that ring. In the regular-local case, finite length of original local cohomology
is equivalent to vanishing of actual complementary Ext at each nonclosed point.
The quotient reduction of both conditions is proved: original local ring maps
are surjective, actual localized coefficient modules agree, and corresponding
prime quotients have equal dimensions. Closed points correspond; outside the
quotient's image all localized coefficients vanish. The shifted condition
tests precisely nonnegative degrees, without truncating negative degrees to
zero. V.3.6 is proved using original localized depth, including infinite depth,
under the same source hypotheses. Its depth bound is quotient-invariant.
No additional V.3.5 hypothesis is supplied in the full V.3.6 theorem.
The homological input for localization regularity is also proved. The actual
localized cyclic module `R/p` is the actual residue field of `R_p`, with its
original element map. Every module over `R_p` has projective dimension at most
the original regular ring's dimension, giving finite global dimension at
every prime. The converse homological regularity criterion is now proved:
finite residue-field projective dimension forces regularity. Actual regular
parameters outside the square of the maximal ideal, quotient-ring linear
splittings, and lifting minimal generators give induction on the bound.
Consequently every prime localization is regular, and its global dimension
equals its own Krull dimension. The separate formula
`dim R_p + dim(R/p) = dim R` is also proved: the top-dual associated-prime
formula forces complementary Ext of `R/p` to be nonzero at `p`, and actual
Ext localization and residue Ext concentration identify its degree with the
local ring dimension. This completes the regular-local argument of V.3.5;
the already proved quotient reduction gives its stated generality.
The algebraic change-of-rings steps in V, formulas (19)--(21), are now proved.
Tensor extension preserves the actual inverse Koszul systems and every power
transition, without flatness. Original Hom adjunction, exact scalar restriction,
and original colimits prove the local-cohomology comparison for every ideal
and arbitrary coefficients over noetherian rings. For surjective local maps
the maximal-ideal cohomology modules and their extended lengths agree. The
Hom-dual comparison is natural in all modules after one coefficient-isomorphism
choice. The actual annihilator quotients, finite generation, and finite-module
support dimension are unchanged. For V.3.2, module-valued supported sections
and higher direct images on arbitrary ringed spaces are now constructed.
Injective module sheaves are flasque, and their direct images are acyclic for
the actual module-valued supported-section functor, without flatness. The
right-derived composite agrees naturally in every degree with supported
cohomology on the source restricted along the actual global ring map.
Bounded-below flasque mapping cones now prove that actual supported sections
preserve the resolution quasi-isomorphisms. Actual cochain representatives
into an additive-injective resolution give, in every degree, a comparison
of the underlying module cohomology with original additive-sheaf cohomology,
including the preexisting global `H_Z`. Augmentation-compatible chain homotopies
now prove naturality of these unchanged maps, for arbitrary choices of the
resolutions. Forgetting scalars is not assumed to preserve injectivity.
The actual global scalar action is retained on the underlying additive
complexes and their derived objects. Canonical truncations of the original
module direct-image resolution, followed by derived Hom from `zZX_closed`,
now give a genuine additive spectral sequence. Its actual E₂ terms identify
with original `H_Z` of the original higher module direct images, and additively
with their module-valued supported cohomology. The retained action now lifts
the actual spectral object to modules over the target global structure ring,
including its original exactness. The resulting module spectral sequence
forgets canonically to the entire original additive sequence, with all
differentials and the original next-page homology isomorphisms. First-quadrant
bounds give a finite exhaustive submodule filtration on its actual total
object; in total degree `n`, every page with `r ≥ n + 2` is its associated
graded, module-linearly. The unchanged localization map now computes supported
derived Hom on every bounded-below flasque complex and is natural in every
additive cochain map. Its scalar compatibility identifies the actual total
module with the original supported-section complex homology, hence with
source supported cohomology restricted along the prescribed global ring map.
The finite exhaustive filtration is transported to that original source
module, retaining its smaller universe. The original E₂ comparison is now
module-linear as well: its canonical page, first-page, truncation/shift and
supported-cohomology factors all intertwine the original global scalar maps.
The linear equivalence has exactly the preexisting additive comparison.
Actual coefficient maps now give a genuine functor to module spectral sequences.
Resolution homotopies prove lift-independence and the identity/composition laws;
canonical changes of resolution are natural and satisfy the cocycle identity.
The unchanged module-linear E₂ and abutment comparisons retain the original
higher-direct-image and source supported-cohomology coefficient maps. These
source maps preserve the actual finite filtration, which is independent of
resolution, and the stable-page isomorphisms retain the genuine associated-graded
maps. Cohen's presentation theorem remains open; it is not assumed in the
proved algebraic results.

## SGA 2, Exposé VI — Ext with support

Entry point: `lean/SGA/SGA2/ExposeVI.lean`.

The affine degree-zero algebra in the proof of VI.2.3 is now formalized in
`ExposeVI/AffineHomColimit.lean`.
`adicQuotientHomTorsionIsColimit` and
`adicQuotientHomColimitIsoPowerTorsion` identify the actual categorical colimit
of `Hom_R(M/IⁿM,N)` with the ideal-power torsion submodule of the original
`Hom_R(M,N)`. The comparison is the original quotient-precomposition map at
every stage, as proved by `adicQuotientHomColimitIsoPowerTorsion_ι` and
`adicQuotientHomTorsionCocone_apply`. It holds for arbitrary modules over any
commutative ring, and reuses the previously proved quotient-annihilator
identifications and actual annihilator colimits from Exposé IV.

`ModuleInternalHom.lean` constructs the actual sheaf of local module-linear
maps on arbitrary ringed spaces. It is the local-linear subpresheaf of the
additive internal Hom; its sheaf condition is proved by checking scalar
linearity on a covering sieve. `moduleLocalHomOverEquiv` identifies sections
with actual module-presheaf morphisms on the slice category. This proves left
exactness of `moduleSheafHomAbFunctor`; its maps are original postcomposition,
and original precomposition is constructed as well. Global sections are
the original module-sheaf Hom through `moduleSheafHomAbGlobalEquiv`.

For closed support, `moduleGammaZSheafFunctor` retains the actual supported
section submodules and is left exact. Its underlying additive sheaf agrees
naturally with the original kernel functor. `moduleSupportedHomFunctorIso`
proves VI.1.4.3 using the actual factorization and inclusion maps, with
contravariant naturality given by `moduleSupportedHomEquiv_precomp`.
`moduleSupportedInternalHomFunctorIso` gives the sheaf version, compatible
with all open restrictions.

`ModuleSupportedExt.lean` right-derives these genuine local-linear Hom functors
in the category of module sheaves. It constructs supported Ext groups and
underlying additive sheaves for closed and arbitrary locally closed support,
with natural degree-zero comparisons and positive-degree vanishing on
injective module sheaves. `moduleSupportedExtViaSupportedSheafIso` derives
the closed supported-Hom identity; it is a comparison of derived composites,
not the spectral sequence of VI.1.6.3.

VI.1.5's flasqueness and acyclicity inputs are proved in
`ModuleOpenSubpresheaf.lean` and `ModuleHomInjectiveFlasque.lean`.
The source module's open subpresheaf embeds into it, so injectivity extends
every local linear map globally. Applied to the underlying module presheaf
of an injective module sheaf, this proves that the genuine local-linear Hom
sheaf is flasque and has zero positive closed or locally closed supported
cohomology. No injectivity of its underlying additive sheaf is assumed.

This is not the full supported sheaf-Ext comparison of VI.2.3. The internal Hom
and derived sheaves still need their structure-ring module actions. VI.1.2's
comparison with Ext derived after restriction to each open, excision,
VI.1.4's locally closed and tensor/support-object comparisons, the three
spectral sequences, support exact sequences, quasi-coherence, and the
higher-degree/sheaf comparisons remain open.
Exposés VII–XIV still have no Lean formalization.

## Axiom verification

Run `lake env lean CheckSGA2Axioms.lean` from `lean/`. The check traverses
every imported declaration in `SGA.SGA2` and its transitive axiom
dependencies. It permits only `propext`, `Classical.choice`, and `Quot.sound`;
additional mathematical axioms, `sorryAx`, and native evaluation axioms
cause failure. This verifies the axiom requirement for the imported library,
not completeness of the source coverage.

## Next geometric dependencies

`InjectiveFlasque.lean` proves that injective abelian sheaves are flasque
using sheafification, free abelian groups, and Yoneda. `FlasqueCohomology.lean`
combines this with mathlib's section-exactness and quotient-flasqueness
theorems to prove ordinary flasque acyclicity for actual Ext-defined
cohomology. `ClosedSupportHom.lean` and `SupportedCohomologyComparison.lean`
now prove the genuine closed-support Hom representation, the natural
comparison of derived supported sections with Ext, and supported flasque acyclicity.
`AffineCohomologyVanishing.lean` now proves ordinary affine vanishing over
noetherian rings, using exactness of the actual associated-sheaf functor.
`AffineCohomologyComparison.lean` proves the higher supported affine comparison,
using exactness of the associated-sheaf functor and supported acyclicity of
associated sheaves of injective modules. Affine/local-stalk compatibility is
now proved, as are the full coherent-module Hartogs equivalence and the actual
connected-components bijection on general locally noetherian schemes.
The all-degree coherent-module depth criterion for original supported-sheaf
vanishing and actual higher ordinary restriction is now proved. The remaining
module-valued internal sheaf Ext criteria need further comparisons. Closed and locally closed supported sheaves have natural
sheafification and flasque acyclicity, and the closed-support model comparison
is proved, alongside the actual closed-support sheaf Ext and open higher-direct-image
comparisons. The canonical closed-support spectral sequence, E₂ identification,
and finite convergence filtration are constructed. Its spectral-object maps,
total and E₂ comparisons, and all-page/next-page coefficient compatibility are
proved. The actual coefficient functor is independent of resolution lifts,
with coherent natural resolution-change isomorphisms. The original convergence
filtration and stable-page/graded-piece comparison are natural, and the
transported filtration on `H_Z` is resolution-independent. The general locally
closed spectral sequence now has the same ambient construction and natural
convergence on original support Ext. The remaining general-scheme criteria and
later exposés are incomplete. Exposé IV now includes the actual supported colimit
representation and categorical equivalence, the full bounded-below delta-functor
vanishing theorem, the original functor's exactness/injectivity criterion,
IV.3.1's full four-condition equivalence and IV.3.2 under its standing hypothesis.
