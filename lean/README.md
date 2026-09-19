# Lean 4 library

Lake project on mathlib. Toolchain: [`lean-toolchain`](lean-toolchain)
(same Lean as mathlib `v4.34.0-rc2`).

```bash
lake exe cache get    # first time: download mathlib oleans
lake build
```

Root modules: `SGA.SGA1.ExposeI`, `SGA.SGA1.ExposeVI`, `SGA.SGA2.ExposeI`,
`SGA.SGA2.ExposeII`, `SGA.SGA2.ExposeIII`, `SGA.SGA2.ExposeIV`, `SGA.SGA2.ExposeV`,
and `SGA.SGA2.ExposeVI`. Lemmas live in the matching
exposé directories and are imported from the barrel modules. SGA 2 has partial Exposé I
foundations, actual open extension by zero, the natural derived-supported-section
comparison with Ext, and ordinary and closed-supported flasque acyclicity,
affine supported-section and degree-zero comparisons in
II.(7.3)–(7.5), the canonical noetherian Ext-to-Koszul isomorphism II.8,
II.9 for the family of all degrees, and the full finite-generator statement
of II.11. Associated sheaves of injective modules are proved flasque over
noetherian rings, and ordinary higher cohomology of all associated module
sheaves vanishes on noetherian affine schemes. Exposé III includes associated
primes, the Ext definition of depth, regular-sequence criteria, quotient and localization formulae,
flat base change, and the depth/local-cohomology criterion. The actual
noetherian affine comparison is proved in all degrees, compatibly with
coefficient boundaries, linking depth to actual supported sheaf cohomology.
Original derived closed and locally closed supported sheaves now have natural
sheafification and flasque acyclicity, independently of the chosen witness.
Genuine internal Hom and sheaf Ext identify with original closed and arbitrary
locally closed ambient supported sheaves; original open-supported derived
sheaves are higher direct images.
The arbitrary-coefficient extension-by-zero sequence uses the original open
counit and closed unit and is functorial; for locally closed supports its
endpoints are actual single-witness extensions, with original arrow and
coefficient-map compatibility. Full arbitrary nested locally closed composition
is proved, including actual support-space and adjunction-map comparisons.
A canonical closed-support local-to-global spectral sequence has actual pages, differentials,
the E₂ cohomology identification, first-quadrant vanishing, and a finite
convergence filtration on total groups identified with original `H_Z`.
Spectral-object, total, E₂, and all-page/next-page coefficient compatibility
are proved. The actual coefficient functor is independent of resolution lifts,
with coherent natural resolution-change isomorphisms. The original convergence
filtration and stable-page/graded-piece comparison are natural, and the transported
filtration on `H_Z` is resolution-independent. The general locally closed spectral
sequence now has the same construction, naturality, and convergence on the
original ambient space, with the original support Ext abutment. The constructed sequence is identified with the Grothendieck/Leray
sequence of the supported-sheaf functor; spectral-level witness change is
proved.
Derived supported sheaves commute with
actual open restriction and vanish off a closed support and, in positive degrees,
on its interior; their literal stalk support lies in the boundary in positive degrees,
and their ordinary cohomology can be computed on the closed subspace.
For locally closed supports, the original derived sheaves have literal stalk
support in the closure, and in the locally closed set's boundary in positive
degrees. Their higher cohomology is naturally computed on that closure using
ordinary closed pullback.
The actual integer-support short exact sequence, original section and supported-sheaf
sequences, and group- and sheaf-valued long exact sequences cover every locally
closed support and every closed subset of it. Flasque surjectivity, actual
connecting maps, and coefficient naturality are proved.
Affine stalk depth is identified with literal stalk depth. Affine Hartogs and
the actual affine connected-components bijection are proved, as are structure-sheaf
Hartogs and the full connected-components bijection on every locally noetherian
scheme. The full Hartogs equivalence also holds for actual coherent module
sheaves, expressed using mathlib's local finite-presentation condition:
literal stalk depth at least two along the support is equivalent to bijective
restriction on every open. The affine finite coefficient presentations and
semilinear stalk comparisons needed for this are proved. In every nonnegative
degree, literal coherent-module stalk depth now characterizes original derived
supported-sheaf vanishing and local supported-cohomology vanishing. The higher
ordinary restriction criterion is proved with the actual ambient-intersection
map. At every threshold at least two, final injectivity is redundant for
arbitrary abelian sheaves, by actual complement-adapted injective effacement
and coefficient dimension shifting. Affine module Ext criteria III.3.3(v)/(vi), connectedness of complements
III.3.7, the antifilter of closed sets, the depth obstruction III.3.10, and
Koszul vanishing III.3.12 are proved. Equidimensionality III.3.9 and the
full III.3.8 component-chain equivalence remain open; III.3.13 has the
principal-curve vanishing and the non-UFD obstruction.
Exposé IV now proves IV.1.1 for the original additive abelian-group-valued
functor, including its canonical scalar action and evaluation map, and the
equivalence between arbitrary modules and left-exact functors on finite modules.
IV.1.3 is proved with the actual colimit of `T(R/Jⁿ)` and the specified canonical
evaluation, together with the supported-module categorical equivalence. IV.1.4's
three-way vanishing theorem holds for arbitrary integer-indexed bounded-below
exact delta functors. IV.2.1 characterizes exactness of the original functor by
injectivity of its actual colimit; IV.2.2 is also proved. IV.1.2 proves canonical
representation on all modules exactly for functors preserving arbitrary
preorder-indexed limits, without filteredness. IV.3.1's full four-condition
equivalence is proved for the original additive functor, with the actual
canonical map into actual `T(T(M))` and its naturality. IV.3.2 derives exactness
and finite values from length preservation under §3's standing left-exactness
hypothesis. The opening of §5 proves the original functor's anti-equivalence,
the actual orthogonal submodule bijection, both length/colength identities,
the Artinian-local ideal-annihilator correspondence, and the equivalence of
actual single generation with the original dual's socle having length at most
one over a local ring. IV.4.3–4.4 prove actual finite coinduction and
quotient-annihilator duality. IV.4.5 proves the actual map `M → M ⊗ Â` is
invertible for arbitrary locally Artinian modules, with genuine tensor/restriction
equivalences of the supported and locally Artinian categories. IV.4.2 constructs
an exact linear duality on the whole finite-length category, with canonical
bidual evaluation and a proved locally Artinian coefficient. IV.4.7 constructs genuine
injective envelopes and proves existence, characterization, and uniqueness of
dualizing modules under the explicit supported-module convention; IV.4.9
proves local Artinianness. IV.5.2 proves the literal Macaulay field-Hom duality
and its actual quotient-dual colimit, canonically identified with the continuous
linear dual of the original adic ring without assuming completeness.
IV.4.6 transfers supported duality through
completion using actual Hom and canonical bidual-evaluation comparisons.
IV.5.1 is proved over arbitrary noetherian local bases with forward exactly
original-ring Hom, inverse completed-ring Hom through canonical scalar
comparisons, and both natural completion-transport squares. Finite biduals
are actual completions and locally Artinian finite-socle duals are complete
with finite-length power quotients. Genuine
regular local rings are proved to be domains with regular systems of parameters.
IV.5.3's global dimension now equals the actual Krull dimension. The bound
holds for all modules, and upper Ext vanishing allows both arguments to be
arbitrary. Support-dimension induction proves the finite-module step; Baer's
criterion and actual injective dimension shifting prove the unrestricted step.
Actual adic completions of noetherian rings are now proved noetherian for
arbitrary ideals. Scalar change and completed-ring Hom identify the original
finite-socle locally Artinian category oppositely with finite completed-ring modules.
IV.5.4 proves that original top Ext is dualizing and represented by actual
top local cohomology, with the original quotient transitions and colimit
stage maps respected. IV.5.5's initial noncanonical comparison with the
Macaulay module is proved. Actual coordinate-power quotients of finite-variable
power series rings have their monomial basis and a perfect product-residue
pairing. The finite residues now glue through the original transitions to
an explicit isomorphism from actual top local cohomology to the continuous
dual and Macaulay module. The glued coefficient-field linear residue has
the original monomial formula and a nondegenerate product pairing. Cohen
presentations and the intrinsic completed-differential clauses remain open.
The actual product-multiplication power-quotient diagram is also identified
with top local cohomology, compatibly with original stage maps.
Original nonlocal additive left-exact functors on finite-length modules are
represented by their actual cofinite-ideal colimits; Hom gives an equivalence
with locally Artinian modules over a noetherian ring. The actual coefficient
of any original linear involutive finite-length functor is locally Artinian
and injective, with length-one maximal-ideal annihilators. These claims do
not extend to arbitrary raw Hom targets with invisible summands. Later
structural and explicit residue-pairing results remain incomplete.
Exposé V now constructs the literal displayed Hom complex, with its actual
Leibniz and homotopy formulas and an explicit sign-normalizing chain
isomorphism. The actual sign-normalized augmentation of two given injective
resolutions is a quasi-isomorphism, and its homology map computes Ext; the
source's incompatible unsigned augmentation claim is not asserted.
The original graded composition descends to a biadditive cohomology pairing
and agrees with Yoneda composition under that same Ext comparison. Actual
unscaled source kernel and quotient data give the literal source pairing;
its normalization contributes exactly the proved factor `(-1)^(ij)`.
Actual mapping-cone lifts also identify the lifted-cocycle boundary with the
derived connecting morphism. On unchanged unsigned projective-resolution
representatives, Yoneda's boundary is `(-1)^(n+1)` times the lifted boundary's
`extMk` class, with original lifts proved to exist for every Ext class.
This is now an equality of the actual module-valued coefficient boundaries
in every degree, including zero via the existing Ext-to-Hom comparison.
The same sign comparison holds on the unchanged filtered Ext colimits and
ideal-power local-cohomology objects.
It also has the actual Yoneda pairing, its two original Ext boundary
identities, and the canonical natural local-duality map on original
local-cohomology objects. Regular-local cohomology vanishes above the actual
dimension for every module; ring coefficients are concentrated in that
dimension and nonzero there. The identity Ext class gives a retraction of
the equal-coefficient top-degree map. The canonical map is now a natural
isomorphism in top degree for every finite module over a regular local ring,
by the finite-presentation argument and proved right exactness of both
original functors. The canonical linear comparison transports exact Yoneda
sequences to the unchanged Ext objects and their local-cohomology colimits.
Stagewise boundary compatibility and descending induction now prove V.2.1
in every complementary degree, naturally on finite modules. The actual
contravariant Hom long exact sequences are now exact and natural into every
degreewise-injective target. For K-injective targets their original connecting
maps agree with the derived connecting arrow, with factor `(-1)^(n+1)` in
the standard convention and no extra sign for the literal source differential
under its fixed unscaled quotient equivalence. The covariant Hom sequence
now also has actual exactness and naturality on degreewise-injective coefficient
complexes, for arbitrary source. Its standard boundary is the derived connecting
arrow with K-injective endpoints; its literal-source boundary has the factor
`(-1)^(n+1)`. The original pairing is natural in the middle complex and its
actual boundary identity has factor `(-1)^(j+1)` in the standard convention
and `(-1)^(i+1)` in the displayed source convention, proved by the explicit
composite of original lifts without boundedness or K-injectivity. An unsigned
source boundary-pairing identity is not asserted. For a supplied augmented
exact sequence of chosen injective resolutions, the original augmentation
squares now identify the connecting arrow with the original extension class.
Both existing double-resolution Ext equivalences carry the original Hom
boundaries to Yoneda boundaries, with factor `(-1)^(n+1)` contravariantly and
no factor covariantly, including degree zero. The same comparison holds for
the original module-valued Ext objects through the unchanged canonical linear
comparison, as additive-group identifications. The injective horseshoe now
constructs augmented exact resolution sequences from enough injectives,
using the snake lemma on actual categorical cokernels. The original maps
extend with strictly commuting augmentation squares, and the resulting
sequence is split in each integer degree. The unchanged horseshoe is now also
an injective resolution of the whole short complex, yielding simultaneous
comparison maps and homotopies that preserve both horizontal arrows. Actual
integer-indexed comparisons strictly preserve the augmentations and commute
with both original Hom boundaries. Identity, composition, and lift independence
hold in the homotopy category; arbitrary injective row-resolution changes are
natural and satisfy the cocycle law. Arbitrary separately specified resolution
sequences now also give simultaneous row resolutions, retaining their original
maps, exactness, and augmentations. They admit actual augmented comparisons
with coherent homotopies and natural model changes satisfying the cocycle law.
The fixed Hom/Ext equivalences respect both precomposition and postcomposition,
and identity model changes preserve the original Ext value, including the
module-valued comparison. Both original Hom boundaries are natural for these
arbitrary-model maps. These results are not assumed in the invertibility proof.
The transpose identifies dual local cohomology with
completed complementary Ext, carrying the canonical transpose to the original
completion map; over a complete regular base this proves V, formula (22), naturally.
All local-cohomology values of finite modules over noetherian local rings are
Artinian, with finite socle and finite-length power annihilators. Their actual
duals satisfy the original complete-category conditions and are finite over a
complete base; their original completions are finite over the actual completed
ring even without completeness of the base. Finiteness of original residue Ext
is preserved through actual injective envelopes and their cokernels; the genuine
coefficient exact sequence proves Artinianity, without Cohen reduction. The
original Matlis category is now proved to consist exactly of Artinian modules
over every noetherian local base. V.3.1(i)'s module-dimension upper vanishing is proved over arbitrary
noetherian local rings: actual parameters modulo the annihilator and the original
consecutive-power Koszul transition give the sharp bound. The ring-dimension
bound also holds for arbitrary coefficient modules. V.3.1(ii)'s completed-dual
dimension bound now holds over arbitrary noetherian local bases: removing actual
torsion preserves positive local cohomology, and the genuine dual regular-element
sequence remains exact under original completion maps, allowing induction on
degree over the completed ring. Over complete noetherian local rings, the
original top dual now has exactly the coefficient support dimension, and
original top local cohomology is nonzero. Simultaneous regular elements and
the genuine dual coefficient sequence give the induction; the zero-dimensional
base holds without completeness. Top nonvanishing now also holds over every
noncomplete noetherian local base: original-ring parameters avoid contracted
associated primes of the preceding completed dual, and the actual completed
dual sequence gives exact top-dual dimension over the completed ring.
The associated-prime formula in V.3.1(iii) is now proved for the original
top dual, even without completeness of the base. V.3.3's criterion for actual
irreducible component families is proved using the original cyclic tests and IV's actual
representing colimit. Right exactness, top nonvanishing, and prime chains
identify the components detected by the actual top dual. The canonical
module-lift comparison preserves its original scalar action, so III.1.3
gives the formula for the unchanged dual, not just an additive replacement.
V.3.4 is now proved for every original irreducible component of any closed
subset with affine complement in a noetherian affine spectrum. Genuine affine
vanishing and the original relative sequence give local-cohomology vanishing
above one. The actual complement localizes to the punctured spectrum at a
component generic point; top nonvanishing bounds that local dimension by one.
The conclusion uses the literal infimum of original structure-stalk dimensions
as codimension, without a principal-support hypothesis.
V.3.5 is proved for finite modules over quotients of regular local rings. Original
Hom duality detects finite length without completeness, and regular-local
local cohomology has the same extended length as complementary Ext.
Degreewise finite projective resolutions give a localized-ring-linear
comparison between localized original Ext and actual Ext over the localized
ring. Finite length of local cohomology is therefore equivalent to vanishing
of complementary Ext over every nonclosed prime localization. The quotient
reduction now preserves both actual conditions, including localized coefficient
modules, point-closure dimensions, and vanishing outside the quotient's image.
Shifted vanishing through a threshold is equivalent to the actual punctured
depth bound, proving V.3.6 under the same source hypotheses. Negative shifted
degrees impose no condition, and zero localized modules retain infinite depth.
The dimension formula `dim R_p + dim(R/p) = dim R` is proved: the top-dual
associated-prime formula forces complementary Ext to be nonzero at `p`, and
localized residue Ext identifies the degree with the local ring dimension.
The homological localization input is proved: actual localizations of `R/p`
are the actual residue fields of `R_p`, preserving original element maps.
All modules over these local rings have projective dimension bounded by the
original regular ring's dimension. The homological regularity criterion is
now proved by induction through actual regular principal quotients. Therefore
every prime localization is regular, and its global dimension equals its
own Krull dimension. No additional local criterion is assumed in V.3.5 or V.3.6.
The algebraic change-of-rings comparisons in V, formulas (19)--(21), are now
proved. Actual Koszul systems commute with tensor extension, including their
power transitions, without flatness. Hom adjunction and exact scalar restriction
give the original local-cohomology comparison for every ideal and coefficient
module over noetherian rings. Surjective local-ring maps preserve maximal-ideal
local cohomology and its extended length. The Hom-dual comparison is natural
in arbitrary modules after one choice of coefficient isomorphism. Actual
annihilator quotients, finite generation, and support dimension are preserved.
For V.3.2, supported sections and their right-derived functors now retain the
actual structure-ring module action on general ringed spaces. Injective module
sheaves are flasque; direct images of injectives are supported-acyclic without
flatness. The right-derived supported-section/direct-image composite is naturally
the source's supported cohomology restricted along the actual global ring map.
Flasque mapping cones now compare module-injective and additive-injective
resolutions: in every degree the underlying additive group is the original
additive-sheaf supported cohomology. This comparison is now natural in the
original coefficient maps, by augmentation-compatible chain homotopies.
Global scalar actions are retained on the underlying complexes and derived
objects. The actual direct-image truncations now give a genuine additive
spectral sequence, with E₂ identified as original supported cohomology of
the original higher module direct images. The retained global action now
lifts the actual spectral object and its exactness to modules. The resulting
module spectral sequence canonically forgets to the entire original additive
sequence, preserving every differential and original next-page isomorphism.
First-quadrant bounds and a finite exhaustive submodule filtration of its
canonical total object are proved; every page with `r ≥ n + 2` in total
degree `n` is module-linearly its genuine associated graded. This total module
now identifies module-linearly with original source supported cohomology
restricted along the prescribed global ring map, and the finite exhaustive
filtration is transported to that original source module. The comparison
uses bounded-below flasque complexes and is natural in all additive cochain
maps, including the original scalar actions. The unchanged E₂ comparison is now
module-linear too: each original page, truncation/shift and supported-cohomology
factor retains the scalar action, and the resulting linear equivalence is
proved to have exactly the original additive comparison. The actual module
spectral sequence is now a coefficient functor: resolution homotopies prove
lift-independence, the functor laws, and canonical natural resolution changes.
The original E₂, source-cohomology abutment and stable-page comparisons commute
with the actual coefficient maps. The original source finite filtration is
preserved by these maps and is independent of resolution. The source's Cohen
presentation remains open and is not assumed in the proved algebraic results.
Exposé VI proves VI.1.2 sheafification of local module Ext, VI.1.3 excision
of the Hom sheaf, VI.1.4.1/VI.1.4.3 Hom representations, VI.1.5 flasque
acyclicity, VI.1.8–VI.1.9 nested-support sequences of Hom, and VI.2.3's
affine degree-zero and structure-sheaf Ext-colimit comparisons. The three
spectral functors of VI.1.6, the tensor form VI.1.4.2, and general
VI.2.3 remain open.
Exposés VII–XIV have no Lean formalization.
See the formalization notes for precise coverage and gaps.

`lake env lean CheckSGA2Axioms.lean` checks every imported `SGA.SGA2`
declaration and its transitive dependencies. Only `propext`, `Classical.choice`,
and `Quot.sound` are allowed; placeholders and additional axioms fail the check.

See [`../docs/formalization.md`](../docs/formalization.md).
