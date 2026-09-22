# Lean 4 library

Lake project on mathlib. Toolchain: [`lean-toolchain`](lean-toolchain)
(same Lean as mathlib `v4.34.0-rc2`).

```bash
lake exe cache get    # first time: download mathlib oleans
lake build
```

Root modules: `SGA.SGA1.ExposeI`, `SGA.SGA1.ExposeVI`, `SGA.SGA2.ExposeI`,
`SGA.SGA2.ExposeII`, `SGA.SGA2.ExposeIII`, `SGA.SGA2.ExposeIV`, `SGA.SGA2.ExposeV`,
`SGA.SGA2.ExposeVI`, and `SGA.SGA2.ExposeVII`. Lemmas live in the matching
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
Koszul vanishing III.3.12 are proved. III.3.7's finite component chains,
III.3.8's full locally noetherian antifilter equivalence, and III.3.9's
equidimensionality from depth and the prime-chain condition are proved.
III.3.13 has the
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
Exposé V proves canonical local duality in every complementary degree for
finite modules over regular local rings. Its Hom complexes include the
signed comparisons with Yoneda products and boundaries, injective
horseshoes, and coherent changes of resolution. The structure results cover
upper vanishing, Artinianity, completed-dual finiteness and dimension bounds,
top nonvanishing and associated primes over noetherian local rings. It also
constructs the module-valued ringed-space spectral sequence for closed
supports, with natural E₂ and abutment comparisons and a finite,
resolution-independent convergence filtration. The component criterion,
affine-complement codimension bound, and finite-length/depth criteria over
quotients of regular local rings are proved. Cohen's presentation theorem
remains unformalized; the general local-ring results use direct proofs.
See [`SGA/SGA2/ExposeV.lean`](SGA/SGA2/ExposeV.lean) for the module map and
sign conventions, and the formalization notes for theorem names and scope.
Exposé VI has actual local Ext evaluation and sheafification, all-degree
locally closed excision, the structure-module and tensor Hom representations,
and genuine supported Ext long exact sequences natural in both arguments.
VI.1.6.1–3 have actual spectral functors, original E₂ and Ext abutment
comparisons and finite convergence for locally closed support, including
coefficient naturality of VI.1.6.3. VI.1.7 has the actual module
support-object sequence and its tensor version. The ordinary Ext endpoints
of VI.1.9, and the standard restriction map in every degree, are identified.
Degree-zero closed-supported Hom and sheaf Ext⁰ are quasi-coherent for
coherent source and quasi-coherent coefficients on locally noetherian
schemes. Several higher-map compatibility statements, higher supported
sheaf Ext quasi-coherence, and general VI.2.3 remain open. VI.2.3 includes
the affine degree-zero quotient-Hom colimit and structure-sheaf
local-cohomology comparison.
Exposé VII proves internal-Hom zero detection on locally noetherian schemes,
with literal stalk supports, a coherent source and an arbitrary quasi-coherent
target. Its remaining vanishing and coherence theorems are open.
Exposés VIII–XIV have no Lean formalization.
See the formalization notes for precise coverage and gaps.

`lake env lean CheckSGA2Axioms.lean` checks every imported `SGA.SGA2`
declaration and its transitive dependencies. Only `propext`, `Classical.choice`,
and `Quot.sound` are allowed; placeholders and additional axioms fail the check.

See [`../docs/formalization.md`](../docs/formalization.md).
