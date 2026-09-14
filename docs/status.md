# Status

Translation of an exposé comes **before** Lean for that exposé.
Tick a box in the same PR that lands the work.

Convention: `[x]` is in the tree; `[ ]` is not. A translation counts as
ticked when TeX + PDF are in `translation/SGA…/` and `make` builds.
A Lean item counts as ticked when the statement lives under `lean/SGA/`
with no `sorry`, is imported from `lean/SGA.lean`, and `lake build` passes.

## Order of work

1. Keep the landed SGA 1 and SGA 2 translations compiling (`make tex`).
2. Formalize SGA 1 VI against mathlib, section by section, starting
   from `lean/SGA/SGA1/ExposeVI.lean`.
3. Translate further exposés of SGA 1 (IV–V, VIII–XIII), then formalize
   each after its English text is in the tree.
4. SGA 2 English drafts proceed in parallel with remaining SGA 1
   exposés; Lean for SGA 2 has partial Exposé I foundations, Exposé II
   module and affine-sheaf arguments, Exposé III's associated-prime,
   depth and Hartogs theory, Exposé IV–VI foundations, Exposé VII complete (affine/algebraic avatars), and compiling scaffolds for Exposés VIII–XIV (see below).
   Formalization follows the English text.

Related public translations (not this project):
[thosgood/sga](https://github.com/thosgood/sga),
[ryankeleti/sga](https://github.com/ryankeleti/sga).

---

## SGA 1 — *Revêtements étales et groupe fondamental*

Source: SMF recomposition, [arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203).
Exposé VII does not exist.

| Exposé | Title | Translation | Lean |
| --- | --- | --- | --- |
| I | Étale morphisms | full draft in tree | compiling |
| II | Smooth morphisms: generalities, differential properties | full draft in tree | — |
| III | Smooth morphisms: extension properties | full draft in tree | — |
| IV | Flat morphisms | — | — |
| V | The fundamental group: generalities | — | — |
| **VI** | **Fibered categories and descent** | **draft in tree** | **compiling** |
| VII | *(does not exist)* | | |
| VIII | Faithfully flat descent | — | — |
| IX | Descent of étale morphisms; application to the fundamental group | — | — |
| X | Specialization of the fundamental group | — | — |
| XI | Examples and complements | — | — |
| XII | Algebraic geometry and analytic geometry | — | — |
| XIII | Cohomological properness (sets and non-commutative groups) | — | — |

### Translation

- [x] **I** — Étale morphisms
  - [x] Opening convention and §§1–6: English TeX and PDF in `translation/SGA1/ExposeI/`
  - [x] §§7–11: English TeX and PDF, including all proofs and footnotes
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeI/README.md`](../translation/SGA1/ExposeI/README.md)
- [x] **II** — Smooth morphisms: generalities, differential properties
  - [x] Opening convention and §§1–5, including errata: English TeX and PDF in `translation/SGA1/ExposeII/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeII/README.md`](../translation/SGA1/ExposeII/README.md)
- [x] **III** — Smooth morphisms: extension properties
  - [x] English TeX in `translation/SGA1/ExposeIII/`
  - [x] PDF in tree (`make tex`)
  - [ ] Scholarly proofreading against the SMF source
- [ ] **IV** — Flat morphisms
- [ ] **V** — The fundamental group: generalities
- [x] **VI** — Fibered categories and descent
  - [x] English TeX in `translation/SGA1/ExposeVI/`
  - [x] PDF in tree (`make tex`)
  - [ ] Proofread against the SMF source (labels, diagrams, numbering)
- [ ] **VIII** — Faithfully flat descent
- [ ] **IX** — Descent of étale morphisms. Application to the fundamental group
- [ ] **X** — Specialization of the fundamental group
- [ ] **XI** — Examples and complements
- [ ] **XII** — Algebraic geometry and analytic geometry
- [ ] **XIII** — Cohomological properness of sheaves of sets and of sheaves of non-commutative groups

### Formalization (Lean 4)

Mathlib already has much of the language of Exposé VI. Import it; do not
copy it. Details: [`formalization.md`](formalization.md).

Scaffold:

- [x] Lake project + mathlib pin (`lean/lean-toolchain`, `lean/lakefile.toml`)
- [x] Root module `SGA.SGA1.ExposeI` imports mathlib étale / unramified / quasi-finite
- [x] Root module `SGA.SGA1.ExposeVI` imports mathlib fibered categories / descent
- [x] `lake build` stays green as files are added

By section (English: `translation/SGA1/ExposeVI/`, Lean: `lean/SGA/SGA1/`):

- [x] **VI.0** Introduction (no mathematics to formalize)
- [x] **VI.1** Universes, categories, equivalence of categories (`Equivalences.lean`)
- [x] **VI.2** Categories over another (`OverCategories.lean`)
- [x] **VI.3** Change of base in categories over *E* (`BaseChange.lean`)
- [x] **VI.4** Fiber-categories; equivalence of categories over *E* (`Fibers.lean`, `BasedEquivalences.lean`)
- [x] **VI.5** Cartesian morphisms, inverse images, cartesian functors (`Cartesian.lean`, `CartesianFunctors.lean`)
- [x] **VI.6** Fibered categories (`Fibered.lean`, `FiberedProducts.lean`, `CartesianFiberProducts.lean`, `PairFiberProducts.lean`, `ChangeOfBaseFibered.lean`: VI.6.10 fiberwise faithfulness; VI.6.11–13)
  - [x] VI.6.1 Fib I / Fib II (`IsPreFibered`, `IsFibered` — mathlib; numbering in `Fibered.lean`)
  - [x] Fibered in groupoids (remark after VI.6.1, with prefiberedness; `Groupoids.lean`)
  - [x] VI.6.2 based equivalence preserves (pre)fiberedness (`FiberedProducts.lean`)
  - [x] VI.6.3–6.5 fiber-product cartesian / (pre)fibered criteria (`PairFiberProducts.lean`)
  - [x] VI.6.6 full cartesian iff after change of base (`ChangeOfBaseFibered.lean`)
  - [x] VI.6.7 change-of-base preserves cartesian functors (`changeOfBaseCartesianFunctors`)
  - [x] VI.6.8 cartesian-lift functors → cartesian sections (one direction; see formalization.md)
  - [x] VI.6.9 change of base preserves `(pre)fibered` (`instIsPreFibered` / `instIsFibered`)
  - [x] VI.6.11–13 (`Fibered.lean`)
- [x] **VI.7** Cloven categories (`Cleavage.lean` + `CleavageExtras.lean`: VI.7.1–7.4 including `pullbackEquiv_of_isIso`, comparison iff, normalized cleavage, assoc)
- [x] **VI.8** Cloven category defined by a pseudofunctor (`Split.lean`, mathlib `∫ᶜ`)
- [x] **VI.9** Example: cloven category defined by a functor (`SplitFibered`)
- [x] **VI.10** Cofibered/bifibered (`Cofibered.lean` + `CofiberedExtras.lean`: VI.10.1 `isFibered_iff_isCofibered`)
- [x] **VI.11** Examples (`BaseExamples.lean` discrete; `ExamplesVI11.lean` arrow target/source, VI.11(f) prefibered-from-`arr`-lifts, constant product split; `Examples.lean` finite checks)
- [x] **VI.12** Functors on a cloven category (`ClovenFunctors.lean` + `ClovenFunctorsIso.lean`: `FiberFunctorData`, Hom injectivity for VI.12.1)

Gaps still open inside those files are listed in [`formalization.md`](formalization.md).

### SGA 1 I — Étale morphisms

English: `translation/SGA1/ExposeI/`. Lean: `lean/SGA/SGA1/ExposeI.lean`.
Section files compile and have no `sorry`. That is **not** a complete
formalization of every numbered statement; remaining items are unchecked
below and in [`formalization.md`](formalization.md).

- [x] **I.1** Differential calculus (`Differentials.lean`: `Ω[S⁄R]`, principal parts)
- [x] **I.2** Quasi-finite morphisms (`QuasiFinite.lean`: isolated in the fibre; artinian I.2.2)
  - [x] I.2.1(iii): `finite_adicCompletion_of_moduleFinite`,
    `isQuasiFiniteLocal_iff_finite_adicCompletion` (module-finite / artinian)
- [x] **I.3** Unramified / net morphisms (`Unramified.lean`: TFAE, graph, stability)
  - [x] I.3.7: `algebraMap_surjective_of_formallyUnramified`,
    `adicCompletion_surjective_of_formallyUnramified`
- [x] **I.4** Étale morphisms and coverings (`Etale.lean`: flat + unramified; stability)
  - [x] I.4.4: `algebraMap_surjective_of_etale`, `adicCompletion_surjective_of_etale`,
    `adicCompletion_bijective_of_bijective_algebraMap`
  - [x] I.4.10 (field case): `etale_iff_isSeparable_of_field`,
    `discr_isUnit_of_etale_field`, `etale_of_isSeparable_field`
- [x] **I.5** Fundamental property (`Fundamental.lean`: I.5.1 étale + radicial = open immersion)
  - [x] I.5.3: `isOpenImmersion_and_isClosedImmersion_of_section`,
    `isClopen_range_of_section`
  - [x] I.5.4 / uniqueness: `eq_of_comp_eq_of_formallyUnramified` (via I.5.5 uniqueness)
  - [ ] I.5.5 existence of the lifted *scheme* (uniqueness proved; gluing / formal schemes absent from mathlib)
  - [ ] I.5.7–I.5.9 fibrewise criteria
- [x] **I.6** Complete local rings (`CompleteLocal.lean`: artinian + complete-local I.6.2)
  - [x] I.6.1 artinian form: `finiteEtale_hom_equiv_residue_artinian`,
    `exists_liftResidue`; sep-closed fibre equivalence already present
  - [x] I.6.1 complete-local maps (adic-complete targets):
    `hom_equiv_residue_of_isAdicComplete`,
    `finiteEtale_hom_equiv_residue_complete`
  - [ ] I.6.1 object-level Hensel essential surjectivity (standard-étale assembly)
- [x] **I.7** Standard étale presentations (`StandardEtale.lean`: I.7.4, I.7.6–I.7.8)
  - [ ] I.7.1–I.7.3, I.7.5, I.7.9–I.7.10
- [x] **I.8** Infinitesimal lifting (`Infinitesimal.lean`: uniqueness half of I.8.3)
  - [x] I.8.3 uniqueness / I.8.4 affine artinian + complete-local:
    `etale_reduction_fullyFaithful_hom`, `etale_covering_residue_equiv`
  - [ ] I.8.3 essential surjectivity (scheme lift); formal schemes absent from mathlib
  - [x] I.8.4 affine complete-local form: `etale_covering_residue_equiv_complete`
- [x] **I.9** Permanence (`Permanence.lean`: reducedness over a field; integral closure)
  - [x] I.9.1 cotangent / maximal-ideal criteria:
    `isRegularLocalRing_iff_finrank_cotangent`, `map_maximalIdeal_of_etale`
  - [x] I.9.5(ii) / I.9.11 packages:
    `IsUnramifiedInjectiveNormalLocal`,
    `formallyUnramified_fractionRing_tensor`,
    `formallyEtale_of_formallyUnramified_of_field`
  - [x] I.9.1 spanFinrank inequality + conditional regularity transfer
    (`spanFinrank_maximalIdeal_le_of_etale`,
    `isRegularLocalRing_of_etale_of_finrank_eq_dim`)
  - [ ] I.9.1 unconditional `IsRegularLocalRing` transfer (needs dim/cotangent equalities)
  - [ ] I.9.2–I.9.4 reduced in general; I.9.5 normality iff (Serre); I.9.10–I.9.12
- [x] **I.10** Coverings of a normal scheme (`NormalCoverings.lean`: ZMT input, finite fibres)
  - [x] I.10.3 / I.10.5 affine: `finiteEtale_toIntegralClosure_bijective`
  - [x] I.10.7–I.10.11: `isLocallyConstant_finrank`, `isIso_iff_finrank_eq_one`,
    `isLocallyConstant_finrank_of_etale_covering`, `one_le_finrank_iff_surjective`
- [x] **I.11** Geometrically unibranch (`Unibranch.lean`: definition)
  - [x] I.11 / IX.4.10 affine descent:
    `FailsGeometricallyUnibranch`,
    `etale_of_etale_tensorProduct_of_faithfullyFlat`,
    `unramified_of_unramified_tensorProduct_of_faithfullyFlat`

Other exposés of SGA 1: start only after the corresponding English text
is ticked above. Exposé II now has English in the tree; Lean for II
has not been started.

---

## SGA 2 — *Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz locaux et globaux*

Source: SMF recomposition, [arXiv:math/0511279](https://arxiv.org/abs/math/0511279).
GitHub checklist: [issue #9](https://github.com/Dharmavati213/SlopdeGeometrieAlgebrique/issues/9).
Exposé XIV is by Michèle Raynaud.

| Exposé | Title | Translation | Lean |
| --- | --- | --- | --- |
| Intro | Grothendieck’s introduction | full draft in tree | — |
| I | Global and local cohomological invariants relative to a closed subspace | full draft in tree | partial, compiling |
| II | Application to quasi-coherent sheaves on preschemes | full draft in tree | partial, compiling |
| III | Cohomological invariants and depth | full draft in tree | partial, compiling |
| IV | Dualizing modules and functors | full draft in tree | partial, compiling |
| V | Local duality and structure of the $H^i(M)$ | full draft in tree | — |
| VI | The functors $\mathrm{Ext}_Z^\bullet(X;F,G)$ and $\underline{\mathrm{Ext}}_Z^\bullet(F,G)$ | full draft in tree | — |
| VII | Vanishing criteria; coherence of $\underline{\mathrm{Ext}}^i_Y(F,G)$ | full draft in tree | — |
| VIII | The finiteness theorem | full draft in tree | — |
| IX | Algebraic geometry and formal geometry | full draft in tree | — |
| X | Application to the fundamental group | full draft in tree | — |
| XI | Application to the Picard group | full draft in tree | — |
| XII | Applications to projective algebraic schemes | full draft in tree | — |
| XIII | Problems and conjectures | full draft in tree | — |
| XIV | Depth and Lefschetz theorems in étale cohomology | full draft in tree | — |

### Translation

- [x] **Introduction** — Grothendieck’s introduction
  - [x] English TeX and PDF in `translation/SGA2/Introduction/`
  - [ ] Scholarly proofreading; source issues recorded in [`Introduction/README.md`](../translation/SGA2/Introduction/README.md)
- [x] **I** — Global and local cohomological invariants relative to a closed subspace
  - [x] English TeX and PDF in `translation/SGA2/ExposeI/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeI/README.md`](../translation/SGA2/ExposeI/README.md)
- [x] **II** — Application to quasi-coherent sheaves on preschemes
  - [x] English TeX and PDF in `translation/SGA2/ExposeII/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeII/README.md`](../translation/SGA2/ExposeII/README.md)
- [x] **III** — Cohomological invariants and depth
  - [x] English TeX and PDF in `translation/SGA2/ExposeIII/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeIII/README.md`](../translation/SGA2/ExposeIII/README.md)
- [x] **IV** — Dualizing modules and functors
  - [x] English TeX and PDF in `translation/SGA2/ExposeIV/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeIV/README.md`](../translation/SGA2/ExposeIV/README.md)
- [x] **V** — Local duality and structure of the $H^i(M)$
  - [x] English TeX and PDF in `translation/SGA2/ExposeV/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeV/README.md`](../translation/SGA2/ExposeV/README.md)
- [x] **VI** — The functors $\mathrm{Ext}_Z^\bullet(X;F,G)$ and $\underline{\mathrm{Ext}}_Z^\bullet(F,G)$
  - [x] English TeX and PDF in `translation/SGA2/ExposeVI/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeVI/README.md`](../translation/SGA2/ExposeVI/README.md)
- [x] **VII** — Vanishing criteria; coherence of $\underline{\mathrm{Ext}}^i_Y(F,G)$
  - [x] English TeX and PDF in `translation/SGA2/ExposeVII/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeVII/README.md`](../translation/SGA2/ExposeVII/README.md)
- [x] **VIII** — The finiteness theorem
  - [x] English TeX and PDF in `translation/SGA2/ExposeVIII/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeVIII/README.md`](../translation/SGA2/ExposeVIII/README.md)
- [x] **IX** — Algebraic geometry and formal geometry
  - [x] English TeX and PDF in `translation/SGA2/ExposeIX/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeIX/README.md`](../translation/SGA2/ExposeIX/README.md)
- [x] **X** — Application to the fundamental group
  - [x] English TeX and PDF in `translation/SGA2/ExposeX/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeX/README.md`](../translation/SGA2/ExposeX/README.md)
- [x] **XI** — Application to the Picard group
  - [x] English TeX and PDF in `translation/SGA2/ExposeXI/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeXI/README.md`](../translation/SGA2/ExposeXI/README.md)
- [x] **XII** — Applications to projective algebraic schemes
  - [x] English TeX and PDF in `translation/SGA2/ExposeXII/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeXII/README.md`](../translation/SGA2/ExposeXII/README.md)
- [x] **XIII** — Problems and conjectures
  - [x] English TeX and PDF in `translation/SGA2/ExposeXIII/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeXIII/README.md`](../translation/SGA2/ExposeXIII/README.md)
- [x] **XIV** — Depth and Lefschetz theorems in étale cohomology (M. Raynaud)
  - [x] English TeX and PDF in `translation/SGA2/ExposeXIV/`
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeXIV/README.md`](../translation/SGA2/ExposeXIV/README.md)

### Formalization (Lean 4)

Scaffold:

- [x] Root modules `SGA.SGA2.ExposeI`–`SGA.SGA2.ExposeXIV`
  imported from `lean/SGA.lean`
- [x] `lake build` stays green
- [x] `lake env lean CheckSGA2Axioms.lean` checks transitive axiom dependencies
  of all imported SGA 2 declarations

Verified imported checkpoint (2026-09-14): the full build passes (4,128 jobs).
All 519 SGA 2 Lean files are reachable from `SGA.lean`. The audit checks
9,596 SGA 2 declarations, including private declarations and transitive
dependencies, with only `propext`, `Classical.choice`, and `Quot.sound`.
No proof admissions or additional mathematical axioms were found.
There are no unimported SGA 2 Lean modules at this checkpoint.

By section (English: `translation/SGA2/ExposeI/`, Lean: `lean/SGA/SGA2/`):

- [x] **I.1** `Γ_Z` / sections with support for **closed** `Z` (`GammaZ.lean`)
- [x] **I.1** sheaf `Γ̲_Z` (`UnderlineGammaZ.lean`: kernel of `F → j_* j^* F`)
- [x] **I.1** original kernel-sheaf sections equal supported sections,
  naturally in coefficients and opens; original left exactness (`SupportedSheafSections.lean`)
- [x] **I.1** locally closed + independence of open (`LocallyClosed.lean`:
  `LocallyClosedIn`, `gammaZSections_restrict_addEquiv`)
- [x] **I.1 special cases** closed pushforward, open restriction, and closed
  `ℤ_{Z,X}` (`ExtensionByZero.lean`)
- [x] **I.1.3–I.1.4, closed and locally closed** genuine arbitrary-coefficient
  adjunctions and injective preservation, with natural original-kernel and
  actual counit comparisons (`ClosedSupportAdjunction.lean`)
- [x] Genuine abelian internal Hom, left exactness, actual open-restriction
  Hom comparison, and sheaf Ext as sheafification of local Ext
  (`InternalHom.lean`, `TopologicalInternalHom.lean`, `SheafExtLocalComparison.lean`)
- [x] Closed integer support commutes with restriction to every open,
  compatibly with its canonical integer presentation (`ClosedSupportRestriction.lean`)
- [ ] **I.1.1–I.1.7** remaining internal Hom identities and ringed-space statements
- [x] **I.1, (17), arbitrary coefficients** the original open extension counit
  is monic and the original closed unit is its cokernel. Exact locally closed
  extension gives the functorial short exact sequence for every coefficient
  sheaf on the support; endpoints are actual single-witness extensions,
  with literal subset equality and original arrow/coefficient-map compatibility
  (`OpenExtensionCounit.lean`, `OpenClosedExtensionSequence.lean`,
  `LocallyClosedExtensionEndpoints.lean`). Full arbitrary nested locally
  closed composition (13) is proved for extension and extraordinary inverse
  image, with original inclusion, unit, and counit comparisons
  (`LocallyClosedComposition.lean`)
- [x] **I.1.8** global nested-support equality and flasque extension
  (`ExactSequences.lean`, `Flasque.lean`)
- [x] **I.1.8, full locally closed section sequence** natural left exactness
  on the original locally closed supported-section groups, and short exactness
  on flasque coefficients (`LocallyClosedNestedGamma.lean`)
- [x] **I.1.9–I.1.10, constant support objects** genuine closed/open short
  exact sequence and open-inclusion adjunction compatibility
  (`ConstantSupportSequence.lean`, `ConstantSupportSequenceCompatibility.lean`)
- [x] **I.1.10, integer-support sequence** actual short exact sequence for
  any locally closed support and any closed subset of its literal support
  space; the difference is proved to represent the actual set difference
  (`NestedSupportObjects.lean`, `NestedSupportLocallyClosed.lean`,
  `NestedSupportSubspace.lean`)
- [x] **I.1.10, internal-Hom map identification** applying actual internal
  Hom to both open/closed-presentation support-object arrows gives the original
  I.1.9 sheaf maps, as an isomorphism of actual short complexes
  (`InternalHomPrecomposition.lean`, `NestedSupportInternalHom.lean`)
- [x] **I.1.9** original ambient nested supported-sheaf sequence is left exact
  and short exact on flasque coefficients, for arbitrary locally closed supports
  and actual closed subsets of their literal support spaces. The maps are actual
  section inclusion/restriction (`NestedSupportedPresheafSequence.lean`,
  `NestedSupportedSheafSequence.lean`, `LocallyClosedNestedSheafSequence.lean`)
- [x] **I.2.3 bis model** `H_Z^n := Ext(ℤ_{Z,X}, F)` (`DerivedFunctors.lean`)
- [x] **I.1.3–I.1.4, open case** genuine exact extension by zero and its
  restriction adjunction; restriction preserves injectives (`OpenExtensionByZero.lean`)
- [x] **I.1.6, closed case** natural additive Hom representation of supported
  sections using actual closed pushforward (`ClosedSupportHom.lean`)
- [x] **I.1.6 / I.2.3 bis, closed case, sheaf-valued** actual internal Hom
  and all-degree sheaf Ext identify naturally with original supported sheaves
  and the unchanged kernel/cokernel model (`ClosedSupportInternalHom.lean`)
- [x] **I.1.6 / I.2.3 bis, arbitrary locally closed case, sheaf-valued**
  internal Hom from the original integer-support sheaf identifies with the
  original ambient supported functor, with actual coefficient and ambient-open
  naturality. Deriving gives the original sheaf Ext comparison in every degree
  (`InternalHomIntersection.lean`, `LocallyClosedSupportInternalHom.lean`)
- [x] **I.1.6 / I.2.3, open case** actual open extension by zero represents
  sections and its Ext computes ordinary cohomology of restriction, compatibly
  with coefficient morphisms and boundaries (`OpenSupportCohomology.lean`)
- [x] **I.2.1 / I.2.3 bis, closed supports** natural comparison with actual
  right-derived supported sections in all degrees (`SupportedCohomologyComparison.lean`)
- [x] **I.2.1 original construction** actual right-derived supported sections,
  left exactness, and natural degree-zero comparison (`DerivedSupportedSections.lean`)
- [x] **I.2.1 (algebraic)** (`LocalCohomology.lean`)
- [x] **I.2.2 degree 0** excision (`I_2_2_degree_zero`)
- [x] **I.2.2, closed supports** actual all-degree excision, natural in
  coefficients (`SupportedExcision.lean`)
- [x] **I.2.1 / I.2.3 bis, chosen locally closed witnesses** genuine extension
  by zero represents supported sections; its Ext computes their original
  derived functors and the closed-support cohomology on the neighbourhood
  (`LocallyClosedCohomology.lean`)
- [x] **I.2.2** arbitrary locally closed witness independence for genuine
  support sheaves and all original/Ext cohomology (`LocallyClosedIndependence.lean`)
- [x] **I.2.4, closed support** natural sheafification comparison for the
  original derived supported sheaves (`DerivedSupportedSheaves.lean`)
- [x] **I.2.4, locally closed support** original ambient supported sheaf,
  original derived functors, natural local-cohomology sheafification, and
  all-degree witness independence (`LocallyClosedSupportedSheaves.lean`)
- [x] **I.2.5** original open-supported derived sheaves are the higher direct
  images of actual restriction (`OpenDerivedSupportedSheaves.lean`)
- [x] **I.2.11 model** `ℋ_Z^n` defined by kernel, cokernel, and derived pushforward
- [x] **I.2.11, all degrees** unchanged model naturally compared with original
  derived kernel-sheaf functor, including the actual degree-one cokernel
  (`SupportedSheafModel.lean`)
- [x] **I.2.6 construction inputs** original supported sheaves preserve
  injectives; the actual supported resolution computes `H_Z`
  (`SupportedSheafInjective.lean`, `LocalToGlobalResolution.lean`)
- [x] **I.2.6 spectral sequence construction** canonical supported truncations
  give genuine pages, differentials, and next-page homology isomorphisms
  (`LocalToGlobalSpectralObject.lean`, `HomologicalSpectralObject.lean`,
  `LocalToGlobalSpectralSequence.lean`)
- [x] **I.2.6 E₂ terms** actual terms of the constructed sequence identify
  with ordinary cohomology of original derived supported sheaves, including
  the E₂ universe comparison (`DerivedTruncationHomology.lean`, `LocalToGlobalE2.lean`)
- [x] **I.2.6 first quadrant** every actual page Eᵣ, r ≥ 2, vanishes outside
  the first quadrant (`LocalToGlobalFirstQuadrant.lean`)
- [x] **I.2.6 total groups** actual spectral-object total cohomology identifies
  with original `H_Z` via K-injectivity and the genuine global-sections complex
  (`HomComplexSingleComparison.lean`, `LocalToGlobalTotalCohomology.lean`)
- [x] **I.2.6 convergence** canonical finite image filtration, zero/exhaustive
  endpoints, and actual stable-page associated-graded cokernels, with uniform
  bound r ≥ n + 2 in total degree n (`SpectralObjectConvergence.lean`,
  `LocalToGlobalConvergence.lean`)
- [x] **I.2.6 spectral-object and total naturality** actual coefficient maps
  preserve the spectral-object connecting maps and intertwine the total
  comparison with `H_Z_map` (`LocalToGlobalSpectralFunctoriality.lean`,
  `HomComplexNaturality.lean`, `LocalToGlobalTotalNaturality.lean`)
- [x] **I.2.6, closed support, page morphisms** actual resolution maps induce
  morphisms respecting all page differentials and next-page homology isomorphisms;
  first-page equality determines these morphisms (`SpectralObjectCoefficientMaps.lean`,
  `SpectralSequenceCoefficientMaps.lean`, `LocalToGlobalPageMaps.lean`,
  `SpectralSequenceFirstPageExt.lean`)
- [x] **I.2.6, closed support, E₂ naturality** the original E₂ comparison
  intertwines actual coefficient maps (`DerivedTruncationNaturality.lean`,
  `SpectralSequenceFirstPageNaturality.lean`, `LocalToGlobalE2Naturality.lean`)
- [x] **I.2.6, closed support, coefficient functor** actual spectral-sequence
  morphisms are independent of compatible resolution lifts; identity,
  composition, and coherent natural resolution-change isomorphisms are proved
  (`LocalToGlobalCoefficientFunctor.lean`)
- [x] **I.2.6, closed support, filtered naturality** the actual convergence
  filtration and original stable-page/graded-piece comparison are natural;
  maps are lift-independent and the transported filtration on original `H_Z`
  is resolution-independent (`SpectralObjectConvergenceNaturality.lean`,
  `LocalToGlobalConvergenceNaturality.lean`)
- [x] **I.2.6, locally closed support** actual ambient spectral sequence,
  E₂ cohomology of original derived supported sheaves on `X`, original
  `H_locallyClosed` abutment, first-quadrant vanishing, and finite convergence;
  coefficient functoriality, original E₂/total/filtered naturality, lift
  independence, and resolution-independent filtration
  (`LocallyClosedLocalToGlobal*.lean`)
- [ ] **I.2.6, comparison refinements** separate identification with a named
  general Leray construction and spectral-level locally closed witness change
- [x] **I.2.7, closed support** actual open base change in all original
  derived degrees; vanishing off the support and positive-degree vanishing
  on its interior, also for sheaf Ext and the unchanged model
  (`SupportedSheafRestriction.lean`, `SupportedSheafBoundary.lean`)
- [x] **I.2.7, closed support, literal stalks** actual nonzero stalks lie in
  the support, and in positive degrees in its boundary, for original derived
  sheaves, sheaf Ext, and the unchanged model (`SupportedSheafStalkBoundary.lean`)
- [x] **I.2.7, closed-space comparison** original supported sheaves are actual
  closed direct images of their ordinary closed pullbacks, and their higher
  cohomology is computed on the closed subspace (`ClosedSupportCohomology.lean`)
- [x] **I.2.7, locally closed support** original derived sheaves restrict to
  zero off the closure and in positive degrees on the interior; literal
  stalk support lies in the closure, and in positive degrees in the boundary
  (`LocallyClosedSheafBoundary.lean`)
- [x] **I.2.7, locally closed cohomology comparison** higher cohomology of the
  original derived locally closed supported sheaves is cohomology of their
  ordinary pullbacks to the actual closure, naturally in coefficients
  (`LocallyClosedSupportCohomology.lean`)
- [x] **I.2.8 input** generic contravariant Ext exactness for a supplied short exact sequence
- [x] **I.2.9** actual closed/open relative long exact sequence in all degrees,
  from the proved constant-support short exact sequence (`RelativeCohomologySequence.lean`)
- [x] **I.2.9, degree-zero maps** actual restriction and inclusion of supported
  sections (`RelativeCohomologySections.lean`)
- [x] **I.2.8** general locally closed nested-support long exact sequence on
  the original ambient Ext groups, with genuine extension-class boundaries,
  coefficient naturality, and actual section maps in degree zero for the
  open/closed presentation (`NestedSupportCohomology.lean`,
  `NestedSupportLocallyClosed.lean`, `NestedSupportSubspace.lean`)
- [x] **I.2.10** original ambient derived nested supported-sheaf sequence,
  exact in every degree and natural in coefficients. Actual derived inclusion
  and restriction maps are retained; the boundary comes from the actual
  sequence on an injective resolution (`RightDerivedFunctorSequence.lean`,
  `LocallyClosedNestedSheafCohomology.lean`). Zeroth-degree maps agree with
  the original supported-sheaf maps under the original degree-zero comparisons.
- [x] **I.2.12 input** higher Ext vanishing on injectives
- [x] **I.2.12 input** every injective abelian sheaf is flasque (`InjectiveFlasque.lean`)
- [x] **I.2.12 ordinary cohomology** flasque sheaves have zero actual higher
  sheaf cohomology (`FlasqueCohomology.lean`)
- [x] **I.2.12 supported-section input** actual supported sections preserve
  short exact coefficient sequences with flasque kernel (`SupportedSectionExactness.lean`)
- [x] **I.2.12 original supported acyclicity** positive-degree right-derived
  supported sections vanish on flasque sheaves (`FlasqueResolution.lean`)
- [x] **I.2.12, closed supported acyclicity** actual Ext-defined `H_Z` vanishes
  in positive degrees on flasque sheaves, also on every open subspace
- [x] **I.2.12, chosen locally closed witnesses** positive-degree vanishing
  of both actual Ext cohomology and original derived supported sections
- [x] **I.2.12, converse** flasqueness iff every closed-support `H_Z¹`
  vanishes, equivalently every positive-degree `H_Z` (`FlasqueVanishingCriterion.lean`)
- [x] **I.2.12, closed support** original and unchanged-model sheaf-valued flasque acyclicity
- [x] **I.2.12** original ambient locally closed sheaf-valued flasque vanishing
  (`LocallyClosedSupportedSheaves.lean`)
- [x] **I.2.13 degrees 0 and 0–1** actual mono/isomorphism criteria and degree-zero restriction injectivity
- [x] **I.2.14 / III.3.1, group-valued input** supported vanishing through
  degree `n` iff relative restriction is bijective below `n` and injective
  in degree `n` (`RelativeCohomologySequence.lean`)
- [x] **I.2.13–I.2.14, main criteria** all-degree ordinary restriction-map
  comparison, and original supported-sheaf lower vanishing iff the ordinary
  restriction condition holds on every open
  (`ExposeIII/OrdinaryCohomologyRestriction.lean`,
  `ExposeIII/CohomologyRestrictionCriterion.lean`)
- [x] **I.2.13, extra clause at `N = 1`** degree-one injectivity follows
  from all-open actual degree-zero bijectivity, for arbitrary abelian sheaves
  (`ExposeIII/RestrictionRedundancy.lean`)
- [x] **I.2.13, extra clause for every `N > 0`** highest-degree ordinary
  restriction injectivity follows from all-open lower-degree bijectivity,
  via actual complement-adapted injective effacement and coefficient
  dimension shifting (`ExposeIII/HigherRestrictionRedundancy.lean`)

Exposé II (English: `translation/SGA2/ExposeII/`):

- [x] **II.4 affine input, noetherian rings** actual ordinary higher sheaf
  cohomology of associated module sheaves vanishes, with no finiteness
  hypothesis on the module (`AffineCohomologyVanishing.lean`)
- [x] Associated abelian sheaves preserve short exact sequences over arbitrary
  rings, and their global sections recover the module (`AffineExactness.lean`,
  `AffineCohomologyVanishing.lean`)
- [x] **II.(7.5) module algebra** ideal-power torsion, annihilator union,
  functorial maps, and quotient Hom equivalence (`Torsion.lean`)
- [x] Radical invariance for finitely generated ideals (`Torsion.lean`)
- [x] **II.(7.3)–(7.4) algebraic reindexing** cofinality of ideal and generator
  powers, and natural isomorphisms of Ext colimits in each degree
  (`FiniteGenerators.lean`, `FiniteGeneratorColimits.lean`)
- [x] **II.(7.5) categorical Hom colimits** both ideal-power and generator-power
  systems naturally identify with torsion (`TorsionColimit.lean`, `GeneratorHomColimit.lean`)
- [x] Degree-zero algebraic local cohomology identifies with ideal-power torsion
  (`LocalCohomologyZero.lean`)
- [x] **II.(4.2) module kernel** torsion is the kernel of the map to the product
  of localizations at a finite generating family (`LocalizationKernel.lean`)
- [x] **II.(4.2)/(5.1), degree zero** actual affine supported sections and Exposé I's
  `gammaZ` identify with ideal-power torsion and stable Koszul degree zero
  (`AffineSupport.lean`, `AffineComparisonZero.lean`)
- [x] **II.(4.2)/(5.1), principal cokernel calculation** singleton stable Koszul H¹
  is the cokernel of actual global restriction to `D(f)`; higher singleton
  cohomology vanishes (`LocalizationCokernelColimit.lean`, `PrincipalCechComparison.lean`)
- [x] **II.(7.5), finite-family Koszul comparison** genuine zeroth homology is the
  generator quotient, finite cohomology is the annihilator, and stable degree
  zero is torsion (`KoszulDegreeZero.lean`, `KoszulCohomologyZero.lean`)
- [x] **II.(7.6), actual comparison map** projective augmentation, lift uniqueness
  up to homotopy, and finite/stable Ext-to-Koszul maps natural in coefficients
  (`KoszulAugmentation.lean`, `ProjectiveComplexLift.lean`, `KoszulExtComparison.lean`)
- [x] **II.(7.6), coefficient boundaries** actual finite and stable connecting
  maps, exactness, and boundary compatibility of the generator-power comparison
  (`KoszulCoefficientSequence.lean`, `ExtCoefficientSequence.lean`, `ExtColimitSequence.lean`)
- [x] **II.8** the actual comparison is invertible over noetherian rings,
  naturally in coefficients, by the proved dimension-shifting criterion
  (`CohomologicalComparison.lean`, `KoszulComparisonIsomorphism.lean`)
- [x] **II.8, ideal-power form** algebraic local cohomology is naturally isomorphic
  to stable Koszul cohomology (`KoszulLocalCohomology.lean`)
- [x] **II.9(c) ⇒ (b), diagram step** zero Hom colimit of an essentially zero
  inverse sequence (`EssentiallyZero.lean`)
- [x] **II.9(b) ⇔ (c), Hom criterion** vanishing on injective coefficients detects
  essentially zero inverse sequences (`InjectiveDetection.lean`)
- [x] **II.9(b) ⇔ (c), actual Koszul complexes** the natural Hom–homology comparison
  on injectives proves the equivalence degree by degree
  (`InjectiveHomology.lean`, `KoszulCohomology.lean`)
- [x] **II.9(a) ⇔ (b) ⇔ (c), all-degree family** invertibility of the constructed
  comparison in all degrees is equivalent to vanishing in all positive degrees
  (`KoszulComparisonIsomorphism.lean`)
- [x] **II.10, principal-open input** injective modules over noetherian rings
  have surjective global restrictions to principal opens
  (`InjectiveLocalization.lean`, `AffineSupport.lean`)
- [x] **II.10, noetherian-ring flasqueness** ideal-power torsion preserves
  injectivity, and every associated-sheaf section on every open extends
  globally (`InjectiveTorsion.lean`, `FiniteFractionCover.lean`, `InjectiveFlasque.lean`)
- [x] **II.11 system arguments** closure under subobjects, quotients, and extensions
- [x] **II.11 principal annihilator argument** stabilization, transition maps,
  naturality, and uniform vanishing (`Principal.lean`)
- [x] Principal inverse system and its vanishing Hom colimits (`PrincipalSystem.lean`)
- [x] **II.11 actual principal Koszul case** homology calculations, chain transitions,
  comparison with annihilators, and essential vanishing (`PrincipalKoszul.lean`)
- [x] **II.11 varying-coefficient argument** fixed-target factorization and
  essential vanishing for a sequence of noetherian modules (`VariableAnnihilators.lean`)
- [x] **II.11** actual finite Koszul complexes, natural scalar short exact
  sequence, and full induction for every noetherian coefficient module
  (`KoszulComplex.lean`, `KoszulCofiber.lean`, `KoszulProZero.lean`)
- [x] Boundary cases: nonzero homology in an essentially zero system, explicit
  zero transition, and empty generating families (`Examples.lean`)
- [x] **II.(4.2)–(4.3), noetherian rings** actual low-degree relative sequence
  and higher supported/open-complement cohomology comparison
  (`AffineRelativeSequence.lean`)
- [ ] **II.1–II.4** quasi-coherence and arbitrary-ring affine sheaf-cohomology statements
- [ ] **II.5–II.7** general higher sheaf comparisons, spectral sequences,
  and the local-to-global argument
- [x] **II.(7.3), noetherian affine case** actual algebraic local cohomology
  agrees with actual supported sheaf cohomology in every degree, naturally in
  arbitrary coefficient modules and compatibly with every coefficient boundary
  (`AffineCohomologyComparison.lean`)
- [x] **II.(7.3)–(7.6)** cofinal ideal-power reindexing and the resulting
  canonical Ext-to-Koszul comparison commute with actual coefficient boundaries
  (`LocalCohomologyReindexing.lean`, `KoszulLocalCohomologySequence.lean`)
- [ ] **II.10** equivalence under only topological noetherianity of the spectrum

Exposé III (English: `translation/SGA2/ExposeIII/`):

- [x] **III.1.1–III.1.3** associated primes, support and annihilator, and
  `Ass Hom(N,M) = Supp N ∩ Ass M` (`AssociatedPrimes.lean`)
- [x] **III.2.1** all five equivalent depth-zero criteria (`AssociatedPrimes.lean`)
- [x] **III.2.2(a)** regular sequences imply Ext vanishing over arbitrary
  commutative rings, without module finiteness assumptions (`RegularExt.lean`)
- [x] **III.2.2(b)** converse over noetherian rings for finite modules (`RegularExt.lean`)
- [x] **III.2.3–III.2.4** depth valued in `ℕ∞`, defined by Ext against all finite
  modules annihilated by an ideal power, and the stated equivalences (`Depth.lean`)
- [x] **III.2.5** quotient by a regular element lowers depth by one, including
  infinite depth (`Depth.lean`)
- [x] **III.2.6, finite depth** extension of any regular sequence to a maximal
  sequence of length equal to depth (`MaximalRegular.lean`; source qualification
  in the formalization notes)
- [x] **III.2.6, infinite depth** any finite regular prefix extends to a single
  infinite regular sequence (`InfiniteRegular.lean`)
- [x] **III.2.7** depth is finite exactly when `Supp M ∩ V(I)` is nonempty
  (`DepthSupport.lean`)
- [x] **III.2.8** the first nonzero Ext degree computes depth, using any finite
  test module of the specified support; in particular the residue module (`Depth.lean`)
- [x] **III.2.9–III.2.10** localization infimum formula and semilocal
  specialization (`DepthLocalization.lean`)
- [x] **III.2.11** flat base change increases depth; faithfully flat base change
  preserves depth (`DepthBaseChange.lean`)
- [x] **III.§3 algebraic input** depth equals the first nonzero actual algebraic
  local cohomology degree (`DepthLocalCohomology.lean`)
- [x] **III.§3 affine group-valued bridge** depth equals the first nonzero
  actual supported sheaf-cohomology degree; equivalent criteria use depths
  of localized modules along the support and Ext from finite test modules
  (`AffineDepth.lean`)
- [x] Actual affine structure and module stalks identify with localizations,
  including scalar compatibility and equality with literal stalk depth
  (`AffineStalkDepth.lean`)
- [x] Boundary cases: infinite depth at the unit ideal, depth zero at the zero
  ideal on a nonzero finite module, and depth of `ℤ` along `(2)` (`Examples.lean`)
- [x] **III.3.4, positive thresholds** local depth/restriction/residue-field Ext criteria
- [x] **III.3.5, affine** actual Hartogs section restriction at depth at least two
- [x] **III.3.5, general locally noetherian schemes, structure sheaf** actual
  structure-stalk depth at least two iff actual restriction is bijective on
  every open (`SchemeHartogs.lean`, `SheafHartogsGluing.lean`, `SchemeHartogsCriterion.lean`)
- [x] **III.3.5, general coherent module sheaves** literal actual module-stalk
  depth at least two iff actual section restriction is bijective on every
  open, using mathlib's local finite-presentation condition and proved finite
  affine presentations, with no assumed stalk/presentation comparison
  (`SchemeModuleStalks.lean`, `AffineQuasicoherentHartogs.lean`,
  `CoherentAffineCharts.lean`, `CoherentHartogs.lean`)
- [x] **III.3.6, affine connectedness equivalence** from actual structure-sheaf
  restriction and clopen characteristic sections (`AffineHartogs.lean`, `AffineClopens.lean`)
- [x] **III.3.6, affine connected components** bijectivity of the actual
  inclusion-induced map (`AffineConnectedComponents.lean`)
- [x] **III.3.6, general locally noetherian schemes** literal structure-stalk
  depth at least two gives bijectivity of the actual complement-inclusion map
  on connected components, using genuine global idempotents and clopens
  (`SchemeClopens.lean`, `SchemeConnectedComponents.lean`)
- [x] **III.3.1(i) iff (iii)** original supported-sheaf lower vanishing iff
  actual supported cohomology vanishes below the same bound on every open,
  for arbitrary abelian sheaves (`SupportedSheafVanishing.lean`)
- [x] **III.3.3(i)/(iii)/(iv)** for actual coherent modules on locally
  noetherian schemes, literal stalk depth at least `n` along the support
  iff original derived supported sheaves vanish below `n`, iff actual
  supported cohomology vanishes below `n` on every open; all nonnegative
  thresholds, with proved affine-chart transport
  (`HomeomorphismSupportedCohomology.lean`, `AffineChartSupportedCohomology.lean`,
  `CoherentDepth.lean`)
- [x] **III.3.1(ii) / III.3.3(ii)** higher ordinary restriction criterion in
  every positive threshold: actual `Hⁱ(V,F) → Hⁱ(V ∩ (X ∖ Z),F)` is bijective
  below the last degree and injective in the last degree. All-degree identity
  with the relative sequence map and actual nested-open/intersection sheaf
  and cohomology comparisons are proved (`OrdinaryCohomologyRestriction.lean`,
  `OpenIntersectionCohomology.lean`, `CohomologyRestrictionCriterion.lean`)
- [x] **III.3.2, threshold two** original supported sheaves vanish in
  degrees zero and one iff actual degree-zero intersection restriction is
  bijective on every open; the discarded degree-one injectivity is proved
  (`RestrictionRedundancy.lean`)
- [x] **III.3.2, all thresholds at least two** lower actual ordinary
  restriction bijectivity suffices for original supported-sheaf vanishing;
  highest-degree injectivity follows. The corresponding coherent stalk-depth
  criterion is proved (`HigherRestrictionRedundancy.lean`)
- [ ] **III.3.3(v)/(vi)** module-valued internal sheaf Ext criteria
- [ ] **III.3.7–III.3.13** remaining geometric depth and connectedness results

Exposé IV (English: `translation/SGA2/ExposeIV/`):

- [x] **IV.1 opening** canonical module structure induced by scalar
  endomorphisms for an additive abelian-group-valued functor, and its linear
  module-valued lift (`AdditiveFunctorModules.lean`)
- [x] **IV.1.1** the actual canonical evaluation map is an isomorphism iff
  the original additive contravariant functor is left exact, over a noetherian
  ring (`FiniteModuleEvaluation.lean`, `FiniteFreeEvaluation.lean`,
  `FiniteModuleRepresentation.lean`)
- [x] **IV.1 after 1.1** equivalence of arbitrary modules with additive
  left-exact contravariant functors on finite modules, using the actual
  restricted Hom functor (`FiniteModuleFunctorEquivalence.lean`)
- [x] **IV.1.2** the original additive functor on all modules is canonically
  represented by `T(R)` iff it preserves arbitrary preorder-indexed limits,
  without filteredness; actual finite-submodule colimit and the equivalence
  between preorder-limit and all-small-limit preservation are proved
  (`FiniteSubmoduleColimit.lean`, `ModuleEvaluation.lean`,
  `ModuleRepresentation.lean`, `PreorderLimitRepresentation.lean`)
- [x] **IV.1.3 foundations** actual abelian category of finite supported modules,
  fully faithful exact quotient-ring stages covering every object, and the
  actual diagram `T(R/Jⁿ)` with canonical scalar actions, annihilator bounds,
  and injective transitions for left-exact functors (`SupportedFiniteModules.lean`,
  `SupportedQuotientStages.lean`, `SupportedFunctorDiagram.lean`)
- [x] **IV.1.3 representation** original canonical evaluation into the actual
  colimit `colim T(R/Jⁿ)` is an isomorphism iff `T` is left exact; scalar
  compatibility, all-power independence, genuine naturality, support of the
  colimit and finite-source factorization are proved (`SupportedStageEvaluation.lean`,
  `SupportedStageRepresentation.lean`, `SupportedFunctorColimit.lean`,
  `SupportedFunctorEvaluation.lean`, `SupportedFunctorRepresentation.lean`)
- [x] **IV.1.3 categorical equivalence** actual restricted Hom gives an
  equivalence of arbitrary supported modules with additive left-exact
  functors on finite supported modules (`SupportedRestrictedHom.lean`,
  `SupportedFunctorEquivalence.lean`)
- [x] **IV.1.4 Hom detection input** any supported target module is zero iff
  Hom from a finite full-support test module is zero; the target need not be
  finite (`SupportedHomDetection.lean`)
- [x] **IV.1.4** all three vanishing conditions for arbitrary integer-indexed
  bounded-below exact delta functors, deriving left exactness from the actual
  connecting sequences (`IntegerCohomologicalSequence.lean`,
  `SupportedFunctorVanishing.lean`, `SupportedDeltaVanishing.lean`)
- [x] **IV.2.1** a supported module is injective iff actual contravariant
  Hom is exact on finite supported modules, via Artin–Rees and Baer's criterion
  (`InjectivityCriterion.lean`)
- [x] **IV.2.1 support bridge** actual support in `V(J)` iff ideal-power
  torsion for arbitrary modules, and the support-hypothesis formulation of
  the Hom criterion (`SupportedModuleTorsion.lean`)
- [x] **IV.2.1 original functor** actual short-exact-sequence preservation,
  equivalently `T.PreservesHomology`, iff the actual colimit of `T(R/Jⁿ)`
  is injective; the original left-exact additive `T` and genuine supported
  category are used (`SupportedFunctorExactness.lean`)
- [x] **IV.2.2** ideal-power torsion in an injective module is injective
- [x] **IV.3.1, actual Hom-duality implication** noetherian `R` and Artinian
  `R/J` imply finite length of every finite supported module. For arbitrary
  injective `H`, residue-field Hom tests at maximal ideals containing `J`
  imply the original canonical bidual evaluation is an isomorphism, Hom
  values are finite, and length is preserved. Simple tests, actual short
  exact sequences, and finite-length induction are proved
  (`ModuleBidual.lean`, `ModuleBidualFiniteLength.lean`,
  `ModuleBidualSimpleTests.lean`, `SupportedArtinianDuality.lean`)
- [x] **IV.3.1, full original-functor equivalence** all four conditions for
  the original additive abelian-group-valued functor, without additional
  left-exactness, finite-value, or representing-module hypotheses. The actual
  canonical map into actual `T(T(M))` and its naturality are constructed;
  scalar compatibility of any original representation is proved
  (`SupportedFunctorDual.lean`, `SupportedFunctorBidualNaturality.lean`,
  `SupportedFunctorDualityConditions.lean`, `SupportedFunctorDuality.lean`)
- [x] **IV.3.2** length preservation alone implies exactness and finite
  values for the original functor under IV §3's standing left-exactness
  hypothesis (`HomDualLengthExactness.lean`, `SupportedFunctorLengthExactness.lean`)
- [x] **IV.4.2, existence and local comparison** actual exact linear Hom
  duality on the whole finite-length module category, with canonical natural
  bidual evaluation and genuine anti-equivalence. The coefficient is the actual
  injective envelope of the sum of all residue fields; its maximal-ideal
  annihilators have length one. The local category is identified with original
  finite supported modules (`LocalFiniteLengthCategory.lean` and its imports)
- [x] **IV.4.2, local Artinianness** the actual injective envelope of the
  sum of residue fields is locally Artinian, via preservation of associated
  primes under essential embeddings (`NonlocalDualizingLocallyArtinian.lean`)
- [x] **IV.4.3** actual finite local coinduction `Hom_A(B,I)` preserves support,
  finite Hom values, and canonical biduality; the genuine adjunction identifies
  the evaluation maps, and injectivity and residue tests are proved
  (`CoinductionHomDuality.lean`, `FiniteCoinductionDuality.lean`,
  `FiniteCoinductionSupport.lean`)
- [x] **IV.4.4, proper quotients** evaluation at one identifies actual quotient
  coinduction with the actual ideal annihilator, with its ordinary quotient-ring
  action; supported duality follows (`QuotientAnnihilatorDuality.lean`)
- [x] **IV.4.5, tensor assertion** the original map `M → M ⊗ Â`, `x ↦ x ⊗ 1`,
  is invertible for every locally Artinian module over a noetherian local ring.
  No finiteness of `M` or completeness of the ring is assumed. Literal local
  Artinianness is proved equivalent to actual closed-point support
  (`AdicTensorNilpotent.lean`, `LocalArtinianSupport.lean`, `AdicTensorSupported.lean`)
- [x] **IV.4.5, categorical conclusion** original tensor extension and
  restriction are inverse equivalences on actual supported modules and the
  literal locally Artinian categories. Every original-ring submodule is stable
  under the completed action; finite generation is unchanged by restriction.
  Only finite generation of the completed maximal ideal is used, with no
  extra noetherianity hypothesis on the completed ring
  (`SupportedScalarChange.lean`, `SupportedCompletionEquivalence.lean`,
  `CompletionSubmodules.lean`, `LocalArtinianFiniteIdeal.lean`,
  `LocalCompletionEquivalence.lean`). The equivalence also restricts to the
  original finite supported categories, retaining the original unit/counit
  (`FiniteSupportedCompletionEquivalence.lean`)
- [x] **IV.4.9, canonical representing module** every finite submodule is
  Artinian. Under duality, the original stage maps identify `T(A/Jⁿ)` with
  the actual finite-length annihilator of `Jⁿ`; the actual inclusions form a
  categorical colimit (`SupportedFunctorAnnihilatorStages.lean`,
  `SupportedLocallyArtinian.lean`, `AnnihilatorFiltrationColimit.lean`)
- [x] **IV.4.7, explicit supported convention** genuine injective envelopes
  are constructed using enough injectives and two Zorn arguments. Supported
  dualizing modules are exactly injective essential extensions of the residue
  field; existence and noncanonical uniqueness follow. The definition is
  proved equivalent to duality of the original abelian-group-valued Hom
  functor together with actual support (`EssentialModuleExtensions.lean`,
  `LocalInjectiveEnvelopes.lean`)
- [x] **IV.4.3–4.4 / IV.4.9, named supported dualizing modules** actual
  coinduction and quotient annihilators preserve the definition; every such
  module is locally Artinian (`SupportedDualizingTransfers.lean`,
  `LocalInjectiveEnvelopes.lean`)
- [x] **IV.5 opening, anti-equivalence** actual original dual functor and its
  right opposite give an anti-equivalence; canonical inverse-evaluation counit
  and both coherent triangle identities are proved (`SupportedFunctorAntiEquivalence.lean`)
- [x] **IV.5 opening, orthogonality** actual vanishing orthogonal and
  coorthogonal are inverse order-reversing submodule bijections, including
  transport through original canonical evaluation to actual `T(M)`
  (`SupportedHomOrthogonality.lean`)
- [x] **IV.5 opening, length/colength** both identities for actual orthogonals,
  also for the original functor; infinite lengths are included (`HomOrthogonalLength.lean`)
- [x] **IV.5 opening, Artinian-local ideals** ideals correspond to actual
  submodules of the specified injective coefficient via ideal annihilation;
  full support of every module is proved in this case (`ArtinianLocalIdealDuality.lean`)
- [x] **IV.5 opening, cyclic/socle criterion** actual existence of one
  generator is equivalent to the original dual's socle having length at most
  one, including zero. Nakayama lifts a residue generator; the maximal-ideal
  annihilator is proved equal to the sum of simple submodules
  (`LocalMonogenicCriterion.lean`, `LocalSocleDuality.lean`)
- [x] **IV.5.2, Macaulay example** the literal coefficient-field Hom functor
  is dualizing with its actual ring action; its actual quotient-dual colimit
  canonically represents it and is supported dualizing. The dimension–length
  formula is proved, requiring only finite residue-field degree, not a finite
  coefficient-field algebra (`CoefficientFieldDuality.lean`,
  `MacaulayDualizingFunctor.lean`, `MacaulayDualizingModule.lean`)
- [x] **IV.5.1, complete-base duality** actual Hom functors give inverse
  equivalences between finite modules and locally Artinian modules with finite
  socle over a complete noetherian local ring. Both original canonical bidual
  evaluations are natural isomorphisms; the original complete category is
  identified with finite modules (`MatlisCategories.lean`, `MatlisCompleteDuality.lean`)
- [x] **IV.5.1, original maps over general bases** the actual bidual of any
  finite module is its actual adic completion, sending canonical evaluation
  to the original completion map. The dual of a locally Artinian finite-socle
  module is complete with finite-length actual power quotients. Restriction
  to annihilators has its proved original kernel and is surjective; actual
  annihilator inclusions form a colimit (`MatlisBidualCompletion.lean`,
  `MatlisDualComplete.lean`, `HomAnnihilatorQuotient.lean`,
  `SupportedAnnihilatorColimit.lean`)
- [x] **Matlis foundations** finite socle implies finite-length power
  annihilators, topological Nakayama proves finiteness, and the actual dualizing
  module cogenerates all modules and Hom reflects isomorphisms. None is an
  additional hypothesis (`FiniteSocleAnnihilators.lean`, `CompleteFiniteModules.lean`,
  `SupportedHomCogenerator.lean`)
- [x] **IV.5.1, finite-socle completion transport** actual tensor extension
  and restriction give `CA(R) ≌ CA(Â)`. The socle restriction comparison is
  identity on elements, with original tensor unit and multiplication counit;
  no noetherianity assumption on `Â` is added (`MatlisArtinianCompletion.lean`)
- [x] **Noetherian completion and completed-ring duality** the actual adic
  completion of a noetherian ring is noetherian for every ideal, via a genuine
  quotient of a finite-variable power series ring. Thus actual scalar change
  and completed-ring Hom give `CA(R)ᵒᵖ ≌ FGModuleCat Â`
  (`NoetherianCompletion.lean`, `MatlisCompletedRingDuality.lean`)
- [x] **IV.5.1, original Hom comparison** the completed-ring equivalence's
  forward functor is naturally identified, after restriction, with original
  `Hom_R(-,H)`. The forward comparison is the specified tensor-unit formula,
  its inverse is actual tensor extension, and source and coefficient
  naturality hold (`MatlisCompletedHomComparison.lean`)
- [x] **IV.5.1, full Artinian characterization** the literal `CA` property
  is equivalent to genuine Artinianity over every noetherian local ring.
  All-module Hom cogeneration gives an orthogonal submodule order embedding;
  the actual completion action preserves the whole supported submodule lattice
  and its descending-chain condition. The converse uses the actual residue-field
  socle (`HomArtinianCriterion.lean`, `CompletionArtinian.lean`,
  `MatlisArtinianModules.lean`)
- [x] **Actual socles in essential extensions** an essential embedding
  induces a bijection on original socles and preserves their finiteness;
  finite socle also passes to arbitrary submodules over a noetherian local
  base (`EssentialSocles.lean`). No finiteness of the whole injective envelope
  is assumed
- [x] **IV.5.1, full general-base equivalence and transport** literal
  `CA(R)ᵒᵖ ≌ DA(R)` with the forward functor exactly original-ring Hom and
  the inverse actual completed-ring Hom through canonical scalar comparisons.
  Actual module-adic completion and restriction identify the original `DA`
  categories; both natural completion-transport squares are proved
  (`MatlisCompleteCompletion.lean`, `MatlisDuality.lean`,
  `MatlisDualityTransport.lean`). The supported dualizing-module convention
  remains explicit; no completeness assumption on `R` is added
- [x] **Regular-local foundations for IV.5.3–5.4** actual regular local rings
  are domains; every minimal maximal-ideal generating list is a regular
  sequence, and a regular system of parameters of Krull-dimension length
  exists (`RegularLocalRegularSequence.lean` and its imports)
- [x] **IV.5.3–5.4, off-degree Ext vanishing** residue-field projective
  dimension equals Krull dimension; finite-length modules have projective
  dimension at most that dimension, and actual Ext into the ring vanishes
  in every other degree (`RegularLocalExtVanishing.lean`)
- [x] **Regular Koszul resolution** the original Koszul augmentation is a
  quasi-isomorphism for every regular sequence over a noetherian local ring;
  the actual complex is a projective resolution and the original finite-stage
  Ext comparison is an isomorphism in all degrees, naturally in coefficients
  (`KoszulRegularResolution.lean`)
- [x] **IV.5.4, top Ext exactness and representation** the actual
  derived-category Ext functor is exact on original finite supported modules
  and canonically represented by its actual injective quotient-Ext colimit
  (`RegularLocalExtFunctor.lean`). Scalar-compatible residue tests and duality
  are supplied by the subsequent result below
- [x] **IV.5.3, actual top residue value** original module-valued
  `Extⁿ_R(k,R)` is isomorphic to `k` as an `R`-module. Concrete top Hom–Koszul
  cohomology is the coefficient quotient for arbitrary rings and lists;
  a shared-projective-resolution additive comparison also gives the
  derived-category Ext value (`KoszulTopCohomology.lean`, `RegularLocalTopExt.lean`,
  `ModuleExtDerivedComparison.lean`). The isomorphism depends on ordered parameters
- [x] **IV.5.4, functor and representing-module duality** the actual top
  Ext functor is dualizing with its canonical source-induced module action,
  and its actual quotient-Ext colimit is supported dualizing. The two Ext
  constructions are compared by a genuine `R`-linear isomorphism, exactly
  agreeing with the original additive comparison (`ModuleExtDerivedLinear.lean`,
  `RegularLocalExtDuality.lean`)
- [x] **IV.5.4, original local cohomology** actual first-variable Ext
  naturality identifies the original quotient diagrams and their colimits,
  respecting the original stage maps. Thus actual `Hⁿ_m(R)` is supported
  dualizing and naturally represents top Ext. The source footnote's actual
  affine supported-sheaf cohomology is also compared as an additive group
  (`ModuleExtDerivedNaturality.lean`, `SupportedExtDiagram.lean`,
  `RegularLocalCohomologyComparison.lean`, `RegularLocalCohomologyDuality.lean`)
- [x] **IV.5.3, global dimension and arbitrary-module upper vanishing** the
  residue-field bound extends to every finite module by induction on actual
  support dimension. Baer's criterion and actual injective dimension shifting
  extend cyclic Ext tests to arbitrary modules. Global dimension equals the
  actual Krull dimension, with equality attained by the original residue
  field; upper vanishing holds for both original Ext models with both
  arguments arbitrary (`ExposeV/FiniteProjectiveDimension.lean`,
  `ExposeV/GlobalProjectiveDimension.lean`)
- [x] **IV.5.3, literal depth and arbitrary lower vanishing** the original
  maximal-ideal depth of the ring equals its Krull dimension. Lower Ext
  vanishes for arbitrary modules killed by a maximal-ideal power, without
  finite-generation or finite-length assumptions (`RegularLocalDepth.lean`)
- [x] **Ext comparison, both variables** the exact original linear bridge
  is natural for original first-argument maps and coefficient maps in every
  degree; no finiteness hypothesis is added
  (`ModuleExtDerivedCoefficientNaturality.lean`, `ModuleExtDerivedNaturality.lean`)
- [x] **IV.5.5, initial existence assertion** the actual local cohomology
  and Macaulay quotient-dual colimit modules are noncanonically isomorphic
  (`RegularMacaulayComparison.lean`)
- [x] **IV.5.5, original power transitions** the original top Koszul
  cohomology diagram becomes multiplication by the product of parameter-power
  differences under the actual quotient isomorphisms. The `r → r+s` and
  monomial-class shift formulas hold over every commutative ring, with no
  regularity or monomial-basis assumption (`KoszulTopTransition.lean`)
- [x] **IV.5.5, actual quotient colimit** the direct diagram of power-ideal
  quotients with actual product-multiplication maps has original top local
  cohomology as its colimit over a noetherian ring. Original stage maps are
  preserved, for arbitrary coefficient modules and generating lists, without
  regularity assumptions (`KoszulTopQuotientColimit.lean`)
- [ ] **IV.5.5, remaining intrinsic identification** coefficient fields and
  Cohen presentations for arbitrary complete regular local rings, completed
  differentials, parameter independence, and coefficient-field compatibility
- [x] **IV.5.5, actual monomial basis** for literal finite-variable power
  series rings, the coordinate-power quotient has the original bounded
  monomial classes as a basis and dimension `r^d`, including zero-variable
  and zero-power cases (`PowerSeriesPowerQuotientBasis.lean`)
- [x] **IV.5.5, finite-stage residue pairing** top-coefficient extraction
  of products gives a perfect pairing on the original positive coordinate-power
  quotient. Complementary monomials recover each coefficient (`PowerSeriesResiduePairing.lean`)
- [x] **IV.5.5, explicit power-series isomorphism** the original coordinate
  ideal is the actual maximal ideal, and the finite residue forms glue through
  the original product transitions. Cofinality and original-stage compatibility
  identify the actual local-cohomology module with the continuous dual and
  original Macaulay module. The comparison is proved equal to the explicit
  colimit construction (`PowerSeriesCoordinateIdeals.lean`,
  `PowerSeriesResidueContinuous.lean`, `PowerSeriesResidueColimit.lean`,
  `PowerSeriesLocalCohomologyResidue.lean`)
- [x] **IV.5.5, glued residue form** the genuine coefficient-field linear
  residue has the original monomial formula and nondegenerate product pairing.
  The original local-cohomology module is supported dualizing via this explicit
  comparison (`AdicContinuousDualEvaluation.lean`, `PowerSeriesResidueDuality.lean`).
  These results concern literal power-series rings and include zero variables
- [x] **IV.5.2, continuous dual** the original Macaulay quotient-dual colimit
  is canonically the continuous coefficient-field linear dual of the original
  adic ring, with its original precomposition scalar action. Continuity iff
  vanishing on an ideal power is proved, without assuming completeness
  (`MacaulayContinuousDual.lean`)
- [x] **IV.5.1, finite-length intersection** finite modules intersect `CA`
  exactly in the original finite-length category. The category equivalence is
  identity on modules; both actual Hom restrictions and canonical evaluations
  agree with finite-length duality (`MatlisFiniteLengthIntersection.lean`)
- [x] **IV.4.2, original nonlocal representation** canonical evaluation
  into the actual cofinite-ideal colimit represents every additive left-exact
  functor on the whole finite-length category, even over arbitrary commutative
  rings. Over a noetherian ring, original Hom gives an equivalence between
  locally Artinian modules and these functors (`CofiniteFunctorRepresentation.lean`,
  `CofiniteFunctorEquivalence.lean` and their imports)
- [x] **IV.4.2, arbitrary original dualizing functors** a linear
  finite-length functor with its natural involution is represented by the
  actual cofinite colimit, which is locally Artinian and injective over a
  noetherian ring. Each actual maximal-ideal annihilator is the corresponding
  residue module and has length one (`NonlocalDualizingRepresentation.lean`).
  The supplied involution is not relabelled canonical evaluation. These are
  claims about the constructed coefficient, not arbitrary raw Hom targets
  with invisible summands
- [x] **IV.4.2, nonlocal injectivity criterion** actual Hom of a locally
  Artinian coefficient is exact on all finite-length modules iff the
  coefficient is injective among all modules. Hence an additive left-exact
  functor is exact iff its actual cofinite colimit is injective, via genuine
  cofinite Artin–Rees and Baer reduction (`NonlocalInjectivityCriterion.lean`,
  `CofiniteFunctorExactness.lean`)
- [x] **IV.4.2, nonlocal representation foundations** finite-length
  annihilator quotients are cofinite, and actual cofinite quotients form a
  reverse-inclusion filtered diagram, over arbitrary commutative rings.
  Over a noetherian ring, actual Hom on finite-length tests is fully faithful
  on locally Artinian coefficients, recovering the specified transformations
  (`CofiniteIdeals.lean`, `FiniteLengthRestrictedHom.lean`)
- [x] **IV.4.6, explicit supported convention** original restriction and
  tensor extension preserve supported duality in both directions. Actual
  linear Hom restriction is an isomorphism, with unchanged values and
  canonical bidual-evaluation compatibility. No noetherianity of the completion
  is added (`CompletionHomDuality.lean`, `CompletionDualizingTransfer.lean`,
  `SupportedDualityTransport.lean`)
- [ ] **IV.4.8 and later results** remaining structural remarks, later
  dualizing-module results

Exposé V (English: `translation/SGA2/ExposeV/`):

- [x] **V.1, displayed Hom differential and signs** the actual complex on the
  original cochains has the literal displayed differential, with proved
  square-zero, Leibniz, cocycle/coboundary and homotopy identities. The explicit
  sign `(-1)^(n(n+1)/2)` gives a chain isomorphism to Mathlib's convention;
  its composition correction is `(-1)^(ij)` (`SourceHomComplex.lean`)
- [x] **V.1.3, actual double-resolution Ext comparison** precomposition by
  a quasi-isomorphism preserves actual Hom-complex cohomology into a K-injective
  target. For two given injective resolutions, the sign-normalized augmentation
  into ordinary Hom is a quasi-isomorphism and its actual homology map computes
  Ext. Its original component formula is proved; the source's incompatible
  unsigned augmentation formula is not asserted (`HomComplexPrecomposition.lean`,
  `InjectiveHomComplexExt.lean`)
- [x] **V.1, original cohomology product and Yoneda comparison** actual graded
  composition descends to a biadditive pairing on cohomology, with its original
  representative formula and associativity. The previously constructed
  double-resolution Ext equivalence identifies the standard Hom-complex product
  with Yoneda composition. The source complex has verified unscaled kernel and
  quotient data; its original homology product is carried to Yoneda composition
  with exactly `(-1)^(ij)` under the specified normalization
  (`HomComplexComposition.lean`, `SourceHomComplexCohomology.lean`,
  `InjectiveHomComplexProduct.lean`)
- [x] **V.1, original lifted-cocycle connecting formula** the actual cone lift
  projects to the original cocycle and composes with the actual third triangle
  arrow to its boundary. This identifies lift-and-differentiate with the derived
  connecting morphism of the original short exact sequence; the literal source
  convention has its proved target-degree sign (`HomComplexConnectingCocycle.lean`)
- [x] **V.1, unsigned projective representatives and Ext boundary** for the
  actual projective-resolution representatives, Yoneda composition with the
  extension class is `(-1)^(n+1)` times the lifted boundary's `extMk` class.
  Original lifts and factorizations exist by projectivity and exactness, and
  their boundary is automatically a cocycle. Every Ext class has such a
  representative formula (`ProjectiveExtConnectingCocycle.lean`)
- [x] **V.1, actual coefficient-boundary comparison** the existing linear
  Ext comparison sends original module-cohomology representatives to their
  original `extMk` classes in every degree, including zero. The transported
  Yoneda coefficient boundary equals `(-1)^(n+1)` times the independently
  constructed Hom boundary on the unchanged module-valued Ext objects.
  The same equality holds on the original Ext diagrams, filtered colimits,
  and ideal-power local-cohomology objects (`ModuleHomologyRepresentatives.lean`,
  `ProjectiveHomologyExtRepresentatives.lean`, `ProjectiveHomologyExtZero.lean`,
  `ModuleExtCoefficientBoundaryComparison.lean`, `LocalCohomologyBoundaryComparison.lean`)
- [x] **V.1, actual contravariant Hom long exact sequences** into any
  degreewise-injective complex, the original reversed Hom sequence is short
  exact, for both the standard and displayed source differentials. Its actual
  connecting maps have lift-and-differentiate formulas on original cocycles,
  exactness at all three positions, and naturality for morphisms of the
  original short exact sequences, in every integer degree
  (`HomComplexContravariantSequence.lean`, `HomComplexContravariantBoundary.lean`,
  `SourceHomContravariantSequence.lean`, `SourceHomContravariantBoundary.lean`,
  `HomComplexContravariantNaturality.lean`)
- [x] **V.1, actual contravariant derived-boundary comparison** for a
  degreewise-injective K-injective target, the unchanged standard connecting
  map is identified with precomposition by the original derived connecting
  arrow, with exactly `(-1)^(n+1)`. The literal source differential needs no
  extra sign under its fixed unscaled quotient-to-derived-Hom equivalence,
  which is also natural for original precomposition. Actual cone primitives
  establish the comparison on original representatives in every integer degree
  (`HomComplexContravariantConnecting.lean`, `HomComplexHomologyRepresentatives.lean`,
  `HomComplexContravariantBoundary.lean`, `SourceHomContravariantBoundary.lean`,
  `HomComplexContravariantNaturality.lean`)
- [x] **V.1, actual covariant Hom long exact sequences** for arbitrary source
  complex and a coefficient short exact sequence with degreewise-injective
  first term, the original Hom sequence is short exact. Actual degreewise
  splittings are derived from injectivity, not assumed as chain splittings.
  Both standard and literal-source differentials give exactness at every
  position, original lift-and-differentiate boundary formulas, and naturality
  in all integer degrees (`HomComplexCovariantSequence.lean`,
  `HomComplexCovariantBoundary.lean`, `SourceHomCovariantSequence.lean`,
  `SourceHomCovariantBoundary.lean`, `HomComplexCovariantNaturality.lean`)
- [x] **V.1, actual covariant derived-boundary comparison** with K-injective
  endpoint coefficients, the original standard Hom boundary is postcomposition
  by the original derived connecting arrow. The literal-source boundary has
  exactly `(-1)^(n+1)` under the same fixed unscaled quotient equivalence,
  which is also natural for the original coefficient maps
  (`HomComplexCovariantBoundary.lean`, `SourceHomCovariantBoundary.lean`,
  `HomComplexCovariantNaturality.lean`)
- [x] **V.1, original Hom pairing and both boundaries** the original product
  is natural in the middle complex. On actual homology it intertwines the two
  independently constructed Hom connecting maps with factor `(-1)^(j+1)` in
  the standard convention and `(-1)^(i+1)` for the displayed source differential.
  The original composite of lifts is an explicit coboundary; no boundedness,
  K-injectivity, or derived-category comparison is required. The source's
  unsigned connecting-pairing identity is not asserted for these unchanged
  conventions (`HomComplexBoundaryPairing.lean`, `HomComplexPairingNaturality.lean`)
- [x] **V.1, augmented resolution connecting arrow** for a supplied augmented
  short exact sequence of chosen injective resolutions, the original
  augmentation squares identify its derived connecting arrow with the
  original extension class. This is proved by naturality of the actual
  cone-derived boundary, not assumed as extra comparison data
  (`InjectiveResolutionSequence.lean`)
- [x] **V.1, chosen double-resolution boundary comparisons** for that supplied
  augmented exact resolution sequence, the previously specified standard and
  normalized source Ext equivalences identify the actual covariant Hom boundary
  with the original Yoneda boundary and the contravariant one with factor
  `(-1)^(n+1)`, in every natural degree including zero. Original cocycles and
  original augmentations are retained (`InjectiveHomContravariantBoundary.lean`,
  `InjectiveHomCovariantBoundary.lean`)
- [x] **V.1, original module-valued boundary specialization** the unchanged
  canonical linear Ext comparison gives additive-group identifications under
  which the same signed double-resolution identities hold for both previously
  defined module-valued Yoneda boundaries. No boundary is redefined to force
  the comparison (`InjectiveHomModuleExtBoundary.lean`)
- [x] **V.1, injective horseshoe construction** every short exact sequence
  in an abelian category with enough injectives now has an actual augmented
  short exact sequence of injective resolutions. Embed each syzygy sequence
  into a split injective row; the snake lemma proves its actual categorical
  cokernel short exact, allowing iteration. The projected augmentations are
  quasi-isomorphisms, the original maps extend with strictly commuting
  augmentation squares, and the integer-indexed sequence is split in each
  degree. This supplies the sequence data required by the boundary comparisons
  (`InjectiveHorseshoeStep.lean`, `InjectiveHorseshoeComplex.lean`,
  `InjectiveHorseshoe.lean`)
- [x] **V.1, simultaneous row-resolution comparison** split injective rows
  are injective objects of `ShortComplex C`; hence the unchanged horseshoe
  is an injective resolution of the entire original short complex.
  Comparison maps and uniqueness, identity, and composition homotopies preserve
  both horizontal arrows simultaneously (`InjectiveHorseshoeRowInjective.lean`,
  `InjectiveHorseshoeRowResolution.lean`)
- [x] **V.1, actual augmented sequence maps** the projected simultaneous
  comparisons extend to the original integer-indexed resolution sequences
  with strictly commuting augmentation squares. The projected identity and
  composition homotopies also extend to these actual models
  (`InjectiveHorseshoeComparison.lean`)
- [x] **V.1, coherent horseshoe functor** the constructed comparison gives a
  functor on original short exact sequences into the homotopy category of
  complexes of rows, independent of the simultaneous augmentation-compatible
  lift. Change between any two injective resolutions of the entire short
  complex is natural and satisfies the identity and cocycle laws
  (`InjectiveHorseshoeFunctor.lean`)
- [x] **V.1, constructed-map boundary naturality** the existing standard and
  literal-source Hom boundaries commute with the actual constructed sequence
  maps, covariantly and contravariantly in every integer degree. No compatible
  resolution map is assumed (`InjectiveHorseshoeBoundaryNaturality.lean`)
- [x] **V.1, Yoneda pairing** the actual linear derived Ext pairing is
  natural in all three variables and compatible with both original Ext
  long-exact-sequence boundaries (`ExtPairing.lean`). The remaining comparison
  through the original module-valued and double-resolution models is listed below
- [x] **V.2, canonical map** the canonical linear Ext comparison transports
  the pairing to original module-valued Ext. The actual quotient-Ext stages
  define the natural local-duality map, preserving original stage maps
  (`ModuleExtPairing.lean`, `LocalDualityMap.lean`)
- [x] **V.2, regular-local vanishing inputs** actual local cohomology vanishes
  above the Krull dimension for arbitrary coefficient modules. With ring
  coefficients it is concentrated and nonzero in the dimension
  (`RegularLocalVanishing.lean`)
- [x] **V.2, identity and rank-one initial case** evaluation at the original
  identity Ext class retracts the equal-coefficient top-degree map. For the
  rank-one ring module, the original canonical map is an isomorphism, over
  any commutative ring and for any ideal and degree
  (`LocalDualityUnit.lean`, `LocalDualityRing.lean`)
- [x] **V.2.1, top degree for every finite module** the actual canonical map
  is a natural isomorphism in the Krull dimension over a regular local ring.
  Additivity proves the finite-free case; actual finite free covers and
  their finite kernels prove the finite-presentation criterion. Right
  exactness of both original functors follows from the genuine coefficient
  sequence, upper vanishing, canonical degree-zero Ext--Hom comparison,
  and the actual injective dualizing module
  (`FiniteFreeComparison.lean`, `FiniteModuleComparison.lean`,
  `LocalDualityFiniteFree.lean`, `TopLocalCohomologyExactness.lean`,
  `LocalDualityTargetExactness.lean`, `LocalDualityTopFinite.lean`)
- [x] **V.2.1, all complementary degrees** the unchanged canonical map is
  a natural isomorphism for every finite module and every `i+j=n`. Actual
  Yoneda boundaries are transported to the original module-valued Ext
  objects; exactness passes to the actual local-cohomology colimits, with
  original stage maps. Stagewise Yoneda associativity gives compatibility
  with the canonical map. Descending induction uses actual finite free
  covers, their finite kernels, and proved free-module vanishing
  (`ModuleExtYonedaBoundary.lean`, `ModuleExtYonedaExactness.lean`,
  `YonedaExtColimitSequence.lean`, `LocalCohomologyYonedaSequence.lean`,
  `LocalDualityTargetYonedaSequence.lean`, `LocalDualityYonedaCompatibility.lean`,
  `RegularLocalFiniteFreeVanishing.lean`, `KernelComparison.lean`, `LocalDuality.lean`).
  The above-dimension vanishing case is also proved
- [x] **V.3, formula (22), canonical dual comparison** dual local cohomology is the actual
  completion of complementary Ext over every regular local ring, and the
  canonical transpose becomes the original completion map. Over a complete
  regular base the original transpose is an isomorphism, naturally on finite
  modules (`ModuleExtFinite.lean`, `LocalDualityTranspose.lean`,
  `LocalCohomologyDualCompletion.lean`)
- [x] **V.3, regular-local finiteness consequences** all local-cohomology
  values of finite modules are Artinian, with finite actual socle and finite-length
  power annihilators, without completeness of the base. For every supported
  dualizing coefficient their actual Hom duals satisfy the original complete
  category's conditions, and are finite over the original ring if it is complete.
  Their original completions are finite over the actual completed ring without
  completeness of the regular base (`LocalCohomologyFiniteness.lean`). This proves
  the completed finite-generation part of V.3.1(ii) over every regular local base,
  and is generalized to arbitrary noetherian local bases below
- [x] **V.3.1(i), sharp module-dimension upper vanishing** for every finite
  module of support dimension `n` over an arbitrary noetherian local ring,
  original local cohomology vanishes for `i > n`. The proof constructs actual
  dimension-length parameters in the annihilator quotient, lifts them and
  prepends annihilator generators; the genuine consecutive-power Hom--Koszul
  transition is zero above degree `n`. Original radical and Koszul-colimit
  comparisons give the result, without a regularity assumption or Cohen
  reduction (`LocalParameters.lean`, `KoszulAnnihilatorVanishing.lean`,
  `ModuleDimensionVanishing.lean`). The negative-degree convention is not a
  separate assertion about these natural-number-indexed algebraic functors
- [x] **General noetherian-local ring-dimension bound** actual parameters of
  length equal to the ring's Krull dimension give vanishing above that dimension
  for arbitrary coefficient modules, not only finite ones
  (`LocalRingUpperVanishing.lean`)
- [x] **General-local Artinianity** finite original residue Ext is preserved
  through the constructed injective envelopes and their actual cokernels.
  Degree zero is the actual finite socle; higher Ext vanishes on injectives,
  and the genuine coefficient sequence preserves finiteness in the cokernel.
  Induction through the original local-cohomology exact sequence proves full
  Artinianity in every degree for modules with finite residue Ext, in particular
  all finite modules (`FiniteResidueExt.lean`, `LocalCohomologyArtinian.lean`)
- [x] **V.3.1(ii), finite generation over arbitrary noetherian local bases**
  for any actual supported dualizing coefficient, the completed original Hom
  dual of local cohomology is finite over the actual completed ring. Original
  duals satisfy the literal Matlis complete-category conditions and are finite
  over the original ring when it is complete. Actual local-cohomology socles
  are finite, and power annihilators have finite length (`LocalRingFiniteness.lean`).
  No regularity, completeness, or Cohen-presentation hypothesis is imposed
- [x] **V.3.1(ii), dimension bound over arbitrary noetherian local bases**
  the original completed Hom dual in degree `i` has support dimension at most
  `i` over the actual completed ring. Removing the original finite power-torsion
  submodule preserves positive local cohomology through the actual quotient map
  and gives a regular element on that quotient. Original scalar maps remain
  scalar maps on local cohomology. Dualizing the genuine regular-element sequence
  bounds the principal quotient of the higher dual by the lower dual; because
  these duals are already complete, their actual completion maps preserve
  exactness over the completed ring. Induction on degree proves the bound,
  without regularity, completeness, or Cohen reduction
  (`PowerTorsionQuotient.lean`, `PowerTorsionLocalCohomology.lean`,
  `LocalCohomologyLinear.lean`, `LocalCohomologyDualDimension.lean`,
  `ExposeIV/CompletionExactness.lean`, `CompletedDualDimension.lean`)
- [x] **V.3.1(iii), complete-base top-dual dimension and nonvanishing**
  for every finite module of actual support dimension `n` over a complete
  noetherian local ring, the original top local-cohomology Hom dual has
  dimension exactly `n`; the original top local-cohomology object is nonzero.
  Removing actual torsion preserves positive support dimension. Simultaneous
  regular elements on the coefficient and preceding dual torsion quotients
  confine the original dual sequence's error to the closed point, while upper
  vanishing makes the parameter regular on the top dual. Induction gives
  equality without regularity of the base. Degree zero is proved over every
  noetherian local base, through the actual torsion inclusion
  (`ClosedPointSupportDimension.lean`, `SimultaneousRegularElements.lean`,
  `LocalCohomologyDualRegularSequence.lean`, `LocalCohomologyZeroNonvanishing.lean`,
  `CompleteTopLocalCohomology.lean`)
- [x] **V.3.1(iii), top nonvanishing over every noetherian local base**
  the original top local-cohomology object is nonzero without completeness
  or regularity of the ring. More strongly, its original completed Hom dual
  has exactly the original coefficient support dimension over the actual
  completed ring. Prime avoidance of contracted associated primes chooses
  an original scalar regular on the coefficient and preceding completed-dual
  torsion quotients. The actual completion maps preserve the genuine dual
  sequences and scalar injectivity; induction on original coefficient dimension
  gives the equality and nonvanishing, without Cohen reduction or an assumed
  local-cohomology base-change comparison (`CompletionRegularElements.lean`,
  `CompletedDualRegularSequence.lean`, `LocalRingTopNonvanishing.lean`)
- [x] **V.1, arbitrary resolution-model transport** full faithfulness of
  extension by zero recovers the original nonnegative maps from arbitrary
  supplied `InjectiveResolutionSequence` data. Their short exactness and
  augmentation squares are retained; the transposed rows are injective and
  give an actual injective resolution of the entire original short complex
  (`InjectiveResolutionNatMap.lean`, `InjectiveResolutionSequenceNat.lean`,
  `InjectiveResolutionSequenceRows.lean`)
- [x] **V.1, arbitrary-model coherent comparison** every original map lifts
  to an actual augmented comparison between arbitrary supplied resolution
  sequences. Simultaneous row homotopies prove uniqueness, identity, and
  composition; model changes are natural and satisfy the cocycle identity
  (`InjectiveResolutionSequenceComparison.lean`)
- [x] **V.1, fixed Hom/Ext model independence** both existing standard and
  normalized-source equivalences intertwine actual precomposition and
  postcomposition with the original Ext maps in all natural degrees, including
  zero. Augmentation-compatible changes over identities preserve the fixed
  Ext value, also for the unchanged original module-valued Ext objects
  (`InjectiveHomExtNaturality.lean`, `InjectiveHomModuleExtModelChange.lean`)
- [x] **V.1, arbitrary-model boundary naturality** both independently
  constructed Hom boundaries commute with the actual arbitrary-model sequence
  comparisons, for both differential conventions in every integer degree
  (`InjectiveResolutionSequenceNaturality.lean`). None of these comparisons
  is an assumed input to canonical local-duality invertibility
- [x] **V.3.3, actual irreducible component criterion** the original
  left-exact supported functor's actual representing colimit has exactly the
  selected component generic points as associated primes. The original cyclic
  modules `R/p` and III.1.3 prove the criterion; the closed-component support
  formulation is also provided. The original topological components are
  accepted directly, with their generic points constructed rather than
  assumed (`SupportedFunctorAssociatedPrimes.lean`, `SupportedFunctorComponents.lean`,
  `ClosedComponentGenericPoint.lean`)
- [x] **V.3.1(iii), associated-prime formula** the original top Hom dual has
  exactly the dimension-`n` associated primes of the original finite coefficient
  module, even without completeness. Original top local cohomology is right
  exact on the actual bounded supported category. Chains of primes identify
  the top components; nonvanishing identifies the dual's vanishing locus.
  V.3.3 computes IV's actual representing colimit, and the canonical module-lift
  comparison retains the original dual's scalar action. III.1.3 gives the
  formula on the unchanged functor values (`SupportedTopLocalCohomology.lean`,
  `TopDimensionalComponents.lean`, `TopLocalCohomologyDualFunctor.lean`,
  `ExposeIV/LinearFunctorModuleLift.lean`, `TopLocalCohomologyAssociatedPrimes.lean`)
- [x] **V.3.4, affine-complement codimension bound** every actual irreducible
  component of any closed subset with affine complement in a noetherian affine
  spectrum has codimension at most one. Original ordinary cohomology is
  transported through actual homeomorphisms and canonical affine charts;
  quasi-coherent vanishing holds on genuine affine opens. The original relative
  sequence and algebraic comparison imply local-cohomology vanishing above one
  for every coefficient module. The complement localizes to the actual punctured
  spectrum at each component generic point, where original top nonvanishing
  bounds the dimension. The conclusion uses the literal infimum of original
  structure-stalk dimensions, not an assumed codimension comparison
  (`ExposeIII/HomeomorphismCohomology.lean`, `ExposeIII/AffineOpenCohomologyVanishing.lean`,
  `AffineComplementLocalization.lean`, `AffineComplementVanishing.lean`,
  `ClosedComponentGenericPoint.lean`, `AffineComplementCodimension.lean`)
- [x] **V, formula (19), algebraic scalar change** original inverse Koszul
  systems commute with tensor extension, including their power transitions.
  Actual Hom adjunction and exact scalar restriction give the original
  local-cohomology comparison for every ideal and arbitrary coefficient over
  noetherian rings, without flatness. Surjective local-ring maps preserve
  maximal-ideal cohomology, extended length, and finite length
  (`ExposeII/HomotopyCofiberNaturality.lean`, `ExposeII/KoszulScalarChange.lean`,
  `ExposeII/KoszulBaseChange.lean`, `ExposeII/HomComplexScalarChange.lean`,
  `ExposeII/LocalCohomologyScalarChange.lean`, `SurjectiveScalarChange.lean`)
- [x] **V, formula (20), Hom-dual comparison** actual coinduction is dualizing
  over the target; one coefficient-isomorphism choice yields the natural
  comparison of specified Hom duals on all original modules. Combined with
  (19), it compares the actual duals of local cohomology (`SurjectiveDualityChange.lean`)
- [x] **V, formula (21)** the induced ring map identifies the original
  annihilator quotients; finite generation and finite-module support dimension
  are unchanged under the actual restriction (`SurjectiveScalarChange.lean`)
- [x] **V.3.2, general ringed-space module foundations** actual supported
  sections carry their `R(U)`-module structure, and forgetting scalars recovers
  Exposé I's section functor. Forgetting from module sheaves to additive sheaves
  is exact. Injective module sheaves are flasque for arbitrary structure rings.
  The module-valued supported-section functor is left exact and preserves short
  exact sequences with flasque kernel. Its actual right-derived functors vanish
  in positive degrees on every flasque module sheaf, in particular on direct
  images of injective module sheaves without a flatness hypothesis
  (`RingedModuleInjectiveFlasque.lean`, `RingedModuleExactForget.lean`,
  `RingedModuleSupportedSections.lean`, `RingedModulePushforward.lean`,
  `RingedModuleFlasqueAcyclic.lean`)
- [x] **V.3.2, module-valued composite abutment comparison** supported sections
  commute naturally with direct image and actual scalar restriction on every
  open. In all degrees, the right-derived composite is naturally the source's
  module-valued supported cohomology restricted along the structure-sheaf ring
  map; globally this uses the actual map `Γ(Y,S) → Γ(X,R)`
  (`RingedModuleSupportedPushforward.lean`, `RingedModuleCompositeDerived.lean`)
- [x] **V.3.2, original additive cohomology comparison** supported
  sections preserve quasi-isomorphisms between bounded-below flasque complexes,
  by the actual mapping-cone argument. This compares module-injective and
  additive-injective resolutions without assuming that forgetting scalars
  preserves injectivity. In every degree, the additive group of the original
  module-derived supported sections is the original additive-sheaf cohomology,
  globally the preexisting `H_Z`. The unchanged objectwise comparisons are
  now natural in every coefficient map: compatible resolution maps give
  the same derived comparison, hence genuinely homotopic cochain maps
  and equal supported homology maps
  (`ExposeI/IntegerCycleSequences.lean`, `ExposeI/FlasqueAcyclicComplex.lean`,
  `ExposeI/FlasqueQuasiIso.lean`, `ExposeI/KInjectiveDerivedComparison.lean`,
  `ExposeI/InjectiveResolutionIntCohomology.lean`,
  `RingedModuleAdditiveResolution.lean`, `RingedModuleAdditiveCohomology.lean`,
  `RingedModuleAdditiveNaturality.lean`)
- [x] **V.3.2, retained global scalar action** global structure-ring scalars
  act by natural additive-sheaf endomorphisms, hence by actual cochain and
  derived endomorphisms of every module complex. All ring laws and
  compatibility with coefficient cochain maps are proved, including for
  noncommutative structure rings (`RingedModuleGlobalAction.lean`)
- [x] **V.3.2, additive spectral sequence and actual E₂ groups** canonical
  truncations of the actual module direct-image resolution and derived Hom
  from the original integer support object give every page, differential,
  and next-page homology isomorphism. The actual E₂ groups are the original
  `H_Z` of the original higher module direct images, and agree additively
  with their original module-valued supported cohomology. The underlying
  derived object retains the actual target global ring action
  (`RingedModulePushforwardSpectralSequence.lean`)
- [x] **V.3.2, genuine module-valued spectral sequence** additivity of the
  canonical truncation/supported-Hom spectral-object functor retains the full
  scalar ring action. This lifts the actual spectral object, with its original
  exactness, to modules over the target's global structure ring. Every page,
  differential and next-page homology isomorphism is module-valued or linear.
  The canonical forgetful comparison is an isomorphism of the entire original
  additive spectral sequence, respecting its interval maps, cycle projections,
  differentials and unchanged next-page isomorphisms, not only its page terms
  (`ExposeI/SpectralObjectPreadditive.lean`,
  `ExposeI/TruncationSpectralObjectAdditive.lean`, `SpectralObjectModuleAction.lean`,
  `SpectralObjectModulePageComparison.lean`, `SpectralObjectModuleDifferentials.lean`,
  `SpectralSequenceModuleComparison.lean`, `RingedModuleSpectralModuleLift.lean`)
- [x] **V.3.2, first quadrant and canonical finite module filtration**
  connectiveness and t-structure orthogonality give first-quadrant bounds on
  the actual module spectral object. Every page vanishes in either negative
  bidegree. The canonical total object has a finite exhaustive filtration by
  submodules, with zero and whole-module endpoints. In total degree `n ≥ 0`,
  all actual pages with `r ≥ n + 2` identify module-linearly with the genuine
  associated-graded quotients (`RingedModuleSpectralFiltration.lean`)
- [x] **V.3.2, actual module-linear abutment** the canonical localization map
  from Hom-complex homology is natural in arbitrary additive cochain maps and
  bijective for bounded-below flasque complexes. An injective replacement
  proves bijectivity without changing the comparison map. Scalar naturality
  under the homology-forgetful comparison identifies the actual spectral total
  module with the original module-supported complex homology. The original
  composite-derived comparison then identifies it module-linearly with source
  supported cohomology restricted along the prescribed global ring map. Its
  finite exhaustive filtration is transported to submodules of that original
  smaller-universe source cohomology, with both endpoints proved
  (`ExposeI/HomComplexDerivedMap.lean`, `ExposeI/FlasqueComplexDerivedHom.lean`,
  `ModuleComplexScalarHomology.lean`, `RingedModuleSpectralAbutment.lean`)
- [x] **V.3.2, original module-linear E₂ identification** the unchanged
  page-forgetful, first-page, normalized truncation/shift and supported-cohomology
  comparisons intertwine the original scalar endomorphisms. Their composite
  identifies the actual module E₂ page linearly with original module-supported
  cohomology of the original higher module direct image. Its underlying additive
  equivalence is proved to be exactly the preexisting comparison, without
  commutativity or flatness assumptions
  (`ExposeI/NaturalTransformationCohomology.lean`,
  `RingedModuleSpectralE2Scalars.lean`, `RingedModuleCohomologyScalars.lean`,
  `SpectralObjectModuleScalars.lean`, `RingedModuleSpectralE2Linear.lean`)
- [x] **V.3.2, actual module coefficient functor** equivariant maps of the
  original additive spectral objects lift to actual module spectral-object and
  spectral-sequence maps. Their page-forgetful comparisons retain all original
  additive coefficient maps. Resolution homotopies prove lift-independence,
  identity/composition laws, and canonical natural change-of-resolution
  isomorphisms with their cocycle identity
  (`ExposeI/SpectralSequenceCoefficientFunctor.lean`,
  `SpectralObjectModuleCoefficientMaps.lean`, `RingedModuleDerivedCoefficientMaps.lean`,
  `RingedModuleSpectralCoefficientFunctor.lean`)
- [x] **V.3.2, original E₂, abutment and filtered naturality** the unchanged
  module-linear E₂ identification commutes with the original module-supported
  cohomology maps of the original higher module direct images. The unchanged
  abutment identification commutes with source supported-cohomology maps under
  the prescribed restriction of scalars. These actual source maps preserve the
  original finite filtration, which is independent of resolution. The original
  stable-page isomorphisms commute with the genuine associated-graded maps
  (`RingedModuleSpectralE2Naturality.lean`, `RingedModuleSpectralAbutmentNaturality.lean`)
- [ ] **Cohen presentation** the source's presentation theorem remains open;
  it is not assumed in the proved algebraic scalar-change or V.3.1 assertions
- [x] **V.3.5, finite-length duality step** original Hom duality detects finite
  length on arbitrary modules without completeness, preserves extended length,
  and the actual bidual evaluation is invertible when the dual has finite
  length (`ExposeIV/MatlisFiniteLengthDetection.lean`)
- [x] **V.3.5, Ext-localization step** actual degreewise finite projective
  resolutions exist among all modules. Original Hom localization commutes
  with their differentials, giving localized-ring-linear isomorphisms between
  localized original Ext and actual Ext over the localized ring. Only the
  first argument must be finite; actual ring coefficients are included
  (`FiniteProjectiveResolution.lean`, `HomLocalization.lean`, `ModuleExtLocalization.lean`)
- [x] **V.3.5, through complementary Ext** over a regular local ring without
  completeness, original local cohomology and complementary Ext have equal
  extended length. Finite length is equivalent to vanishing of actual
  complementary Ext over every nonclosed prime localization
  (`FiniteLengthLocalization.lean`, `LocalCohomologyFiniteLength.lean`)
- [x] **V.3.5, quotient reduction** the actual induced local ring map is
  surjective and identifies the original localized coefficients after scalar
  restriction. Prime-quotient dimensions agree, closed points correspond, and
  coefficients vanish outside the image. Both the finite-length condition and
  the full shifted punctured vanishing condition are invariant under a quotient
  presentation, without finite-generation hypotheses for this reduction
  (`SurjectiveLocalization.lean`, `LocalCohomologyQuotientTransport.lean`)
- [x] **V.3.6, depth deduction** shifted punctured vanishing through a threshold
  is equivalent to the original localized depth bound over any noetherian local
  ring and finite module. Negative degrees impose no condition, and infinite
  depth is retained. The implication from V.3.5 and quotient invariance of the
  depth condition are proved (`PuncturedDepthCriterion.lean`)
- [x] **V.3.5, full statement** for finite modules over quotients of regular
  local rings, finite length of original local cohomology is equivalent to
  the shifted vanishing of actual local cohomology at every nonclosed point.
  The quotient reduction, localization regularity, and dimension formula
  are all proved; negative shifted degrees are not truncated to degree zero,
  and degrees above the ring dimension use genuine upper vanishing
  (`LocalCohomologyFiniteLengthCriterion.lean`)
- [x] **V.3.5, homological localization input** the actual localized cyclic
  module `R/p` is the actual residue field of `R_p`, linearly over `R_p` and
  with the original map on elements. All modules over every prime localization
  have projective dimension bounded by the original regular ring's dimension.
  (`ResidueFieldLocalization.lean`, `GlobalProjectiveDimension.lean`)
- [x] **V.3.5, regularity of prime localizations** the full homological
  criterion is proved: finite projective dimension of the residue field
  forces a noetherian local ring to be regular. Actual finite free covers
  stay exact modulo a regular element; a cotangent functional splits the
  residue field from the reduced maximal ideal over the quotient ring.
  This lowers the bound, and lifting generators completes induction.
  Every prime localization of a regular local ring is consequently regular,
  with global dimension equal to its own Krull dimension
  (`RegularElementProjectiveDimension.lean`, `HomologicalRegularParameter.lean`,
  `RegularParameterResidueRetract.lean`, `HomologicalRegularityCriterion.lean`)
- [x] **V.3.5, regular-local dimension formula** the actual dimensions satisfy
  `dim R_p + dim(R/p) = dim R`. The top-dual associated-prime formula forces
  complementary Ext of `R/p` to be nonzero at `p`; original Ext localization
  and residue Ext concentration determine the local dimension, without
  a catenarity assumption (`RegularLocalDimensionFormula.lean`)
- [x] **V.3.6, full statement** over quotients of regular local rings,
  finite length through degree `n` is equivalent to the actual punctured
  depth bound, including infinite depth. No additional V.3.5 hypothesis is
  supplied (`LocalCohomologyFiniteLengthCriterion.lean`)
- [x] **VI.1.1, genuine local linear Hom** the local-linear subpresheaf of
  additive internal Hom is a sheaf, by locality of scalar-linearity. Its
  original coefficient functor is additive and left exact; sections are
  actual Hom on the slice category, and global sections are the original
  module-sheaf Hom. Original precomposition maps are also constructed
  (`ExposeVI/ModuleInternalHom.lean`, `ExposeVI/ModuleInternalHomFunctor.lean`,
  `ExposeVI/ModuleGlobalHom.lean`)
- [x] **VI.1.4.3, closed support** the actual supported-section submodules
  form a module sheaf, naturally the original additive support kernel after
  forgetting scalars. The original factorization maps prove
  `Γ_Z(Hom_R(F,G)) ≅ Hom_R(F,Γ̲_Z(G))`, naturally in both variables, with
  a sheaf-level comparison compatible with every open restriction
  (`ExposeVI/ModuleSupportedSheaf.lean`, `ExposeVI/ModuleSupportedHom.lean`)
- [x] **VI.1.1, additive-valued supported Ext** the actual supported Hom
  functors are right-derived in the category of module sheaves, for closed
  and arbitrary locally closed supports. Degree-zero comparisons and
  positive-degree vanishing on injective module sheaves are proved. The
  closed supported-Hom identity gives an all-degree natural comparison of
  the actual derived composites (`ExposeVI/ModuleSupportedExt.lean`)
- [x] **VI.1.5, flasqueness and supported-section acyclicity** every local
  linear map into an injective module presheaf extends globally through the
  open subpresheaf of its source. The genuine Hom sheaf into an injective
  module sheaf is therefore flasque, and its positive closed and locally
  closed supported cohomology vanishes. This does not assume that forgetting
  module structure preserves injectivity (`ExposeVI/ModuleOpenSubpresheaf.lean`,
  `ExposeVI/ModuleHomInjectiveFlasque.lean`)
- [x] **VI.2.3, affine degree-zero algebra** the actual quotient-Hom diagram
  `Hom_R(M/IⁿM,N)` has categorical colimit the ideal-power torsion submodule
  of the original `Hom_R(M,N)`. The comparison retains precomposition by the
  original quotient maps, without noetherianity or finite generation
  (`ExposeVI/AffineHomColimit.lean`)
- [ ] **VI.1 and VI.2, remaining statements** structure-ring module actions
  on internal Hom and derived sheaves; VI.1.2's restriction-derived local Ext
  comparison; excision; the locally closed and tensor/support-object forms
  of VI.1.4; the three spectral sequences; support exact sequences;
  quasi-coherence; and the higher-degree/sheaf comparison of VI.2.3
- [x] **VII** vanishing criteria / Ext̲ coherence (all numbered items of the English
  exposé, affine/algebraic avatars matching Exposé I honesty):
  VII.1.1 sheaf-level Hom/local-cohomology representation
  (`ExposeVII/SupportedExtHomComparison.lean`, affine end in
  `HomSupportAnnihilator.lean`); VII.1.2 equivalent vanishing criteria
  (`VanishingCriteria.lean`); VII.1.3 Hom-vanishing (`HomVanishing.lean`);
  VII.1.4 Cohen–Macaulay depth/codimension
  (`DepthCodimension.lean`, `CohenMacaulayCodimension.lean`); VII.1.5 exact
  transfer (`ExactContravariantCoherence.lean`); VII.1.6–VII.1.7 Ext coherence
  (`SupportedExtCoherence.lean`); VII.2.1 upper vanishing and coherence
  (`RegularUpperExt.lean`, `RegularSupportedExtBounds.lean`); VII.2.2
  dimension-set interval (`DimensionSetInterval.lean`); VII.2.3 coherence
  outside `D(P)` (`ExtCoherenceGap.lean`)
- [x] **VIII scaffold** finite projective-dimension Ext vanishing for VIII.1
  (`ExposeVIII/FiniteProjectiveDimension.lean`); biduality spectral sequences open
- [x] **IX scaffold** adic-completion exactness (`ExposeIX/AdicCompletionExact.lean`);
  formal/algebraic comparisons open
- [x] **X scaffold** connectedness inputs (`ExposeX/ConnectedPiOne.lean`); π₁ Lefschetz open
- [x] **XI scaffold** units / Picard degree-zero input (`ExposeXI/UnitsPicard.lean`);
  Picard Lefschetz open
- [x] **XII scaffold** polynomial-ring inputs (`ExposeXII/ProjectiveSpaceNonempty.lean`);
  projective Lefschetz open
- [x] **XIII scaffold** Krull-dimension comparisons (`ExposeXIII/ProblemsScaffold.lean`);
  conjectures open
- [x] **XIV scaffold** algebraic depth inputs for étale Lefschetz
  (`ExposeXIV/DepthEtaleScaffold.lean`); étale theorems open

Exposés I–VI remain partial; VII is complete at the Exposé I honesty standard;
VIII–XIV have compiling scaffolds with algebraic section modules. Precise scope and missing comparisons are listed in
[`formalization.md`](formalization.md).


---

## Later volumes

- [ ] SGA 3 — Group schemes (three tomes)
- [ ] SGA 4 — Topos theory and étale cohomology of schemes
- [ ] SGA 4½ — Étale cohomology (Deligne)
- [ ] SGA 5 — ℓ-adic cohomology and L-functions
- [ ] SGA 6 — Intersection theory and the Riemann–Roch theorem
- [ ] SGA 7 — Monodromy groups in algebraic geometry
