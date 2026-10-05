# Status

What is in the tree, as a checklist: `[x]` done, `[ ]` not done. Tick a box in
the pull request that lands the work.

- A translation is done when its TeX and PDF are in `translation/SGA<n>/` and
  `make` builds it.
- A Lean item is done when it is proved under `lean/SGA/` with no `sorry`, is
  imported from `lean/SGA.lean`, and `lake build` passes.

An exposé is translated before it is formalized. What the Lean proves, with
declaration names, is in [`formalization.md`](formalization.md); the SGA 1
results that rest on theories quoted from elsewhere are in
[`lean/SGA/Foundations/README.md`](../lean/SGA/Foundations/README.md).

Other English translations of SGA, not part of this project:
[thosgood/sga](https://github.com/thosgood/sga),
[ryankeleti/sga](https://github.com/ryankeleti/sga).

---

## SGA 1 — *Revêtements étales et groupe fondamental*

Source: SMF recomposition, [arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203).
There is no Exposé VII. In the Lean column, "proved" means that every numbered statement is
proved, apart from the restrictions in [`formalization.md`](formalization.md) and the
out-of-scope items in [`lean/SGA/Foundations/README.md`](../lean/SGA/Foundations/README.md).

| Exposé | Title | Translation | Lean |
| --- | --- | --- | --- |
| — | Preface, Introduction, Foreword | full draft in tree | — |
| I | Étale morphisms | full draft in tree, reviewed | proved |
| II | Smooth morphisms: generalities, differential properties | full draft in tree, reviewed | proved |
| III | Smooth morphisms: extension properties | full draft in tree, reviewed | partial |
| IV | Flat morphisms | full draft in tree | proved |
| V | The fundamental group: generalities | full draft in tree | proved |
| VI | Fibered categories and descent | full draft in tree, reviewed | proved |
| VII | *(does not exist)* | | |
| VIII | Faithfully flat descent | full draft in tree | proved |
| IX | Descent of étale morphisms; application to the fundamental group | full draft in tree | partial |
| X | Specialization of the fundamental group | full draft in tree | partial |
| XI | Examples and complements | full draft in tree | proved (out of scope: XI.1.4, reduced to Hodge symmetry; XI.2.1 in characteristic p) |
| XII | Algebraic geometry and analytic geometry | full draft in tree | partial |
| XIII | Cohomological properness (sets and non-commutative groups) | full draft in tree | partial |

"Reviewed": an earlier English version was compared sentence by sentence
with the corrected French and corrected (2026-09-24). The other exposés were
translated chunk by chunk, and a second reader checked each chunk against the
French. No exposé has had a scholarly proofreading. Apparent misprints in the
French are listed in each exposé's README.

### Translation

- [x] **Front matter** — Preface, Introduction (1970), Foreword (1963)
  - [x] English TeX and PDF in `translation/SGA1/Introduction/`
- [x] **I** — Étale morphisms
  - [x] Opening convention and §§1–6: English TeX and PDF in `translation/SGA1/ExposeI/`
  - [x] §§7–11: English TeX and PDF, including all proofs and footnotes
  - [x] Sentence-by-sentence review against the corrected French (2026-09-24)
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeI/README.md`](../translation/SGA1/ExposeI/README.md)
- [x] **II** — Smooth morphisms: generalities, differential properties
  - [x] Opening convention and §§1–5, including errata: English TeX and PDF in `translation/SGA1/ExposeII/`
  - [x] Sentence-by-sentence review against the corrected French (2026-09-24)
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeII/README.md`](../translation/SGA1/ExposeII/README.md)
- [x] **III** — Smooth morphisms: extension properties
  - [x] English TeX in `translation/SGA1/ExposeIII/`
  - [x] PDF in tree (`make tex`)
  - [x] Sentence-by-sentence review against the corrected French; statement numbering fixed (2026-09-24)
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeIII/README.md`](../translation/SGA1/ExposeIII/README.md)
- [x] **IV** — Flat morphisms (`translation/SGA1/ExposeIV/`)
- [x] **V** — The fundamental group: generalities (`translation/SGA1/ExposeV/`)
- [x] **VI** — Fibered categories and descent
  - [x] English TeX in `translation/SGA1/ExposeVI/`
  - [x] PDF in tree (`make tex`)
  - [x] Proofread against the SMF source (labels, diagrams, numbering), 2026-09-24
  - [ ] Scholarly proofreading; source issues recorded in [`ExposeVI/README.md`](../translation/SGA1/ExposeVI/README.md)
- [x] **VIII** — Faithfully flat descent (`translation/SGA1/ExposeVIII/`)
- [x] **IX** — Descent of étale morphisms. Application to the fundamental group (`translation/SGA1/ExposeIX/`)
- [x] **X** — Specialization of the fundamental group (`translation/SGA1/ExposeX/`)
- [x] **XI** — Examples and complements (`translation/SGA1/ExposeXI/`)
- [x] **XII** — Algebraic geometry and analytic geometry (`translation/SGA1/ExposeXII/`)
- [x] **XIII** — Cohomological properness of sheaves of sets and of sheaves of non-commutative groups (`translation/SGA1/ExposeXIII/`)
- [ ] Scholarly proofreading of IV, V, VIII–XIII; source issues recorded in each exposé's README

### Formalization (Lean 4)

Barrels `SGA.SGA1.ExposeI` … `SGA.SGA1.ExposeXIII` and `SGA.Foundations`, all imported by
`lean/SGA.lean`. Conventions: [`lean/SGA/SGA1/CONVENTIONS.md`](../lean/SGA/SGA1/CONVENTIONS.md).
`lake env lean CheckSGA1Axioms.lean` (from `lean/`) checks the axioms. An exposé is ticked when
every numbered statement is proved, possibly with the restrictions listed in
[`formalization.md`](formalization.md).

- [x] Lake project + mathlib pin (`lean/lean-toolchain`, `lean/lakefile.toml`)
- [x] Foundations: prerequisites missing from mathlib (`lean/SGA/Foundations/`)
- [x] **I** Étale morphisms
- [x] **II** Smooth morphisms (II.2.5 and the sufficiency half of II.2.6 not stated)
- [ ] **III** Infinitesimal lifting
  - proved: III.2–III.4, III.7.4
  - in special cases: III.5–III.6
  - not formalized: III.7.1–III.7.3
- [x] **IV** Flat morphisms
- [x] **V** The fundamental group: generalities
- [x] **VI** Fibered categories and descent
- [x] **VIII** Faithfully flat descent
- [ ] **IX** Descent of étale morphisms
  - proved over an arbitrary base: IX.2.6, IX.4.6, IX.4.9, IX.4.12, IX.6.8, IX.6.11
  - partial: IX.1.10 for projective and for integral normal `X`; IX.5.2 in abstract form for
    connected `S'`, `S''`, and for schemes when `S` is noetherian and connected and `g` proper
    surjective; of IX.5.4, only a consequence, under replacement hypotheses
  - not formalized: IX.5.1 for disconnected `S'` or `S''`, IX.5.3, IX.5.5, IX.5.7
- [ ] **X** Specialization of the fundamental group
  - X.2.1–X.2.4 for projective `X`; X.2.1 also for integral normal `X`
  - X.2.9 and X.2.12 for `k` of characteristic 0 with `#k ≤ 𝔠`, in universe 0; out of scope
    otherwise
  - X.3.8 and X.3.9 over a complete DVR with separably closed residue field; X.3.8 is open in
    general
- [x] **XI** Examples and complements. Out of scope (see the Foundations README):
  - XI.1.4, reduced to Hodge symmetry `h^{0,q} = h^{q,0}`, which is open
  - XI.2.1 in characteristic `p`, where it is equivalent to its `p`-primary clause; XI.2.1 is
    proved in characteristic 0, and its `ℓ`-primary clauses for `ℓ ≠ p`
- [ ] **XII** Algebraic geometry and analytic geometry
  - §1 for separated `X`, with the universal property of `X^an` for affine `X` only;
    XII.1.3.1 not formalized
  - §2 except XII.2.5
  - §3 on the spaces of points `X(ℂ)`; for `f^an`, XII.3.1 (i)–(iv), with étale read as flat
    and unramified and smooth as flat with regular fibres, and XII.3.1 (ix), (xi) and
    XII.3.2 (i), (ii) for quasi-compact `f`
  - §4 (GAGA): XII.4.3–XII.4.6 stated, not proved; Oka coherence and Theorem B for `𝒪` on
    `Δ × ℂᵃ × (ℂ*)ᵇ` proved
  - §5: XII.5.2 from XII.5.1 alone; XII.5.1 for schemes over `ℂ` of dimension `≤ 1`, for `ℂ`
    minus finitely many points, and a few other cases, open in higher dimension;
    XII.5.3–XII.5.5 not formalized
- [ ] **XIII** Cohomological properness
  - §1–§4 and Appendix I in part, including XIII 1.4 for sheaves of sets over a locally
    noetherian base, and 3.2 1)
  - the rest of 1.4, 2.12, 2.13, §3, 4.4 and 4.6: see the Foundations README

---

## SGA 2 — *Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz locaux et globaux*

Source: SMF recomposition, [arXiv:math/0511279](https://arxiv.org/abs/math/0511279).
Exposé XIV is by Michèle Raynaud. No SGA 2 exposé has been checked against the French by a
second reader yet.

| Exposé | Title | Translation | Lean |
| --- | --- | --- | --- |
| Intro | Grothendieck’s introduction | full draft in tree | — |
| I | Global and local cohomological invariants relative to a closed subspace | full draft in tree | partial |
| II | Application to quasi-coherent sheaves on preschemes | full draft in tree | partial |
| III | Cohomological invariants and depth | full draft in tree | partial |
| IV | Dualizing modules and functors | full draft in tree | partial |
| V | Local duality and structure of the $H^i(M)$ | full draft in tree | partial |
| VI | The functors $\mathrm{Ext}_Z^\bullet(X;F,G)$ and $\underline{\mathrm{Ext}}_Z^\bullet(F,G)$ | full draft in tree | partial |
| VII | Vanishing criteria; coherence of $\underline{\mathrm{Ext}}^i_Y(F,G)$ | full draft in tree | partial (VII.1.3 only) |
| VIII | The finiteness theorem | full draft in tree | — |
| IX | Algebraic geometry and formal geometry | full draft in tree | — |
| X | Application to the fundamental group | full draft in tree | — |
| XI | Application to the Picard group | full draft in tree | — |
| XII | Applications to projective algebraic schemes | full draft in tree | — |
| XIII | Problems and conjectures | full draft in tree | — |
| XIV | Depth and Lefschetz theorems in étale cohomology | full draft in tree | — |

### Translation

- [x] **Introduction** — Grothendieck’s introduction (`translation/SGA2/Introduction/`)
- [x] **I** — Global and local cohomological invariants relative to a closed subspace (`translation/SGA2/ExposeI/`)
- [x] **II** — Application to quasi-coherent sheaves on preschemes (`translation/SGA2/ExposeII/`)
- [x] **III** — Cohomological invariants and depth (`translation/SGA2/ExposeIII/`)
- [x] **IV** — Dualizing modules and functors (`translation/SGA2/ExposeIV/`)
- [x] **V** — Local duality and structure of the $H^i(M)$ (`translation/SGA2/ExposeV/`)
- [x] **VI** — The functors $\mathrm{Ext}_Z^\bullet(X;F,G)$ and $\underline{\mathrm{Ext}}_Z^\bullet(F,G)$ (`translation/SGA2/ExposeVI/`)
- [x] **VII** — Vanishing criteria; coherence of $\underline{\mathrm{Ext}}^i_Y(F,G)$ (`translation/SGA2/ExposeVII/`)
- [x] **VIII** — The finiteness theorem (`translation/SGA2/ExposeVIII/`)
- [x] **IX** — Algebraic geometry and formal geometry (`translation/SGA2/ExposeIX/`)
- [x] **X** — Application to the fundamental group (`translation/SGA2/ExposeX/`)
- [x] **XI** — Application to the Picard group (`translation/SGA2/ExposeXI/`)
- [x] **XII** — Applications to projective algebraic schemes (`translation/SGA2/ExposeXII/`)
- [x] **XIII** — Problems and conjectures (`translation/SGA2/ExposeXIII/`)
- [x] **XIV** — Depth and Lefschetz theorems in étale cohomology (M. Raynaud) (`translation/SGA2/ExposeXIV/`)
- [ ] Check of every exposé against the French by a second reader
- [ ] Scholarly proofreading; source issues to be recorded in each exposé's README

### Formalization (Lean 4)

Scaffold:

- [x] Root modules `SGA.SGA2.ExposeI`, `SGA.SGA2.ExposeII`, `SGA.SGA2.ExposeIII`,
  `SGA.SGA2.ExposeIV`, `SGA.SGA2.ExposeV`, `SGA.SGA2.ExposeVI`, and `SGA.SGA2.ExposeVII`
  imported from `lean/SGA.lean`
- [x] `lake build` stays green
- [x] `lake env lean CheckSGA2Axioms.lean` checks transitive axiom dependencies
  of all imported SGA 2 declarations

The imported library is checked by `lake build +SGA`, followed by
`lake env lean CheckSGA2Axioms.lean`. The audit includes private declarations
and transitive dependencies and permits only `propext`, `Classical.choice`,
and `Quot.sound`. Successful compilation and this axiom audit establish proof
validity for the imported statements; coverage still follows the section
checklist below.

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
- [x] **I.1.1–I.1.7** remaining internal Hom identities and ringed-space statements:
  first-variable precomposition of Hom and sheaf Ext
  (`InternalHomPrecomposition.lean`, `InternalHomBifunctor.lean`:
  `abelianSheafHomPrecomp`, `internalSheafExtPrecomp`);
  nested-open local Ext restriction
  (`SheafExtRestriction.lean`: `localExtRestriction`,
  `internalExtPresheafSectionsEquiv_restrict`);
  connecting maps of local Ext
  (`SheafExtConnecting.lean`: `localExtδ`, `restrictToOpen_map_shortExact`);
  ringed-space I.1.6/I.1.7
  (`RingedSpaceSupportHom.lean`: `ringedSpaceSupportHomEquiv`)
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
- [x] **I.2.6, comparison refinements** the constructed sequence is the
  Grothendieck spectral sequence of the supported-sheaf functor
  (`OpenInclusionLeray.lean`: `grothendieckSpectralSequenceOfSupportedSheaf`,
  `openInclusionLerayE2Equiv`); spectral-level locally closed witness change
  (`LocallyClosedWitnessChangeSpectral.lean`:
  `locallyClosedTruncationSpectralSequenceE2WitnessEquiv`);
  closed supports as locally closed witnesses
  (`ClosedAsLocallyClosed.lean`: `LocallyClosedIn.ofClosed`)
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
- [x] **II.3, closed support in degree zero** actual supported-module sheaves
  of quasi-coherent modules are quasi-coherent on locally noetherian schemes
  (`ExposeVI/QuasiCoherentSupportedModules.lean`: `schemeModuleGammaZ_isQuasicoherent`)
- [ ] **II.1–II.3** quasi-coherence of higher supported cohomology sheaves
  on general schemes (mathlib higher direct images of quasi-coherent modules
  under quasi-compact open immersions). Open-support identification
  `II_1_open` and affine-chart restriction `II_3_restriction` are proved.
- [x] **II.4 / II.7, noetherian affine** the local-to-global spectral sequence
  degenerates by ordinary affine vanishing
  (`AffineExtColimitComparison.lean`: `II_7_affine_ordinary_vanishing`)
- [x] **II.5** stable Koszul cohomology of an arbitrary finite family agrees
  with topological supported cohomology on a noetherian affine, in every
  degree; degree zero holds without noetherianity
  (`KoszulSupportedComparison.lean`: `II_5`, `II_5_addEquiv`, `II_5_zero`)
- [x] **II.6–II.7, noetherian affine** Ext-colimit / algebraic local cohomology
  agrees with supported sheaf cohomology; the sheaf comparison of II.6.a is
  this identification (`AffineExtColimitComparison.lean`: `II_6_a_affine`,
  `II_6_b_affine`)
- [ ] **II.6–II.7, general schemes** sheaf Ext colimits
  `colim SheafExt(𝒪/Iⁿ, F) ≅ SheafH_Y(F)` and the local-to-global argument
  off affines. The noetherian affine case remains `II_6_a_affine` /
  `II_6_b_affine`.
- [x] **II.(7.3), noetherian affine case** actual algebraic local cohomology
  agrees with actual supported sheaf cohomology in every degree, naturally in
  arbitrary coefficient modules and compatibly with every coefficient boundary
  (`AffineCohomologyComparison.lean`)
- [x] **II.(7.3)–(7.6)** cofinal ideal-power reindexing and the resulting
  canonical Ext-to-Koszul comparison commute with actual coefficient boundaries
  (`LocalCohomologyReindexing.lean`, `KoszulLocalCohomologySequence.lean`)
- [x] **II.10, noetherian ring** injective associated sheaves are flasque,
  hence positive Koszul groups vanish on injectives via II.5
  (`TopologicalNoetherianFlasque.lean`: `II_10_koszul_vanishing_of_injective`,
  `II_10_flasque_implies_koszul`)
- [ ] **II.10, topological noetherianity only** the same flasque criterion
  when `Spec A` is a noetherian space but `A` need not be a noetherian ring

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
- [x] **III.3.3(v)/(vi), affine** module Ext criteria for depth
  (`SheafExtDepth.lean`: `III_3_3_v`, `III_3_3_vi`, `III_3_3_vi_quotient`)
- [ ] **III.3.3(v)/(vi), sheaf Ext** vanishing of `SheafExt^i_𝒪(G,F)` for
  coherent `G` supported on `Y`, on a general locally noetherian scheme
- [x] **III.3.7, complements** under the depth/dimension hypothesis,
  removing a closed set of local dimension `≥ d` induces a bijection on
  connected components (`ConnectednessInCodimension.lean`:
  `III_3_7_complement`, `III_3_7_of_minDim`)
- [x] **III.3.7, component chain** an actual finite chain of irreducible
  components with `codim(X_i ∩ X_{i+1}) ≤ d-1`, using the infimum of actual
  structure-stalk dimensions (`ComponentChains.lean`: `III_3_7`,
  `III_3_7_list`, `III_3_7_codimension_list`)
- [x] **III.3.8, antifilter** of closed sets and finiteness of irreducible
  components (`AntifilterConnectedness.lean`: `ClosedAntifilter`)
- [x] **III.3.8, dual graph** on a connected noetherian space any two
  irreducible components are joinable by a chain of adjacent components
  (`AntifilterEquivalence.lean`: `exists_irreducibleComponents_connected_chain`)
- [x] **III.3.8, (ii) ⇒ (i)** a component chain with consecutive
  intersections outside the antifilter implies complements of members are
  preconnected (`AntifilterEquivalence.lean`: `III_3_8_ii_implies_i`)
- [x] **III.3.8, full equivalence** on a locally noetherian space,
  local membership in the antifilter and connectedness of complements give
  chains with `X_i ∩ X_{i+1} ∉ Ff` (`III_3_8_i_implies_ii`, `III_3_8`)
- [x] **III.3.9** equidimensionality of `Spec A` from the actual localized
  depth/dimension hypothesis and the prime-chain condition. Equality of lengths
  of saturated chains proves the needed adjacent-component dimension comparison
  (`Catenary.lean`, `EquidimensionalityCriterion.lean`: `III_3_9`)
- [x] **III.3.10** if removing a closed set fails to induce a bijection on
  connected components, some point of the closed set has depth `< 2`
  (`ConnectednessInCodimension.lean`: `III_3_10_depth_lt_two`)
- [x] **III.3.12** higher supported vanishing above the number of equations,
  detected on the structure sheaf
  (`HigherVanishingOnStructure.lean`: `III_3_12`, `III_3_12_koszul`,
  `III_3_12_structure`)
- [x] **III.3.13, principal curve / non-UFD / relative vanishing**
  vanishing above one equation, a non-principal height-one prime in a
  non-UFD noetherian domain, and the relative comparison
  `H_Y^{n+2}(𝒪) ≅ H^{n+1}(X-Y, 𝒪)` on a noetherian affine
  (`ExamplesIII313.lean`: `III_3_13_principal`,
  `III_3_13_exists_non_principal`, `III_3_13_relative`)
- [ ] **III.3.13, normal surface** existence of a curve on a normal
  2-dimensional local ring that is not cut by one equation and whose
  complement is affine

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

- [x] **V.1** Displayed Hom complex, composition, both long exact sequences,
  naturality in all three complexes, and signed comparisons with Yoneda Ext;
  injective horseshoes and coherent changes of chosen resolutions.
- [x] **V.2.1** Canonical local duality, naturally in finite modules over
  regular local rings, in every complementary degree.
- [x] **V, formula (22)** Dual local cohomology is completed complementary
  Ext; over a complete regular base, the canonical transpose is invertible.
- [x] **V.3.1(i)** Vanishing above the coefficient support dimension; the
  ring-dimension bound also holds for arbitrary coefficient modules.
- [x] **V.3.1(ii)** Artinianity of local cohomology, completed-dual finite
  generation, and the dual dimension bound over noetherian local rings.
- [x] **V.3.1, support criteria** Conditions (a)–(c) after formula (22)
  and the Ext support-dimension/codimension bounds, including empty support.
- [x] **V.3.1(iii)** Top nonvanishing, completed top-dual dimension, and the
  associated-prime formula. Over complete bases the dual itself is finite
  with the stated dimension.
- [x] **V.3.2** Module-valued spectral sequence for closed supports, with
  E₂, source abutment, finite convergence filtration, additive coefficient
  maps, and coherent, filtration-preserving changes of resolution.
- [x] **V.3.3** Associated primes of the representing module from actual
  irreducible component families and the functor's vanishing criterion.
- [x] **V.3.4** Every component of a closed subset with affine complement
  has codimension at most one.
- [x] **V.3.5–V.3.6** Finite-length and punctured-depth criteria over
  quotients of regular local rings, including the localization regularity,
  dimension formula, and scalar-change arguments.
- [ ] **Cohen presentation** The source's reduction to a regular local
  ring is not formalized. The general local-ring results above use direct
  proofs and do not assume this theorem.

The module map and sign conventions are in `lean/SGA/SGA2/ExposeV.lean`;
[`formalization.md`](formalization.md) records the individual declarations
and precise scope. Negative-degree algebraic local cohomology is not
separately constructed; negative shifts in the punctured criteria are vacuous.

Exposé VI:

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
- [x] **VI.1.1, module-valued Ext** ordinary and arbitrarily locally supported
  sheaf Ext have actual local module structures; global supported Ext has its
  global-ring module structure. Exact-forgetting comparisons recover the
  unchanged additive constructions (`ModuleSheafExtLinear.lean`,
  `ModuleLocallyClosedSheafExtLinear.lean`)
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
- [x] **VI.1.2, actual local values and sheafification** ordinary and locally
  supported Ext are computed in the actual module categories of the opens;
  their presheaves sheafify to the original supported sheaf Ext
  (`moduleExtPresheafEvalIso`, `moduleLocallySupportedExtPresheafEvalIso`,
  `moduleLocallySupportedExtSheafificationIso`)
- [ ] **VI.1.2–1.3, higher-map compatibility** explicit agreement with
  higher Ext maps between nested opens and with coefficient connecting maps
- [x] **I.1.7 / VI ringed Hom** maps from the structure sheaf into a
  supported module sheaf recover supported sections
  (`ExposeI/RingedSpaceSupportHom.lean`: `ringedSpaceSupportHomEquiv`)
- [x] **VI.1.3, all degrees** coefficient-natural excision of actual supported
  module Ext for every locally closed support and every open neighborhood
  (`ModuleOpenRestrictionLocallyClosed.lean`: `VI_1_3`)
- [x] **VI.1.4.1 / VI.1.4.3, closed support** actual structure-module Hom
  representation and supported factorization (`VI_1_4_1`, `VI_1_4_3`)
- [x] **VI.1.4.1–2, arbitrary locally closed support** the actual sheafified tensor
  `𝒪_{X,Z} ⊗ F` represents supported Hom, naturally in both variables;
  `moduleLocallyClosedSupportedExtTensorIso` gives the all-degree Ext comparison,
  whose actual coefficient and source naturality are proved
- [ ] **VI.1.4, connecting maps** compatibility of the tensor comparison with
  the source and coefficient connecting morphisms
- [x] **VI.1.5, supported-module injectives** the actual closed module-support
  functor preserves injectives through a proved mono-preserving quotient left adjoint
- [x] **VI.1.4.3 / VI.1.5, locally closed support** the actual module-valued
  support functor has its natural Hom factorization and preserves injectives
  through its proved closed-support, restriction and direct-image decomposition
- [x] **VI.1.6.1–2** genuine coefficient spectral functors for arbitrary locally
  closed support, with original E₂ identifications and Ext abutments, finite
  filtrations and stable-page quotient comparisons
- [x] **VI.1.6.3, closed support** the corresponding genuine spectral functor
  with E₂ `Ext^p(F, SheafH_Z^q(G))` and actual supported Ext abutment
- [x] **VI.1.6.3, locally closed support** genuine spectral functor with
  E₂ `Ext^p(F, SheafH_W^q(G))` and original locally supported Ext abutment,
  with coefficient naturality of E₂ and abutment
  (`ModuleLocallyClosedSupportSpectralSequence.lean`,
  `ModuleLocallyClosedSupportSpectralNaturality.lean`,
  `ModuleEndofunctorSpectralAbutmentNaturality.lean`)
- [x] **VI.1.7** the actual module support-object short exact sequence and its
  tensor version, with the original source maps
  (`ModuleSupportObjectSequence.lean`, `TensorSupportObjectSequence.lean`,
  `SheafTensorFunctor.lean`, `ExposeI/RepresentedFunctorSequence.lean`)
- [x] **VI.1.8** genuine long exact sequences of the original supported
  Ext groups and supported sheaf Ext, for every locally closed support and
  every closed subset of its literal support space. The actual inclusion,
  restriction and connecting maps are natural in both module arguments;
  degree-zero maps are the original Hom maps (`VI_1_8_exact`,
  `VI_1_8_sheaf_exact`, `ExtSequenceFirstVariable.lean`)
- [x] **VI.1.9, sequence and endpoints** the transported original sequence
  is exact with actual closed-supported Ext, ordinary ambient Ext, and ordinary
  Ext of the restricted modules. Its degree-zero restriction agrees with
  actual Hom.over under the standard Ext₀ = Hom comparison
  (`ModuleRelativeExtSequence.lean`, `ModuleRelativeExtCompatibility.lean`)
- [x] **VI.1.9, standard higher restriction** the transported restriction
  agrees with the independent map induced by the exact restriction functor
  in every degree (`moduleRelativeExtRestriction_eq_functor` in
  `ModuleRelativeExtCompatibility.lean`; `ExposeI/ExtRightDerivedMap.lean`)
- [x] **VI.2.3, affine degree zero / structure sheaf** quotient-Hom colimit
  and Ext-colimit of `R/I^n` (`VI_2_3_zero`, `VI_2_3_structure`,
  `VI_2_3_sheaf`)
- [ ] **VI.2.3** `colim Ext(M/I^n M, N) → Ext_Y(X; F, G)` for general
  coherent `F` on a locally noetherian scheme
- [x] **VI.2.1, degree zero** quasi-coherence of supported Hom and sheaf Ext⁰
  for coherent source and quasi-coherent coefficients on locally noetherian
  schemes (`QuasiCoherentSupportedModules.lean`:
  `coherent_closedSupportedHom_isQuasicoherent`,
  `coherent_closedSheafExtZero_isQuasicoherent`)
- [ ] **VI.2.1** quasi-coherence of higher supported sheaf Ext for coherent
  source and quasi-coherent coefficients
- [x] **VI.2.1, affine ordinary Hom prerequisite** actual internal Hom
  is canonically the associated sheaf of module Hom when the source module
  is finitely presented, over any commutative ring (`AffineInternalHom.lean`)
- [x] **VI.2.1, ordinary Hom on schemes** actual internal Hom commutes with
  open restriction and is quasi-coherent for coherent source and quasi-coherent
  target on locally noetherian schemes (`CoherentInternalHom.lean`)
- [x] **VII.1.3, locally noetherian schemes** actual internal Hom detects an
  arbitrary quasi-coherent target whose literal stalk support is contained in
  that of a coherent source (`VII_1_3_locallyNoetherian`)
- [ ] **VII, remaining statements** general VII.1.3 without local
  noetherianity; vanishing criteria and coherence results
- [ ] **VIII–XIV** no Lean formalization yet

All seven started exposés remain partial. Precise scope and missing comparisons are listed
in [`formalization.md`](formalization.md).


---

## Later volumes

- [x] SGA 3 English — Group schemes (three tomes): foreword, introduction and Exposés I–XXVI, translated from the Gille–Polo recomposition; individual PDFs and a combined volume build with `make tex`. Indexes not included; not yet independently reviewed. See [`translation/SGA3/README.md`](../translation/SGA3/README.md).
- [ ] SGA 4 — Topos theory and étale cohomology of schemes
- [ ] SGA 4½ — Étale cohomology (Deligne)
- [ ] SGA 5 — ℓ-adic cohomology and L-functions
- [ ] SGA 6 — Intersection theory and the Riemann–Roch theorem
- [ ] SGA 7 — Monodromy groups in algebraic geometry
