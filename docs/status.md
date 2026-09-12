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
3. Translate further exposés of SGA 1 (III–V, VIII–XIII), then formalize
   each after its English text is in the tree.
4. SGA 2 English drafts proceed in parallel with remaining SGA 1
   exposés; Lean for SGA 2 waits until the corresponding English is
   ticked.

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
| III | Smooth morphisms: extension properties | — | — |
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
- [ ] **III** — Smooth morphisms: extension properties
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
- [x] **VI.6** Fibered and prefibered categories
  - [x] VI.6.1 Fib I / Fib II (`IsPreFibered`, `IsFibered` — mathlib; numbering in `Fibered.lean`)
  - [x] Fibered in groupoids (remark after VI.6.1, with prefiberedness; `Groupoids.lean`)
  - [x] VI.6.2 based equivalence preserves (pre)fiberedness (`FiberedProducts.lean`)
  - [x] VI.6.11–13 (`Fibered.lean`)
- [x] **VI.7** Cloven categories over *E* (`Cleavage.lean`: cleavage, comparison `c_{f,g}`)
- [x] **VI.8** Cloven category defined by a pseudofunctor (`Split.lean`, mathlib `∫ᶜ`)
- [x] **VI.9** Example: cloven category defined by a functor (`SplitFibered`)
- [x] **VI.10** Cofibered categories, bifibered categories (`Cofibered.lean`)
- [x] **VI.11** Various examples (discrete base in `BaseExamples.lean`; finite checks in `Examples.lean`)
- [x] **VI.12** Functors on a cloven category (`ClovenFunctors.lean`: fiber functors and constraints)

Gaps still open inside those files are listed in [`formalization.md`](formalization.md).

### SGA 1 I — Étale morphisms

English: `translation/SGA1/ExposeI/`. Lean: `lean/SGA/SGA1/ExposeI.lean`.
Section files compile and have no `sorry`. That is **not** a complete
formalization of every numbered statement; remaining items are unchecked
below and in [`formalization.md`](formalization.md).

- [x] **I.1** Differential calculus (`Differentials.lean`: `Ω[S⁄R]`, principal parts)
- [x] **I.2** Quasi-finite morphisms (`QuasiFinite.lean`: isolated in the fibre; artinian I.2.2)
  - [ ] I.2.1(iii): quasi-finite via finiteness of completions
- [x] **I.3** Unramified / net morphisms (`Unramified.lean`: TFAE, graph, stability)
  - [ ] I.3.7: unramified iff the map of completions is a quotient
- [x] **I.4** Étale morphisms and coverings (`Etale.lean`: flat + unramified; stability)
  - [ ] I.4.2–I.4.4: étale detected on completions
  - [ ] I.4.10: discriminant / trace pairing
- [x] **I.5** Fundamental property (`Fundamental.lean`: I.5.1 étale + radicial = open immersion)
  - [ ] I.5.3–I.5.4 in full (iso onto a connected component; morphisms agreeing at a point)
  - [ ] I.5.5 existence of the lifted morphism (uniqueness is proved)
  - [ ] I.5.7–I.5.9 fibrewise criteria
- [x] **I.6** Complete local rings (`CompleteLocal.lean`: artinian I.6.2)
  - [ ] I.6.1 over a complete local ring
- [x] **I.7** Standard étale presentations (`StandardEtale.lean`: I.7.4, I.7.6–I.7.8)
  - [ ] I.7.1–I.7.3, I.7.5, I.7.9–I.7.10
- [x] **I.8** Infinitesimal lifting (`Infinitesimal.lean`: uniqueness half of I.8.3)
  - [ ] I.8.1–I.8.2 local existence; I.8.3 essential surjectivity; I.8.4 formal schemes
- [x] **I.9** Permanence (`Permanence.lean`: reducedness over a field; integral closure)
  - [ ] I.9.1 regularity; I.9.2–I.9.4 reduced in general; I.9.5 normality; I.9.10–I.9.12
- [x] **I.10** Coverings of a normal scheme (`NormalCoverings.lean`: ZMT input, finite fibres)
  - [ ] I.10.1–I.10.3, I.10.7–I.10.12 counting geometric fibre points
- [x] **I.11** Geometrically unibranch (`Unibranch.lean`: definition)
  - [ ] I.11 examples; étale descent along a universal homeomorphism (IX.4.10)

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
| I | Global and local cohomological invariants relative to a closed subspace | full draft in tree | — |
| II | Application to quasi-coherent sheaves on preschemes | full draft in tree | — |
| III | Cohomological invariants and depth | full draft in tree | — |
| IV | Dualizing modules and functors | full draft in tree | — |
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

Lean for SGA 2 is not started.

---

## Later volumes

- [ ] SGA 3 — Group schemes (three tomes)
- [ ] SGA 4 — Topos theory and étale cohomology of schemes
- [ ] SGA 4½ — Étale cohomology (Deligne)
- [ ] SGA 5 — ℓ-adic cohomology and L-functions
- [ ] SGA 6 — Intersection theory and the Riemann–Roch theorem
- [ ] SGA 7 — Monodromy groups in algebraic geometry
