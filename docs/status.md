# Status

Translation of an exposé comes **before** Lean for that exposé.
Tick a box in the same PR that lands the work.

Convention: `[x]` is in the tree; `[ ]` is not. A translation counts as
ticked when TeX + PDF are in `translation/SGA…/` and `make` builds.
A Lean item counts as ticked when the statement lives under `lean/SGA/`
with no `sorry`, is imported from `lean/SGA.lean`, and `lake build` passes.

## Order of work

1. Keep the SGA 1 VI translation compiling (`make tex`).
2. Formalize SGA 1 VI against mathlib, section by section, starting
   from `lean/SGA/SGA1/ExposeVI.lean`.
3. Translate further exposés of SGA 1 (I–V, VIII–XIII), then formalize
   each after its English text is in the tree.
4. Only then: later SGA volumes, if the same tree still fits.

Related public translations (not this project):
[thosgood/sga](https://github.com/thosgood/sga),
[ryankeleti/sga](https://github.com/ryankeleti/sga).

---

## SGA 1 — *Revêtements étales et groupe fondamental*

Source: SMF recomposition, [arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203).
Exposé VII does not exist.

| Exposé | Title | Translation | Lean |
| --- | --- | --- | --- |
| I | Étale morphisms | — | — |
| II | Smooth morphisms: generalities, differential properties | — | — |
| III | Smooth morphisms: extension properties | — | — |
| IV | Flat morphisms | — | — |
| V | The fundamental group: generalities | — | — |
| **VI** | **Fibered categories and descent** | **draft in tree** | **scaffold** |
| VII | *(does not exist)* | | |
| VIII | Faithfully flat descent | — | — |
| IX | Descent of étale morphisms; application to the fundamental group | — | — |
| X | Specialization of the fundamental group | — | — |
| XI | Examples and complements | — | — |
| XII | Algebraic geometry and analytic geometry | — | — |
| XIII | Cohomological properness (sets and non-commutative groups) | — | — |

### Translation

- [ ] **I** — Étale morphisms
- [ ] **II** — Smooth morphisms: generalities, differential properties
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
- [x] Root module `SGA.SGA1.ExposeVI` imports mathlib fibered categories / descent
- [ ] `lake build` on `main` stays green as files are added

By section (English: `translation/SGA1/ExposeVI/`, Lean: `lean/SGA/SGA1/`):

- [ ] **VI.0** Introduction (no mathematics to formalize)
- [ ] **VI.1** Universes, categories, equivalence of categories
- [ ] **VI.2** Categories over another
- [ ] **VI.3** Change of base in categories over *E*
- [ ] **VI.4** Fiber-categories; equivalence of categories over *E*
- [ ] **VI.5** Cartesian morphisms, inverse images, cartesian functors
- [ ] **VI.6** Fibered and prefibered categories
  - [ ] VI.6.1 Fib I / Fib II (`IsPreFibered`, `IsFibered` — already in mathlib; record the numbering)
  - [ ] Fibered in groupoids (remark after VI.6.1)
- [ ] **VI.7** Cloven categories over *E*
- [ ] **VI.8** Cloven category defined by a pseudofunctor
- [ ] **VI.9** Example: cloven category defined by a functor
- [ ] **VI.10** Cofibered categories, bifibered categories
- [ ] **VI.11** Various examples
- [ ] **VI.12** Functors on a cloven category

Other exposés of SGA 1: start only after the corresponding English text
is ticked above.

---

## Later volumes

Leave these until SGA 1 has more than one exposé translated.

- [ ] SGA 2 — Local cohomology of coherent sheaves; local and global Lefschetz theorems
- [ ] SGA 3 — Group schemes (three tomes)
- [ ] SGA 4 — Topos theory and étale cohomology of schemes
- [ ] SGA 4½ — Étale cohomology (Deligne)
- [ ] SGA 5 — ℓ-adic cohomology and L-functions
- [ ] SGA 6 — Intersection theory and the Riemann–Roch theorem
- [ ] SGA 7 — Monodromy groups in algebraic geometry
