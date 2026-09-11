# Checklist

Tick a box in the same PR that lands the work. Translation of an exposé
comes **before** Lean for that exposé.

Convention: `[x]` is in the tree; `[ ]` is not. A translation counts as
ticked when TeX + PDF are in `translation/SGA…/` and `make` builds.
A Lean item counts as ticked when the statement lives under `SGA/` with
no `sorry`, imported from `SGA.lean`, and `lake build` passes.

---

## Translation

### SGA 1 — *Revêtements étales et groupe fondamental*

Source: SMF recomposition, [arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203).
Exposé VII does not exist.

- [ ] **I** — Étale morphisms
- [ ] **II** — Smooth morphisms: generalities, differential properties
- [ ] **III** — Smooth morphisms: extension properties
- [ ] **IV** — Flat morphisms
- [ ] **V** — The fundamental group: generalities
- [x] **VI** — Fibered categories and descent
  - [x] English TeX in `translation/SGA1/ExposeVI/`
  - [x] PDF in tree (`make` in that directory)
  - [ ] Proofread against the SMF source (labels, diagrams, numbering)
- [ ] **VIII** — Faithfully flat descent
- [ ] **IX** — Descent of étale morphisms. Application to the fundamental group
- [ ] **X** — Specialization of the fundamental group
- [ ] **XI** — Examples and complements
- [ ] **XII** — Algebraic geometry and analytic geometry
- [ ] **XIII** — Cohomological properness of sheaves of sets and of sheaves of non-commutative groups

### Later volumes

Leave these until SGA 1 has more than one exposé translated.

- [ ] SGA 2 — Local cohomology of coherent sheaves; local and global Lefschetz theorems
- [ ] SGA 3 — Group schemes (three tomes)
- [ ] SGA 4 — Topos theory and étale cohomology of schemes
- [ ] SGA 4½ — Étale cohomology (Deligne)
- [ ] SGA 5 — ℓ-adic cohomology and L-functions
- [ ] SGA 6 — Intersection theory and the Riemann–Roch theorem
- [ ] SGA 7 — Monodromy groups in algebraic geometry

---

## Formalization (Lean 4)

Mathlib already has much of the language of Exposé VI. Import it; do not
copy it. Details: [`docs/FORMALIZATION.md`](docs/FORMALIZATION.md).

### Scaffold

- [x] Lake project + mathlib pin (`lean-toolchain`, `lakefile.toml`)
- [x] Root module `SGA.SGA1.ExposeVI` imports mathlib fibered categories / descent
- [ ] `lake build` on `main` stays green as files are added

### SGA 1, Exposé VI — by section

English text: `translation/SGA1/ExposeVI/`.
Lean files: `SGA/SGA1/ExposeVI/`.

- [ ] **VI.0** Introduction (no mathematics to formalize)
- [ ] **VI.1** Universes, categories, equivalence of categories
- [ ] **VI.2** Categories over another
- [ ] **VI.3** Change of base in categories over *E*
- [ ] **VI.4** Fiber-categories; equivalence of categories over *E*
- [ ] **VI.5** Cartesian morphisms, inverse images, cartesian functors
- [ ] **VI.6** Fibered and prefibered categories
  - [ ] VI.6.1 Fib I / Fib II (`IsPreFibered`, `IsFibered` — already in mathlib; record the numbering)
  - [ ] Fibered in groupoids (remark after VI.6.1)
- [ ] **VI.7** Cloven categories over \(\mathcal{E}\)
- [ ] **VI.8** Cloven category defined by a pseudofunctor
- [ ] **VI.9** Example: cloven category defined by a functor
- [ ] **VI.10** Cofibered categories, bifibered categories
- [ ] **VI.11** Various examples
- [ ] **VI.12** Functors on a cloven category

### Other exposés of SGA 1

Start only after the corresponding English text is ticked above.

- [ ] I
- [ ] II
- [ ] III
- [ ] IV
- [ ] V
- [ ] VIII
- [ ] IX
- [ ] X
- [ ] XI
- [ ] XII
- [ ] XIII
