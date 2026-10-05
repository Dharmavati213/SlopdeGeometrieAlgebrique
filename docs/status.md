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
  - X.3.8 and X.3.9 over every locally noetherian base
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
| V | Local duality and structure of the $H^i(M)$ | full draft in tree | proved |
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

Barrels `SGA.SGA2.ExposeI` … `SGA.SGA2.ExposeVII`, imported by `lean/SGA.lean`.
`lake env lean CheckSGA2Axioms.lean` (from `lean/`) checks the axioms of every imported SGA 2
declaration. A sub-item is ticked when the Lean proves it as SGA states it, or with the
restrictions noted; details in [`formalization.md`](formalization.md).

- [ ] **I** Global and local cohomological invariants relative to a closed subspace (partial; detail in [`formalization.md`](formalization.md))
  - [x] **I.1** `Γ_Z` and `Γ̲_Z` for closed and locally closed `Z`, independent of the open; composition (13) and the sequence (17)
  - [ ] **I.1.1–I.1.2** `i^!(F)` and `i_!(G)` as subsheaves of `i^*(F)` and `i_*(G)` (the functors are constructed directly)
  - [x] **I.1.3–I.1.4, I.1.6** `i_! ⊣ i^!`; `i^!` and `Γ̲_Z` preserve injectives; `Γ_Z = Hom(ℤ_{Z,X}, −)`, `Γ̲_Z = ℋom(ℤ_{Z,X}, −)`
  - [ ] **I.1.5** `ℋom(i_!G, F) = i_*ℋom(G, i^!F)`: only for `G = ℤ_Z`
  - [ ] **I.1.7** Modules: I.1.6 only; the module `i_! ⊣ i^!` and I.1.5 are missing
  - [x] **I.1.8–I.1.10** nested-support sequences of supported sections, supported sheaves and `ℤ_{Z,X}`
  - [x] **I.2.1–I.2.5** `H_Z^*` and `ℋ_Z^*` as derived functors and as Ext; excision; sheafification; open supports
  - [x] **I.2.6–I.2.7** local-to-global spectral sequence for locally closed `Z`, functorial and convergent; support bounds; E₂ computed on `Z̄`
  - [ ] **I.2.6–I.2.7, comparisons** with the Leray spectral sequence for open `Z`, and between two presentations of `Z`: E₂ terms only
  - [x] **I.2.8–I.2.14** long exact sequences, the formulas of I.2.11, flasque acyclicity and its converse, restriction criteria
  - [ ] **I.2.8 and I.2.10** the sheaf sequence as the sheafification of the group sequence (connecting maps)
  - [ ] **Remark after I.2.14** normal orientation sheaf and Gysin map, (30)–(32)
- [ ] **II** Application to quasi-coherent sheaves on preschemes (partial; detail in [`formalization.md`](formalization.md))
  - [ ] **II.1–II.3** quasi-coherence of `ℋ_Z^i(F)`; proved only for closed `Z` in degree 0 on a
    locally noetherian scheme
  - [x] **II.4** on a noetherian affine: vanishing of `H^i(X, F)` for `i > 0`, (4.2) and (4.3)
  - [ ] **II.4–II.5** (4.1); (4.2), (4.3) and II.5 in positive degrees over a non-noetherian ring
  - [x] **II.5** over a noetherian ring; degree 0 over any ring
  - [x] **II.6–II.7** on a noetherian affine, for global sections (II.(7.3) in every degree)
  - [ ] **II.6–II.7** the sheaf form of II.6 a), II.6 b) off affines, Lemma II.7
  - [x] **II.(7.3)–(7.6)** reindexing by powers of generators, degree-zero identifications, the map
    (7.6) and its compatibility with connecting maps
  - [x] **II.8** over a noetherian ring; at each finite stage for a regular sequence
  - [x] **II.9** (b) ⇔ (c) in each degree; (a) ⇔ (b) ⇔ (c) with all positive degrees together
  - [x] **II.10** over a noetherian ring
  - [ ] **II.10** when `Spec A` is a noetherian space but `A` is not a noetherian ring
  - [x] **II.11**
- [ ] **III** Cohomological invariants and depth (partial; detail in [`formalization.md`](formalization.md))
  - [x] **III.1.1–III.1.3** associated primes, support, `Ass Hom(N, M) = Supp N ∩ Ass M`
  - [x] **III.2.1–III.2.5** depth-zero criteria, regular sequences and `Ext`, depth in `ℕ∞` and its
    criteria, quotient by a regular element
  - [x] **III.2.6** at finite depth; at infinite depth, extension to an infinite regular sequence
  - [x] **III.2.7–III.2.11** finiteness of depth, `Ext` description, localization, flat base change
  - [x] **III.3.1–III.3.2** for any abelian sheaf on a space; injectivity in the top degree is
    redundant from threshold 2 on
  - [x] **III.3.3** (i)–(iv) for coherent modules on a locally noetherian scheme; (v)–(vi) in
    module form on an affine
  - [ ] **III.3.3** (v)–(vi) with sheaf `𝓔xt` on a locally noetherian scheme
  - [x] **III.3.4–III.3.6** local criteria, Hartogs for coherent modules, Hartshorne's connectedness
    theorem on locally noetherian schemes
  - [x] **III.3.7–III.3.9** connectedness in codimension, the antifilter lemma, equidimensionality
  - [ ] **III.3.10** the example ring `k[X_1, …, X_5]/(𝔭 ∩ 𝔮)`; the depth obstruction is proved
  - [ ] **III.3.12** for a closed `Y` on a scheme; proved for `Y` cut out by `m` equations on a
    noetherian affine
  - [ ] **III.3.13** a curve on a normal 2-dimensional local ring with affine complement, not cut
    out by one equation; the cohomological and algebraic steps are proved
- [ ] **IV** Dualizing modules and functors (partial; detail in [`formalization.md`](formalization.md))
  - [x] **IV.1** module structure on `T(M)`; representation theorems IV.1.1–1.3 and the
    equivalences after them; IV.1.4 vanishing for exact `∂`-functors
  - [x] **IV.2** exactness of `T` iff injectivity of its representing module (IV.2.1); IV.2.2
  - [x] **IV.3** the four conditions of IV.3.1; length preservation suffices (IV.3.2)
  - [x] **IV.4.1–4.2** dualizing modules (supported at the closed point) and functors; nonlocal
    existence, representation, injectivity, local Artinianness, length-one socle components
  - [x] **IV.4.3–4.6** finite coinduction, quotient annihilators, `M ≅ M ⊗ Â` for locally
    Artinian `M`, completion of dualizing modules
  - [x] **IV.4.7, IV.4.9** existence, noncanonical uniqueness, injective-envelope
    characterization; dualizing modules are locally Artinian
  - [ ] **IV.4.8** reduction to complete regular rings (needs Cohen's structure theorem)
  - [x] **IV.5, opening** anti-equivalence, orthogonality, length/colength, monogenic modules,
    ideals of an Artinian ring; `DA ≃ DÂ`
  - [x] **IV.5.1** `CA(A)ᵒᵖ ≃ DA(A)` over every noetherian local ring, with completion transport and
    the finite-length case; `CA` is the category of Artinian modules
  - [x] **IV.5.2–5.4** Macaulay's dualizing module and the continuous dual; Ext over regular local
    rings; `Extⁿ(-, A)` is dualizing and represented by `Hⁿ_𝔪(A)`
  - [ ] **IV.5.5** proved: `Hⁿ_𝔪(A) ≅ A'`, the Koszul transitions, and `v` and the residue form
    for `K[[x₁, …, xₙ]]`; open: coefficient fields and Cohen presentations, completed
    differentials, independence of parameters and of the base field
- [x] **V** Local duality and structure of the `Hⁱ(M)` (detail in [`formalization.md`](formalization.md))
  - [x] **V.1** Hom complexes with SGA's sign convention: composition, both long exact sequences, comparison with `Ext` and the Yoneda product, injective horseshoes
  - [x] **V.2.1** local duality for finite modules over a regular local ring, natural, in every degree
  - [x] **V, formula (22)** the dual of `Hⁱ(M)` is completed complementary `Ext`, and is that `Ext` over a complete regular local ring
  - [x] **V.3.1(i)** vanishing above the dimension of `M`, and above `dim R` for any module, over any noetherian local ring
  - [x] **V.3.1(ii)** `Hⁱ(M)` Artinian; completed dual finite of dimension `≤ i`; the support criteria after (22)
  - [x] **V.3.1(iii)** top nonvanishing; dimension and associated primes of the top dual
  - [x] **V.3.2** spectral sequence for closed supports on ringed spaces, over the global ring, with E₂, abutment, convergence and functoriality
  - [x] **V.3.3** associated primes of the representing module
  - [x] **V.3.4** components of a closed subset of `Spec R` with affine complement have codimension `≤ 1`, `R` noetherian
  - [x] **V.3.5–V.3.6** finite-length and depth criteria over quotients of regular local rings, with formulas (19)–(21)
  - SGA's proof of V.3.1 uses Cohen's structure theorem, which is not formalized; the Lean proof
    does not need it
- [ ] **VI** The functors `Ext^•_Z(X; F, G)` and `ℰxt^•_Z(F, G)` (partial; detail in [`formalization.md`](formalization.md))
  - [x] **VI.1.1** `ℋom` of module sheaves; `Ext_Z` and `ℰxt_Z` for locally closed `Z`, with module structures
  - [x] **VI.1.2–VI.1.3** sheaf `Ext` as sheafified local `Ext`; excision in every degree
  - [x] **VI.1.4** formulas (VI.1.4.1)–(VI.1.4.3) and the isomorphism `θ` in every degree, locally closed `Z`
  - [x] **VI.1.5** `ℋom` into an injective is flasque; `Γ̲_Z` preserves injectives
  - [x] **VI.1.6** the three spectral functors, locally closed `Z`
  - [x] **VI.1.7–VI.1.9** support-object sequences and the long exact `Ext` sequences
  - [x] **VI.2.1, degree zero** quasi-coherence of supported `ℋom` and `ℰxt⁰_Z` for closed `Z`
  - [x] **VI.2.3, special cases** degree zero on affine schemes; `F = 𝒪_X` on noetherian affine schemes
  - [ ] **VI.1.2–VI.1.4, higher maps** compatibility with restriction between nested opens and with connecting maps
  - [ ] **VI.2.1** positive degrees, and non-closed `Z`
  - [ ] **VI.2.3** general coherent `F`
- [ ] **VII** Vanishing criteria; coherence of `ℰxtⁱ_Y(F, G)` (partial; detail in [`formalization.md`](formalization.md))
  - [x] **VII.1.3** on locally noetherian schemes
  - [ ] **VII.1.3** without local noetherianity
  - [ ] **VII.1.1–VII.1.2, VII.1.4–VII.1.7** vanishing criteria for `i < n`
  - [ ] **VII.2.1–VII.2.3** coherence for `i > n`
- [ ] **VIII–XIV** not started


---

## Later volumes

- [x] SGA 3 English — Group schemes (three tomes): foreword, introduction and Exposés I–XXVI, translated from the Gille–Polo recomposition; individual PDFs and a combined volume build with `make tex`. Indexes not included; not yet independently reviewed. See [`translation/SGA3/README.md`](../translation/SGA3/README.md).
- [ ] SGA 4 — Topos theory and étale cohomology of schemes
- [ ] SGA 4½ — Étale cohomology (Deligne)
- [ ] SGA 5 — ℓ-adic cohomology and L-functions
- [ ] SGA 6 — Intersection theory and the Riemann–Roch theorem
- [ ] SGA 7 — Monodromy groups in algebraic geometry
