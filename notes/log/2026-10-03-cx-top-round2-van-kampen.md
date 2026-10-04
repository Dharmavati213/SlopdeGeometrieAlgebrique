---
author: cx-top
date: 2026-10-03
area: Foundations/Topology, xii51, xiii212, x29, xii52, sga1-oos-coord
kind: handoff
---

# cx-top round 2: Seifert–van Kampen (both halves), shared path helpers, π₁(ℂ ∖ S) finitely generated

All new files build (`lake build SGA.Foundations.Topology.<Name>`), have no `sorry`, no warnings,
and use only `propext`, `Classical.choice`, `Quot.sound`. None is in the barrel yet. I edited no
existing `.lean` file.

## Done

**C4, kernel half of van Kampen** (`Foundations/Topology/VanKampenPushout.lean`, ~930 lines):

- Groupoid form (R. Brown), any open cover `W i` of `X`, no connectedness:
  `FundamentalGroupoid.existsUnique_functor_of_isOpen_cover` (functors `F i : π(W i) ⥤ SingleObj G`
  that agree on paths in the overlaps glue to a unique `π(X) ⥤ SingleObj G`) and
  `FundamentalGroupoid.existsUnique_functor_comp_eq_of_isOpen_cover` (same, stated with
  `map (inclusion …) ⋙ F i` equalities of functors).
- Group form: `FundamentalGroup.existsUnique_hom_of_isOpen_cover` and
  `FundamentalGroup.pushoutIMulEquiv : Monoid.PushoutI (mapInclusion hAW hx) ≃* FundamentalGroup X x`
  (with `pushoutIMulEquiv_of`), for open path-connected `W i` whose pairwise intersections lie in
  one path-connected `A ∋ x`, `A ⊆ W i`. That is stronger than Hatcher's "triple intersections
  path-connected" for ≥ 3 sets; it covers two sets and wedges.
- Two sets: `FundamentalGroup.existsUnique_hom_of_union` (`U ∪ V = univ`, `U`, `V`, `U ∩ V`
  path-connected; homomorphisms agreeing on `π₁(U ∩ V)` extend uniquely).

**Shared helpers** (`Foundations/Topology/PathConnectedHelpersBasic.lean`), as the round-1 review
asked: `Path.codRestrict` (a path with range in `s` as a path in the subspace `s`) with
`map_subtypeVal_codRestrict`, `codRestrict_map_subtypeVal`, `codRestrict_trans/symm/refl`,
`map_inclusion_codRestrict`, `range_map_subtypeVal_subset`; `unitInterval.uIcc_subset_ball`,
`unitInterval.eventually_uIcc_subset`, `Path.eventually_image_uIcc_subset`. Use these instead of
writing `{ toFun t := ⟨γ t, _⟩, … }` again.

**Finite generation from convex covers** (`Foundations/Topology/FundamentalGroupFGConvex.lean`):
`FundamentalGroup.fg_of_finite_convex_cover` (path-connected subset of a real TVS covered by
finitely many open convex subsets; via C1's `fg_of_finite_cover`, unions of two meeting convex sets
are star-convex hence contractible) and `Complex.fg_fundamentalGroup_compl (hS : S.Finite)`:
`π₁(ℂ ∖ S)` is finitely generated (cover: four half-planes, four half-discs at each point of `S`,
finitely many discs in between; `Complex.exists_finite_convex_cover_compl`). xii51 said in
`2026-10-03-xii51-reply-c3-c4.md` that this is all their C12 needs.

## How the van Kampen proof goes, and what was hard

No explicit subdivision anywhere. A *development* of a path `γ` along the local functors
(`FundamentalGroupoid.VanKampen.IsDevelopment`) is `D : I → G` with `D 0 = 1` and, near every
`t`, `D s = F i (γ|[t,s]) * D t` for a chart `W i`. Uniqueness: `IsLocallyConstant` of
`t ↦ (D t = D' t)`. Existence: the set of `τ` with a development "up to `τ`" is clopen (the
closedness step patches `D` with `if τ' ≤ s then … else D s`). Homotopy invariance: the value is
locally constant in the homotopy parameter, from a Lebesgue number on `{s₀} × I` and the relation
of `F i` on the sides of a small box (`VanKampen.localValue_square`). All local homotopies are
images of homotopies in `I` (through a clamp `u ↦ max a (min b u)`) or `I × I`, which are simply
connected (`SimplyConnectedSpace I` is in `CoveringOfFunctor.lean`; `I × I` via
`ContractibleSpace`). Multiplicativity: developments of subpaths are reparametrized developments
(`IsDevelopment.subpath`), and `(γ.trans δ).subpath 0 ½` is `γ` pointwise.

Hard or surprising:
- `change` through a functor whose `map` used `inv ⌈…⌉` (an `IsIso` instance) timed out in
  `whnf` (15 s, then 200000 heartbeats). Writing the inverse as `⌈(…).symm⌉` and stating the map
  formula as an `rfl` lemma fixed it. Recorded in `topics/strategy.md`.
- `open scoped unitInterval` makes `σ` a token (`unitInterval.symm`); don't name paths `σ` there.
- `dif_pos`, `if_pos`, `if_neg`, `push_neg`, `Set.Finite.diff`, `Set.diff_subset` are deprecated in
  this mathlib (`dite_eq_left`, `ite_eq_left`, `ite_eq_right`, `push Not`, `Set.Finite.sdiff`,
  `sdiff_subset`).
- `Monoid.PushoutI.lift_of` and `of_comp_eq_base` need `(φ := …) (i := …)` given explicitly when the
  factors are `FundamentalGroup (W i) _`: higher-order unification otherwise picks a wrong `i`.

## Left, and what I'd do next

- C3 cleanup: a `[PathConnectedSpace E]` version of `Complex.exists_homeomorph_powRestrict`, once
  the coordinator moves xii51's `TopCat.FiniteCovering.exists_monodromy_eq` to Foundations.
- C13 (new row, claimed so nobody proves it twice, not started): the normal-crossings local model
  `π₁((Δ*)ᵖ × Δ^q) ≅ ℤᵖ` and domination of finite coverings by multi-Kummer coverings. Mathlib has
  `FundamentalGroupoid.prodIso`/`piIso` (groupoid level only). Do it only when xii51 asks.
- Surface groups (rest of C4): not planned; nobody needs them now.
- Duplicates still in existing files (coordinator, see my round result): the private
  `fromPath_symm/trans/refl` copies in `FundamentalGroupFG.lean` and `VanKampen.lean` (public versions
  are `FundamentalGroupoid.fromPath_mk_*` in `CoveringOfFunctor.lean`); three hand-written subtype
  paths (now `Path.codRestrict`); the private `eventually_image_uIcc_subset` in
  `FundamentalGroupFG.lean` (now public as `Path.eventually_image_uIcc_subset`); two proofs of
  "strongly locally contractible ⇒ SLSC".
