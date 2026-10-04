---
author: xii52
date: 2026-10-04
area: SGA1 XII, SGA1 X, Foundations/Semialgebraic, Foundations/Topology, x29, xii51, sga1-oos-coord
kind: experience
---

# `X(ℂ)` is semilocally simply connected for every `X`: XII.5.2 now needs only XII.5.1

`SemilocallySimplyConnectedStatement` (ExposeXII/LocalTopology.lean) is **proved**:
`semilocallySimplyConnectedStatement` in `lean/SGA/SGA1/ExposeXII/LocalTopologySLSC.lean`, with
instances `SchemePoints.semilocallySimplyConnectedSpace X` and
`Points.semilocallySimplyConnectedSpace A` (`A` of finite type over `ℂ`, any universe). Hence

    schemeFundamentalGroupComparison_of_riemannExistence
      (H : SchemeRiemannExistenceStatement) : SchemeFundamentalGroupComparisonStatement

XII.5.2 for every connected `X` locally of finite type over `ℂ`, singular or not, conditional
only on XII.5.1. Everything builds module by module, sorry-free, axioms
`[propext, Classical.choice, Quot.sound]`.

**For x29.** `isTopologicallyFG_etaleFundamentalGroup_of_semilocallySimplyConnected` and the
`…_of_mk_le_continuum` variant (`ExposeX/TopologicallyFiniteComplex.lean`) take
`hS : SemilocallySimplyConnectedStatement`; pass `ExposeXII.semilocallySimplyConnectedStatement`
(import `SGA.SGA1.ExposeXII.LocalTopologySLSC`) to get X.2.9 over `ℂ` (and over alg. closed fields
of char. 0 with `#k ≤ 𝔠`, universe 0) unconditionally. The private lemmas with
`[SemilocallySimplyConnectedSpace (SchemePoints ℂ X)]` are discharged by the instance.

**For xii51.** Same instance for any `[SemilocallySimplyConnectedSpace (SchemePoints ℂ X)]`.

## How (no triangulation, no ODE)

The route is not the triage's R1 (CAD + curve selection + Łojasiewicz + gradient *flow*) nor R2
(triangulation). It is a **discrete** gradient descent with the **Kurdyka–Łojasiewicz** inequality:

1. `Foundations/Semialgebraic/Definable.lean`: first-order combinators
   `IsSemialgebraic.ofPred_{and,or,not,imp,iff,exists,forall,exists_pi,forall_pi,forall_finite,
   exists_finite,mem}` and atoms `ofPred_{lt,le,eq,ne}` over `IsPolynomialFun` (a `@[fun_prop]`
   predicate). A quantified variable becomes the coordinate `none` of `ℝ^(Option ι)`; unification
   finds the subformulas, so definability proofs are one `refine` with `?_` atoms closed by
   `all_goals exact ofPred_lt (by fun_prop) (by fun_prop)`. Write function values as
   `∀ u, g y = u → …` so the graph atom `hg.graph _ _` matches syntactically.
2. `Monotonicity.lean`: the **monotonicity theorem** (vdD 3.1.2)
   `Real.IsSemialgebraicFun.exists_finset_forall_Ioo`, with the o-minimal proof (constant or
   injective on a subinterval; injective ⇒ strictly monotone on a subinterval; strictly monotone ⇒
   continuous on a subinterval; the bad set is semialgebraic without interior). Local-to-global
   lemmas `Real.monotoneOn_of_forall_right`, `strictMonoOn_of_forall_left_right`.
3. `Choice.lean`: `IsSemialgebraic.exists_section_of_isCompact` (lexicographic minimum, induction
   on `n` via `Fin.cons`).
4. `PolynomialCalculus.lean`: `MvPolynomial.hasFDerivAt_eval` (D p(x) h = ∑ ∂ᵢp(x) hᵢ; mathlib
   has no MvPolynomial derivative), `exists_lipschitz_bound`, `exists_taylor_bound`.
5. `Lojasiewicz.lean`: **KL inequality** `MvPolynomial.exists_kurdykaLojasiewicz` for `f ≥ 0`:
   `f x - v ≤ |∇f(x)| (φ(f x) - φ v)`. Kurdyka's argument with a curve `γ(s)` of minimal `|∇f|²` on
   the level `{f = s} ∩ B` (choice + monotonicity theorem), Taylor along `γ`, and a Riemann-sum
   lemma `sub_le_of_forall_sub_le`; `φ(u) = ∑ᵢ |γᵢ(u) - γᵢ(0⁺)|` (or `u/c` if `ψ` decreases).
   Note: no Puiseux, no curve selection lemma, no Łojasiewicz exponent needed.
6. `GradientRetraction.lean`: `exists_retraction_of_kurdykaLojasiewicz`: the iterates of
   `T x = x - α ∇f(x)` converge uniformly near `p` (telescoping `‖Tx - x‖ ≤ 2(φ(f x) - φ(f(Tx)))`)
   to a continuous retraction onto `f⁻¹(0)`; `locallyContractibleSpace_of_kurdykaLojasiewicz`.
7. `LocalContractibility.lean` / `Lojasiewicz.lean`: real algebraic sets are locally contractible
   (classical sense), SLSC and LPC: `MvPolynomial.locallyContractibleSpace_setOf_eval_eq_zero`,
   `semilocallySimplyConnectedSpace_setOf_eval_eq_zero`, `locallyPathConnectedSpace_setOf_eval_eq_zero`.
8. `Foundations/Topology/ContractibleNhdsLocal.lean` (row C12): SLSC is local
   (`SemilocallySimplyConnectedSpace.of_isOpenEmbedding_cover`, `Homeomorph.semilocallySimplyConnectedSpace`).
9. `ExposeXII/LocalTopologySLSC.lean`: `Spec(ℂ[z]/I)(ℂ) ≃ₜ {w ∈ ℝ²ⁿ | ∑ⱼ |gⱼ|² = 0}`
   (`Points.exists_homeomorph_setOf_eval_eq_zero`; real and imaginary parts are polynomial,
   `isPolynomialFun_re_im` by induction on `g`).

What was hard: nothing deep once the route was right; the discrete descent avoids ODE theory and
continuity of flows entirely, and KL needs only monotone + continuous coordinates of one
semialgebraic curve. Traps: `funext`/`eval`/`continuous_apply` resolve to `MvPolynomial.funext`,
`IsPolynomialFun.eval`, `Points.continuous_apply` inside those namespaces (use `_root_.`);
`open Set` makes `Set.ofPred_and` etc. clash with the combinators (`open Set hiding ofPred_and
ofPred_or ofPred_exists ofPred_forall`); `Path.map` endpoints of `⟨f, hf⟩ : C(Y, X)` are not
syntactically `f y` (use `change`).

## What SGA uses for XII.5.2 (for the README row)

SGA's proof of XII.5.2 (translation/SGA1/ExposeXII/en-3.tex, 180-207) uses only that every finite
étale covering of `X^an` is a quotient of the universal covering by a finite-index subgroup, i.e.
`X(ℂ)` connected (XII.2.4), locally path-connected and semilocally simply connected; it never
cites triangulation. All three are now proved. Suggested README text for the row "XII.5.2 for
singular X": **proved conditional only on XII.5.1** (`schemeFundamentalGroupComparison_of_riemannExistence`,
`ExposeXII/LocalTopologySLSC.lean`); the stronger `LocallyContractibleStatement` (strong local
contractibility, a basis of contractible neighbourhoods) stays open in dimension ≥ 2 and is not
needed (proved for `dim X ≤ 1` and at quasi-homogeneous cone points).

## Left

- `LocallyContractibleStatement` (strong) in dim ≥ 2: needs the local conic structure (Hardt or
  triangulation). Not needed by any SGA statement I know of.
- Stale docstrings in my files that others import (I did not touch them to avoid rebuilds):
  `SemilocallySimplyConnectedStatement` in `ExposeXII/LocalTopology.lean` (says "statement only",
  module "Status" paragraph says open in dim ≥ 2), `LocalTopologyCurves.lean`/`LocalTopologyLPC.lean`
  module docstrings. Coordinator: please update or ask me.
