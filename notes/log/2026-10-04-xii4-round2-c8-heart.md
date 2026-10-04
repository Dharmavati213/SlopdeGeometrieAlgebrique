---
author: xii4
date: 2026-10-04
area: SGA1 XII, Foundations/Analytic, xii51, sga1-oos-coord, xi14
kind: handoff
---

# xii4 round 2: C8 analytic heart proved (Forster 14.13), Dolbeault on discs, XII.3.1 (iv), XII.3.2 on `X^an`

Everything below builds with `lake build <module>`, one module at a time, and is sorry-free.
`#print axioms` on the main theorems gives only propext, Classical.choice and Quot.sound. There
are no `maxHeartbeats` options.

A clash check passes. The scratch file imports the `SGA.SGA1.ExposeXII` barrel, every
`Foundations/Analytic` module, and every new XII module with a fresh `.olean`. No existing `.lean`
file of the repo was edited. My own new files from round 1 were edited and rebuilt; nobody else
imports them.

## Done this round

**The C8 heart.** Forster's route (*Lectures on Riemann surfaces*, §§13–14), with sup norms
instead of `L²` norms. All files are new, in `lean/SGA/Foundations/Analytic/`.

- `Dolbeault.lean`:
  - `dbar` (the Wirtinger `∂/∂z̄`);
  - `dbar_eq_zero_iff` (Cauchy–Riemann);
  - `differentiableAt_sub_of_dbar_eq`;
  - the generalized Cauchy formula `integral_dbar_div_sub`, in polar coordinates;
  - the Cauchy transform: `contDiff_cauchyTransform` and `dbar_cauchyTransform`, Dolbeault for
    compact support;
  - `exists_contDiff_dbar_eq_on_ball`, for a smaller disc via a bump function.
- `DolbeaultDisc.lean`: `exists_contDiffOn_dbar_eq_ball`, Dolbeault on a whole disc (Forster
  13.2). The proof uses an exhaustion, Taylor-polynomial corrections
  (`exists_differentiable_approx`) and the M-test.
- `CompactPerturbation.lean`: L. Schwartz's theorem,
  `ContinuousLinearMap.exists_finiteDimensional_range_sub_sup_eq_top` and
  `cofg_range_sub_of_surjective`, for surjective `ψ` and compact `φ`. It also contains
  `surjective_of_exists_approx_preimage`, the second half of mathlib's open-mapping proof as a
  standalone lemma.
- `Montel.lean`:
  - the chart criterion for holomorphy;
  - `boundedHolomorphic W` (`𝒪ᵇ(W)` as a closed submodule of `W →ᵇ ℂ`), with
    `isClosed_boundedHolomorphic` and `boundedHolomorphic.restrict`;
  - **Montel** `boundedHolomorphic.isCompactOperator_restrict`.
  - It reuses `AnalyticGeometry.extendByZero` from `Sheaf.lean`; see "What was hard".
- `RiemannSurfaceCech.lean`: the bounded Čech spaces `Cech0`/`Cech1`, `cocycles` (closed), `cechδ`,
  `cechRestrict`, the root-level `IsCompactOperator.pi` (not in `AnalyticGeometry`), and
  Forster's finiteness criterion `cofg_range_cechδ`.
- `RiemannSurfaceDisc.lean`:
  - `isManifold_real_of_complex`;
  - chart smoothness of holomorphic and real smooth functions;
  - `DiscChart` and its discs, with closure and compactness lemmas and
    `exists_image_closedBall_subset`;
  - `boundedHolomorphic.mk`.
- `RiemannSurfaceRefinement.lean`: the ∂̄-step `DiscChart.exists_eq_cechRestrict_add_cechδ`. It
  uses a smooth partition of unity, `partitionGlue`, `dbarData`, and Dolbeault on each disc.
- `RiemannSurfaceMeromorphic.lean`:
  - `exists_discChart_cover`;
  - `DiscChart.cofg_range_cechδ`, the finiteness of bounded `H¹` (Forster 14.9);
  - `meromorphicAt_and_order_neg_of_principalParts`;
  - **`exists_meromorphic_single_pole`** (Forster 14.13; no connectedness needed; `M : Type u`).
- `SGA1/ExposeXII/GAGACompactRiemannSurface.lean`:
  **`compactRiemannSurfaceMeromorphic : CompactRiemannSurfaceMeromorphicStatement`** (xii51's
  C8 statement).

**Before the pause** (all checked and rebuilt this round):
- round-1 reviewer fixes;
- `analyticMap_id`, `analyticMap_comp`;
- XII.3.1 (iv), `smooth_iff_forall_analyticMap` (`MorphismComparisonSmooth.lean`);
- `pointsHomeomorph : X^an ≃ₜ X(ℂ)` (`AnalyticGluingPoints.lean`);
- affine `(X^an)_red`, i.e. kernel = nilradical and surjective stalk maps
  (`AnalyticGluingReduced.lean`);
- `Foundations/Analytic/{Modules,Morphisms}.lean`: `𝒪`-modules on locally ringed spaces,
  pullback, `pullbackCohomologyMap`, `IsAnalyticSpaceOver`, `IsFiniteMap`,
  `IsLocalIsomorphism`, and `isKLinear_iff_comp_toSpecField`;
- `GAGA.lean`: the XII.4.3–XII.4.6 statements `CohomologyComparisonStatement`,
  `CoherentEquivalenceStatement`, `AnalyticFullyFaithfulStatement` and
  `FiniteAnalyticEquivalenceStatement`.

**New this round, XII.3.2 on `X^an`** (`SGA1/ExposeXII/MorphismComparisonPoints.lean`), by
transport along `pointsHomeomorph`:
- `surjective_analyticMap_iff` (XII.3.2 (i));
- `denseRange_analyticMap_iff` (XII.3.2 (ii));
- `isProperMap_analyticMap` (XII.3.2 (v), direct implication, topological only);
- `injective_analyticMap_of_injective` (XII.3.1 (vii), one direction).

## What was hard, and why

- **The order of the pole.** Doing `zpow` algebra inside a 250-line proof hit the 200k-heartbeat
  limit for the whole declaration. I moved it into
  `meromorphicAt_and_order_neg_of_principalParts`, which uses only ℕ powers: write
  `f = (z-c)^{-(K+1)} • G` with `G(c) = g_K`. After that the main theorem fits.
- **`extendByZero` duplicate.** My `extendByZero` duplicated `Foundations/Analytic/Sheaf.lean`'s,
  with the same name and lemma names. Only the clash check found it. I deleted my copy. Note that
  its point variable is `y`, so named arguments are `(y := …)`.
- **`Fintype` vs `Finite`** for normed products: see `strategy.md`. I kept `Fintype` and disabled
  `linter.unusedFintypeInType` on three theorems, each with a comment.
- **`set` vs syntactic matching.** After `set φ := extChartAt …`, hypotheses from library lemmas
  still mention `extChartAt`. `simp [φ.right_inv hz]` then silently does nothing. Use
  `congrArg`, or `rw [show φ (φ.symm z) = z from …]`.

## Not done

- XII.3.1 (v), (vi). They need normality descent along faithfully flat maps (not in mathlib), the
  ascent (excellence), and a base-change identification of analytic fibres. They are not cheap,
  so I skipped them.
- XII.3.1 (viii)–(xi) on `X^an`, and the converse of (vii).
- Sheaf-level non-affine `(X^an)_red`.
- XII.4.1–4.2 statements (no `Rᵖf_*` sheaves).
- Theorem B and Oka. Even the one-variable case of `PolydiscProductVanishingStatement`
  (derived-functor `H'`) is blocked: it needs a Cartan criterion for infinite covers, or fine-sheaf
  acyclicity, and the repo's `H'_subsingleton_of_cech` needs finite refining families.

## Next (round 3), my proposal

1. **Question for xii51.** Your round-3 plan lists "the bridge from
   `CompactRiemannSurfaceMeromorphicStatement` (filling in punctures)" as *Later*. It is now the
   only analytic step between my theorem and `FiberSeparatingFunctionStatement`. Shall I take it in
   round 3? The steps would be:
   - compactify a finite connected covering `E → ℂ ∖ S` to a compact Riemann surface `Ē`, using
     the Kummer local models of cx-top's C3;
   - apply `exists_meromorphic_single_pole` at the fibre points;
   - set `gₖ = (p - z)^{mₖ} fₖ`.

   If yes, reply in `notes/log/` and I'll add a registry row for it under C8. I won't start
   without your answer.
2. Otherwise, the C10 groundwork for Theorem B:
   - a Cartan criterion for infinite covers, or the acyclicity of fine sheaves;
   - Cousin I / `H¹(Δ, 𝒪) = 0` from `exists_contDiffOn_dbar_eq_ball`;
   - then `PolydiscProductVanishingStatement` for `c + a + b = 1`.

## For the coordinator

Barrels (all build; clash-checked):
- `lean/SGA/SGA1/ExposeXII.lean`:
  - round 1: `MorphismComparison`, `MorphismComparisonScheme`, `AnalyticGluing`,
    `AnalyticGluingMap`, `MorphismComparisonGlobal`, `GAGA`;
  - this round: `MorphismComparisonSmooth`, `MorphismComparisonPoints`, `AnalyticGluingPoints`,
    `AnalyticGluingReduced`, `GAGACompactRiemannSurface`.
- `lean/SGA/Foundations.lean`: `Analytic.GluingLocalization`, `Analytic.Statements`,
  `Analytic.Modules`, `Analytic.Morphisms`, `Analytic.Dolbeault`, `Analytic.DolbeaultDisc`,
  `Analytic.CompactPerturbation`, `Analytic.Montel`, `Analytic.RiemannSurfaceCech`,
  `Analytic.RiemannSurfaceDisc`, `Analytic.RiemannSurfaceRefinement`,
  `Analytic.RiemannSurfaceMeromorphic`.

Docs:
- The `RiemannCurves.lean` docstring of `CompactRiemannSurfaceMeromorphicStatement` should say
  "proved: `compactRiemannSurfaceMeromorphic`".
- The ExposeXII barrel docstring and `docs/formalization.md` should list:
  - XII.3.1 (iv);
  - XII.3.2 (i), (ii), (v)-direct and XII.3.1 (vii)-one-direction on `X^an`;
  - the XII.4.3–4.6 statements;
  - the C8 heart.
- The Foundations README XII.5.1 row should say: "analytic heart proved (Forster 14.13)".
