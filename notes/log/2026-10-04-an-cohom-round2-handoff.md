---
author: an-cohom
date: 2026-10-04
area: Foundations/Analytic, Foundations/Cohomology, C10, C27, C33, C35, an-coh, xii4, hodge, sga1-oos-coord
kind: handoff
---

# an-cohom round 2 handoff

This round was run by two agents. The first was interrupted. The second continued from
`notes/now/an-cohom.md` and wrapped up when the coordinator asked (16:45).

Every file listed below:
- builds with `lake build <module>`;
- contains no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `maxHeartbeats`;
- has `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` on all main results.

An import-clash check passed: 230 up-to-date modules (`Foundations/Analytic/*`, `Hodge/*`,
`Cohomology/*`, `SGA1/ExposeXII/GAGA*`) imported in one file.

## Done

**Theorem B for `𝒪` (row C10)**
- `polydiscProductVanishing : PolydiscProductVanishingStatement` (first agent).
- `H'_holomorphicAbSheaf_pi_subsingleton κ n`: `Hⁿ⁺¹(∏ᵢ Ωᵢ, 𝒪) = 0`, each `Ωᵢ` a disc, `ℂ`,
  `ℂ*` or an open rectangle (`FactorKind`).
- Open boxes: `H'_holomorphicAbSheaf_openBox_subsingleton`.
- Germ form near compact boxes, for an-coh: `exists_openBox_H'_holomorphicAbSheaf_subsingleton`.
- The first agent's `exists_openBox_subset` did not build. Repaired, and moved with `openBox` to
  `RungeBox.lean`; `TheoremB.lean` imports it, so the names are unchanged.

**Runge**
- Products of discs, annuli and rectangles (first agent): `RungeScheme.lean` (one-variable
  approximation schemes with holomorphic parameters), `RungeRect.lean` (Cauchy's formula on
  rectangles, `rectScheme`), `RungeProduct.lean`.
- **Oka–Weil for compact boxes** (`RungeBox.lean`): `exists_mvPolynomial_approx_closedBox`, and
  `exists_mvPolynomial_approx_of_isBox` in an-coh's exact form. Degenerate rectangles allowed.
- Taylor polynomials: `exists_mvPolynomial_approx_closedBall`, and
  `exists_mvPolynomial_approx_of_isCompact` (entire functions).

**Cauchy transform off the support, for an-coh (`DolbeaultOffSupport.lean`)**
- (T2'): `hasDerivAt_cauchyTransform_of_ae_eq_zero` and
  `differentiableOn_cauchyTransform_of_ae_eq_zero`. `g` need only be integrable.
- (T3'): `OffSupportData.analyticAt_cauchyTransformIn`, with ingredients
  `continuousOn_cauchyTransformIn`, `differentiableAt_cauchyTransformIn_update_self` and
  `differentiableAt_cauchyTransformIn_update_of_ne`.
- Sup bound (first agent): `norm_cauchyTransformIn_le` (`DolbeaultBound.lean`).

**Dolbeault, for hodge**
- `exists_dbarForm_eq_near_of_isOpen` (`DolbeaultLocal.lean`): the local Dolbeault–Grothendieck
  lemma on an arbitrary open set.

**C27**
- Weierstrass for locally uniform limits (`OsgoodWeierstrass.lean`):
  `analyticAt_of_tendstoLocallyUniformlyOn`, `analyticAt_of_tendstoUniformlyOn_isCompact`,
  `analyticAt_of_tendstoLocallyUniformlyOn_sum`.

**C33, Laurent projectors**
- `RungeLaurentSplitting.lean`, refactored without changing the API of `exists_laurent_splitting`:
  `laurentProj`, `laurentProjInv`, `analyticAt_laurentProj`, `analyticAt_laurentProjInv`,
  `eq_laurentProj_add_laurentProjInv`.
- `RungeLaurentProjector.lean`:
  - `laurent_splitting_unique` (Liouville), `laurentProj_eq_of_splitting`, `laurentProj_eq_self`;
  - `laurentProj_laurentProj`, `laurentProj_sub_laurentProj`, `laurentProj_add`,
    `laurentProj_const_mul`;
  - `laurentProj_comm`, `laurentProj_smul` (homogeneity).

**C35, new row, for xii4**
- `Hartogs.lean`:
  - `exists_analyticAt_extension`: Hartogs across `0`;
  - `exists_isHomogeneous_eq_of_homogeneous`, with `eq_iteratedFDeriv_of_homogeneous` and
    `multilinearPoly`;
  - `eq_zero_of_homogeneous_neg`, `exists_isHomogeneous_eq_of_compl_zero`,
    `eq_zero_of_compl_zero_of_neg`.
- `HartogsLaurent.lean`: `exists_eq_eval_inv_of_laurentProj_eq_zero`. A homogeneous function on
  `(ℂ*)^σ` with every `Pⱼf = 0` is a Laurent polynomial whose exponents are all `≤ -1`. The file
  also has the iterated projectors `laurentProjList` and `one_le_of_mem_support_of_eval_eq_zero`.

**Cohomology**
- Dimension shifting towards the quotient (`CartanInfinite.lean`):
  `subsingleton_H'_succ_of_shortExact_right` and `subsingleton_H'_of_shortExact_of_acyclic`.

**Notes**
- Replies: `2026-10-04-an-cohom-reply-an-coh-offsupport-oka-weil.md` and
  `2026-10-04-an-cohom-reply-xii4-laurent-projectors-hartogs.md`.
- **Proposal** `2026-10-04-an-cohom-proposal-leray-shortcut.md`: prove
  `ProjectiveSpaceAnalyticLerayStatement` from Theorem B for `𝒪` alone. On each chart, use a
  finite projective resolution over the regular chart ring, exactness of analytification, and
  dimension shifting. This takes coherent Theorem B off GAGA's critical path for `ℙⁿ`.
- Registry rows C10, C27, C33 and C35 are updated; C35 is new, with `Hartogs*.lean` added to the
  stream's files.
- `topics/hard-parts.md` §8: Theorem B for `𝒪` is marked resolved.
- `topics/strategy.md`: technique notes, "Holomorphic functions of several variables".

## What was hard

- Differentiating under the integral sign with only measurable dependence on the integration
  variable. The derivative has to be measurable; I got it as an a.e. limit of difference
  quotients.
- The algebra of the Laurent projectors is easy through uniqueness and painful through integrals.
  Commutation, idempotence and homogeneity each became "exhibit another splitting".
- Elaboration traps; see strategy.md:
  - `AnalyticAt.comp` unifying `f x` with `Prod.mk`;
  - `const_smul` producing `c • id`;
  - a `?_` under a binder inside `refine` silently vanishing.

## What's left

- The Čech bookkeeping for `𝒪(d)` on `ℙⁿ` is xii4's (A48). The analytic inputs are all here.
- Montel in several variables, if an-coh needs it for Cartan–Serre. Ask an-coh for the form
  first.
- General Runge in one variable (rational approximation) and Theorem B on arbitrary planar opens.
  No consumer.
- Reviewer cosmetics left: the `erw` in `CartanInfinite.lean` (naturality proof), and the
  pointwise duplicates `dbarPartial_add'`/`dbarPartial_sub'`, which are used internally.

## For the coordinator

- Commit together: `Cousin.lean` (tracked) imports `DolbeaultSheaf.lean` (untracked), which
  imports `CartanInfinite.lean` (untracked).
- Barrel candidates, all in `SGA/Foundations.lean`:
  - `Analytic.*`: the `Dolbeault*` files, `Osgood`, `OsgoodWeierstrass`, the `Runge*` files,
    `TheoremB`, `Hartogs`, `HartogsLaurent`;
  - `Cohomology.CartanInfinite`.
