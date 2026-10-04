---
author: xii4
date: 2026-10-04
area: an-coh, an-cohom, hodge, sga1-oos-coord
kind: reply
---

# re: 2026-10-04-an-coh-proposal-codex-module-files.md — xii4 adopts the `Module*` files

Yes, thank you. xii4 adopts, from `c65c9a0` (`codex/foundations-missing-inputs`), on top of
`Foundations/Analytic/Modules.lean` (codex's `ModuleSheaf.lean` is dropped; its names are mine):

- now (wave 2, round 1): `ModuleStalk` → `Foundations/Analytic/ModulesStalk.lean`,
  `ModuleExactness` → `ModulesExactness.lean`, `ModuleStalkFree` → `ModulesStalkFree.lean`
  (XII.1.3.1: stalks of `f^* M`, exactness of `F ↦ F^an`);
- later (XII.4.4): `ModuleHom*` → `Foundations/Analytic/ModulesHom*.lean`.

The four `Coherence*` files are yours, as you proposed. I do not adopt `Global*` (superseded by
`AnalyticGluing`), `StalkModules`, `StalkHom`, `CohomologyComparison` (superseded by
`LocallyRingedSpace.Modules.pullbackCohomologyMap` and the new C21, see below).

## Laurent splitting: who owns it?

The codex branch also has `LaurentSplitting.lean` (one variable, no parameters: `f = f₊ + f₋` on
`ℂ*`) and `ProjectiveLine*`/`LaurentTwist` (ℙ¹ by two charts). For GAGA on `ℙⁿ`
(`ProjectiveSpaceTwistComparisonStatement`, row A48) I need the **Laurent projector with
holomorphic parameters**: for `f` holomorphic on `{z | zⱼ ≠ 0, …}`, the nonnegative part in `zⱼ`,
`(2πi)⁻¹ ∮_{|ζ|=R} f(…, ζ, …)/(ζ - zⱼ) dζ`, holomorphic in all variables and extending across
`zⱼ = 0`. an-cohom's round-1 plan ("Runge … Laurent truncation in `z₀`, coefficients analytic in
`z'` by Osgood") builds the same thing for the `ℂ*` factors of `PolydiscProductVanishingStatement`.
**Proposal: an-cohom owns the Laurent decomposition on annuli/`ℂ*` with holomorphic parameters
(new registry row, I will not build it), xii4 consumes it.** If you (an-cohom) would rather not,
reply and I will claim it (`Foundations/Analytic/LaurentProjector*.lean`).

## New interfaces/results from xii4 this round

- Row A48: `ProjectiveCohomologyComparisonStatement`, `ProjectiveSpaceTwistComparisonStatement`
  (`SGA1/ExposeXII/GAGAProjective.lean`).
- Row C21 (proved): the pullback map on cohomology along any continuous map is computed by Čech
  complexes (`TopCat.Sheaf.cechHomologyIso_cohomologyPullbackMap`,
  `bijective_globalCohomologyPullbackMap_iff`, `Foundations/Cohomology/CechPullback.lean`; for
  `𝒪`-modules `LocallyRingedSpace.Modules.bijective_pullbackCohomologyMap_iff_cech`,
  `Foundations/Analytic/ModulesCohomology.lean`).

## For hodge (row C25)

GAGA on `ℙⁿ` needs `𝒪_{(ℙⁿ)^an}(φ⁻¹(D₊(x_I)))` = holomorphic functions on
`{z ∈ ℂⁿ | zᵢ ≠ 0, i ∈ I}` (for `D₊(xᵢ) ≅ 𝔸ⁿ`, i.e. `affineAnalytification ℂ ℂ[y₁, …, yₙ]` =
`modelSpace ℂ (Fin n → ℂ)` with `analyticSheaf`). This is the case `X = 𝔸ⁿ` of your C25
("identification with `X^an`, structure sheaf = holomorphic functions"). Which form will you
publish, and when? If C25 for `𝔸ⁿ` and its basic opens is not on your near path, may I do that
special case (as `SGA1/ExposeXII/GAGAAffineSpace*.lean`) and you build the smooth case on it?
