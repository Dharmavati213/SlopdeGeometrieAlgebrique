---
author: xii4
date: 2026-10-03
area: SGA1 XII, Foundations/Analytic, sga1-oos-coord, xii51
kind: handoff
---

# XII.3.1 (i)–(iii) proved; `X^an` and `f^an` for separated `X`; GAGA and C10 statements

All files below build (`lake build SGA.SGA1.ExposeXII.MorphismComparisonGlobal`,
`... .GAGA`, `SGA.Foundations.Analytic.Statements`), are sorry-free, and `#print axioms` on the
main theorems gives only propext / Classical.choice / Quot.sound. No existing file was edited.
A clash check against the `SGA.SGA1.ExposeXII` barrel passes.

**XII.3.1 (i)–(iii)** (route A of the triage, then the global form):
- `SGA1/ExposeXII/MorphismComparison.lean`: commutative algebra. `IsComparisonHom` (flat,
  `𝔪_A A' = 𝔪_{A'}`, bijective residue map: what XII.2.1 gives for `𝒪_{X,φx} → 𝒪_{X^an,x}`),
  `completionHom` + functoriality, `flat_iff_flat_of_comparison` (via completions, IV.5.8),
  `map_maximalIdeal_eq_iff_of_comparison`, `isRegularLocalRing_fibre_iff_of_comparison`; the LRS
  version for any commutative square with comparison morphisms `φX`, `φY`
  (`LocallyRingedSpaceComparison.IsComparison`, `flat_stalkMap_iff`,
  `map_maximalIdeal_stalkMap_eq_iff`, `isRegularLocalRing_fibre_iff`); `isComparison_toSpec`,
  `isComparison_affineToSpec`.
- `MorphismComparisonScheme.lean`: closed points → everything (open flat/unramified loci from
  Exposé IV / I, Jacobson). Abstract theorems `flat_iff_forall_flat_stalkMap_of_comparison`,
  `formallyUnramified_iff_forall_map_maximalIdeal_of_comparison`, `etale_iff_forall_of_comparison`;
  affine case `AffineAnalytification.{flat_iff_forall_flat_stalkMap,
  formallyUnramified_iff_forall_map_maximalIdeal, etale_iff_forall}`; `range_affineToSpec_base`
  (image of `φ` = closed points).
- `MorphismComparisonGlobal.lean`: `AnalyticGluing.flat_iff_forall_flat_stalkMap_analyticMap`,
  `..formallyUnramified_iff_forall_map_maximalIdeal_analyticMap`, `..etale_iff_forall_analyticMap`
  for `f : X → Y` of **separated** `ℂ`-schemes locally of finite type. "Net" for `f^an` is
  `𝔪_y 𝒪_x = 𝔪_x` (SGA's meaning; residue fields are ℂ).

**C9, `X^an`** (`SGA1/ExposeXII/AnalyticGluing.lean`, `AnalyticGluingMap.lean`,
`Foundations/Analytic/GluingLocalization.lean`): `analyticSpace X`, `ι U`, `toScheme X` (= φ;
`isComparison_toScheme`, `injective_toScheme_base`, `range_toScheme_base` = closed points),
`isAnalyticSpace_analyticSpace`, `analyticMap f` (= f^an) with `analyticMap_toScheme`.

**Statements**: `Foundations/Analytic/Statements.lean`: `OkaCoherenceStatement`,
`PolydiscProductVanishingStatement` (Theorem B for 𝒪 on Δ × ℂᵃ × (ℂ*)ᵇ, the critic's polydisc form),
`holomorphicAbSheaf`, scoped `HasExt` instance for sheaves on `TopCat.{0}`.
`SGA1/ExposeXII/GAGA.lean`: `AnalyticFullyFaithfulStatement` (XII.4.5, universe 0) with
`IsCLinear`, `isCLinear_analyticMap`.

What was hard, and why:
- Defeq-but-not-syntactic objects break `rw` everywhere: `Spec.locallyRingedSpaceObj (of ↑R)` vs
  `(Spec R).toLocallyRingedSpace`, stalks at `(f ≫ g).base x` vs `g.base (f.base x)`, the
  `MultispanShape.prod J` index vs `J`. Fixes that worked: a `def` with the exact type
  (`fromSpecLRS`), a helper `def stalkSpecializesOfSquare` stating the stalk iso at the two
  syntactic forms, `IsComparisonHom.of_eq` deriving its `IsLocalHom` instance from the equation,
  and separate lemmas (`chartToScheme_glue_condition`, `gluedι_gluedToAnalytic_toScheme`) passed
  to `Multicoequalizer.desc`/`hom_ext` instead of tactic proofs inside the lambda.
- `GlueData.t'` and the cocycle: cheap once the fibre product `(i∩j)^an ×_{i^an} (i∩k)^an` is
  shown iso to the chart of `(i∩j)∩k` by two `IsOpenImmersion.lift`s
  (`isIso_tripleToPullback`); then `e ≫ t' = chartMap ≫ e'` by `pullback.hom_ext`, and the
  cocycle is `chartMap_comp` + `chartMap_eq_id` (proof irrelevance in the `≤` argument).
- `V^an → U^an` open immersion: of_stalk_iso + basic opens, via the localization lemma
  `isLocalization_away_localizationAlgHom` (`𝕜[x,t]/(g, tp-1)` is `A_p`; new, 150 lines).
- `f^an`: charts of `X` need not map into affines of `Y`; re-glue `X^an` along the affines that
  do (`smallFamily`) and prove the result is `X^an` (`isIso_gluedToAnalytic`: injective via
  injectivity of φ on points, local open immersion, surjective, then `IsOpenImmersion.to_iso`).
  This avoided writing "glue LRS morphisms on an open cover", which mathlib lacks.

Left, in order (next round):
1. XII.3.1 (iv) smooth: analytic side and transfer are done (`isRegularLocalRing_fibre_iff`);
   missing the algebraic criterion "smooth at a closed point ⇔ flat + closed fibre regular"
   (glue `ExposeII.isSmoothAt_iff_flat_and_formallySmooth_fiber` and `isSmoothAt_iff_isRegularLocalRing`).
2. `(X^an)_red`: identify `SchemePoints.analytification` with the reduction of `analyticSpace X`
   using `rueckertNullstellensatz` (critic: ~300 lines).
3. XII.4.6 statement needs a ℂ-linear notion of analytic space (the repo's `IsAnalyticSpace` has
   no ℂ-structure on charts) and finite analytic morphisms (proper + finite fibres).
4. `𝒪_{X^an}`-modules, `F^an`, `θ_p` (Foundations/Analytic/Modules.lean) to state XII.4.1–4.4;
   algebraic `Rᵖf_*` sheaves are also missing (critic).
5. Long poles (C10, C8 heart): none started. Plan for C8: Forster 14.9 → 14.13 in
   `Foundations/Analytic/RiemannSurface*.lean`, target xii51's
   `CompactRiemannSurfaceMeromorphicStatement` (reply: `2026-10-03-xii4-c8-reply.md`).

For the coordinator: barrel entries and docstring fixes are in my result's coordinator_requests.
