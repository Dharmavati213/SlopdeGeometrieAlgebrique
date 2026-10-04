---
author: xii4
date: 2026-10-04
area: SGA1 XII, Foundations/Analytic, xii51, sga1-oos-coord, xiii212, xiii213, x29
kind: handoff
---

# xii4 round 3: compactification of coverings (RET for `ℂ ∖ S` unconditional), XII.3.1 (ix) and (xi), Cousin I on a disc

This was the stream's last planned round. Everything below:
- builds with `lake build <module>`, one module at a time;
- is sorry-free;
- has `#print axioms` giving only `propext`, `Classical.choice` and `Quot.sound`;
- uses no `maxHeartbeats`.

A clash check passes. It is one scratch file importing every `Foundations/Analytic` module, every
untracked `SGA1/ExposeXII` module and the `ExposeXII` barrel. No pre-existing `.lean` file was
edited. My own files from earlier rounds were edited (the reviewer fixes, two docstrings, one
import), and nobody else imports them except as noted below.

## Done

1. **Round-2 reviewer fixes, all of them.**
   - Deleted the duplicate `HasCompactSupport.exists_eq_zero_of_lt_norm`; `Dolbeault.lean` now
     uses mathlib's `exists_pos_le_norm`.
   - Dropped "XII.1.1" from `AnalyticGluingReduced.lean`. It now says "auxiliary, used for
     XII.2.1 (vii) and XII.2.2".
   - `GAGA.lean`: `F^an` is now labelled XII.1.3.
   - Registry C10 is now `partial:` and lists the Modules/Morphisms API.
   - Registry, log and notes now give `IsCompactOperator.pi` as a root-level name.
   - "XII.3.1 (vii)" replaces the wrong "XII.3.2 (vii)" in the notes.
   - `hard-parts.md` no longer lists the heart as open.
   - `exists_contDiffOn_dbar_eq_ball` now says it covers finite `R` only.
   - The first Dolbeault lemma is retitled "on a smaller disc".
   - `MorphismComparisonPoints.lean` states its deviations (separatedness, quasi-compact instead
     of finite type).
   - The stale coordinator request is dropped.
2. **C8a, the compactification of finite coverings of `ℂ ∖ S`.** Split with xii51: see
   `2026-10-04-xii51-reply-c8a-split.md` and `2026-10-04-xii4-c8a-compactification-proved.md`.
   - `puncturedPlaneCompactification : PuncturedPlaneCompactificationStatement`
     (`SGA1/ExposeXII/GAGAFiberSeparating.lean`).
   - With xii51's derivations, these are now **unconditional**:
     - `fiberSeparatingFunction`;
     - **`PuncturedPlane.riemannExistence_coordRing`**, XII.5.1 for `ℂ ∖ S`;
     - `PuncturedPlane.riemannExistence_finiteEtale`;
     - `PuncturedPlane.etaleFundamentalGroup_mulEquiv_completion_freeGroup`, genus-0 `π₁`.
   - Foundations:
     - `RiemannSurfacePunctures.lean`: `PuncturedPlaneCovering`, the ends, the Kummer
       coordinates, `punctureCoord`, and the general covering lemmas
       `IsCoveringMap.isClosedMap_of_finite`, `isProperMap_of_finite`, `t2Space` and
       `comp_subtypeVal_of_isClopen`. **xii51 imports the first two**: keep their names and
       signatures.
     - `RiemannSurfaceCompactification.lean`: `PuncturedPlaneCovering.Fill` with `T2Space`,
       `CompactSpace`, `ChartedSpace ℂ` and `IsManifold 𝓘(ℂ) ω`.
3. **XII.3.1 (ix)** `AnalyticGluing.isIso_iff_isIso_analyticMap` (`MorphismComparisonIso.lean`).
   **XII.3.1 (xi)** `AnalyticGluing.isOpenImmersion_iff_isOpenImmersion_analyticMap`
   (`MorphismComparisonOpenImmersion.lean`).
   - Both assume quasi-compact `f`; the direct implication of (xi), `isOpenImmersion_analyticMap`,
     does not.
   - Scheme side: `isOpenImmersion_of_injective_map`, an étale qcqs morphism injective on
     `ℂ`-points is an open immersion. It is built on xii51's `isIso_of_bijective_map`.
   - Algebra: `isLocalization_appLE_of_isOpenImmersion`.
   - **XII.3.2 (vi)**, direct implication: `isFiniteMap_analyticMap` (`MorphismComparisonPoints.lean`).
4. **Cousin I on a disc (C10)**, in `Foundations/Analytic/Cousin.lean`:
   - `AnalyticGeometry.exists_differentiableOn_sub_eq_of_cocycle`, for arbitrary open covers,
     i.e. Čech `Ȟ¹(𝔘, 𝒪) = 0`;
   - `exists_partitionOfUnity_ball`.

## What was hard, and why

- **Concurrency.** xii51's reply proposing a split arrived while I worked. I had already
  written the separation step `gₖ = (p - z)^{mₖ} fₖ` a second time
  (`Foundations/Analytic/RiemannSurfaceSeparating.lean`). Theirs came first, so I deleted mine
  and its build artifacts. Lesson, in `strategy.md`: re-read `ls -t notes/log` before each
  milestone.
- **Building a manifold by hand.** The technique notes are in `strategy.md`, "Building a manifold
  by hand":
  - the inductive type instead of `Sum`;
  - the final topology as `⨆ coinduced`;
  - charts as `toOpenPartialHomeomorph.symm ≫ toOpenPartialHomeomorph`;
  - `HasDerivAt.of_local_left_inverse` for the root branches.

  The whole of C8a was about 1000 lines and built with few iterations.
- **(xi), direct implication.** The open immersion is local, through charts in which `f` is the
  inclusion of a basic open `D(t) ⊆ f(X)`. The ring map `Γ(V) → Γ(f⁻¹D(t))` is then a
  localization: transfer `IsAffineOpen.isLocalization_basicOpen` along the iso `f.app (D t)` with
  `IsLocalization.isLocalization_iff_of_ringEquiv`. After that the existing
  `isOpenImmersion_affineAnalytificationMap_of_isLocalization` applies.

## Not done

- XII.3.1 (v), (vi) (excellence), the converse of (vii) (EGA IV 9.6.1), and (viii), (x)
  (fibre products of analytic spaces).
- XII.3.2 (iii), (iv), the converse of (v), and the converse of (vi).
- Sheaf-level `(X^an)_red` for non-affine `X`.
- XII.4.1–4.2 statements. θ_p comes from Leray edge maps. A faithful statement needs `Rᵖf_*` on
  both sides; the simplest form is the sheafification of `V ↦ Hᵖ(f⁻¹V, F)` and its map from
  `pullbackCohomologyMap`.
- Theorem B beyond Cousin I.

## Next (for whoever continues C9/C10)

1. Derived `H¹(Δ, 𝒪) = 0`. Write the H¹ half of `TopCat.Sheaf.H'_subsingleton_of_cech`
   (Cartan.lean) for arbitrary index types: `surjective_app_of_cech` plus the `zero` case. The
   repo's Čech API (`cechComplex U P` with `U : ι → Opens X`) already takes any `ι`. Then
   transport `exists_differentiableOn_sub_eq_of_cocycle` to `holomorphicAbSheaf (Fin 1 ⊕ Fin 0 ⊕
   Fin 0)` on `polydiscProduct 1 0 0 r`.
2. Higher degrees: the Dolbeault resolution and fine sheaves, ∂̄ with holomorphic parameters,
   and polydiscs by induction (Hörmander 2.3).
3. Curve RET (xii51's stream ended). What is left after `ℂ ∖ S` is the extension of RET across
   finitely many points of a smooth curve, plus Noether normalization: see xii51's round-3
   handoff.

## For the coordinator

- Barrel candidates:
  - `SGA/SGA1/ExposeXII.lean`: `GAGAFiberSeparating`, `MorphismComparisonIso`,
    `MorphismComparisonOpenImmersion`, plus the round-1/2 list in
    `2026-10-04-xii4-round2-c8-heart.md`;
  - `SGA/Foundations.lean`: `Analytic.RiemannSurfacePunctures`,
    `Analytic.RiemannSurfaceCompactification`, `Analytic.Cousin`, plus the round-2 list.
- Stale docstrings in xii51's files:
  - `PuncturedPlaneCompactificationStatement` and `FiberSeparatingFunctionStatement` say
    "(statement only)"; both are proved, in `GAGAFiberSeparating.lean`;
  - `isEquivalence_pointsFunctor_coordRing` could point to `PuncturedPlane.riemannExistence_coordRing`.
- `docs/formalization.md` and the ExposeXII barrel docstring should list:
  - XII.3.1 (ix), (xi) (quasi-compact `f`) and XII.3.2 (vi)-direct;
  - XII.5.1 for `ℂ ∖ S` and its finite étale covers (this project's route).
- The Foundations README XII.5.1 row: RET is proved for `ℂ ∖ S` and for its finite étale covers.
