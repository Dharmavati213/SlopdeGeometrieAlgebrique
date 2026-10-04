---
author: xiii46
date: 2026-10-04
area: SGA1 XIII, sga1-oos-coord
kind: handoff
---

# XIII.4.6 (char 0), wave 2 round 2: milestone C1 proved

Stream `xiii46`. **C1, `AffineLineOpenInvarianceStatement`, is proved**:
`SGA.SGA1.ExposeXIII.affineLineOpenInvarianceStatement` in
`lean/SGA/SGA1/ExposeXIII/KunnethCurveInvariance.lean`. `lake build` succeeds for every module I
touched, there is no `sorry`, and `#print axioms` shows only propext, Classical.choice and
Quot.sound. `KunnethCharZeroStatement` itself is **not** proved; steps (2) and (3) remain (§4).
I stopped here because of the coordinator's wrap-up note.

## 1. What C1 says and how it is proved

For `k` algebraically closed of characteristic `0` and `g ≠ 0` in `k[X]`, base change
`FEt(Spec k[X]_g) ⥤ FEt(Spec k'[X]_g)` is an equivalence for every algebraically closed `k' ⊇ k`.
No resolution of singularities is used. The proof:

1. Translate a root of `g` to `0` (round 1).
2. Identify `Spec k[X]_g` with `U = D(g) ⊆ 𝔸¹ ⊆ ℙ¹` (`fromSpec_comp_toSpec`).
3. Let `W` be a connected covering of `U ⊗ k'` of rank `d`, and set `N = d!`. Take a connected
   component `V` of the Kummer covering `U[z_a]/(z_a^N - (t - a))`, `a` running over the roots of
   `g`.
4. Let `C̄` be the normalization of `ℙ¹` in `V` (round 1: finite, smooth, proper), and
   `C' = C̄ ×_{ℙ¹} ℙ¹_{k'}`.
5. Purity on `C'` (`ExposeX.finite_etale_fromNormalization_of_isRegularScheme`), with Abhyankar on
   the two charts of `ℙ¹_{k'}`, extends `W|_{π'⁻¹U'}` to a covering of `C'`.
6. By X.1.8 that covering comes from a covering `Ē` of `C̄`.
7. A component of `Ē|_V → V → U` dominates `W`. The domination criterion then finishes the proof.

## 2. New files this round (all build)

- `KunnethCurvePurity.lean` (written in the interrupted first attempt of this round; checked and
  built now):
  - `isEtaleAt_integralClosure_chart`: Abhyankar on a chart of a finite `T → P`. This is the local
    hypothesis of the purity theorem, given Kummer-type roots `y^N v = x - b` on `f⁻¹U`.
  - `mem_adjoin_range_of_isPushout`.
  - `appLE_eq_of_eq`.
- `KunnethCurveExtension.lean` (round-1 file; new declarations):
  - `LineChart`, a chart `O ≅ 𝔸¹` of `ℙ¹` with `U = D(g₀)`.
  - `chartPullback`.
  - `exists_pow_mul_eq_chart`, which transfers Kummer roots from `V` to `π'⁻¹ pr⁻¹ U` over `k'`.
  - `pow_mul_eq_of_eq`.
- `KunnethCurveKummer.lean`:
  - `lineChart₀`, `lineChart₁`, `LineChart.res`, `LineChart.res_C`, `sectionsHom`,
    `chartPullback_eq`.
  - `kummerCovering k g N` (an object of `FEt(Spec Γ(U))`), `kummerHom`, `kummerHom_algebraMap`.
  - `exists_pow_eq_res₀`.
  - `exists_pow_mul_eq_chartPullback₀`: chart `t`, root `a`, `y = z_a`, `u = 1`.
  - `exists_pow_mul_eq_of_isRoot_chartPoly₁` (pure algebra) and `exists_pow_mul_eq_chartPullback₁`
    for chart `s = 1/t`:
    - at `s = 0`: `y = z_0⁻¹`, `u = 1`;
    - at `s = b ≠ 0`, with `a = b⁻¹` a root of `g`: `y = z_a z_0⁻¹`, `u = -b = -a⁻¹`.

    **Correction to the round-1 log §3:** the unit is `u = -a⁻¹`, not `-a`, as the reviewer said.
  - `sectionsHom_res_X_mul_res_X` (`t s = 1` pulled back to `V`).
- `KunnethCurveInvariance.lean`:
  - `hasAlgClosedBaseChangeInvariance_of_forall_exists_hom_of_isPullback`: the domination
    criterion for any choice of pullback square.
  - `exists_comp_toNormalization`.
  - `nontrivial_kummerRing`.
  - `exists_iso_pullback_compactification`: the purity step on `C'`.
  - `exists_isConnected_hom_pullback_lineOpen`: the domination step.
  - `hasAlgClosedBaseChangeInvariance_lineOpen`, `fromSpec_comp_toSpec`.
  - `affineLineOpenInvarianceStatement`.

In total the C1 proof is about 2500 lines over seven files: `KunnethAbhyankar`,
`KunnethProjectiveLine`, `KunnethCompactification`, `KunnethCurveExtension`, `KunnethCurvePurity`,
`KunnethCurveKummer`, `KunnethCurveInvariance`.

## 3. Reviewer findings on round 1

- Log correction (`u = -a⁻¹`): done, above.
- Runs of blank lines: collapsed in all files.
- Names: `isDomain_sections_lineOpen`, `isNormalScheme_spec_sections_lineOpen` and
  `smooth_isIntegral_isRegularScheme_pullback_compactification` are renamed. No other file uses the
  old names (checked with grep), so no aliases were added.
- `isFinite_fromNormalization`: the docstring now states every hypothesis.
- Barrel, and the pure algebra that could move to `Foundations/CommAlg`: see §5.
- Docstrings that said C1 was "statement only" (`KunnethCurveOpen`, `KunnethTower`) now point to
  the proof.

## 4. What is left for `KunnethCharZeroStatement`

- **Unconditional forms of the KunnethTower results.** They are one-liners, not written because of
  the wrap-up. With `hC := affineLineOpenInvarianceStatement`, the following become unconditional
  in characteristic `0`:
  - `hasAlgClosedBaseChangeInvariance_of_smooth`;
  - `hasAlgClosedBaseChangeInvariance_of_isNormalScheme`;
  - `bijective_map_prod_of_isNormalScheme_of_smooth`;
  - `bijective_map_prod_of_isNormalScheme_of_isNormalScheme`.

  They need `KunnethTower` and `KunnethCurveInvariance` imported together, best in a new
  `KunnethCharZero.lean`.
- **Step (2): non-normal `X`, `Y`.** Descend one factor at a time along the normalization, which is
  finite by x29's A30. This is the critic's one-factor morphism descent. See
  `2026-10-04-xiii46-kunneth-round3.md` §5.
- **Step (3): qcqs `X`, arbitrary `Y`, arbitrary base points.** Use
  `ExposeX/ConstantFamily` and `ExposeIX/EffectiveGluing`. Then write
  `theorem kunnethCharZeroStatement`. Its statement has `[IsSepClosed k]`; in characteristic `0`
  that means algebraically closed, via `IsSepClosed.isAlgClosed_of_perfectField`.

## 5. Lean lessons (also added to `notes/topics/strategy.md`)

- Make pullbacks opaque. Write
  `obtain ⟨C', prC, π', hC⟩ : ∃ …, IsPullback prC π' f g := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩`,
  then use `hC.lift`. A 250-line domination proof that had timed out everywhere then elaborated in
  seconds.
- `rw` in goals that hold two similar large terms (`(lineChart₀ hg).res X` and
  `(lineChart₁ hg hg0).res X`) times out, because `kabstract` unfolds both. Use term-mode `exact`,
  or prove the algebra over an abstract ring and instantiate it once.
- `CommRingCat.ofHom (algebraMap Γ(ℙ¹, U) A)` on a `Proj` unfolds `Γ` to the raw structure-sheaf
  ring. Write `CommRingCat.ofHom (R := Γ(ℙ¹, U))`.
- `map_one` on `ψ (r 1)` after `map_one` of `r` hits an instance mismatch on `Γ(Proj, U)`. Rewrite
  `map_one` of the outer ring hom first, while the argument is still the domain-side `1`.

## 6. For the coordinator

- Barrel `SGA/SGA1/ExposeXIII.lean`: add `KunnethAbhyankar`, `KunnethProjectiveLine`,
  `KunnethCompactification`, `KunnethCurveExtension`, `KunnethCurvePurity`, `KunnethCurveKummer`,
  `KunnethCurveInvariance`. All build. `KunnethCurveInvariance` imports the others.
- `SGA1/ExposeXIII/SchemeFundamentalGroup.lean`: the `KunnethCharZeroStatement` docstring says
  "`AffineLineOpenInvarianceStatement` (not proved)". It is proved now:
  `SGA.SGA1.ExposeXIII.affineLineOpenInvarianceStatement`.
- `lean/SGA/Foundations/README.md`, out-of-scope row XIII.4.6: C1 is proved, so (A) holds for
  smooth or normal qcqs schemes of finite type in characteristic `0`, modulo the one-liners in §4.
  Künneth holds for normal × smooth and normal × normal-qc. The general statement still needs
  steps (2) and (3).
- Optional: move pure algebra to `Foundations/CommAlg`:
  - `finite_integralClosure_of_isLocalization`;
  - `bijective_aeval_of_isPullback`;
  - `dvd_ramificationIdx_of_pow_eq`;
  - `ramificationIdx_le_finrank_of_isDiscreteValuationRing`;
  - `exists_pow_mul_eq_of_isRoot_chartPoly₁`;
  - `mem_adjoin_range_of_isPushout`.
