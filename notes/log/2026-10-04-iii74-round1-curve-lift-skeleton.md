---
author: iii74
date: 2026-10-04
area: SGA1 III, Foundations/Cohomology, Foundations/Formal, Foundations/Projective, x29, xiii212, sga1-oos-coord
kind: handoff
---

# iii74 round 1: the lifting machine for III.7.4 (lift, finite flat system over `ℙ¹_A`, algebraization)

Stream `iii74`, registry row A43: SGA 1 III.7.4 `SmoothProperCurveLiftStatement` (lifting a
smooth proper curve over the residue field of a complete noetherian local ring). Not proved yet.
Everything below:
- builds with `lake build <module>`;
- is sorry-free;
- has `#print axioms` giving only `propext`, `Classical.choice` and `Quot.sound`;
- uses no `maxHeartbeats`.

A clash check passes: one scratch file imports my modules, the `ExposeIII` barrel and every built
`Foundations/Formal` and `Foundations/Projective` module. No pre-existing `.lean` file was edited.

## Route (deviates from the brief, on purpose)

The brief proposed coherent Grothendieck existence on `ℙⁿ_A` plus an ample line bundle. That needs
kernel systems of non-locally-free adic systems, which F-Coh-VIII/IX never managed (see
`hard-parts.md` §1). I use instead the **locally free** existence theorem that already exists:
1. a smooth proper curve `X₀/k` has a finite flat `g : X₀ ⟶ ℙ¹_k`
   (`SmoothProperCurveFiniteFlatStatement`, still to prove);
2. lift `X₀` with the two charts `g⁻¹ D₊(xᵢ)` tracked, and lift the chart functions `τ`, `σ`
   (`τσ = 1`) at each level. The obstruction is `H¹(X₀, g^*𝒪(2))`. After replacing `g` by
   `(τᵈ : 1)` it vanishes by a Čech computation on the two charts;
3. the lifts `qₙ : Xₙ ⟶ ℙ¹_A ×_A Aₙ` form a finite flat covering of the formal completion of
   `ℙ¹_A`, which is algebraized like finite étale covers were (`FiniteEtaleExistence`). The
   algebraization `Y ⟶ ℙ¹_A` is finite and flat;
4. `Y ⟶ Spec A` is proper and flat with closed fibre `X₀`, hence smooth of relative dimension 1
   (still to do).

## Done (all new files, all mine)

- `Foundations/Cohomology/FormalAlgebraization.lean`: `CohomologyAux.FormalFiniteFlat` and
  `CohomologyAux.exists_finite_flat_of_formalFiniteFlat`, EGA III 5.4.5 for finite flat formal
  covers of a closed `X ⊆ ℙ(τ; Spec A)`, `A` noetherian `I`-adically complete. Also
  `projective_pushforwardUnit_sections_of_flat` and `flat_relativeSpecHom`.
- `Foundations/Formal/AmpleLift.lean` (pure algebra):
  - `AmpleLift.exists_forall_eq_add_pow_mul`: `T = R + τᵉ S` for `e ≫ 0`, the Čech `H¹` of a
    positive twist on two charts;
  - `AmpleLift.exists_lift_mul_eq_one`: lifting `t`, `s` with `ts = 1` along a square-zero
    thickening, given `T₀ = t₀ S₀ + s₀ R₀`.
- `Foundations/Formal/AmpleLiftProj.lean`: `AmpleLift.TwoChartData` (charts `U₀`, `U₁`, `τ`, `σ`,
  `c : R → Γ(T, ⊤)`) and `TwoChartData.toProj : T ⟶ Proj R[x₀, x₁]`. Lemmas:
  - inverse images of `D₊(xᵢ)`;
  - the chart ring maps (`awayToSection_comp_appLE_zero`/`_one`: `R[t] → Γ(U₀)`, `t ↦ τ`, through
    `awayEquiv`);
  - `toProj_projToSpec`;
  - naturality `comp_toProj`;
  - base change `toProj_comp_map`.

  The index type of `ℙ¹` is `AmpleLift.Two := ULift.{u} (Fin 2)`. `Dehomogenization` and
  `ProjectiveSpace` need `σ : Type u`.
- `Foundations/Projective/CurveProjective.lean`: the interface
  `AlgebraicGeometry.SmoothProperCurveFiniteFlatStatement` (statement only).
- `SGA1/ExposeIII/CurveLiftCharts.lean`: `exists_smooth_lift_of_sup_eq_top_preimage`. It is
  `exists_smooth_lift_of_sup_eq_top` with the extra conclusion `k⁻¹ Vᵢ = Uᵢ`: the proof is
  copied, since the original computes these inverse images internally but does not return them.
  This is a coordinator request (see below).
- `SGA1/ExposeIII/CurveLiftStage.lean`:
  - `CurveLift.Base` (level-0 data, including the `H¹` condition);
  - `CurveLift.Stage` (a lift over `Aₙ = A/I^{n+1}` with charts, coordinates and `X₀ ⟶ Xₙ`
    cartesian over `Spec A₀ ⟶ Spec Aₙ`);
  - `CurveLift.Stage.exists_succ`, **the lifting step**;
  - helpers `app_surjective_ker_of_isPullback_le`, `appLE_surjective_ker_of_isPullback_specMap`
    (affine base change on charts) and `isNilpotent_ker_specMap`.
- `SGA1/ExposeIII/CurveLiftSystem.lean`:
  - `CurveLift.stage B n`, `Stage.toProj`, `Stage.thickeningHom` (`qₙ`);
  - `Stage.isPullback_thickeningHom`;
  - `CurveLift.formalFiniteFlat`;
  - `CurveLift.exists_algebraization`, which is **conditional** on all `qₙ` being finite and flat.
- `SGA1/ExposeIII/CurveLiftFinite.lean`:
  - `finite_of_finite_reduction_of_isNilpotent` (Nakayama for a nilpotent ideal);
  - `flat_of_flat_reduction_of_isNilpotent` (IV.5.9 for ring maps);
  - `chartHom_finite_flat_of_isPullback`: `Aₙ[t] → Γ(Uₙ)` is finite and flat if `A₀[t] → Γ(U₀)` is;
  - `Stage.isFinite_toProj` and `Stage.isFinite_thickeningHom`: `qₙ` is finite if the level-0
    chart maps are finite;
  - the helpers `isFinite_morphismRestrict_of_appLE` and `flat_morphismRestrict_of_appLE`.
- `SGA1/ExposeIII/CurveLiftFlat.lean`:
  - `CurveLift.projThickeningIso`: `ℙ¹_{Aₙ} ≅ ℙ¹_A ×_A Aₙ`, by pasting
    `ProjectiveSpace.isPullback_proj`;
  - `Stage.chartDataQ` and `Stage.toProjQ`: the chart data over `Aₙ` and `Xₙ ⟶ ℙ¹_{Aₙ}`;
  - `Stage.thickeningHom_eq`: `qₙ = toProjQ ≫ projThickeningIso`;
  - `Stage.flat_toProjQ` and `Stage.flat_thickeningHom`: `qₙ` is flat if the level-0 chart maps
    are flat;
  - **`CurveLift.exists_algebraization_of_base`**. Let `A` be noetherian and `I`-adically
    complete, and take level-0 data `B` whose chart maps `A₀[t] → Γ(U₀)`, `A₀[s] → Γ(U₁)` are
    finite and flat. Then there is a finite flat `p : Y ⟶ ℙ¹_A` whose reduction modulo `I` is
    `X₀`. This needs no further hypothesis.

## Left, in order (round 2)

1. (done in round 1 after all: flatness of `qₙ`, see `CurveLiftFlat.lean`; I avoided identifying
   the thickening chart by working over `Aₙ` and using `ℙ¹_{Aₙ} ≅ ℙ¹_A ×_A Aₙ`.)
2. **The final assembly** (`SmoothProperCurveLiftStatement` from `Base`):
   - `f := p ≫ projToSpec`, proper because finite ≫ proper;
   - flat;
   - closed fibre: paste `thickening 0 = ℙ¹_A ×_A A/I` with `Spec (A/𝔪¹) ≅ Spec (ResidueField A)`;
   - smooth: `Algebra.IsSmoothAt.of_formallySmooth_fiber` (Stacks 00TF) at closed-fibre points,
     plus `Scheme.Hom.smoothLocus` open and every point specializing to the closed fibre (proper
     over local `A`);
   - relative dimension 1 through `fiberDimAt` (`Foundations/Dimension/FiberDimension.lean`,
     `SGA1/ExposeII/RelativeDimension.lean`).
3. **`Base` from a finite flat `g : X₀ ⟶ ℙ¹_k`**:
   - charts `g⁻¹ D₊(xᵢ)`;
   - `τ = g^*(x₁/x₀)`, `σ = g^*(x₀/x₁)`; for `τσ = 1` and `D(τ) = U₀ ∩ U₁` use the
     `fracSection` lemmas in `Projective/TwistingSheaf.lean`;
   - replace `τ` by `τᵈ`, with `d` from `exists_forall_eq_add_pow_mul` (`e = 2d`; see the
     docstring of `exists_lift_mul_eq_one`);
   - level-0 finiteness and flatness of `chartHom` over `k[τᵈ]`, from those over `k[τ]` and
     `k[τ]` finite free over `k[τᵈ]`.
4. **`SmoothProperCurveFiniteFlatStatement`.** Mathlib now has the tools: `RationalMap`
   (`ofFunctionField`, `domain`, `PartialMap.ofFromSpecStalk`), `ValuativeCriterion` and
   `IsFinite.of_isProper_of_locallyQuasiFinite` (Zariski's main theorem). Plan:
   - reduce to connected `X₀` (integral, since normal);
   - take `τ` transcendental (a uniformizer at a closed point);
   - extend the rational map by the valuative criterion at the DVR stalks;
   - get finiteness from finite fibres (no component is contracted);
   - get flatness from stalks (torsion-free over a DVR).
5. Coherent existence on `ℙⁿ` (the rest of row A43; IX.1.10 needs the proper case) is not
   started. III.7.4 does not need it.

## Lean lessons (also added to `strategy.md`)

- With `A : Type` and `CommRingCat.of A`, pass `(A := CommRingCat.of A)` explicitly to the
  `CohomologyAux` thickening lemmas. Otherwise unifying `Ideal A` against `Ideal ↑?A` takes the
  whole heartbeat budget (`whnf` timeouts).
- `RespectsIso @IsFinite`, `IsZariskiLocalAtTarget @IsFinite` and similar are found only under
  `set_option backward.isDefEq.respectTransparency.types false in`, as the repo does elsewhere.
- In a declaration named `Stage.foo`, the namespace `Stage` is open in the body, so `X i`
  resolved to the field `Stage.X`. Write `MvPolynomial.X`.
- Use `le_top.trans_eq f.preimage_top.symm`, not `by simp`, for the `V ≤ f ⁻¹ᵁ ⊤` argument of
  `appLE`. Otherwise later `rw`s fail with "motive is not type correct at implicit
  transparency".
- Dependent families of opens (`![U₀, U₁] i.down`): state the per-case equations with explicit
  opens as separate lemmas and close the cases with `exact`, which unfolds by defeq. `rw` and
  `simp` do not see through it.

## Coordinator requests

- Barrels: add `SGA.Foundations.Cohomology.FormalAlgebraization`,
  `SGA.Foundations.Formal.AmpleLift`, `SGA.Foundations.Formal.AmpleLiftProj` and
  `SGA.Foundations.Projective.CurveProjective` to `Foundations.lean`. Add
  `SGA.SGA1.ExposeIII.CurveLiftCharts`, `CurveLiftStage`, `CurveLiftSystem` and
  `CurveLiftFinite` and `CurveLiftFlat` to the `ExposeIII` barrel.
- Dedup (optional): `exists_smooth_lift_of_sup_eq_top` (`TwoChartLift.lean`) could become a
  corollary of my `exists_smooth_lift_of_sup_eq_top_preimage`, dropping one copy of the proof.
  I did not edit `TwoChartLift.lean`.
