---
author: xiii46
date: 2026-10-03
area: SGA1 XIII, SGA1 II, SGA1 XII, Foundations/Fields, Foundations/Smooth, sga1-oos-coord, xi14, xi21t
kind: handoff
---

# XIII.4.6 (Künneth, char 0), round 2: main lemma and transcendence-degree tower proved

Stream `xiii46`, Route A (resolution-free). Everything listed below builds with
`lake build <module>`, has no sorry, and `#print axioms` shows only propext, Classical.choice and
Quot.sound. I edited only my own round-1 files and created new ones. `KunnethCharZeroStatement`
itself is **not** proved. What remains is the curve input plus the reductions to non-normal and
non-finite-type schemes (see "Plan for round 3").

## 1. Reviewer's dedupe findings (all fixed or handed to the coordinator)

- `Foundations/Smooth/Normal.lean` is **deleted**. It re-proved II.3.1 (normal, ascent).
  - `SGA1/ExposeXIII/KunnethNormal.lean` now derives `isNormalScheme_of_smooth_of_isNormalScheme`
    in a few lines from `ExposeII.IsSmoothAt.of_smooth_localizationAtPrime` and
    `ExposeII.isDomain_and_isIntegrallyClosed_localization_of_smooth`.
  - Its docstring says "II.3.1 (normal, ascent), without the noetherian hypothesis".
- Nullstellensatz: the canonical copy is now `IsAlgClosed.{exists_algHom_ker_eq, nonempty_algHom,
  isNilpotent_of_forall_algHom_eq_zero}` in `Foundations/Fields/GeometricallyConnected.lean`. The
  `CohomologyAux` namespace is gone for these, and `exists_fg_mem_range_map` moved to
  `Algebra.TensorProduct`. The XII copies need the coordinator (request below).
- Also in `GeometricallyConnected.lean`:
  - `connectedSpace_spec_of_trivialIdempotents` is deleted; the file now uses the Foundations
    lemma `CohomologyAux.connectedSpace_of_trivialIdempotents`.
  - `connectedSpace_pullback_of_geometricallyConnected` is renamed
    `GeometricallyConnected.connectedSpace_pullback_of_subsingleton`.
  - The idempotent proof now goes through `IsIdempotentElem.eq_zero_of_isNilpotent`.
  - `geometricallyConnected_of_isAlgClosed` keeps its name: xiii14's `ProperBaseChangeField` and
    x29's `TopologicallyFiniteComplex` use it. I checked that both still compile.
- `autMap_refl` is now derived from `ExposeIX.autMap_eq_conjAut_comp`.
- New bridge `hasAlgClosedBaseChangeInvariance_of_isProper`: X.1.8 gives
  `HasAlgClosedBaseChangeInvariance`.
- New named lemma `surjective_map_pullback_fst_of_isAlgClosed` (KunnethSurjective.lean). It
  generalizes `ExposeX.surjective_map_pullback_of_isAlgClosed` by dropping properness.
- Docstrings fixed:
  - `surjective_map_prod_of_isAlgClosed` now states the IsAlgClosed-versus-IsSepClosed deviation.
  - `InvarianceCharZeroStatement` is marked "statement only".
  - `aut_eq_one_affineLine` now starts with "XIII.2.12 (g = 0, n = 1, p = 0)".
- Interface drift: everything I produce is stated with `ExposeI.IsNormalScheme`. It feeds
  `ExposeX.isIntegral_of_isNormalScheme` by defeq. No new predicate.

## 2. New results

- **Main lemma** (`SGA1/ExposeXIII/KunnethMain.lean`):
  `bijective_map_prod_of_isNormalScheme_of_invariance`.
  - Statement: let `X` be connected, normal and lft, and `T` smooth, qcqs and connected with (A),
    over `k` algebraically closed, in any characteristic. Then `π₁(X×T) → π₁(X)×π₁(T)` is
    bijective at every geometric point.
  - The proof is simpler than the round-1 plan; no spreading out and no extension of
    isomorphisms is needed. Let `T_K` be the generic fibre of `pr₁`. Then:
    1. `π₁(T_K) → π₁(X×T)` is surjective (`isConnected_pullback_of_isPullback_genericPoint`).
       A connected cover `W` of the normal scheme `X×T` is irreducible, and `W_K ↪ W` is a
       preimmersion whose image contains the generic point.
    2. `σ` lifts to `σ'`, and `σ'` comes from `π₁(Spec K)` through the constant section `t₀⊗K`
       (`ker_map_fst_le_range_map_constSection`, factored out of the round-1 V.6.11 step).
    3. `ι∘(t₀⊗K)` is `Spec K → X → X×T`, `x ↦ (x,t₀)`. So every cover pulled back along it comes
       from `X`, and `σ = 1`.
  - Normality is used only in step 1. The lemma with that step as a hypothesis is
    `bijective_map_prod_of_genericPoint_of_invariance`. Use it for normal×normal later: only
    "connected covers of `X×T` are irreducible" is needed.
- `bijective_map_prod_affineLine_of_isNormalScheme` (KunnethCurve.lean): `π₁(X × 𝔸¹) ≅ π₁(X)`
  for normal `X` in char 0.
- Generic smoothness, registry row **A26**:
  - `Algebra.exists_ne_zero_smooth_localization_away` (`Foundations/Smooth/GenericSmoothness.lean`,
    any perfect field).
  - Subalgebra form `exists_le_fg_smooth`.
- `isEquivalence_pullback_fst_of_cofinal` and `hasAlgClosedBaseChangeInvariance_of_cofinal`
  (KunnethInvariance.lean): (A) for normal `X`, given cofinally many smooth f.g. `B ⊆ k'` whose
  spectra have (A).
- **Tower** (`SGA1/ExposeXIII/KunnethTower.lean`):
  - `SmoothCurveInvarianceStatement` (statement only): (A) for `Spec B`, `B` a smooth domain of
    trdeg ≤ 1 over an algebraically closed char-0 field. It is a special case of
    `InvarianceCharZeroStatement`.
  - `isEquivalence_pullback_fst_of_trdeg_le_one`: the trdeg-1 step.
  - `exists_isAlgClosed_trdeg_eq`: field theory. Inside `L` of trdeg `n+1`, there is an
    algebraically closed `L'` with trdeg `n` under `L` and `trdeg_{L'} L = 1`.
  - `isEquivalence_pullback_fst_of_isScalarTower`: FEt-equivalences compose along a field tower.
  - `isEquivalence_pullback_fst_of_trdeg_eq`: induction on `n`, for smooth `X`.
  - From these, given `SmoothCurveInvarianceStatement`:
    - `hasAlgClosedBaseChangeInvariance_of_smooth`: (A) for every smooth qcqs connected `X`,
      for every `k'`.
    - `hasAlgClosedBaseChangeInvariance_of_isNormalScheme`: (A) for every normal qcqs lft `X`.
    - `bijective_map_prod_of_isNormalScheme_of_smooth`: Künneth for normal × smooth.

## What was hard, and Lean traps

- `W.hom` for `W : FEt Z` has codomain `(Functor.fromPUnit Z).obj W.right`. Instance search then
  fails (ConnectedSpace, IsLocallyNoetherian of the codomain). Fix: `let q : W.left ⟶ Z := W.hom`.
- `MorphismProperty.of_isPullback (h : IsPullback fst snd f g) : P f → P snd`. To transfer to
  the base change of `g`, pass `h.flip`.
- `(algebraicClosure F L).restrictScalars k`:
  - `IsAlgClosed` comes from the `F`-version by defeq: `have : IsAlgClosed L' := hL₀`. Asking
    for `IsAlgClosure F L'` fails.
  - `IsScalarTower k L' L` is found only for the `restrictScalars` version.
- A singleton family for `cardinalMk_le_trdeg` must live in the right universe: `PUnit.{u+1}`.
- `FundamentalGroup.map` is a `def`, not an abbrev. `ExposeX.map_hom_app_eq_id` etc. still apply
  by `exact`/`apply`.

## Plan for round 3 (in order)

1. **Curves.** The tower only needs (A) for the smooth f.g. subalgebras `B` that it picks
   cofinally in a trdeg-1 `k'` (`exists_le_fg_smooth` in `isEquivalence_pullback_fst_of_trdeg_le_one`).
   Cheapest route:
   - (a) `AffineLineOpenInvarianceStatement`: (A) for `U = 𝔸¹ ∖ Z(g)`. The case `r = 0` is
     done. For `r ≥ 1`: explicit Kummer cover `y_iⁿ = t − a_i` (smooth by the Jacobian), its
     compactification, Abhyankar at the boundary (`absoluteAbhyankarAt_of_ringKrullDim_eq_one`),
     then X.1.8. This is the big piece.
   - (b) (A) passes to connected finite étale covers `C → U`: `FEt(C) ≌ FEt(U)/C`; use
     `ExposeV.FEt.postcomp`.
   - (c) Generic étaleness. A f.g. domain `A ⊆ k'` of trdeg 1 over `k` contains a transcendental
     `t`, and `A_g` is finite étale over `k[t]_g` for some `g`. Then change the cofinal family in
     `isEquivalence_pullback_fst_of_trdeg_le_one` to such `A_g`. This avoids proving
     `SmoothCurveInvarianceStatement` for all smooth curves.
2. **Normal × normal** (for Künneth with `Y` normal instead of smooth): needs geometric normality
   of `A ⊗_k L` (`k` algebraically closed, char 0). Plan:
   - `L` is the union of smooth f.g. `B` (generic smoothness, now available).
   - `A ⊗ B` is normal by II.3.1.
   - A directed union of integrally closed domains is integrally closed.
   - Domain-ness of `A ⊗ L` needs "integral over an algebraically closed field ⇒ geometrically
     integral". Use the same Nullstellensatz pattern as `trivialIdempotents_tensorProduct_of_isAlgClosed`.
3. Descent to non-normal `X`, `Y` (critic's one-factor morphism descent), then qcqs `X` and
   arbitrary `Y`, then `kunnethCharZeroStatement`. Proving `KunnethCharZeroStatement ⇐
   InvarianceCharZeroStatement` also needs step 3; only `⇒` is done.

## For the coordinator (also in this round's result)

- Make `ExposeXII.Points.exists_ker_eq`, the `←` half of `Points.nonempty_iff_nontrivial` and
  `Points.isNilpotent_of_forall_apply_eq_zero` (`SGA1/ExposeXII/Comparison.lean:161,178,190`)
  one-line wrappers of `IsAlgClosed.exists_algHom_ker_eq`, `IsAlgClosed.nonempty_algHom` and
  `IsAlgClosed.isNilpotent_of_forall_algHom_eq_zero`. `Points K A` is `A →ₐ[K] K` by definition.
- Re-derive these special cases of my general versions:
  - `ExposeX.trivialIdempotents_tensor_of_isAlgClosed` (finite `B`) from
    `CohomologyAux.trivialIdempotents_tensorProduct_of_isAlgClosed`;
  - `ExposeX.connectedSpace_pullback_of_isAlgClosed` (proper) and `ExposeXI.connectedSpace_pullback`
    from `connectedSpace_pullback_of_isAlgClosed_of_connectedSpace`;
  - `ExposeX.surjective_map_pullback_of_isAlgClosed` from
    `ExposeXIII.surjective_map_pullback_fst_of_isAlgClosed`. The latter needs only ExposeV and
    Foundations, so it can move into ExposeX.
- X.1.8 copies: re-derive `ExposeX.hom_app_eq_id_of_forall_hom_app_pullback_eq_id` and
  `ExposeX.isEquivalence_pullback_fst_of_isReduced` from
  `ExposeXIII.hom_app_eq_id_of_injective_map_prod` and
  `isEquivalence_pullback_fst_of_injective_map_prod` (`P := FG`, injectivity from X.1.7), or move
  the general ones into `ExposeX/BaseChangeAlgClosed.lean`.
- "Smooth over a field ⇒ normal" has two copies, both corollaries of II.5.3 / II.3.1:
  `ExposeXI.isNormalScheme_of_smooth` (xi14, `ExposeXI/UnirationalCurves.lean:127`) and
  `ExposeXI.isNormalScheme_of_smooth` (xi21t, `ExposeXI/AbelianVarietyMulN.lean:45`, same name
  and namespace, so the two files cannot be imported together). The tower inlines the II.5.3
  route instead of adding a third copy.
- Three equal-bodied `IsNormalScheme` predicates exist: `ExposeI.IsNormalScheme` (Permanence:694),
  `ExposeX.IsNormalScheme` (Purity:58) and `ExposeXI.IsNormalScheme` (Geometry:221). Make the
  latter two abbrevs of the first.
- Move `isDomain_and_isIntegrallyClosed_localization_of_isSmoothAt` and
  `isNormalScheme_of_smooth_of_isNormalScheme` (KunnethNormal.lean) into
  `ExposeII/PermanenceSmooth.lean` as II.3.1 corollaries. Move `exists_isAlgClosed_trdeg_eq`
  (KunnethTower.lean) to `Foundations/Fields`.
- `ExposeX.autHom_refl` (SpecializationGeometric:203) and `ExposeXIII.autMap_refl`, with
  `ExposeXIII.autHom` having the same body as `ExposeV.autMap`: dedupe.
- Barrel entries for `Foundations/Fields/GeometricallyConnected`,
  `Foundations/Smooth/GenericSmoothness`, and `SGA1/ExposeXIII/Kunneth{Surjective,Field,Normal,
  Main,Invariance,Curve,Tower}`. Remove `Foundations/Smooth/Normal` if it was listed.
