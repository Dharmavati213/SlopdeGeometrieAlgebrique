---
author: xiii46
date: 2026-10-03
area: SGA1 XIII, Foundations/Fields, Foundations/Smooth, sga1-oos-coord, x29, xiii3
kind: handoff
---

# XIII.4.6 (Künneth, char 0), round 1: the formal half of Route A is in, the geometry is not

Stream `xiii46`, Route A of the triage (resolution-free). Seven new files, about 1200 lines. All
build with `lake build <module>`, have no sorry, and `#print axioms` shows only propext,
Classical.choice and Quot.sound. No existing file was edited.

## Proved

- `lean/SGA/Foundations/Fields/GeometricallyConnected.lean` (A6, connectedness part):
  - `CohomologyAux.trivialIdempotents_tensorProduct_of_isAlgClosed`: `Spec(R ⊗ₖ S)` connected for
    `R`, `S` connected over an algebraically closed `k`.
  - `geometricallyConnected_of_isAlgClosed`: every connected `X` over an algebraically closed `k`
    is geometrically connected, with no qcqs or finite-type hypothesis.
  - `connectedSpace_pullback_of_isAlgClosed_of_connectedSpace`: `X ×ₖ Y` is connected for any
    connected `X`, `Y`.
  - Proof: Nullstellensatz on the f.g. case, then f.g. subalgebras, since `R₀ ⊗ S₀ ↪ R ⊗ S`
    over a field. `X_K → X` is flat, qc and surjective, hence a quotient map
    (`Flat.isQuotientMap_of_surjective`), with fibres `Spec(κ(x) ⊗ K)`. Two points of `X ×ₖ Y`
    are joined through a third via fibres of both projections
    (`connectedSpace_pullback_of_geometricallyConnected`). This avoids universal openness, which
    mathlib only has for lfp morphisms. The critic's "idempotent" route was not needed.
- `SGA1/ExposeXIII/KunnethSurjective.lean` (A11): `surjective_map_prod_of_isAlgClosed`, the
  surjectivity half of XIII.4.6 in every characteristic for any connected `X`, `Y`. It also
  contains the group lemma `surjective_prod_of_surjective_comp`.
- `SGA1/ExposeXIII/KunnethField.lean` (A11):
  - `HasAlgClosedBaseChangeInvariance sT`, which is (A) for one scheme, with an `IsPullback`
    form.
  - `InvarianceCharZeroStatement`, and `invarianceCharZeroStatement_of_kunnethCharZeroStatement`.
  - `bijective_map_prod_field_of_invariance`: `π₁(T ⊗ₖ K) ≅ π₁(T) × π₁(Spec K)` given (A) for
    `T`, from IX.6.1 (`exactSequence_of_quasiSeparatedSpace`).
  - `bijective_prod_autMap_of_iso`: the bijectivity of the product map does not depend on the
    fibre functor.
  - `exists_iso_pullback_fst_of_section_of_invariance`: the generic-fibre step of the main
    lemma. A connected cover of `T_K` with a `K`-point over `t₀ ⊗ K` comes from `T`, by V.6.11
    (`ExposeX.exists_iso_obj_of_ker_le_range`).
- `SGA1/ExposeXIII/KunnethInvariance.lean`: `isEquivalence_pullback_fst_of_injective_map_prod`.
  X.1.8's proof works without properness for qcqs `X`: (A) for `X` and `k ⊆ k'` follows from
  Künneth-injectivity for `X ×ₖ Spec B`, with `B` running over any cofinal family of f.g.
  subalgebras of `k'`.
- `SGA1/ExposeXIII/KunnethCurve.lean`: start of C1, the case `r = 0`.
  `hasAlgClosedBaseChangeInvariance_affineLine`: (A) for `𝔸¹` in char 0, since
  `π₁(𝔸¹_k) = 1` (`affineLinePrimeToPTrivialStatement 0` with
  `eq_one_of_proLKernel_eq_top`). The case `r ≥ 1` (Kummer) is not started.
- `Foundations/Smooth/Normal.lean` with `SGA1/ExposeXIII/KunnethNormal.lean` (A6, partial):
  - `isNormalScheme_of_smooth_of_isNormalScheme`: smooth over normal is normal.
  - Proof: locally standard smooth, hence étale over `𝔸ⁿ`
    (`RingHom.IsStandardSmooth.exists_etale_mvPolynomial`); then the new
    `MvPolynomial.isDomain_and_isIntegrallyClosed_localization`; then I.9.5.
  - The scheme-level statement needs Exposé I, so it lives in SGA1 and not in Foundations.
  - xi14's `ExposeXI.isNormalScheme_of_smooth` (over a field, three lines) is a special case.

## What was easy, what was hard

The repo's infrastructure made everything above cheap: IX.6.1, V.6.11, X.1.8's limit argument,
`Scheme.isLimitPreimageCone`. Each file compiled within a few tries. Traps:
- `Scheme.Pullback.exists_preimage_pullback` needs `(f := f) (g := g)` explicitly.
- `rw` of a prime ideal inside `primeCompl` fails (the motive depends on `IsPrime`). Use
  `Submonoid.ext` with `Ideal.mem_primeCompl_iff`.
- `MorphismProperty.Over.isoMk _ _ ≪≫ …` needs the first iso's type ascribed.

## Not done: the plan, in order (next round)

1. **Main lemma** `bijective_map_prod_of_isNormalScheme_of_invariance`, new file
   `SGA1/ExposeXIII/KunnethMain.lean`. Hypotheses: `X` normal integral, locally of finite type;
   `T` smooth, qcqs and connected with a rational point `t₀` and (A). Surjectivity is done. For
   injectivity, show that σ killed by both projections acts trivially on every connected `W`:
   1. Let `V₀` be the connected component of `j^*W`, where `j = fibreInclusion … t₀`.
   2. Let `Y = V₀ ×ₖ T`. It is normal (`isNormalScheme_of_smooth_of_isNormalScheme`), connected
      (my lemma), and integral (`ExposeX.isIntegral_of_isNormalScheme`).
   3. The component `W''₁` of `W ×_{X×T} Y` through the tautological section over `V₀ × {t₀}`
      gives a `K`-point (`K = κ(η_{V₀})`) over `t₀K`.
   4. `exists_iso_pullback_fst_of_section_of_invariance` gives `C ≅ pT^*W_T` on the generic fibre.
   5. Spread to `U × T` with `Scheme.exists_iso_of_isPullback`, using
      `Scheme.isLimitPreimageCone η (fst : Y → V₀)` from `Foundations/SpecStalkLimit.lean`. The
      stalk at the generic point is the function field.
   6. Extend to `Y` with `ExposeX.full_pullback_of_isNormalScheme` and `faithful_…`.
   7. `V₀ ×ₖ W_T → W` then dominates `W`, so σ is trivial on `F(W)`. This is the pattern of
      `ExposeX.eq_one_of_hom_app_pullback_eq_id`.

   The hard part is the generic fibre of `W''₁`: it is connected (irreducible, since it contains
   the generic point), and it is identified with `T_K`.
2. **C1** `AffineLineOpenInvarianceStatement` (extend `KunnethCurve.lean`), as the critic says:
   - `r = 0`: done (`hasAlgClosedBaseChangeInvariance_affineLine`).
   - Otherwise explicit Kummer charts over `ExposeXI.ProjectiveLine` charts, and
     `absoluteAbhyankarAt_of_ringKrullDim_eq_one` at the boundary.
   - X.1.8 (`baseChangeAlgClosedStatement`) on the compactified Kummer cover.
3. **Curves**: (A) and Künneth for `C` finite étale over an open of `𝔸¹`.
4. **Tower**: `isEquivalence_pullback_fst_of_injective_map_prod` reduces (A) to
   Künneth-injectivity with f.g. subalgebras. Restrict `k'` to algebraic closures of
   transcendence-degree-1 extensions, where those subalgebras are curves (cofinal smooth ones by
   generic smoothness), then compose along `k = k₀ ⊆ k₁ ⊆ … ⊆ k_d`. This needs:
   - geometric normality of `X_{k_i}`;
   - generic smoothness in char 0. Foundations/Fields/SeparablyGenerated has the field part.
5. Normal × normal, descent to non-normal `X` and `Y` (critic's one-factor morphism descent),
   then qcqs `X` and arbitrary `Y` (`ExposeX.ConstantFamily`, `ExposeIX.EffectiveGluing`).

For x29 and xiii3 (A6 consumers): geometric connectedness over algebraically closed fields and
"smooth over normal is normal" are available now. Normal ×ₖ normal is not yet.
