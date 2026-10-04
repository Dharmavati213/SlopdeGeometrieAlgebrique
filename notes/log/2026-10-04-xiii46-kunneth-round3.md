---
author: xiii46
date: 2026-10-04
area: SGA1 XIII, SGA1 II, SGA1 V, SGA1 VIII, Foundations/Fields, Foundations/Smooth, sga1-oos-coord, x29, xiii43
kind: handoff
---

# XIII.4.6 (Künneth, char 0), round 3: tower reduced to opens of 𝔸¹, normal × normal

Stream `xiii46`, Route A (resolution-free), last round of wave 1. Every module listed below builds
with `lake build <module>`, is sorry-free, and `#print axioms` shows only propext,
Classical.choice and Quot.sound. `KunnethCharZeroStatement` itself is **not** proved. The only
geometric input missing for the normal finite-type case is now the curve milestone C1,
`AffineLineOpenInvarianceStatement`. A precise blueprint for it is below.

## 1. Reviewer's findings on round 2 (all fixed)

- Docstrings of `bijective_map_prod_of_isNormalScheme_of_invariance` (KunnethMain) and
  `bijective_map_prod_field_of_invariance` (KunnethField) now list "full π₁ instead of π₁^{p'}",
  and the latter also "k algebraically closed (SGA: separably closed)".
- KunnethNormal's module docstring is rewritten: normality is only used to make connected
  covers of `X ×ₖ T` irreducible.
- `irreducibleSpace_of_isNormalScheme` is renamed `irreducibleSpace_left_of_isNormalScheme`. It is
  now `ExposeI.isNormalScheme_of_etale` + `ExposeI.irreducibleSpace_of_isDomain_stalk` (I.9.10,
  I.9.11).
- `hom_app_pullback_eq_id_of_map` is now the iff `map_hom_app_eq_id_iff`. The `←` direction is
  `ExposeX.map_hom_app_eq_id`. Moving it to ExposeV is a coordinator request.
- `constSection` is now *defined* as `ExposeX.fibreInclusion _ sT t₀ ht₀ ≫ (pullbackSymmetry _ _).hom`.
- GenericSmoothness is derived from `Algebra.isSmoothAt_bot_iff_isGeometricallyReduced` and
  `IsGeometricallyReduced.of_perfectField_of_field`. `exists_le_fg_smooth` moved there as
  `Subalgebra.exists_le_fg_smooth`.
- `bijective_map_prod_of_genericPoint_of_invariance` no longer takes the redundant
  `ConnectedSpace (X ×ₖ T)` / `Surjective pr₁` instances; the proof derives them.
- hard-parts entry: main lemma is for `X` locally of finite type (not qc).
- Registry: the stale `Foundations/Smooth/Normal*.lean` pattern is dropped.
- Correction of a round-2 coordinator request: only `ExposeX.IsNormalScheme` (Purity:58) has the
  same body as `ExposeI.IsNormalScheme`. `ExposeXI.IsNormalScheme` (Geometry:221) is weaker (no
  `IsDomain`) and must **not** become an abbrev.

## 2. New results (all build)

- `SGA1/ExposeXIII/KunnethFiniteEtale.lean`:
  - `HasAlgClosedBaseChangeInvariance.of_isFinite_of_etale`: invariance (A) passes to connected
    finite étale covers. Proof: the graph embeds a cover `Y` of `C_{k'}` into
    `(E ×_X C)_{k'}`, then apply `hom_app_eq_id_of_mono`.
  - `hasAlgClosedBaseChangeInvariance_of_forall_exists_hom`: a **domination criterion**. (A)
    holds if every connected cover of `X_{k'}` receives a map from `E_{k'}` with `E` connected.
    This is the form C1 should be proved in.
  - `hom_app_eq_id_of_mono`, `hom_app_eq_id_of_epi`.
- `SGA1/ExposeXIII/KunnethCurveOpen.lean`:
  - `AffineLineOpenInvarianceStatement` (C1, statement only): (A) for `Spec k[X]_g`, char 0.
    - Implied by `InvarianceCharZeroStatement`
      (`affineLineOpenInvarianceStatement_of_invarianceCharZeroStatement`).
    - The unit case `g ∈ k[X]ˣ` is proved
      (`hasAlgClosedBaseChangeInvariance_localization_away_of_isUnit`).
  - **Generic finite étaleness** `exists_finite_etale_away`. Let `S` be of finite type and
    algebraic over a noetherian char-0 domain `R`. Then `(S_f)_r` is finite étale over `R_r`.
    Proof: mathlib's `Algebra.exists_etale_of_isEtaleAt` at the generic point, plus
    `ExposeVIII.exists_finite_away_of_finite_localization` at `p = ⊥`.
  - `isAlgebraic_polynomial_of_trdeg_le_one`.
  - `exists_le_fg_invariance_of_trdeg_le_one`: the cofinal family of `Spec B` étale over opens of
    `𝔸¹`.
  - `isEquivalence_pullback_fst_of_trdeg_le_one`: the trdeg-1 step, from C1.
- `SGA1/ExposeXIII/KunnethTower.lean`: the tower now takes `hC : AffineLineOpenInvarianceStatement`.
  - Round 2's `SmoothCurveInvarianceStatement` is **deleted**. C1 is a special case of it, so
    every tower result got stronger.
  - New theorem `bijective_map_prod_of_isNormalScheme_of_isNormalScheme`: Künneth for `X` normal
    lft × `Y` normal qcqs lft, given C1.
- `Foundations/Fields/GeometricallyIntegral.lean` (new, registry A6):
  - `Algebra.TensorProduct.isDomain_of_isAlgClosed`: `R ⊗ₖ S` is a domain for `k` algebraically
    closed. Proof: Nullstellensatz plus a basis of `S`.
  - Linear algebra `TensorProduct.mem_range_map_of_mem_range_lTensor_of_mem_range_rTensor`: in
    `K ⊗ L`, `(K ⊗ B) ∩ (A ⊗ L) = A ⊗ B`.
- `SGA1/ExposeXIII/KunnethNormalProduct.lean` (new; it needs II.3.1, so it can't be in
  Foundations):
  - `isIntegrallyClosed_tensorProduct_fractionRing`: `B ⊗ Frac A` is normal. `A_f` is smooth,
    `B ⊗ A_f` is normal by II.3.1, then localize.
  - `isIntegrallyClosed_tensorProduct`: `A ⊗ₖ B` is normal for `A`, `B` normal f.g. domains,
    char 0. Proof by the intersection trick.
  - `isNormalScheme_pullback`: `X ×ₖ Y` is normal.
  - Charts `exists_isOpenImmersion_spec_of_isNormalScheme`, `isNormalScheme_spec`, and the helper
    `isIntegrallyClosedIn_of_isLocalization`.
- `KunnethMain`: new `bijective_map_prod_of_isNormalScheme_pullback_of_invariance`, the main lemma
  with "`X ×ₖ T` normal" as hypothesis instead of `T` smooth. The smooth version is now a
  one-line corollary.

## 3. What was hard, Lean traps

- `exists_fg_mem_range_map` returns `z ∈ (map _ _).range`. After `obtain ⟨_, rfl⟩` the term is
  `(map _ _).toRingHom z₀`, and `rw` with `map_mul` fails. Fix: `change map R₀.val S₀.val z₀ * … = 0
  at h` first.
- `Module.Flat k S'` for a subalgebra `S'` over a field times out in instance search. Give
  `Module.Flat.of_free` explicitly.
- `IsLocalization.AtPrime` is a `def`: `change IsLocalization (⊥ : Ideal R).primeCompl _` before
  `simpa [Ideal.primeCompl_bot]`.
- `isTranscendenceBasis_of_trdeg_le_of_finite` needs the index type in the universe of the
  algebra: use `PUnit.{u + 1}` and `Cardinal.mk_punit`.
- `MvPolynomial.pUnitAlgEquiv` is deprecated; use `MvPolynomial.uniqueAlgEquiv k PUnit`.
- `IsIntegral.tower_top` with several `toAlgebra` instances needs `(A := …)`.
- For `IsIrreducible`, use `hC.2.open_subset` (it is a pair).
- `IsDomain` from `(⊥ : Ideal R).IsPrime`: `IsDomain.of_bot_isPrime`. Nilradical:
  `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`.

## 4. Blueprint for C1 (`AffineLineOpenInvarianceStatement`), next round

Use `hasAlgClosedBaseChangeInvariance_of_forall_exists_hom`. Setup: `U = Spec k[t]_g`, `W` a
connected cover of `U_{k'}` of degree `d`, `n = d!`.

1. **Kummer cover.**
   - `N := ExposeXIII.KummerAlgebra (fun _ ↦ n) (fun i ↦ t - aᵢ)` over `k[t]_g`, with `aᵢ` the
     roots of `g`. It is étale by `KummerAlgebra.etale` and free, hence finite.
   - Take a connected component `V = Spec N₁` (any one). It is not necessary to prove that `N` is
     a domain: every point of the normalization above `aᵢ` or `∞` has ramification divisible by
     `n`, because `zᵢⁿ = t - aᵢ` and `z₁⁻ⁿ = 1/(t - a₁)`.
2. **Compactification.**
   - `C̄ :=` the relative normalization of `ℙ¹_k` (ExposeXI/ProjectiveLine; proper `toSpec`) in
     `Spec Frac(N₁)`.
   - It is finite over `ℙ¹`, hence proper, by x29's Noether finiteness
     (`Foundations/CommAlg/NoetherFiniteness.lean`, `Foundations/NormalizationFinite.lean`,
     registry A30).
   - It is normal of dimension 1, hence smooth (x29's
     `ExposeX.smooth_of_isNormalScheme_of_topologicalKrullDim_le_one`).
   - `V ⊆ C̄` is the preimage of `U` (ExposeX/PurityDenseOpen
     `isIso_normalizationDesc_pullbackFst_of_isNormalScheme`).
3. **Base change.** `C̄_{k'}` is smooth, hence regular (`ExposeII.isRegularLocalRing_stalk_of_smooth_field`).
   It is connected (`connectedSpace_pullback_of_isAlgClosed_of_connectedSpace`), hence integral
   (`ExposeX.isIntegral_of_isRegularScheme`).
4. **Extension over `C̄_{k'}`.** Let `W' := W ×_U V`. Apply xiii43's
   `ExposeX.finite_etale_fromNormalization_of_isRegularScheme` and
   `exists_iso_pullback_of_fromNormalization` (`ExposeX/TameLiftingPurity.lean`). The local
   hypothesis at the height-one primes over `aᵢ`, `∞` is Abhyankar
   `ExposeXIII.etale_integralClosure_of_dvd` (AbhyankarBasic:359, XIII.5.2 dim 1):
   - `R = 𝒪_{ℙ¹_{k'}, b}`, a DVR;
   - `K'` the function field of `V_{k'}`, `L` that of a component of `W`;
   - tameness is automatic in char 0;
   - ramification of `L` divides `d!`, that of `K'` is divisible by `n`.
   The hard part is the bridge from "localization of the normalization of `Γ(Vᵢ)` in `Γ(W')`" to
   `integralClosure R F`.
5. **X.1.8.** `ExposeX.baseChangeAlgClosedStatement k k' (C̄ → Spec k)` gives `E` on `C̄` with
   `E_{k'} ≅` the extension. Then `E|_V → V → U` is a cover of `U` whose base change maps onto
   `W` through `W' → W`. Take a connected component.

xiii212's `ExposeXI/MultiplicativeGroupCovering.lean` does steps 1, 4 and 5 for `𝔾_m`, ring by
ring: Kummer pullback, then Abhyankar at `T = 0` with `etale_integralClosure_compositum`. Read it
first.

## 5. After C1

- Step 7, non-normal `X`, `Y`: the critic's one-factor morphism descent along the
  normalization, which is finite by x29's A30.
- Step 8: qcqs `X` and arbitrary `Y`. Use ExposeX/ConstantFamily for local constancy and
  ExposeIX/EffectiveGluing.
- Then `theorem kunnethCharZeroStatement`.
- `InvarianceCharZeroStatement ⇒ KunnethCharZeroStatement` also needs steps 7 and 8. For normal
  factors it is already `bijective_map_prod_of_isNormalScheme_of_isNormalScheme` composed with
  `affineLineOpenInvarianceStatement_of_invarianceCharZeroStatement`.
