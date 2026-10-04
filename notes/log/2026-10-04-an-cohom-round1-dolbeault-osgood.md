---
author: an-cohom
date: 2026-10-04
area: Foundations/Analytic, Foundations/Cohomology, C10, C27, xii4, an-coh, hodge, sga1-oos-coord
kind: handoff
---

# an-cohom round 1: Dolbeault resolution of 𝒪 on ℂⁿ, Osgood, Theorem B reduced to global ∂̄

Everything below builds with `lake build <module>`, is sorry-free, and `#print axioms` gives only
`propext`, `Classical.choice`, `Quot.sound`. No `maxHeartbeats`. No pre-wave-1 file edited; the
files handed over by xii4 (CartanInfinite, DolbeaultSheaf, DolbeaultPartial, the Cousin edit) were
repaired/finished.

## Done (all `AnalyticGeometry.*` unless noted)

- `Foundations/Cohomology/CartanInfinite.lean` (handed over, finished): Cartan's criterion for
  families indexed by arbitrary types `TopCat.Sheaf.H'_subsingleton_of_cechAcyclicFor`,
  `H'_one_subsingleton_of_cech`, `H'_subsingleton_of_forall_cech`; dimension shifting
  `subsingleton_H'_one_of_shortExact`, `subsingleton_H'_succ_succ_of_shortExact`; **new**:
  `TopCat.Sheaf.shortExact_of_sections` (left exact on sections + locally surjective ⇒ short exact),
  `isLimitKernelForkOfSections`.
- `DolbeaultSheaf.lean`: `smoothSheaf E F` is now **F-valued** (API change from xii4's draft:
  `smoothSheaf E` ⇒ `smoothSheaf E ℂ`; nobody else imported it). Fine: `cechComplex_smoothSheaf_exactAt`;
  acyclic: `H'_smoothSheaf_subsingleton`.
- `DolbeaultPartial.lean`: `dbarPartial j f` (∂/∂z̄ⱼ), sheaf maps `holomorphicToSmooth`,
  `dbarPartialHom`; one variable: `dolbeaultShortComplex_shortExact`,
  `H'_holomorphicAbSheaf_subsingleton_of_dbar`, **Theorem B on a disc**
  `H'_polydiscProduct_one_zero_zero_subsingleton` (case c=1, a=b=0 of
  `PolydiscProductVanishingStatement`).
- `DolbeaultForms.lean`: coordinate `(0,q)`-forms `Finset σ → (σ → ℂ) → ℂ` (needs `[LinearOrder σ]`
  for signs `koszulSign`), `dbarForm`, `dbarForm_dbarForm` (∂̄²=0),
  `dbarPartial_dbarPartial_comm`, `dbarPartial_eq_zero_of_dbarForm_eq_zero` (closed forms involving
  only `A` are holomorphic in the other variables).
- `DolbeaultParam.lean`: `cauchyTransformIn m h` (Cauchy transform in `zₘ`, other variables as
  parameters; hypotheses bundled in `CauchyTransformInData`): smooth
  (`contDiffOn_cauchyTransformIn`, via mathlib's `contDiffOn_convolution_left_with_param_comp`),
  `dbarPartial_cauchyTransformIn_self`, `dbarPartial_cauchyTransformIn_of_ne` (holomorphy in
  parameters preserved, via `hasFDerivAt_convolution_right_with_param` +
  `convolution_precompR_apply`).
- `DolbeaultLocal.lean`: **Dolbeault–Grothendieck lemma near compact products** (Hörmander 2.3.2)
  `exists_dbarForm_eq_near_compact`, `exists_dbarForm_eq_of_involves`, `exists_dbarForm_eq_near`;
  `exists_cutoff` (smooth cutoff on ℂ, 1 near compact K, compact support in W).
- `DolbeaultFormSheaf.lean`: `FormCoeff σ q`, `formSheaf σ q` (fine), `closedFormSheaf σ q`,
  `dbarOn`, `dbarFormHom`, **`dolbeaultSeq_shortExact`** (`0 → Zᵠ → 𝒞^{0,q} → Z^{q+1} → 0`),
  `DbarExactOn V q`, `H'_closedFormSheaf_subsingleton`.
- `Osgood.lean` (new row **C27**, proved): `torusIntegral_cauchy` (Cauchy formula on polydiscs,
  `Fin n`), `cauchyCoeff`, `norm_cauchyCoeff_le`, `hasSum_cauchyCoeff`, `hasSum_prod_fin`,
  **`analyticAt_of_continuousOn_of_separately`** (Osgood, any finite σ), `analyticAt_of_differentiableOn`,
  `analyticAt_tsum_of_summable_norm` (Weierstrass for normally convergent series).
- `DolbeaultHolomorphic.lean`: `analyticAt_of_dbarPartial_eq_zero'` (smooth ∂̄-closed ⇒ analytic),
  `holomorphicToForm`, `holomorphicSeq_shortExact` (`0 → 𝒪 → 𝒞^{0,0} → Z¹ → 0`), and
  **`H'_holomorphicAbSheaf_subsingleton_of_dbarExact`**: `Hⁿ(V, 𝒪) = 0` for `n > 0` as soon as
  `∀ q, DbarExactOn V q`. This is the whole sheaf-theoretic half of Theorem B.
- `DolbeaultGlobal.lean` (Hörmander 2.3.3 on product domains): `ProductExhaustion Ω` (compact
  products `Kᵛ ⊆ interior Kᵛ⁺¹` exhausting `∏ Ωᵢ`), `ProductExhaustion.IsRunge` (functions analytic
  near `Kᵛ⁺¹` are uniform limits on `Kᵛ` of functions analytic on `∏ Ωᵢ`); positive degree
  `exists_dbarForm_eq_global_succ`/`dbarExactOn_pi_succ` (no Runge needed; correction by
  `∂̄(ψw)`, `exists_productCutoff`); degree 0 `exists_dbarForm_eq_global_zero`/`dbarExactOn_pi_zero`
  (from `IsRunge`, Weierstrass); **`H'_holomorphicAbSheaf_two_le`** (`H^{n+2}(∏Ωᵢ, 𝒪) = 0` for any
  product with an exhaustion) and **`H'_holomorphicAbSheaf_subsingleton_of_isRunge`**
  (`Hⁿ(∏Ωᵢ, 𝒪) = 0`, `n > 0`, for a Runge exhaustion); `dbarExactOn_of_exists` (coefficient form
  ⇒ `DbarExactOn`); `H'_closedFormSheaf_subsingleton_of_le` (DolbeaultFormSheaf.lean).

## What is left for `PolydiscProductVanishingStatement` (my plan, in order)

1. **Runge property** (`ProductExhaustion.IsRunge`) for the standard exhaustion of
   `polydiscProduct c a b r` (file `Runge*.lean`): `Kᵢᵛ` = closed disc of radius
   `rᵢ (1 - 1/(ν+2))` (Δ factors; if `rᵢ ≤ 0` then Ω = ∅ and everything is trivial), closed disc of
   radius `ν + 1` (ℂ factors), closed annulus `1/(ν+2) ≤ |z| ≤ ν + 2` (ℂ* factors); approximants
   are Laurent polynomials (negative powers only in ℂ* coordinates).
   - Polydisc part (b = 0) is cheap with C27: rescale coordinates to equal radii, then
     `hasSum_cauchyCoeff` + `norm_cauchyCoeff_le` give `|aₐ zᵅ| ≤ M ∏ θ^{αⱼ}` with `θ < 1` on the
     smaller polydisc; truncate to a finite set of multi-indices with small tail (summable
     multi-geometric `hasSum_prod_geometric`); the partial sum is a polynomial, analytic everywhere.
   - Annuli: one route is induction on the number of variables, one variable at a time: Laurent
     truncation in `z₀` with explicit geometric error (annulus Cauchy formula from mathlib's
     `circleIntegral_eq_of_differentiable_on_annulus_off_countable` applied to `dslope`), coefficients
     `cₘ(z') = (2πi)⁻¹∮ h(ζ, z') ζ^{-m-1}` analytic in `z'` by Osgood (continuity:
     `continuous_parametric_intervalIntegral_of_continuous`; separate holomorphy: differentiate under
     the integral, `hasDerivAt_integral_of_dominated_loc_of_deriv_le`). Alternative: a polyannulus
     Cauchy formula generalizing `torusIntegral_cauchy` (one or two circles per coordinate).
2. **Exhaustion** of `polydiscProduct c a b r` as a `ProductExhaustion` (`Ωᵢ` = disc, ℂ, ℂ*).
3. **Final assembly**: `σ = Fin c ⊕ Fin a ⊕ Fin b` has no `LinearOrder` instance: use
   `letI := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective` (only
   `H'_holomorphicAbSheaf_subsingleton_of_isRunge` needs it; `holomorphicAbSheaf` does not), and
   identify `polydiscProduct c a b r` with `univ.pi Ω` as an `Opens`.
4. Promised to an-coh: `norm_cauchyTransformIn_le` (sup-norm bound for the parametric Cauchy
   transform), see `2026-10-04-an-cohom-reply-an-coh-hodge.md`.

## What was hard / lessons

- `ω` is a reserved token under `open scoped ContDiff` (it is `⊤ : ℕ∞ω`): never name a variable `ω`.
- `ContDiffAt ℝ ∞ f x` is **not** an open condition (only finite orders are): don't try to
  propagate it to a neighbourhood; state smoothness at every point of an open set.
- Named arguments with lambdas (`(g := fun β ↦ …)`) need binder types, else elaboration times out
  (`hasSum_prod_fin`); `Equiv.summable_iff`/`hasSum_iff` need the function given explicitly
  (`(f := …)`) to avoid higher-order unification timeouts.
- Recursive theorems by pattern matching on `n` timed out in the equation compiler; `induction n`
  in tactic mode was fine.
- `if_pos`/`if_neg` are deprecated in this mathlib: use `ite_eq_left`/`ite_eq_right`.

## Not done / hygiene

- `unusedFintypeInType` linter warnings remain in `DolbeaultPartial.lean`, `DolbeaultForms.lean`
  (`dbarPartial` no longer needs `[Fintype σ]` in its type since mathlib's `fderiv` works on
  topological vector spaces); cosmetic.
- Not in barrels (coordinator): see coordinator_requests in the structured result.
