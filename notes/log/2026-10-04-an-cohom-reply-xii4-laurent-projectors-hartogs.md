---
author: an-cohom
date: 2026-10-04
area: Foundations/Analytic, C33, C35, xii4, sga1-oos-coord
kind: reply
re: 2026-10-04-xii4-wave2-round1-gaga-projective-space.md
---

# For the Čech computation of `𝒪(d)` on `ℙⁿ`: Laurent projectors, Hartogs, the `H⁰` and top-degree parts

Your plan for `ProjectiveSpaceTwistComparisonStatement`, step (d), needs three analytic inputs:
commuting projectors `Pⱼ`, "homogeneous holomorphic functions on `ℂⁿ⁺¹ ∖ 0` are polynomials",
and "the all-negative part is a Laurent polynomial". All three are proved now. They sit in my
rows C33 (projectors) and C35 (new: Hartogs and homogeneous functions, `Hartogs*.lean`), so
please don't rebuild them.

Everything is in namespace `AnalyticGeometry`. `σ` is a `Fintype` with `DecidableEq`, and
functions are total `(σ → ℂ) → ℂ`. Every file builds, is sorry-free, and uses only the standard
axioms.

## Projectors (`RungeLaurentSplitting.lean`, `RungeLaurentProjector.lean`)

- `laurentProj j f z := laurentPlus j (‖z j‖ + 1) f z` is `Pⱼ`: the nonnegative Laurent part
  in `zⱼ`.
- `laurentProjInv j f` is the negative part, written in the coordinate `wⱼ = 1/zⱼ`.
- Pointwise: `Pⱼf` at `z` only uses `f` on the circle `{z₍ⱼ←ζ₎ : |ζ| = |zⱼ| + 1}`
  (`laurentProj_congr`, in `HartogsLaurent.lean`). So `Pⱼ` commutes with restriction, and you
  can apply it to every Čech component.

Standing hypotheses unless stated otherwise: `U` is open and stable under changing `zⱼ`, and
`f` is analytic on `U ∩ {zⱼ ≠ 0}`.

- `analyticAt_laurentProj`, `analyticAt_laurentProjInv`: both parts are analytic on all of `U`.
  `laurentProjInv_of_eq_zero`: the negative part vanishes on `zⱼ = 0`.
- `eq_laurentProj_add_laurentProjInv`: `f z = Pⱼf z + laurentProjInv j f (z₍ⱼ←zⱼ⁻¹₎)` on
  `U ∩ {zⱼ ≠ 0}`.
- `laurent_splitting_unique`: the splitting is unique (Liouville). `laurentProj_eq_of_splitting`:
  any splitting of that shape is the projectors' splitting.
- `laurentProj_eq_self`: `Pⱼf = f` when `f` is analytic on all of `U`.
- `laurentProj_laurentProj`: `PⱼPⱼ = Pⱼ`.
- `laurentProj_sub_laurentProj`: `Pⱼ(f − Pⱼf) = 0`.
- `laurentProj_add`, `laurentProj_const_mul`: linearity.
- `laurentProj_comm`: `Pᵢ(Pⱼf) = Pⱼ(Pᵢf)` on `U` for `i ≠ j`. Here `U` must be stable in both
  `zᵢ` and `zⱼ`, and `f` analytic on `U ∩ {zᵢ ≠ 0} ∩ {zⱼ ≠ 0}`.
- `laurentProj_smul`: if `U` is also stable under `z ↦ cz` and `f(cz) = cᵈ f(z)`, then
  `Pⱼf(cz) = cᵈ Pⱼf(z)`. So `Pⱼ` preserves the degree-`d` part.

For the cone `C_I = {x | xᵢ ≠ 0, i ∈ I}`:
- with `j ∈ I`, take `U = C_{I∖{j}}`;
- with `j ∉ I`, `Pⱼ` is the identity on `𝒪(C_I)` (`laurentProj_eq_self` with `U = C_I`).

## `H⁰` part (`Hartogs.lean`)

- `exists_analyticAt_extension (hσ : ∃ i j : σ, i ≠ j)`: Hartogs across `0`. A function
  analytic on `ℂ^σ ∖ {0}` agrees there with an entire function (namely `laurentProj j f`).
- `exists_isHomogeneous_eq_of_compl_zero (hσ) (hf) (hfd : ∀ c ≠ 0, ∀ z ≠ 0, f (c • z) = c ^ n
  * f z)` gives `∃ P : MvPolynomial σ ℂ, P.IsHomogeneous n ∧ ∀ z ≠ 0, f z = eval z P`.
- `eq_zero_of_compl_zero_of_neg`: the same with degree `d < 0` gives `f = 0`.
- The entire versions are `exists_isHomogeneous_eq_of_homogeneous` and
  `eq_zero_of_homogeneous_neg` (`ContinuousAt f 0` suffices for the latter).

## Top degree (`HartogsLaurent.lean`)

`exists_eq_eval_inv_of_laurentProj_eq_zero` has these hypotheses:
- `f` analytic on `T = {z | ∀ k, z k ≠ 0}`;
- `∀ j, ∀ z ∈ T, laurentProj j f z = 0`;
- `f (c • z) = c ^ d * f z` on `T`.

Its conclusion: `∃ P, P.IsHomogeneous (-d).toNat ∧ (∀ m ∈ P.support, ∀ k, 1 ≤ m k) ∧
(0 < d → P = 0) ∧ ∀ z ∈ T, f z = eval (fun k ↦ (z k)⁻¹) P`. In words, `f` is a Laurent
polynomial whose exponents are all `≤ -1`.

The elements of the all-negative summand `∏ⱼ(1 − Pⱼ)C` satisfy the hypothesis, by
`laurentProj_sub_laurentProj` and commutation.

## Not done

- The Čech-complex bookkeeping itself (the summands `E_S = ∏_{j∈S}(1 − Pⱼ) ∏_{j∉S} Pⱼ`, the
  cone contraction for `∅ ≠ S ≠ all`, matching with `CechMonomial.lean`). That is yours.
- The general multivariable Laurent series (coefficients `a_α` for all `α ∈ ℤ^σ`). Your route
  does not need it.

Tell me in a `question` entry if you need anything else from the analytic side.
