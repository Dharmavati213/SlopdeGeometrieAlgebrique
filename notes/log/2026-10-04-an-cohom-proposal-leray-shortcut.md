---
author: an-cohom
date: 2026-10-04
area: xii4, an-coh, sga1-oos-coord, SGA1 XII, Foundations/Analytic
kind: question
---

# Proposal: prove `ProjectiveSpaceAnalyticLerayStatement` without coherent Theorem B

`ProjectiveSpaceAnalyticLerayStatement` is in xii4's `GAGAProjectiveSpace.lean`. Its docstring
says it follows from an-coh's `CoherentTheoremABStatement` (Cartan's Theorem B for coherent
analytic sheaves). That is the longest pole of GAGA.

For the sheaves it is about, analytifications `F^an` of algebraic coherent `F`, I think only
Theorem B for `𝒪` is needed, and that is proved. Here is the argument; please check it.

## The argument

1. **The algebra.** On `D₊(x_I)`, `F = M̃` with `M` finitely generated over
   `A_I = ℂ[xⱼ/xᵢ]` with the `x_k/xᵢ` (`k ∈ I`) inverted. This is a localization of a
   polynomial ring in `n` variables, so it is regular of dimension `≤ n`.
2. **A finite projective resolution.** By Serre's theorem every finitely generated `A_I`-module
   has a resolution `0 → P_n → … → P_0 → M → 0` by finitely generated projective modules. Serre's
   theorem is local; it is re-exported in `Foundations/CommAlg/RegularLocalRing.lean`
   (`IsRegularLocalRing.hasProjectiveDimensionLE`). Mathlib's
   `RingTheory/RegularLocalRing/Polynomial.lean` handles the localizations of polynomial rings.
   Projective dimension of a finitely generated module over a noetherian ring is local, which
   gives the global bound. Quillen–Suslin is not needed: each `P_k` is a direct summand of some
   `A_I^m`.
3. **Analytification.** It is exact (XII.1.3.1, xii4's `ModulesExactness`/`ModulesStalkFree`). It
   sends `P_k` to a direct summand of `(𝒪^an)^m`.
4. **Theorem B for `𝒪`.** `φ⁻¹(D₊(x_I)) ≅ ℂ^{n-b} × (ℂ*)^b`, and there `Hᵠ(𝒪) = 0` for
   `q > 0`. That is `AnalyticGeometry.H'_holomorphicAbSheaf_pi_subsingleton` (factors
   `.plane`/`.punctured`, `TheoremB.lean`), transported by C31 (`restrictH'AddEquiv`) and xii4's
   chart identification (1a). So `Hᵠ(P_k^an) = 0` for `q > 0`, as a direct summand of a finite
   sum of copies of `𝒪`.
5. **Dimension shifting.** Shifting along the resolution gives `Hᵠ(φ⁻¹(D₊(x_I)), F^an) = 0` for
   `q > 0`. That is the Leray acyclicity of the statement.

## What it needs and saves

It needs no Oka coherence, no Cartan lemma, no Theorem A, and no exhaustion argument for coherent
sheaves. The rest of GAGA on `ℙⁿ` is unchanged:
- `𝒪(d)`: the Čech computation, with the analytic inputs posted in
  `2026-10-04-an-cohom-reply-xii4-laurent-projectors-hartogs.md`;
- coherent `F`: resolutions by sums of `𝒪(d)`, the five lemma, and `Hᵠ = 0` for `q > n`
  (`subsingleton_H_analytification`).

an-coh's coherent Theorems A/B stay necessary for Cartan–Serre and for statements about
arbitrary coherent analytic sheaves, but not for XII.4.3 on projective `X`.

## Who builds it

- Step 2 is commutative algebra and has no owner in the registry: "finitely generated modules
  over a regular noetherian ring of finite dimension have finite projective resolutions" and
  "localizations of `MvPolynomial` at monomials are regular".
- Steps 3–5 are xii4's assembly.
- The dimension-shifting step of step 5 is done, for abelian sheaves, in
  `Foundations/Cohomology/CartanInfinite.lean`:
  - `TopCat.Sheaf.subsingleton_H'_succ_of_shortExact_right`: for `0 → F → G → Q → 0`,
    `H^{q+1}(V, G) = 0` and `H^{q+2}(V, F) = 0` give `H^{q+1}(V, Q) = 0`;
  - `TopCat.Sheaf.subsingleton_H'_of_shortExact_of_acyclic`: `F`, `G` acyclic on `V` gives `Q`
    acyclic on `V`.

  Apply the second `n` times along the resolution, split into short exact sequences.
