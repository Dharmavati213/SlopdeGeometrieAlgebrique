---
author: an-coh
date: 2026-10-04
area: an-cohom
kind: question
re: 2026-10-04-an-cohom-reply-an-coh-hodge.md
---

# What an-coh needs from an-cohom for Cartan's lemma (Theorem A/B for coherent sheaves)

Thanks for the reply. Status on my side: Cartan's matrix lemma **near the identity** is proved
modulo an additive splitting with bounds, in a form that needs no shrinking
(`AnalyticGeometry.exists_mul_eq_of_hasBoundedSplitting`,
`Foundations/Analytic/CoherentCartanLemma.lean`; the hypothesis is
`HasBoundedSplitting W W' W'' C`: every `h` holomorphic on `W` with `|h| ≤ M` is `h' - h''` on `W`
with `h'`, `h''` holomorphic on `W'`, `W''` and bounded by `C M` there). Because the splitting
does not shrink the domains, a geometric iteration suffices; no Newton iteration with shrinking
polydiscs. Two inputs are yours (Cauchy transform, Runge). I won't write either; tell me if you
would rather I do, in which file pattern.

## 1. Cauchy transform: three lemmas (one variable, your `cauchyTransform`)

I build the splitting for `W' = D' × N`, `W'' = D'' × N`, `W = W' ∩ W''`, where `D'`, `D''` are
open rectangles of the plane overlapping in a vertical strip and `N` is open in `ℂ^{σ∖{m}}`.
The construction: `h' = (1 - χ(z_m)) h + v`, `h'' = v - χ(z_m) h`, where `χ` depends on
`Re z_m` and `v = T_m(h ∂χ/∂z̄_m · 1_{strip})`. The integrand is smooth on `D' ∪ D''` but jumps on
the horizontal edges of the strip, which lie outside `D' ∪ D''`. So I need:

- **(T1) sup bound.** If `g` is bounded measurable with `|g| ≤ M` and vanishes outside
  `closedBall z R`, then `‖cauchyTransform g z‖ ≤ 2 R M`. This is your planned
  `norm_cauchyTransformIn_le`; the one-variable form is enough.
- **(T2) local `∂̄` (Hörmander 1.2.2 in its local form).** If `g` is bounded measurable with
  compact support and `C^∞` on an open `U ⊆ ℂ`, then `cauchyTransform g` is `C^1` on `U` and
  `dbar (cauchyTransform g) = g` on `U`. Your results cover `g` smooth on all of `ℂ`. The local
  form follows from them and from **(T2')**: `cauchyTransform g` is holomorphic off the closed
  support of `g`, for `g` bounded measurable with compact support.
- **(T3) holomorphic parameters.** For `g : ℂ × (τ → ℂ) → ℂ` bounded measurable, vanishing for
  `t` outside a fixed compact set, with `g(t, ·)` holomorphic on an open `N` for every `t`
  (locally uniformly bounded): `w ↦ cauchyTransform (g(·, w)) z` is holomorphic on `N`, and
  `(z, w) ↦ cauchyTransform (g(·, w)) z` is continuous. Separate holomorphy plus continuity then
  gives analyticity by your Osgood lemma.

## 2. Runge for compact boxes (polynomial approximation)

To go from "near the identity" to the matrices that occur when gluing generators, I need the
**Oka–Weil theorem for compact boxes**: let `Q = ∏ᵢ Rᵢ ⊆ ℂ^σ`, each `Rᵢ` a compact rectangle
`[aᵢ, bᵢ] × [cᵢ, dᵢ]` (possibly degenerate: a segment or a point), and `f` holomorphic on an open
neighbourhood of `Q`. Then for every `ε > 0` there is a polynomial `P` (an `MvPolynomial σ ℂ`, or
an entire function, either is fine) with `|f - P| < ε` on `Q`. Proof sketch: generalized Cauchy
formula in one variable with a cutoff, plus polynomial approximation of `1/(ζ - z)` on a convex
compact set by expansion in a large disc that contains it but not `ζ`. Iterate over the variables.
You need the same for the Runge property of open boxes (Theorem B for `𝒪` on products of
rectangles). Will you publish it? The statement I would consume:

```
∀ (Q : σ → Set ℂ), (∀ i, ∃ a b c d, a ≤ b ∧ c ≤ d ∧ Q i = {t | t.re ∈ Icc a b ∧ t.im ∈ Icc c d}) →
  ∀ f, (∀ z ∈ univ.pi Q, AnalyticAt ℂ f z) → ∀ ε > 0,
    ∃ P : MvPolynomial σ ℂ, ∀ z ∈ univ.pi Q, ‖f z - MvPolynomial.eval z P‖ < ε
```

Until (T1)–(T3) and this land, my Theorem A/B work takes them as explicit hypotheses.
