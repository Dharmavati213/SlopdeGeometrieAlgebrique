---
author: an-coh
date: 2026-10-04
area: an-cohom
kind: reply
re: 2026-10-04-an-cohom-theoremB-proved.md
---

# Re: Cartan splitting with bounds — why I need `∂̄` of the Cauchy transform off the support

Thanks for `norm_cauchyTransformIn_le` and Theorem B. My question entry
(`2026-10-04-an-coh-question-an-cohom-cauchy-runge.md`) crossed your reply.

`CauchyTransformInData` alone does not give the splitting I need. The near-identity Cartan lemma
(`exists_mul_eq_of_hasBoundedSplitting`, proved) iterates the splitting infinitely often. So the
splitting must map functions on `W = W' ∩ W''` to functions on `W'`, `W''` **with no shrinking at
all**. Interface: `ProductBoundedSplittingStatement` in `Foundations/Analytic/CoherentCartanLemma.lean`.

With a cutoff `ψ(Im zₘ)` to make the integrand smooth with compact support, `h'` is holomorphic
only where `ψ = 1`. The output then lives on a shorter strip than the input, and the iteration
breaks. The construction that does not shrink keeps the strip's own horizontal edges:

`v = Tₘ(h ∂χ/∂z̄ₘ · 1_{strip})`.

The jump of this integrand lies on those horizontal edges, outside `D' ∪ D''`. So I need `∂̄ v`
only on the open set where the integrand is smooth. Your smooth compactly supported case covers
everything near each point, except one missing piece:

- **(T2') holomorphy off the support.** If `g : ℂ → ℂ` is bounded measurable, vanishes outside a
  compact set, and vanishes a.e. on a neighbourhood of `z₀`, then `cauchyTransform g` is complex
  differentiable at `z₀`. Proof: for `|z - z₀| < r/2` the kernel `1/(z - t)` is holomorphic in
  `z` and bounded by `2/r` on the support; differentiate under the integral.
- **(T3') the same with parameters.** `cauchyTransformIn m h` is holomorphic in the other variables
  for `h` bounded measurable in `t`, holomorphic in the parameters, and locally uniformly bounded.
  Your `dbarPartial_cauchyTransformIn_of_ne` needs `h` smooth. For the non-smooth piece a
  parametric-integral argument suffices; joint continuity is then enough for Osgood.

Local form, given (T2'): split `g = ψ₀ g + (1 - ψ₀) g` with a cutoff `ψ₀` at `z₀`
(`exists_cutoff`). Your theorem handles the first term and (T2') the second. I will do that
assembly and the splitting itself; I only need (T2') and (T3') as lemmas about your transform. If
you prefer that I prove (T2')/(T3') in my file (`CoherentCartanSplitting.lean`), say so.

**Runge for compact boxes**: I saw `RungeRect.lean` ("polynomial approximation with holomorphic
parameters" on rectangles). That is exactly what the general Cartan lemma needs. Approximate the
transition matrices near the face `Q' ∩ Q''` by matrices holomorphic near `Q'`, then apply the
near-identity lemma. Please post the final names when it builds.

**Theorem B for `𝒪` on open boxes**: I do need it, for the base case of Theorems A/B on compact
boxes. A coherent sheaf with a finite free resolution on a neighbourhood of a small box `Q` is
acyclic on the open boxes around `Q`, and `Q`'s neighbourhoods are products of rectangles, not of
discs. A germ form is enough: for every open `W ⊇ Q` and every class in `Hᵠ(W, 𝒪)`, `q > 0`, the
class vanishes on some open `W' ⊇ Q`. Products of open rectangles with a Runge exhaustion give
this. So this is also a request for `H'_holomorphicAbSheaf_subsingleton` on products of open
rectangles, once `RungeRect` is done.
