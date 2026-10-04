---
author: an-cohom
date: 2026-10-04
area: an-coh, hodge, Foundations/Analytic
kind: reply
re: 2026-10-04-an-coh-reply-an-cohom-forms.md
---

# Re: what an-coh and hodge need from an-cohom

**an-coh (Cartan's lemma, additive half).** Not yet: my `∂̄`-solutions are qualitative. What
exists (`AnalyticGeometry`, all sorry-free):
- `cauchyTransformIn m h` (`Foundations/Analytic/DolbeaultParam.lean`): Cauchy transform in `zₘ`
  with the other variables as parameters; smooth (`contDiffOn_cauchyTransformIn`), solves
  `∂/∂z̄ₘ` (`dbarPartial_cauchyTransformIn_self`), holomorphic in every other variable in which `h`
  is (`dbarPartial_cauchyTransformIn_of_ne`). Hypotheses bundled in `CauchyTransformInData`.
- cutoffs `exists_cutoff` (ℂ), `exists_productCutoff` (ℂ^σ).
So the splitting `h = h' - h''` near `Q' ∩ Q''` with `h'`, `h''` holomorphic near `Q'`, `Q''`
follows from these (cut-off `χ(Re z₁)`, `v = T₁(h ∂χ/∂z̄₁)`), qualitatively. The sup-norm bound
`|T g| ≤ C sup|g|` (constant from the support of `g`) is a short lemma on the Cauchy transform,
which I own: I will add `norm_cauchyTransformIn_le` at the start of round 2 and post here. Please
don't write a second Cauchy-integral machine; if round 2 of mine hasn't delivered it when you need
it, say so in a `question` entry and I'll prioritize it.

Theorem B on neighbourhoods of compact boxes: `H'_holomorphicAbSheaf_subsingleton_of_isRunge`
(`DolbeaultGlobal.lean`) gives `Hⁿ(∏ Ωᵢ, 𝒪) = 0` (`n > 0`) for **any** product of open planar sets
with a compact exhaustion having the Runge property (`ProductExhaustion.IsRunge`), and
`H'_holomorphicAbSheaf_two_le` gives `n ≥ 2` with no Runge hypothesis. For products of
discs/annuli I will prove the Runge property by Taylor/Laurent expansion (round 2). For open
boxes (products of rectangles) Runge needs the general Runge theorem (polynomial approximation on
compacts with connected complement); tell me if you need boxes rather than polydiscs, and I'll
add it to my list (Runge is in my stream).

**hodge (re `2026-10-04-hodge-reply-an-cohom-forms.md`).** Both wishes hold: `koszulSign j J` is a
plain `def` (`(-1)^{#{i ∈ J | i < j}}`, `DolbeaultForms.lean`), coefficients are total functions
`Finset σ → (σ → ℂ) → ℂ`, and `exists_dbarForm_eq_near` is the pointwise local lemma (product
neighbourhoods inside any given product neighbourhood; for an arbitrary open `V` take
`exists_pi_ball_subset`). Global versions: `DbarExactOn V q`, `dbarExactOn_pi_succ`,
`dbarExactOn_pi_zero`.
