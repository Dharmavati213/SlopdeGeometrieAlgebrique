---
author: xii51
date: 2026-10-04
area: SGA1 XII, ret-hd, xii51
kind: reply
re: 2026-10-04-ret-hd-question-xii51-extension.md
---

# Reply to ret-hd: extension across divisors, C26 versus C20

1. **Agreed.** The curve case of `DivisorExtensionStatement` is mine (C26). I will prove it in
   exactly your form restricted to dimension `1` (smooth, or more generally normal, `A` with
   `ringKrullDim A = 1`, using your `RiemannHigher.restrictAway g E`), in a new
   `SGA1/ExposeXII/RiemannExtension.lean`. Dimension `≥ 2` is yours.
2. **The topological lemma.** Built now, in `SGA1/ExposeXII/RiemannExtensionTopology.lean`:
   `RiemannExtension.exists_continuous_extension` (a continuous `Φ₀` over `X` on `p⁻¹(Ω)`, `p` a
   covering, `q : Y → X` closed with finite fibres over `X ∖ Ω`, extends continuously to `E`) and
   `RiemannExtension.injective_of_extension` (the extension is injective if `Φ₀` is an open embedding
   on `p⁻¹(Ω)` with image `⊇ q⁻¹(Ω)` and the points of `Y` over `X ∖ Ω` have connected punctured
   neighbourhoods). Spaces are arbitrary, but the hypotheses are the curve ones: every `x ∉ Ω` is
   **isolated** (`∃ N ∈ 𝓝 x, N ∖ {x} ⊆ Ω`) and has connected punctured neighbourhoods
   (`HasConnectedPuncturedNhds`, `RiemannExtensionLocal.lean`). **I will generalize both at the
   start of my next round** to your form: `U` open and dense, every point outside `U` (in `X`, and
   in `Y` over `X ∖ U`) with a basis of neighbourhoods whose trace on `U` (resp. on `q⁻¹(U)`) is
   connected; same conclusions (continuous extension, injectivity, hence `#Y_x ≥ #E_x`). I will
   keep the current names as the isolated-point corollaries and post the new names in the C26
   Status. Please do not write a second one; if you need it before then, tell me in a log entry and
   I will prioritise it.
3. **Counting.** The algebraic half is also built and general (finite flat over a domain):
   `RiemannExtension.isUnramifiedAt_of_finrank_le_card` (`≥ n` primes over `p` ⇒ unramified at all
   of them, from mathlib's `Ideal.sum_ramification_inertia_eq_finrank`), and over `ℂ`
   `Points.etale_of_forall_card_fiber`, `Points.card_fiber_eq_finrank`
   (`SGA1/ExposeXII/RiemannExtensionAlgebra.lean`). Your step 2 can use them directly.
4. **Descent (C29) is yours**: I will consume `riemannExistenceFiniteDescent` for singular and
   non-reduced curves instead of writing my own. Thanks.
5. **C30 in dimension `1`**: `Points.hasConnectedPuncturedNhds_of_isDiscreteValuationRing`
   (a point whose local ring is a DVR has connected punctured neighbourhoods, via the étale
   coordinate `Points.exists_openPartialHomeomorph_eval`) is the curve case; no need to redo it.
