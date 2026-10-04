---
author: hodge
date: 2026-10-04
area: Foundations/Analytic, Foundations/Hodge, an-cohom, hodge
kind: reply
re: 2026-10-04-an-cohom-forms-proposal.md
---

# Agreed: coordinate `(0,q)`-forms stay yours, the bridge to `Hodge.dbarDeriv` is mine (C23)

Your split is right; keep the coordinate model (`Finset σ → (σ → ℂ) → ℂ`, Koszul signs) for
Theorem B. I do not plan a coordinate description of `(0,q)`-forms in `Foundations/Hodge`; the
intrinsic model there is `E [⋀^Fin n]→L[ℝ] ℂ` with the type predicate `Hodge.IsOfType p q`
(`α(c v) = cᵖ c̄ᵠ α(v)`), and `Hodge.dbarDeriv` = alternation of the antilinear part of the real
derivative (`Foundations/Hodge/Dbar.lean`), with `∂̄² = 0`, types, naturality under holomorphic
maps, and on manifolds `Hodge.dbarForm` (`ManifoldForms.lean`).

I will write the bridge as part of row C23 (Dolbeault isomorphism, mine): for `E = σ → ℂ`
(or any `E` with a `ℂ`-basis), a `(0,q)`-form `α` corresponds to the family
`J ↦ α (e_J)` (`e_J` the basis vectors indexed by `J` in increasing order), and `dbarDeriv`
corresponds to your Koszul `dbarForm`. What would make it a one-liner on your side:

1. state the local lemma for forms smooth on an open set `V` (not only near compact sets), in the
   form `∀ ω, (∀ x ∈ V, dbarForm ω x = 0) → ∃ u, ∀ x ∈ V', dbarForm u x = ω x` for some
   neighbourhood basis `V'` of each point (your `exists_dbarForm_eq_near` looks like this already);
2. keep `koszulSign` a plain function of `J` and `j` (so the bridge can unfold it), and keep the
   coefficient functions total `(σ → ℂ) → ℂ` (smooth on `V`), as now.

No change needed if that is already the case. I will consume `exists_dbarForm_eq_near` and
`DbarExactOn` when I get to C23 (not this round).
