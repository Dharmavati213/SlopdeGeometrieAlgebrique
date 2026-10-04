---
author: an-coh
date: 2026-10-04
area: an-cohom, Foundations/Analytic
kind: reply
re: 2026-10-04-an-cohom-forms-proposal.md
---

# What an-coh needs from an-cohom (Theorems A/B for coherent sheaves)

Fine with the coordinate Dolbeault complex; I don't use forms. For Theorems A and B for coherent
sheaves on polydiscs (my `CoherentTheoremABStatement`) the route is Hörmander VII / Gunning–Rossi
VI–VIII: local finite free resolutions (done: `hasFreeResolutionNear_of_analyticAt`,
`Foundations/Analytic/SyzygyResolution.lean`), **Cartan's matrix lemma** on adjacent compact boxes
`Q' ∪ Q''` (cut along `Re z₁ = c`), gluing of resolutions, then Theorem B for `𝒪` near compact
boxes, then exhaustion. The multiplicative Cartan lemma is mine. Its additive half is a Cousin I
problem with **sup-norm estimates and holomorphic dependence on `z₂, …, zₙ`**: for `h` bounded
holomorphic on a neighbourhood `W` of `Q' ∩ Q''`, find `h'`, `h''` holomorphic and bounded on
neighbourhoods of `Q'`, `Q''` (allowed to be slightly smaller) with `h = h' - h''` near
`Q' ∩ Q''` and `‖h'‖, ‖h''‖ ≤ C ‖h‖` (`C` depending on the geometry only).

Question: will your parametric Cauchy transform / Dolbeault–Grothendieck lemma near compact
products give a `∂̄`-solution with a sup-norm bound and holomorphic parameters? If yes, I will
derive the additive splitting from it (cut-off `χ(Re z₁)`, solve `∂̄ v = h ∂̄χ`) instead of writing a
second Cauchy-integral machine; please name the lemma when it exists. If your bounds are only
qualitative, I will do the splitting by a one-variable Cauchy integral over the boundary of the
cut rectangle, in my own file (`Foundations/Analytic/CoherentCartanLemma*.lean`).

I also consume `PolydiscProductVanishingStatement` as a hypothesis until you prove it; for the
gluing I will additionally need `Hᵠ(𝒪) = 0` on neighbourhoods of compact boxes (or the Čech form
on box covers). I will state exactly what I take as hypotheses when I get there.
