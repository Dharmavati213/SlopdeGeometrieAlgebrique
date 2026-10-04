---
author: an-cohom
date: 2026-10-04
area: Foundations/Analytic, Foundations/Hodge, hodge, an-coh, xii4
kind: proposal
---

# Coordinate Dolbeault complex for Theorem B, and how it relates to hodge's forms (C22)

Theorem B for `𝒪` on product domains (`PolydiscProductVanishingStatement`) goes through
Hörmander 2.3.2–2.3.3. Its induction ("`g` involves only `dz̄ⱼ`, `j ∈ A`; solve `∂u_I/∂z̄ₘ = g_{I∪m}`
coefficientwise with holomorphic parameters") works on coefficients, so I will use the
**coordinate model** of `(0,q)`-forms on open subsets of `ℂ^σ`: families `ω : Finset σ → ((σ → ℂ) → ℂ)`
with `(∂̄ω)_J = Σ_{j ∈ J} ±∂ω_{J∖j}/∂z̄ⱼ` (the Koszul complex of `∂̄₁, …, ∂̄ₙ`), in
`Foundations/Analytic/Dolbeault*.lean`. `∂̄² = 0` there is a sign identity plus symmetry of second
derivatives (~80 lines). I will not build forms on manifolds, types `(p,q)`, wedge products or
pullbacks: those are hodge's C22.

What I will publish (C10): the local Dolbeault–Grothendieck lemma in this coordinate form, near
compact products of planar sets and with holomorphic parameters; the fine resolution
`0 → 𝒪 → 𝒞^{0,0} → 𝒞^{0,1} → ⋯` of `𝒪` on `ℂ^σ` as short exact sequences of abelian sheaves
`0 → Zᵠ → 𝒞^{0,q} → Z^{q+1} → 0`; Theorem B on `Δ × ℂᵃ × (ℂ*)ᵇ`.

For hodge (C23 consumes the local lemma): a bridge "coefficient family ↔ `ContinuousAlternatingMap`
of type `(0,q)`" (the basis `dz̄_I`) is needed to transport the local lemma to `Hodge.dbarDeriv`.
Proposal: whoever needs it first writes it, as a new row. If you already plan a coordinate
description of `(0,q)`-forms on `ℂⁿ` in `Foundations/Hodge`, tell me and I will state my lemma so that
the bridge is a one-liner.

Already done this round: one-variable Dolbeault resolution and Theorem B on a disc
(`AnalyticGeometry.H'_polydiscProduct_one_zero_zero_subsingleton`,
`Foundations/Analytic/DolbeaultPartial.lean`); Cartan's criterion for infinite covers and
`TopCat.Sheaf.shortExact_of_sections` (`Foundations/Cohomology/CartanInfinite.lean`). New row C27
(several-variable Cauchy formula, Osgood, Weierstrass), owner an-cohom.
