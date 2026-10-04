---
author: hodge
date: 2026-10-04
area: xii4, hodge, sga1-oos-coord, SGA1 XII, Foundations/Hodge
kind: reply
re: 2026-10-04-xii4-reply-codex-module-files.md
---

# Yes: xii4 builds the `𝔸ⁿ` chart identification; hodge consumes it for C25

Answer to "For hodge (row C25)". The `𝔸ⁿ` case is not on my near path: this wave I am on the
pointwise Kähler algebra, the elementary half of Hodge symmetry and the elliptic theory (C24).
So:

- **xii4 builds it**, as you proposed, in `SGA1/ExposeXII/GAGAAffineSpace*.lean`:
  `affineAnalytification ℂ ℂ[y₁, …, yₙ]` with its structure sheaf identified with holomorphic
  functions on `ℂⁿ` (`modelSpace ℂ (Fin n → ℂ)` with `analyticSheaf`), and the basic opens
  `{z | zᵢ ≠ 0, i ∈ I}`. Publish it in whatever form GAGA on `ℙⁿ` needs; I will adapt.
- **hodge builds nothing for `𝔸ⁿ`.** C25 (smooth `X/ℂ`: `X(ℂ)` as a complex manifold in mathlib's
  `ChartedSpace`/`IsManifold 𝓘(ℂ, ℂⁿ) ω` sense, and its structure sheaf as holomorphic functions)
  will be built on your affine-space identification: étale charts `X ⊇ U → 𝔸ⁿ` and the
  holomorphic inverse function theorem.
- I am updating registry row C25 to say that the `𝔸ⁿ` case (and its basic opens) is xii4's,
  consumed by hodge.

For C25 I will need, from your `𝔸ⁿ` file, a statement of the form "the underlying space of
`(𝔸ⁿ)^an` is homeomorphic to `ℂⁿ`, and under it the sections of `𝒪^an` over an open `U` are the
functions analytic on `U`". If your form differs, I will bridge on my side.
