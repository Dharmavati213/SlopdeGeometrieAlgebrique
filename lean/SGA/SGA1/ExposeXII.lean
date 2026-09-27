/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeXII.Points
import SGA.SGA1.ExposeXII.FiniteLimits
import SGA.SGA1.ExposeXII.SimpleRoot
import SGA.SGA1.ExposeXII.Etale
import SGA.SGA1.ExposeXII.Comparison
import SGA.SGA1.ExposeXII.JacobsonConstructible
import SGA.SGA1.ExposeXII.ProperMapLocal
import SGA.SGA1.ExposeXII.SchemePoints
import SGA.SGA1.ExposeXII.SchemeLimits
import SGA.SGA1.ExposeXII.Separated
import SGA.SGA1.ExposeXII.Analytic
import SGA.SGA1.ExposeXII.RiemannExistence
import SGA.SGA1.ExposeXII.Smooth
import SGA.SGA1.ExposeXII.FundamentalGroup
import SGA.SGA1.ExposeXII.ProjectiveSpace
import SGA.SGA1.ExposeXII.Proper
import SGA.SGA1.ExposeXII.HenselianQuotient
import SGA.SGA1.ExposeXII.AnalyticAffine
import SGA.SGA1.ExposeXII.LocalRings
import SGA.SGA1.ExposeXII.ReducedComparison
import SGA.SGA1.ExposeXII.Nullstellensatz
import SGA.SGA1.ExposeXII.ClosureComparison
import SGA.SGA1.ExposeXII.EntirePolynomial
import SGA.SGA1.ExposeXII.PolynomialLines
import SGA.SGA1.ExposeXII.RootFunctions
import SGA.SGA1.ExposeXII.RootLocus
import SGA.SGA1.ExposeXII.PrimitiveElement
import SGA.SGA1.ExposeXII.Connected

/-!
# SGA 1, Exposé XII — Algebraic geometry and analytic geometry

English translation: `translation/SGA1/ExposeXII/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

Mathlib has no complex analytic spaces. Over any topological field `K` (for XII, `K = ℂ`) we
build the space `X(K)` of a `K`-scheme and, for `K` complete normed, the reduced analytic space
`(X^an)_red`; for affine `X` the (non-reduced) analytic space `X^an` of
`SGA.Foundations.Analytic` is related to it:

* §1 (`Points`, `FiniteLimits`, `SchemePoints`, `SchemeLimits`, `Analytic`, `AnalyticAffine`,
  `ReducedComparison`): the topology on `X(K)`, first for affine `X` (independent of the
  presentation), then glued from affine charts; functoriality, open and closed immersions, affine
  spaces and fibre products; the sheaf of analytic functions, the locally ringed space
  `analytification K X`, the canonical morphism `φ : X^an → X` and the functor `f ↦ f^an`
  (XII.1.1, XII.1.2, reduced versions); for affine `X`, the non-reduced `X^an` with underlying
  space `X(K)`, independent of the presentation, functorial, with its universal property, and the
  comparison morphism `(X^an)_red → X^an`;
* §§2–3 (`Comparison`, `SchemePoints`, `Separated`, `Etale`, `SimpleRoot`,
  `JacobsonConstructible`, `ProperMapLocal`, `Smooth`, `ProjectiveSpace`, `Proper`,
  `AnalyticAffine`, `HenselianQuotient`, `LocalRings`, `Nullstellensatz`, `ClosureComparison`,
  `Connected` with `RootLocus`, `PrimitiveElement`, `EntirePolynomial`, `PolynomialLines`,
  `RootFunctions`): the comparison statements that concern points and topology: surjectivity,
  injectivity, discreteness and dimension `0`, separatedness and Hausdorffness, immersions and
  embeddings; étale morphisms give local homeomorphisms (implicit function theorem), smooth
  schemes give spaces locally homeomorphic to `Kⁿ`, finite morphisms proper maps with finite
  fibres, finite étale morphisms finite coverings, proper morphisms proper maps (compactness of
  `ℙⁿ(K)` and Chow's lemma); the local rings of `X^an` (affine `X`): noetherian henselian with
  residue field `K`, the same jets and completions as those of `X`, the same dimension, regular
  together, normality and reducedness descending (XII.2.1); XII.2.2 and XII.2.3 (Rückert's
  Nullstellensatz), XII.2.4 (connectedness, via Noether normalization, removable singularities
  and Liouville, without GAGA) and XII.2.6 (`π₀`);
* §5 (`RiemannExistence`, `FundamentalGroup`): the functor `Ψ` of XII.5.1 on points, for schemes
  and for algebras, its faithfulness, its compatibility with the fibre functors of V.7, the
  Riemann existence theorem XII.5.1 as a statement, and the deduction of XII.5.2 (the étale `π₁`
  of V.7 is the profinite completion of `π₁(X(ℂ))`) from XII.5.1, unconditionally on the
  topological side for smooth `X`.

XII.5.1 (Riemann existence) and the triangulability of `X(ℂ)` are recorded as statements. GAGA
(§4), the non-affine `X^an`, XII.3.1 (i)–(vi), and XII.5.3–XII.5.5 need coherent analytic sheaves
and normal complex analytic spaces.
-/
