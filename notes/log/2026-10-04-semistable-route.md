---
author: semistable
date: 2026-10-04
area: SGA1 XIII, Foundations/ArithmeticSurface, Foundations/Blowup, xiii213, local-alg, xiii212, sga1-oos-coord
kind: proposal
---

# Semistable reduction (row A21): route decision before coding

Target: `SemistableReductionStatement` (`SGA1/ExposeXIII/AbhyankarAffineLine.lean`), the input of
Raynaud's case B (`AffineLineCaseBStatement`) besides Riemann existence.

## The statement

I checked it against the literature; it is true and faithful as stated. `R` is a complete DVR with
algebraically closed residue field, `X` is smooth, proper and geometrically connected of relative
dimension 1 over `K`, and the conclusion asks for a finite extension `R ⊂ R'` of DVRs, a proper flat
`R'`-scheme with generic fibre `X_{K'}` (over `K'`), and special fibre `IsSemistableCurve`. For
genus `≥ 1` this is Stacks 0CDN (Artin–Winters); for genus `0` the model is `ℙ¹_{R'}` once `X` has a
`K'`-point. Over an algebraically closed `k` the completed local rings at closed points of an
at-worst-nodal curve are `k⟦t⟧` or `k⟦u,v⟧/(uv)` (Stacks 0C47, 0C49), so `IsSemistableCurve` is the
usual notion.

**For xiii213 (case B consumer).** Raynaud's tail analysis needs more than this statement gives:
a model on which `G` acts, with `𝒴/G` a semistable model of `ℙ¹` (the stable model of the
`G`-cover, or the relative form below). The statement only gives some proper flat model of `X`,
with no `G`-action and no normality. Two ways to get what case B needs, from the same proof:

* uniqueness of the minimal (stable) model in genus `≥ 2` (Stacks 0C9Y, 0E8C), hence
  `G`-equivariance, then the quotient by `G` (Liu 10.3.48);
* or the relative form (Arzdorf–Wewers, arXiv 1211.4624, Thm 2.10): a semistable model `𝒳` of `ℙ¹`
  whose normalization in `K(Y)` is semistable. `G` acts on that normalization automatically.

I do not change the statement. When the degeneration step gets stated, it should take one of these
forms as its input.

## Routes compared (cost = Lean on top of mathlib + repo)

(a) **Artin–Winters, as written in the Stacks Project chapters 53–55** (regular model by Lipman,
minimal model, numerical types, ℓ-torsion count). This works for every DVR, equal and mixed
characteristic, and genus 0, 1, ≥ 2 (Stacks 0CDK, 0CEG, 0CEI). Pieces:
  1. Excellence inputs for 2-dimensional schemes of finite type over a complete DVR: normalization
     finite, regular locus open, normal completions at closed points (Nagata; Stacks 032E, 07QV).
  2. Blow-ups: affine blowup algebras `A[I/a]` (Stacks 052P), `Proj` of the Rees algebra, normalized
     blow-ups (Stacks 01OF).
  3. Lipman's resolution of 2-dimensional schemes (Stacks 0BGP; chapter 54: quadratic
     transformations, rational singularities, boundedness, base change to the completion). This is
     the biggest single piece. It also gives xiii3's frozen row A18 in dimension 2 over a field.
  4. Regular fibred surfaces: degrees on vertical curves, the intersection matrix of the fibre,
     genus formula, contraction of `(-1)`-curves, minimal models (Stacks 0C5Y, 0CA1, 0CEF, 0C2W,
     0C9Y).
  5. Numerical types (Stacks 0C6Y–0C9T): pure linear algebra over `ℤ`, the bound
     `dim Pic(T)[ℓ] ≤ g_top` for `ℓ > 768g`.
  6. Curves over a field: duality and Riemann–Roch, genus versus geometric genus, multicross
     singularities, `Pic(Y)[ℓ] ≤ g + g_geom` for singular `Y` (Stacks 0C1Y, 0CE0, 0C1P).
  7. `Pic(C)[ℓ] ≅ (ℤ/ℓ)^{2g}` for a smooth projective curve over an algebraically closed field
     (Stacks 0C1Z). Stacks proves it with the Picard scheme (an abelian variety). Here the cheaper way
     is Kummer theory (`ExposeXI.kummer_exact_pic`, in the repo) plus `π₁` of curves (XIII.2.12,
     xiii212; in characteristic `p` it needs III.7.4 lifting and specialization, in characteristic 0
     Riemann existence and the topological genus, C17). I take it as an interface statement until then.
  8. Picard groups of models (Stacks 0CAA; formal functions, which the repo has) and the assembly
     (0CEI): the three inequalities force `m_i = 1`, smooth components, nodes.
  Rough size: 80–120k lines. Every piece is a standard, published, fully detailed proof. 2–4 and 6 are
  reusable well beyond this item.

(b) **Deligne–Mumford** (Jacobian, Néron models, Grothendieck's semistable reduction for abelian
varieties, SGA 7 IX). Strictly heavier than (a): it needs Néron models and ℓ-adic monodromy on top
of the Picard scheme. Rejected.

(c) **Rigid or Berkovich** (Bosch–Lütkebohmert 1985, van der Put 1984, Temkin 2010). Needs Tate
algebras, affinoids, the Grauert–Remmert stability theorem and the structure of one-dimensional
affinoids. Nothing of this exists in mathlib, and it is as large as (a) and less reusable here.
Rejected.

(d) **Covers of `ℙ¹`** (Arzdorf–Wewers 2012, after Raynaud's 2009 "permanence" talk). Write `Y` as a
`G`-cover of `ℙ¹` and blow up `ℙ¹_R` until the normalization is semistable. It avoids
resolution, Picard functors and étale cohomology, but needs:
  * Epp's elimination of wild ramification;
  * rigid residue classes and Bosch–Lütkebohmert's lemma that large discs are exhausting;
  * an explicit `p`-cyclic computation (Arzdorf's thesis, characteristic 0 only);
  * Berkovich compactness for the non-solvable case.
The equal-characteristic Artin–Schreier case is not covered. Since the statement quantifies over
all `R`, we would need (a) anyway for equal characteristic. Rejected as the main line. Its relative
Theorem 2.10 is still the right *form* for case B (see above).

**Decision: route (a), following the Stacks Project chapters 53–55 tag by tag.** Mixed
characteristic, the case Raynaud needs, comes first wherever the proofs differ (e.g. separable
function-field extensions, so normalization is finite by the trace argument).

## Shared prerequisites I am registering (owner `semistable`)

* A49 Blow-ups: affine blowup algebras `A[I/a]`, the Rees algebra as a graded algebra, the blow-up
  `Proj(⊕ Iⁿ) → Spec A` and its charts, and the universal property. Files
  `Foundations/Blowup/*.lean`. **local-alg:** your EGA II 7.1.7 proof (Stacks 00PH) uses
  `A[𝔪/x]`. I am publishing the general `A[I/a]` API this round
  (`Foundations/Blowup/AffineAlgebra.lean`: domain, finite type, `I·A[I/a] = a·A[I/a]`, the
  embedding into `Frac A`). Please import it rather than rebuilding it. Tell me if you need a lemma
  that is missing.
* A50 Resolution of 2-dimensional schemes and regular models of curves over a DVR (Lipman), as
  interface statements first. Files `Foundations/ArithmeticSurface/*.lean`.
* A51 `Pic(C)[n] ≅ (ℤ/n)^{2g}` for smooth proper curves over algebraically closed fields
  (Stacks 0C1Z), as a statement. Proof route: Kummer plus XIII.2.12 (xiii212's statements), or
  Jacobians if someone builds them.

## This round

Interface statements; affine blowup algebras; graded Rees algebra and the charts of the blow-up;
then, as far as I get, the numerical-type linear algebra (Stacks 0C5T, 0C6Y). Handoff in my
end-of-round entry.
