/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannExistence
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Meromorphic.Order

/-!
# SGA 1, Exposé XII, 5.1 for curves: statements

The Riemann existence theorem XII.5.1 for curves is the case most of SGA 1 uses (X.2.6, XIII.2.12
in characteristic `0`), and its proof has a single transcendental input. This file records the
statements that split the proof into an analytic and an algebraic-topological part.

* `CurveRiemannExistenceStatement`: XII.5.1 for affine curves over `ℂ`: for `A` of finite type
  over `ℂ` of Krull dimension `≤ 1`, the functor `Ψ` from finite étale `A`-algebras to finite
  coverings of `X(ℂ)`, `X = Spec A`, is an equivalence.
* `CompactRiemannSurfaceMeromorphicStatement`, the analytic heart: on a compact Riemann surface,
  for every point `y` there is a meromorphic function whose only pole is at `y` (Forster,
  *Lectures on Riemann surfaces*, 14.13; it follows from the finiteness of `H¹(M, 𝒪)`, Forster
  14.9, through the Riemann–Roch inequality). This is the form of "compact Riemann surfaces are
  algebraic" that the proof of XII.5.1 for curves needs.
* `SeparatingFunctionStatement`, the analytic heart in the language of coverings: every
  connected finite covering `E` of `ℂ ∖ S` carries a function holomorphic on `E`, meromorphic at
  the punctures and at infinity, and injective on some fibre. It follows from
  `CompactRiemannSurfaceMeromorphicStatement` applied to the compact Riemann surface obtained by
  filling in the punctures of `E`; from it, the symmetric functions of `F` on the fibres are
  regular functions on `ℂ ∖ S` (`exists_polynomial_of_differentiableOn`), so `E` is the covering
  of `ℂ ∖ S` defined by an algebraic equation, which gives XII.5.1 for `ℂ[t][1/f]` and then, by
  Noether normalization, for all affine curves. The algebraic half actually needs a separating
  function for *every* fibre: that is `FiberSeparatingFunctionStatement`
  (`SGA.SGA1.ExposeXII.RiemannCurvesSymmetric`), which supersedes this statement as the
  interface between the two halves.

`CompactRiemannSurfaceMeromorphicStatement` is proved (`compactRiemannSurfaceMeromorphic`,
`SGA.SGA1.ExposeXII.GAGACompactRiemannSurface`), and so are `FiberSeparatingFunctionStatement`
(`fiberSeparatingFunction`, `SGA.SGA1.ExposeXII.GAGAFiberSeparating`) and
`SeparatingFunctionStatement` (`separatingFunctionStatement`,
`SGA.SGA1.ExposeXII.StatementCorollaries`), hence XII.5.1 for `ℂ`
minus a finite set (`PuncturedPlane.riemannExistence_coordRing`) and for its finite étale
coverings (`PuncturedPlane.riemannExistence_finiteEtale`, same file).
`CurveRiemannExistenceStatement` remains open. The route through these statements is this
project's, not SGA's.

SGA itself proves XII.5.1 in all dimensions at once, by Hironaka's resolution and GAGA (or,
before Hironaka, by the Grauert–Remmert extension theorem XII.5.4).
-/

noncomputable section

open scoped Manifold ContDiff

namespace SGA.SGA1.ExposeXII

/-- XII.5.1 for affine curves (statement only): for `A` of finite type over `ℂ` and of Krull
dimension at most `1`, the functor `Ψ : S ↦ S(ℂ)` from finite étale `A`-algebras to finite
coverings of `X(ℂ)`, `X = Spec A`, is an equivalence of categories. This is
`RiemannExistenceStatement` restricted to curves, in universe `0`
(`curveRiemannExistence_of_riemannExistence`). Proved cases: the affine line, written
`A = MvPolynomial (Fin 1) ℂ` (`riemannExistence_mvPolynomial 1`,
`SGA.SGA1.ExposeXII.RiemannSimplyConnected`), `𝔾_m`, `A = ℂ[T, T⁻¹]`
(`riemannExistence_laurentPolynomial`, `SGA.SGA1.ExposeXII.RiemannKummer`), `ℂ` minus a finite
set `S`, `A = ℂ[t][1/∏_{a ∈ S} (t - a)]` (`PuncturedPlane.riemannExistence_coordRing`), and the
finite étale `A`-algebras for that `A` (`PuncturedPlane.riemannExistence_finiteEtale`; both in
`SGA.SGA1.ExposeXII.GAGAFiberSeparating`). -/
def CurveRiemannExistenceStatement : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ringKrullDim A ≤ 1 →
    (pointsFunctor ℂ A).IsEquivalence

/-- XII.5.1 for all affine `X` implies XII.5.1 for affine curves. -/
theorem curveRiemannExistence_of_riemannExistence (H : RiemannExistenceStatement.{0}) :
    CurveRiemannExistenceStatement := fun A _ _ _ _ ↦ H A

/-- The analytic heart of the Riemann existence theorem for curves (proved:
`compactRiemannSurfaceMeromorphic`, `SGA.SGA1.ExposeXII.GAGACompactRiemannSurface`): on a
compact Riemann surface `M` (a compact, connected, Hausdorff complex manifold of dimension `1`),
for every point `y` there is a meromorphic function `f` whose only pole is at `y`: `f` is
holomorphic on `M ∖ {y}` and, in the chart at `y`, meromorphic at `y` of negative order.
(Forster, *Lectures on Riemann surfaces*, Corollary 14.13, from the finiteness of `H¹(M, 𝒪)`,
Theorem 14.9. The value `f y` is irrelevant.) -/
def CompactRiemannSurfaceMeromorphicStatement : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] (y : M),
    ∃ f : M → ℂ, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f {y}ᶜ ∧
      MeromorphicAt (f ∘ (extChartAt 𝓘(ℂ) y).symm) (extChartAt 𝓘(ℂ) y y) ∧
      meromorphicOrderAt (f ∘ (extChartAt 𝓘(ℂ) y).symm) (extChartAt 𝓘(ℂ) y y) < 0

/-- The analytic heart of the Riemann existence theorem for curves, in the language of coverings:
let `S ⊂ ℂ` be finite and `p : E → ℂ ∖ S` a connected finite covering. Then
there is a continuous `F : E → ℂ` which is
* holomorphic on `E`: `F ∘ s` is holomorphic for every continuous local section `s` of `p` over
  an open `U ⊆ ℂ ∖ S`;
* meromorphic at the punctures and at infinity:
  `‖F e‖ * ∏_{a ∈ S} ‖p e - a‖ ^ N ≤ C * (1 + ‖p e‖) ^ (N * (|S| + 1))` for some `C`, `N`;
* injective on some fibre of `p`.

Classically: `E` is the complement of finitely many points in a compact Riemann surface `Ē`
(fill in the punctures with the local models `w ↦ w ^ e`), and `F` is a meromorphic function on
`Ē` with poles only over `S ∪ {∞}` separating the points of an unramified fibre, built from
functions with a single pole (`CompactRiemannSurfaceMeromorphicStatement`).

Superseded as the interface for the algebraic half by `FiberSeparatingFunctionStatement` (one
separating function for every fibre), which implies it
(`separatingFunctionStatement_of_fiberSeparatingFunctionStatement`); one injective fibre is not
enough, since `ℂ[t][1/f][F]` is not étale where the values of `F` collide. Proved:
`separatingFunctionStatement` (`SGA.SGA1.ExposeXII.StatementCorollaries`), from
`fiberSeparatingFunction` (`SGA.SGA1.ExposeXII.GAGAFiberSeparating`). -/
def SeparatingFunctionStatement : Prop :=
  ∀ (S : Finset ℂ) (E : Type) [TopologicalSpace E] [ConnectedSpace E]
    (p : E → {z : ℂ // z ∉ S}), IsCoveringMap p → (∀ z, (p ⁻¹' {z}).Finite) →
    ∃ F : E → ℂ, Continuous F ∧
      (∀ (U : Set ℂ) (_ : IsOpen U) (_ : ∀ z ∈ U, z ∉ S) (s : U → E), Continuous s →
        (∀ z : U, (p (s z) : ℂ) = z) →
          DifferentiableOn ℂ (Function.extend (fun z : U ↦ (z : ℂ)) (F ∘ s) 0) U) ∧
      (∃ (C : ℝ) (N : ℕ), ∀ e, ‖F e‖ * ∏ a ∈ S, ‖(p e : ℂ) - a‖ ^ N ≤
        C * (1 + ‖(p e : ℂ)‖) ^ (N * (S.card + 1))) ∧
      ∃ z, Set.InjOn F (p ⁻¹' {z})

end SGA.SGA1.ExposeXII
