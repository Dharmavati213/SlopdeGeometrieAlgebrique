/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupComparison
import SGA.SGA1.ExposeXII.RiemannLocal
import SGA.SGA1.ExposeV.QuotientHasQuotients
import SGA.Foundations.Topology.SurfaceGenusZero
import SGA.Foundations.Topology.SurfaceFilling

/-!
# SGA 1, XIII.2.12 over `ℂ`: inertia groups and loops around the removed points

In the proof of XIII.2.12 in characteristic `0`, SGA says that the loop `σⱼ` around the removed
point `aⱼ`, "the image of a generator of the local fundamental group `π₁(Dⱼ)` of a small disk
centered at `aⱼ`", is "a generator of an inertia group corresponding to the point `aⱼ`". This
compares an algebraic object (the inertia group, the image of `π₁` of `U ×_X X̃`, `X̃` the strict
localization of `X` at `aⱼ`, `IsInertiaSubgroupAt`) with a topological one (a loop in `U(ℂ)`),
through the comparison homomorphism `π₁(U(ℂ), x) → π₁(U, x)` of XII.5.2
(`comparisonHom`). This file states the comparison and reduces it to finite levels.

A loop around the centre of a chart `φ : W ≃ₜ D(0, r)` is
`FundamentalGroup.IsLoopAround (Complex.chartCoord φ ∘ ι) 0`, with cx-top's `Complex.chartCoord`
(`SGA.Foundations.Topology.SurfaceFilling`: the chart extended by `0` outside `W`).

* `InertiaLoopComparisonStatement` (statement only; registry row C32): for `X` an integral normal
  scheme locally of finite type over `ℂ`, a point `a ∈ X(ℂ)` whose local ring is a discrete
  valuation ring, an open `U` of `X` which is principal in an affine neighbourhood of `a`, and a
  chart `W ≅ D(0, r)` of `X(ℂ)` at `a` with `W ∩ U(ℂ) = W ∖ {a}`, the image under
  `comparisonHom` of a loop around `a` topologically generates, modulo the kernel of
  `π₁(U) → π₁^L(U)`, an inertia subgroup at `a`.
* `exists_isInertiaSubgroupAt_of_forall_isGalois`: the reduction to finite levels. It suffices
  that for every Galois étale covering `E` of `U`, the `Aut(E)`-sets of orbits of an inertia
  subgroup and of `σ` on the fibre have conjugate stabilizers; the conjugating elements, which
  depend on `E`, are made coherent by compactness
  (`exists_conj_topologicalClosure_sup_proLKernel_eq`).
-/

universe u

noncomputable section

open CategoryTheory AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeXIII

open ExposeXII

/-- **XIII.2.12 over `ℂ`, inertia versus loops** (statement only; registry row C32, owner
`xiii212`). Let `X` be an integral normal scheme locally of finite type over `ℂ`, `U` a connected
open of `X`, and `a ∈ X(ℂ)` a point whose local ring is a discrete valuation ring (so `X` is a
curve). Let `V` be an affine open of `X` containing `a` with `U ∩ V = D(h)` for some
`h ∈ Γ(X, V)`, and `φ : W ≃ₜ D(0, r)` a chart of `X(ℂ)` at `a` (`W` open, contained in `V(ℂ)`,
`φ a = 0`) with `W ∩ U(ℂ) = W ∖ {a}`. Let `x ∈ U(ℂ)` and let `σ ∈ π₁(U(ℂ), x)` be a loop around
`a` in the chart (conjugate to a small circle around `0` in the coordinate `φ`,
`FundamentalGroup.IsLoopAround`). Then for every set of primes `L` there is an inertia subgroup
`H` of `π₁(U, x)` at `a` (`IsInertiaSubgroupAt`) such that `H` and the image
`comparisonHom U x σ` of `σ` in the étale fundamental group (XII.5.2) generate the same closed
subgroup modulo the kernel of `π₁(U, x) → π₁^L(U, x)`:
`closure (H · proLKernel) = closure (σ^ℤ · proLKernel)`.

This is SGA's "`σⱼ` is a generator of an inertia group corresponding to `aⱼ`" in the proof of
XIII.2.12 in characteristic `0`; the inertia group is defined up to conjugation, which the
existential quantifier on `H` reflects. The affine open `V` and the function `h` (an explicit
affine neighbourhood of `a` in which `U` is a principal open) are part of the data so that the
normalization of `V` in an étale covering of `U` can be written down; for a smooth curve they
always exist. -/
def InertiaLoopComparisonStatement : Prop :=
  ∀ (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    [IsIntegral X], ExposeI.IsNormalScheme X →
    ∀ (U : X.Opens) [ConnectedSpace U] (a : SchemePoints ℂ X) [IsDomain (X.presheaf.stalk a.pt)],
    IsDiscreteValuationRing (X.presheaf.stalk a.pt) →
    ∀ (V : X.Opens), IsAffineOpen V → a.pt ∈ V → ∀ h : Γ(X, V), U ⊓ V = X.basicOpen h →
    ∀ (W : Set (SchemePoints ℂ X)) (r : ℝ) (φ : W ≃ₜ Metric.ball (0 : ℂ) r) (haW : a ∈ W),
      IsOpen W → (∀ y ∈ W, y.pt ∈ V) → (φ ⟨a, haW⟩ : ℂ) = 0 →
      letI := RiemannLocal.overVia U.ι
      haveI := RiemannLocal.isOverVia U.ι
      (∀ y ∈ W, y ∈ Set.range (SchemePoints.map (K := ℂ) U.ι) ↔ y ≠ a) →
      ∀ (x : SchemePoints ℂ U) (σ : _root_.FundamentalGroup (SchemePoints ℂ U) x),
        FundamentalGroup.IsLoopAround (fun y ↦ Complex.chartCoord φ (SchemePoints.map U.ι y)) 0 σ →
        ∀ L : Set ℕ, ∃ H : Subgroup (ExposeV.etaleFundamentalGroup ℂ x.1),
          IsInertiaSubgroupAt U a.1 x.1 H ∧
          (H ⊔ proLKernel L _).topologicalClosure =
            (Subgroup.zpowers (comparisonHom U x σ) ⊔ proLKernel L _).topologicalClosure

section FiniteLevels

open ExposeV

variable {X : Scheme.{u}} {U : X.Opens} [ConnectedSpace U] {Ω₀ : Type u} [Field Ω₀]
  [IsSepClosed Ω₀] {xb : Spec (.of Ω₀) ⟶ X} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  {ξ : Spec (.of Ω) ⟶ (U : Scheme.{u})}

/-- **Reduction of the inertia condition to finite levels.** Let `H₀` be an inertia subgroup of
`π₁(U, ξ)` at `x̄` and `σ ∈ π₁(U, ξ)`. Suppose that for every Galois étale covering `E` of `U`
there are points `e`, `e'` of the fibre `F(E)` at `ξ` such that an automorphism `φ` of `E` maps
`e` into its `H₀`-orbit iff it maps `e'` into its `σ^ℤ`-orbit. Then for every set of primes `L`,
some inertia subgroup `H` at `x̄` (a conjugate of `H₀`) satisfies
`closure (H · proLKernel) = closure (σ^ℤ · proLKernel)`. -/
theorem exists_isInertiaSubgroupAt_of_forall_isGalois {H₀ : Subgroup (etaleFundamentalGroup Ω ξ)}
    (hH₀ : IsInertiaSubgroupAt U xb ξ H₀) (σ : etaleFundamentalGroup Ω ξ)
    (h : ∀ (E : FEt (U : Scheme.{u})) [IsGalois E], ∃ e e' : (FEt.fiber Ω ξ).obj E,
      ∀ φ : Aut E, (∃ k ∈ H₀, k • e = (FEt.fiber Ω ξ).map φ.hom e) ↔
        (∃ k ∈ Subgroup.zpowers σ, k • e' = (FEt.fiber Ω ξ).map φ.hom e'))
    (L : Set ℕ) :
    ∃ H : Subgroup (etaleFundamentalGroup Ω ξ), IsInertiaSubgroupAt U xb ξ H ∧
      (H ⊔ proLKernel L _).topologicalClosure =
        (Subgroup.zpowers σ ⊔ proLKernel L _).topologicalClosure := by
  obtain ⟨g, hg⟩ := exists_conj_topologicalClosure_sup_proLKernel_eq (L := L) H₀
    (Subgroup.zpowers σ) fun N hN ho _ ↦
      exists_conj_sup_eq_of_forall_isGalois (FEt.fiber Ω ξ) H₀ (Subgroup.zpowers σ) N ho
        fun E _ ↦ h E
  exact ⟨_, hH₀.conj g, hg⟩

end FiniteLevels

section Matching

/-- **Matching stabilizers through a transitive `G`-set.** Let `Γ` and `G` act on `α` with
commuting actions, and let `G` act transitively on `β`. Suppose that for some `a₀ ∈ α`, `b₀ ∈ β`,
`g ∈ G` maps `a₀` into its `A`-orbit iff `g` fixes `b₀`, and similarly for `B`, `a₁`, `b₁`. Then
for suitable `a, a' ∈ α` the elements of `G` mapping `a` into its `A`-orbit are exactly those
mapping `a'` into its `B`-orbit (take `a = t • a₀` with `t • b₀ = b₁`). In XIII.2.12 over `ℂ`:
`Γ = π₁(U)`, `G = Aut E`, `A` an inertia group, `B` the closed subgroup generated by a loop, and
`β` the points of the normalization of the curve in `E` over the removed point. -/
theorem exists_forall_iff_of_forall_iff_smul_eq {Γ G α β : Type*} [Group Γ] [Group G]
    [MulAction Γ α] [MulAction G α] [MulAction G β]
    (hcomm : ∀ (k : Γ) (g : G) (a : α), k • g • a = g • k • a) (A B : Subgroup Γ)
    (htrans : ∀ b b' : β, ∃ t : G, t • b = b') {a₀ a₁ : α} {b₀ b₁ : β}
    (hA : ∀ g : G, (∃ k ∈ A, k • a₀ = g • a₀) ↔ g • b₀ = b₀)
    (hB : ∀ g : G, (∃ k ∈ B, k • a₁ = g • a₁) ↔ g • b₁ = b₁) :
    ∃ a a' : α, ∀ g : G, (∃ k ∈ A, k • a = g • a) ↔ (∃ k ∈ B, k • a' = g • a') := by
  obtain ⟨t, ht⟩ := htrans b₀ b₁
  refine ⟨t • a₀, a₁, fun g ↦ ?_⟩
  rw [hB, ← ht]
  have h1 : (∃ k ∈ A, k • t • a₀ = g • t • a₀) ↔ ∃ k ∈ A, k • a₀ = (t⁻¹ * g * t) • a₀ := by
    refine exists_congr fun k ↦ and_congr_right fun _ ↦ ?_
    rw [hcomm, mul_smul, mul_smul, ← smul_left_cancel_iff t⁻¹, inv_smul_smul]
  rw [h1, hA, mul_smul, mul_smul, inv_smul_eq_iff]

end Matching

end SGA.SGA1.ExposeXIII
