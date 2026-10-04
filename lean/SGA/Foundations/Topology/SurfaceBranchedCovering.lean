/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.SurfacePresentation

/-!
# Branched coverings of the sphere and the presentation of `π₁` of a punctured surface

A compact Riemann surface `Y` with a nonconstant meromorphic function `p : Y → ℙ¹(ℂ)` is a
*branched covering of the sphere*: away from a finite set `B ⊆ ℙ¹(ℂ)`, `p` is a finite covering of
some degree `d`, and near each point `q` over `B` it reads `w ↦ wᵉ` in a chart `φ` of `Y` at `q`
and the standard coordinate of `ℙ¹(ℂ)` at `p q` (`Complex.sphereCoord`). This file states, for
such data, the classical presentation of `π₁(Y ∖ P)` for `P ⊆ p⁻¹(B)`:

`π₁(Y ∖ P) = ⟨a₁, b₁, …, a_g, b_g, c₁, …, c_n | ∏ᵢ [aᵢ, bᵢ] ∏ⱼ cⱼ⟩`,

with `cⱼ` a loop around the `j`-th point of `P` and `2 - 2g = 2d - ∑_q (e_q - 1)` (the
Riemann–Hurwitz formula). It is the topological input of SGA 1 XIII.2.12 in characteristic `0`
(with `Y = X(ℂ)` and `p` a finite morphism `X → ℙ¹`, which is a branched covering in this sense).

* `Complex.surfaceRelator g n`: the relator `∏ᵢ xᵢ yᵢ xᵢ⁻¹ yᵢ⁻¹ ∏ⱼ zⱼ` (the word of
  `SGA.SGA1.ExposeXIII.surfaceWord`) in the free group on `(Fin g ⊕ Fin g) ⊕ Fin n`;
* `Complex.BranchedCoveringOfSphere`: the data (`B`, `d`, a chart and a ramification index at each
  point over `B`) and the axioms;
* `Complex.BranchedCoveringOfSphere.IsLoopAround`: a loop around a point over `B`, read in its
  chart;
* `Complex.BranchedCoveringPresentationStatement`: the presentation (statement only).

What is proved so far is the case of the sphere itself minus points
(`Complex.exists_presentation_fundamentalGroup_compl_of_infty_mem`). The planned proof of the
statement (cut `ℙ¹(ℂ)` along a tree through `B`, so that `Y` is `d` polygons glued along their
edges according to the monodromy, compute `π₁` by van Kampen, and bring the presentation into
normal form by the cut-and-paste moves of the classification of surfaces, done on the
presentations) is described in `notes/log/2026-10-04-cx-top-wave2-round1.md`.

## References

* [W. S. Massey, *Algebraic Topology: An Introduction*, Chapter 1][massey1967]
* [O. Forster, *Lectures on Riemann Surfaces*, §17 (Riemann–Hurwitz)][forster1981]
* [SGA 1, Exposé XIII, 2.12][grothendieck1971]
-/

open Set Topology OnePoint

noncomputable section

namespace Complex

/-- The relator `∏ᵢ xᵢ yᵢ xᵢ⁻¹ yᵢ⁻¹ · ∏ⱼ zⱼ` of the fundamental group of a closed orientable
surface of genus `g` minus `n` points, in the free group on the letters `xᵢ = inl (inl i)`,
`yᵢ = inl (inr i)`, `zⱼ = inr j`; the products are taken in increasing order of the indices. -/
def surfaceRelator (g n : ℕ) : FreeGroup ((Fin g ⊕ Fin g) ⊕ Fin n) :=
  (List.ofFn fun i : Fin g ↦ FreeGroup.of (.inl (.inl i)) * FreeGroup.of (.inl (.inr i)) *
    (FreeGroup.of (.inl (.inl i)))⁻¹ * (FreeGroup.of (.inl (.inr i)))⁻¹).prod *
    (List.ofFn fun j : Fin n ↦ FreeGroup.of (.inr j)).prod

lemma lift_surfaceRelator {G : Type*} [Group G] {g n : ℕ} (a b : Fin g → G) (c : Fin n → G) :
    FreeGroup.lift (Sum.elim (Sum.elim a b) c) (surfaceRelator g n) =
      (List.ofFn fun i ↦ a i * b i * (a i)⁻¹ * (b i)⁻¹).prod * (List.ofFn c).prod := by
  simp [surfaceRelator, map_list_prod, List.map_ofFn, Function.comp_def]

/-- In genus `0` the surface relator is the product of the `n` letters (`prodRelator`). -/
lemma surfaceRelator_zero_eq (n : ℕ) :
    FreeGroup.map (Sum.elim (Sum.elim Fin.elim0 Fin.elim0) id) (surfaceRelator 0 n) =
      FreeGroup.prodRelator n := by
  simp [surfaceRelator, FreeGroup.prodRelator, map_list_prod, List.map_ofFn,
    Function.comp_def]

/-- A **branched covering of the sphere** `p : Y → ℙ¹(ℂ) = OnePoint ℂ`, with the data needed to
read it: a finite set `B ⊆ ℙ¹(ℂ)` outside which `p` is a covering of degree `d` with finite
fibres, and at each point `q` over `B` an open neighbourhood `W q`, a homeomorphism
`φ q : W q ≃ₜ D(0, r q)` with `φ q q = 0`, and a ramification index `e q ≥ 1` such that
`p` reads `w ↦ wᵉ` in these coordinates: `sphereCoord (p q) (p y) = (φ q y) ^ e q` on `W q`
(`sphereCoord t` is `z - t` at a finite point `t`, `1 / z` at `∞`).

The fields `W`, `r`, `e`, `φ` are functions on all of `Y`, but only their values at points over
`B` are constrained or used; at the other points any value will do, for instance `W q = ∅`,
`r q = 0` (so that `D(0, r q) = ∅`), `e q = 1` and `φ q` the unique homeomorphism `∅ ≃ₜ ∅`. -/
structure BranchedCoveringOfSphere (Y : Type*) [TopologicalSpace Y] (p : Y → OnePoint ℂ) where
  /-- The branch locus (and possibly more points). -/
  B : Finset (OnePoint ℂ)
  /-- The degree. -/
  d : ℕ
  continuous : Continuous p
  isCoveringMap : IsCoveringMap fun y : p ⁻¹' (↑B : Set (OnePoint ℂ))ᶜ ↦
    (⟨p y, y.2⟩ : ((↑B : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ)))
  card_fibre : ∀ z ∉ B, (p ⁻¹' {z}).ncard = d
  finite_fibre : ∀ z, (p ⁻¹' {z}).Finite
  /-- The chart domain at a point over `B`. -/
  W : Y → Set Y
  /-- The radius of the chart at a point over `B`. -/
  r : Y → ℝ
  /-- The ramification index at a point over `B`. -/
  e : Y → ℕ
  /-- The chart at a point over `B`. -/
  φ : ∀ q, W q ≃ₜ Metric.ball (0 : ℂ) (r q)
  isOpen_W : ∀ q ∈ p ⁻¹' B, IsOpen (W q)
  mem_W : ∀ q ∈ p ⁻¹' B, q ∈ W q
  r_pos : ∀ q ∈ p ⁻¹' B, 0 < r q
  e_pos : ∀ q ∈ p ⁻¹' B, 0 < e q
  φ_self : ∀ (q : Y) (hq : q ∈ p ⁻¹' B), (φ q ⟨q, mem_W q hq⟩ : ℂ) = 0
  sphereCoord_eq : ∀ q ∈ p ⁻¹' B, ∀ y : W q, sphereCoord (p q) (p y) = (φ q y : ℂ) ^ e q

namespace BranchedCoveringOfSphere

variable {Y : Type*} [TopologicalSpace Y] {p : Y → OnePoint ℂ} (D : BranchedCoveringOfSphere Y p)

/-- The points over `B` form a finite set. -/
lemma finite_preimage : (p ⁻¹' (↑D.B : Set (OnePoint ℂ))).Finite := by
  rw [← Set.biUnion_preimage_singleton]
  exact D.B.finite_toSet.biUnion fun z _ ↦ D.finite_fibre z

open Classical in
/-- The chart at `q` as a function on all of `Y` (`0` outside its domain, a junk value that loops
around `q` never see, since they live where the coordinate is a nonzero number). -/
def coord (q : Y) (y : Y) : ℂ := if h : y ∈ D.W q then (D.φ q ⟨y, h⟩ : ℂ) else 0

/-- `σ ∈ π₁(Z, z)` is a *loop around `q`* (a point over `B`), for `j : Z → Y`: a loop around `0`
in the chart at `q` (`FundamentalGroup.IsLoopAround`: conjugate to a small circle, run
counterclockwise in that chart). Typically `Z = Y ∖ P` and `j` is the inclusion. -/
def IsLoopAround {Z : Type*} [TopologicalSpace Z] (j : Z → Y) (q : Y) {z : Z}
    (σ : FundamentalGroup Z z) : Prop :=
  FundamentalGroup.IsLoopAround (fun z ↦ D.coord q (j z)) 0 σ

end BranchedCoveringOfSphere

/-- **The presentation of `π₁` of a punctured compact Riemann surface** (statement only), in the
form of branched coverings of the sphere: let `p : Y → ℙ¹(ℂ)` be a branched covering of the
sphere (`BranchedCoveringOfSphere`) of degree `d`, with `Y` compact, Hausdorff and connected, and
`P ⊆ p⁻¹(B)` a finite set of `n` points (for punctures outside `p⁻¹(B)`, first add their images to
`B`, with charts of ramification index `1`). Then the integer `g` with
`2g + 2d = 2 + ∑_{q ∈ p⁻¹(B)} (e_q - 1)` (Riemann–Hurwitz) exists, and at every base point `x` of
`Y ∖ P` there are an enumeration `P = {q₀, …, q_{n-1}}` and elements `aᵢ, bᵢ, cⱼ` of
`π₁(Y ∖ P, x)` such that `⟨xᵢ, yᵢ, zⱼ | ∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⟩ → π₁(Y ∖ P, x)`,
`xᵢ ↦ aᵢ, yᵢ ↦ bᵢ, zⱼ ↦ cⱼ`, is well defined and bijective, and `cⱼ` is a loop around `qⱼ`
in its chart. -/
def BranchedCoveringPresentationStatement : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [ConnectedSpace Y]
    (p : Y → OnePoint ℂ) (D : BranchedCoveringOfSphere Y p) (P : Finset Y),
    (↑P : Set Y) ⊆ p ⁻¹' D.B →
    ∃ g : ℕ, 2 * g + 2 * D.d = 2 + ∑ q ∈ D.finite_preimage.toFinset, (D.e q - 1) ∧
      ∀ x : ((↑P : Set Y)ᶜ : Set Y),
      ∃ (q : Fin P.card ≃ P) (a b : Fin g → FundamentalGroup ((↑P : Set Y)ᶜ : Set Y) x)
        (c : Fin P.card → FundamentalGroup ((↑P : Set Y)ᶜ : Set Y) x),
        (∀ j, D.IsLoopAround Subtype.val (q j : Y) (c j)) ∧
        ∃ h : ∀ r ∈ ({surfaceRelator g P.card} : Set (FreeGroup _)),
          FreeGroup.lift (Sum.elim (Sum.elim a b) c) r = 1,
          Function.Bijective (PresentedGroup.toGroup h)

end Complex
