/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.RungeProduct
import SGA.Foundations.Analytic.RungeBox
import SGA.Foundations.Analytic.Statements

/-!
# Theorem B for `𝒪` on products of discs, planes, punctured planes and rectangles

Let `σ` be a finite type and, for each `i ∈ σ`, let `Ωᵢ ⊆ ℂ` be an open disc `|z| < ρᵢ` (possibly
empty), the plane `ℂ`, the punctured plane `ℂ*` or an open rectangle
(`AnalyticGeometry.FactorKind`). Then
`Hⁿ(∏ᵢ Ωᵢ, 𝒪) = 0` for all `n > 0` (`AnalyticGeometry.H'_holomorphicAbSheaf_pi_subsingleton`),
where `Hⁿ` is sheaf cohomology (`CategoryTheory.Sheaf.H'`) of the sheaf `𝒪` of holomorphic
functions on `ℂ^σ`, over the open set `∏ᵢ Ωᵢ`. In particular
`AnalyticGeometry.PolydiscProductVanishingStatement` holds
(`AnalyticGeometry.polydiscProductVanishing`): Theorem B for `𝒪` on `Δ × ℂᵃ × (ℂ*)ᵇ`. The cases
`c = 0` cover `ℂⁿ`, the standard affine charts of `ℙⁿ` and all their intersections. Products of
open rectangles (open boxes, `AnalyticGeometry.openBox`) are covered too
(`AnalyticGeometry.H'_holomorphicAbSheaf_openBox_subsingleton`); they form a basis of
neighbourhoods of every compact box (`AnalyticGeometry.exists_openBox_subset`), so `𝒪` has no
higher cohomology near compact boxes
(`AnalyticGeometry.exists_openBox_H'_holomorphicAbSheaf_subsingleton`).

The proof: the Dolbeault resolution of `𝒪` by fine sheaves reduces the vanishing to global
solvability of `∂̄` on `∏ Ωᵢ` (`H'_holomorphicAbSheaf_subsingleton_of_dbarExact`); the
Dolbeault–Grothendieck lemma near compact products and the exhaustion argument give this in
positive degree, and in degree `0` given the Runge property of the exhaustion
(`H'_holomorphicAbSheaf_subsingleton_of_isRunge`); the Runge property of the standard exhaustion
by products of closed discs, annuli and rectangles is proved by Laurent truncation, respectively by
Cauchy integrals over the sides of rectangles, with holomorphic parameters
(`FactorKind.isRunge_exhaustion`).

References: Hörmander, *An introduction to complex analysis in several variables*, Theorem 2.3.3
and its proof (for polydiscs; here for products of discs, planes, punctured planes and
rectangles), 5.6;
Gunning–Rossi, *Analytic functions of several complex variables*, I.D.
-/

noncomputable section

open Set Complex

namespace AnalyticGeometry

/-- **Theorem B for `𝒪` on products of discs, planes, punctured planes and open rectangles**: for
every finite family `κ` of factor kinds, `Hⁿ(∏ᵢ (κ i).domain, 𝒪) = 0` for all `n > 0`. -/
theorem H'_holomorphicAbSheaf_pi_subsingleton {σ : Type} [Fintype σ] (κ : σ → FactorKind)
    (n : ℕ) :
    Subsingleton ((holomorphicAbSheaf σ).H' (n + 1)
      (⟨univ.pi fun i ↦ (κ i).domain, isOpen_univ_pi fun i ↦ (κ i).isOpen_domain⟩ :
        TopologicalSpace.Opens (TopCat.of (σ → ℂ)))) :=
  H'_holomorphicAbSheaf_subsingleton_of_isRunge (fun i ↦ (κ i).isOpen_domain)
    (FactorKind.exhaustion κ) (FactorKind.isRunge_exhaustion κ) n

variable {σ : Type} [Fintype σ]

/-- **Theorem B for `𝒪` on open boxes**: `Hⁿ(∏ᵢ (aᵢ, bᵢ), 𝒪) = 0` for `n > 0`, for every product
of open rectangles (`AnalyticGeometry.openBox`). -/
theorem H'_holomorphicAbSheaf_openBox_subsingleton (a b : σ → ℂ) (n : ℕ) :
    Subsingleton ((holomorphicAbSheaf σ).H' (n + 1)
      (⟨openBox a b, isOpen_openBox a b⟩ : TopologicalSpace.Opens (TopCat.of (σ → ℂ)))) :=
  H'_holomorphicAbSheaf_pi_subsingleton (fun i ↦ .rect (a i) (b i)) n

/-- **Theorem B for `𝒪` near compact boxes** (germ form): every open neighbourhood `V` of a
compact box `Q = ∏ᵢ [aᵢ, bᵢ]` (`(aᵢ).re ≤ (bᵢ).re`, `(aᵢ).im ≤ (bᵢ).im`, degenerate rectangles
allowed) contains an open box `W ⊇ Q` with `Hⁿ(W, 𝒪) = 0` for all `n > 0`. In particular every
class in `Hⁿ(V, 𝒪)`, `n > 0`, vanishes on a neighbourhood of `Q`. -/
theorem exists_openBox_H'_holomorphicAbSheaf_subsingleton {a b : σ → ℂ}
    (hab : ∀ i, (a i).re ≤ (b i).re ∧ (a i).im ≤ (b i).im) {V : Set (σ → ℂ)} (hV : IsOpen V)
    (hQV : univ.pi (fun i ↦ closedRect (a i) (b i)) ⊆ V) :
    ∃ a' b' : σ → ℂ, univ.pi (fun i ↦ closedRect (a i) (b i)) ⊆ openBox a' b' ∧
      openBox a' b' ⊆ V ∧ ∀ n : ℕ, Subsingleton ((holomorphicAbSheaf σ).H' (n + 1)
        (⟨openBox a' b', isOpen_openBox a' b'⟩ : TopologicalSpace.Opens (TopCat.of (σ → ℂ)))) := by
  obtain ⟨ε, hε, hεV⟩ := exists_openBox_subset hab hV hQV
  exact ⟨_, _, pi_closedRect_subset_openBox hε, hεV,
    fun n ↦ H'_holomorphicAbSheaf_openBox_subsingleton _ _ n⟩

/-- The factor kinds of `Δ(r) × ℂᵃ × (ℂ*)ᵇ`: discs of radii `r i`, then `a` planes, then `b`
punctured planes. -/
def polydiscProductKind (c a b : ℕ) (r : Fin c → ℝ) : Fin c ⊕ Fin a ⊕ Fin b → FactorKind
  | Sum.inl i => .disc (r i)
  | Sum.inr (Sum.inl _) => .plane
  | Sum.inr (Sum.inr _) => .punctured

/-- `Δ(r) × ℂᵃ × (ℂ*)ᵇ` is the product of the domains of `polydiscProductKind c a b r`. -/
lemma polydiscProduct_eq_pi (c a b : ℕ) (r : Fin c → ℝ) :
    polydiscProduct c a b r =
      ⟨univ.pi fun i ↦ (polydiscProductKind c a b r i).domain,
        isOpen_univ_pi fun i ↦ (polydiscProductKind c a b r i).isOpen_domain⟩ := by
  ext z
  simp [polydiscProduct, polydiscProductKind, FactorKind.domain, Set.mem_pi, Sum.forall,
    Metric.mem_ball, dist_zero_right]

/-- **Theorem B for `𝒪` on `Δ × ℂᵃ × (ℂ*)ᵇ`**: `PolydiscProductVanishingStatement` holds, i.e.
`Hᵠ(Δ(r) × ℂᵃ × (ℂ*)ᵇ, 𝒪) = 0` for all `q > 0`, every polyradius `r` (entries `≤ 0` give empty
discs) and all `a`, `b`. -/
theorem polydiscProductVanishing : PolydiscProductVanishingStatement := by
  intro c a b q r
  rw [polydiscProduct_eq_pi]
  exact H'_holomorphicAbSheaf_pi_subsingleton _ q

end AnalyticGeometry
