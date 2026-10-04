/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Sheaf
import SGA.Foundations.Cohomology.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Statements: Oka's coherence theorem and Theorem B for `𝒪` on product domains

Two classical theorems of several complex variables that the comparison of algebraic and analytic
geometry (GAGA, Riemann existence) rests on, and which mathlib does not have. They are recorded
here as `Prop`s, the targets of their proofs; consequences are proved from them as hypotheses.

* `OkaCoherenceStatement` (Oka's coherence theorem, germ form; Grauert–Remmert, *Coherent
  analytic sheaves*, 2.5; Gunning–Rossi, IV.C): the sheaf of relations between finitely many
  holomorphic functions on an open subset of `ℂⁿ` is of finite type.
* `PolydiscProductVanishingStatement` (Theorem B for `𝒪` on `Δ × ℂᵃ × (ℂ*)ᵇ`, `Δ` a polydisc;
  Hörmander, *An introduction to complex analysis in several variables*, 2.7.8 and 5.6;
  Gunning–Rossi, I.D): `Hᵠ(Δ × ℂᵃ × (ℂ*)ᵇ, 𝒪) = 0` for `q > 0`, where `Hᵠ` is sheaf cohomology
  (`CategoryTheory.Sheaf.H'`). The factor `ℂᵃ × (ℂ*)ᵇ` covers the standard affine opens of `ℙⁿ`
  and their intersections; the polydisc factor is needed for the relative and proper cases of
  GAGA (SGA 1 XII.4.2), where the base is covered by small polydiscs.

Both are stated over `ℂ` with the sheaf `analyticSheaf ℂ (Fin n → ℂ)` of holomorphic functions.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology Filter

namespace AnalyticGeometry

/-- The sheaf `𝒪` of holomorphic functions on `ℂ^σ`, as an abelian sheaf. -/
def holomorphicAbSheaf (σ : Type) [Fintype σ] :
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (σ → ℂ)) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj
    (analyticSheaf ℂ (σ → ℂ))

/-- The open set `Δ(r) × ℂᵃ × (ℂ*)ᵇ ⊆ ℂ^{c + a + b}`: the first `c` coordinates in the polydisc of
polyradius `r`, the next `a` coordinates arbitrary, the last `b` coordinates nonzero. -/
def polydiscProduct (c a b : ℕ) (r : Fin c → ℝ) :
    Opens (TopCat.of (Fin c ⊕ Fin a ⊕ Fin b → ℂ)) :=
  ⟨(⋂ i, {z | ‖z (Sum.inl i)‖ < r i}) ∩ ⋂ j, {z | z (Sum.inr (Sum.inr j)) ≠ 0},
    (isOpen_iInter_of_finite fun i ↦
        isOpen_lt (continuous_norm.comp (continuous_apply (Sum.inl i))) continuous_const).inter
      (isOpen_iInter_of_finite fun j ↦
        isOpen_ne_fun (continuous_apply (Sum.inr (Sum.inr j))) continuous_const)⟩

/-- **Theorem B for `𝒪` on `Δ × ℂᵃ × (ℂ*)ᵇ`** (statement only): for every polydisc `Δ ⊆ ℂᶜ`
(of any polyradius, possibly with nonpositive entries, when it is empty) and all `a`, `b`,
`Hᵠ(Δ × ℂᵃ × (ℂ*)ᵇ, 𝒪) = 0` for `q > 0`. -/
def PolydiscProductVanishingStatement : Prop :=
  ∀ (c a b q : ℕ) (r : Fin c → ℝ),
    Subsingleton ((holomorphicAbSheaf (Fin c ⊕ Fin a ⊕ Fin b)).H' (q + 1) (polydiscProduct c a b r))

/-- **Oka's coherence theorem** (statement only), germ form: let `f₁, …, f_p` be holomorphic on
an open `U ⊆ ℂⁿ` and `x₀ ∈ U`. There are a neighbourhood `V ⊆ U` of `x₀` and finitely many
relations `s₁, …, s_m ∈ 𝒪(V)^p` (`∑ᵢ s_{j,i} fᵢ = 0` on `V`) whose germs generate the module of
relations between the germs of the `fᵢ` at every point `y ∈ V`. -/
def OkaCoherenceStatement : Prop :=
  ∀ (n p : ℕ) (U : Set (Fin n → ℂ)) (_ : IsOpen U) (f : Fin p → (Fin n → ℂ) → ℂ)
    (hf : ∀ i, ∀ x ∈ U, AnalyticAt ℂ (f i) x), ∀ x₀ ∈ U,
    ∃ V ∈ 𝓝 x₀, ∃ (hVU : V ⊆ U) (m : ℕ) (s : Fin m → Fin p → (Fin n → ℂ) → ℂ)
      (hs : ∀ j i, ∀ y ∈ V, AnalyticAt ℂ (s j i) y),
      (∀ j, ∀ y ∈ V, ∑ i, s j i y * f i y = 0) ∧
      ∀ (y : Fin n → ℂ) (hy : y ∈ V), ∀ g : Fin p → (analyticPresheaf ℂ (Fin n → ℂ)).stalk y,
        ∑ i, g i * germOf (f i) (hf i y (hVU hy)) = 0 →
          g ∈ Submodule.span ((analyticPresheaf ℂ (Fin n → ℂ)).stalk y)
            (Set.range fun j i ↦ germOf (s j i) (hs j i y hy))

end AnalyticGeometry
