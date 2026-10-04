/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.CoherentCohomology
import SGA.Foundations.Analytic.Statements
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Statements: coherent analytic sheaves (Cartan's Theorems A and B, Cartan–Serre, Cartan)

The theorems on coherent analytic sheaves that the comparison of algebraic and analytic geometry
(SGA 1 XII §4, Serre's GAGA) rests on, recorded as `Prop`s. A *coherent* analytic sheaf is
taken to be a finitely presented module (`SheafOfModules.IsFinitePresentation`); on a complex
analytic space this is equivalent to SGA's "coherent" because the structure sheaf is coherent
(Oka's theorem, proved as `AnalyticGeometry.okaCoherence`; for local models
`AnalyticGeometry.LocalModelData`, see `SGA.Foundations.Analytic.StructureSheafCoherent`).

* `CoherentTheoremABStatement` (Cartan's Theorems A and B on `Δ × ℂᵃ × (ℂ*)ᵇ`, `Δ` an open
  polydisc; Gunning–Rossi, *Analytic functions of several complex variables*, Chapter VIII;
  Grauert–Remmert, *Theory of Stein spaces*; Hörmander, *An introduction to complex analysis in
  several variables*, Chapter VII): for a finitely presented `𝒪`-module `M` on `Δ × ℂᵃ × (ℂ*)ᵇ`, the
  global sections generate `M` (Theorem A) and `Hᵠ(Δ × ℂᵃ × (ℂ*)ᵇ, M) = 0` for `q > 0`
  (Theorem B). The domains are those of `PolydiscProductVanishingStatement` (Theorem B for `𝒪`):
  the polydisc factor covers the local theory, the factor `ℂᵃ × (ℂ*)ᵇ` the standard affine opens
  of `ℙⁿ` and their intersections.
* `CartanSerreFinitenessStatement` (H. Cartan and J.-P. Serre, *Un théorème de finitude concernant
  les variétés analytiques compactes*, C. R. Acad. Sci. Paris 237 (1953), 128–130;
  Grauert–Remmert, *Coherent analytic sheaves*): for a finitely
  presented `𝒪_X`-module `M` on a compact (Hausdorff) complex analytic space `X`, every
  `Hᵠ(X, M)` is a finite-dimensional `ℂ`-vector space. The `ℂ`-structure of `Hᵠ(X, M)` is the
  one induced by `ℂ → Γ(X, 𝒪_X)` (`LocallyRingedSpace.Modules.cohomologyModule`,
  `LocallyRingedSpace.structureRingHom`); `Hᵠ(X, M)` is the cohomology over the open `⊤`
  (`CategoryTheory.Sheaf.H'`), isomorphic to `LocallyRingedSpace.Modules.H M q` by
  `CategoryTheory.Sheaf.H'.addEquivH`. Hausdorffness is needed: gluing two copies of `ℙ¹`
  along the complement of a point gives a compact non-Hausdorff space with
  `dim H¹(X, 𝒪) = ∞` (Mayer–Vietoris and `Γ(ℂ, 𝒪)` infinite-dimensional).
* `IdealSheafCoherentStatement` (Cartan's coherence theorem for the full ideal sheaf of an
  analytic set, germ form; H. Cartan 1950; Grauert–Remmert, *Coherent analytic sheaves*;
  Gunning–Rossi, Chapter IV): if `Z = {g₁ = ⋯ = g_r = 0}` in an open `U ⊆ ℂⁿ`, then near every
  point of `U` finitely many holomorphic functions vanishing on `Z` generate, at every nearby
  point `y`, the ideal of all germs at `y` vanishing on `Z` near `y`. This is the finite type
  half of Cartan's theorem; coherence of the ideal sheaf follows from it by Oka's theorem
  (`AnalyticGeometry.okaCoherence`: the relations between finitely many holomorphic functions
  form a sheaf of finite type).
-/

noncomputable section

open CategoryTheory TopologicalSpace Filter AlgebraicGeometry
open scoped Topology

namespace AnalyticGeometry

/-- The complex analytic space `Δ(r) × ℂᵃ × (ℂ*)ᵇ`: the open subspace `polydiscProduct c a b r`
of the model space `ℂ^{c + a + b}` (with its sheaf of holomorphic functions). -/
abbrev polydiscProductSpace (c a b : ℕ) (r : Fin c → ℝ) : LocallyRingedSpace.{0} :=
  (modelSpace ℂ (Fin c ⊕ Fin a ⊕ Fin b → ℂ)).restrict (polydiscProduct c a b r).isOpenEmbedding

/-- **Cartan's Theorems A and B for coherent sheaves on `Δ × ℂᵃ × (ℂ*)ᵇ`** (statement only):
for every finitely presented `𝒪`-module `M` on `Δ(r) × ℂᵃ × (ℂ*)ᵇ` (any polyradius `r`), the
global sections of `M` generate it (Theorem A: a family of global sections whose morphism from
the free module is an epimorphism) and `Hᵠ(Δ(r) × ℂᵃ × (ℂ*)ᵇ, M) = 0` for `q > 0`
(Theorem B). -/
def CoherentTheoremABStatement : Prop :=
  ∀ (c a b : ℕ) (r : Fin c → ℝ) (M : (polydiscProductSpace c a b r).Modules),
    SheafOfModules.IsFinitePresentation.{0} M →
      Nonempty (SheafOfModules.GeneratingSections.{0} M) ∧
        ∀ q : ℕ, Subsingleton (LocallyRingedSpace.Modules.H M (q + 1))

/-- **The Cartan–Serre finiteness theorem** (statement only): let `X` be a compact Hausdorff
complex analytic space (`IsAnalyticSpaceOver ℂ X s`: locally `ℂ`-linearly isomorphic to local
models in `ℂⁿ`, with structure morphism `s : X ⟶ Spec ℂ`). For every finitely presented
`𝒪_X`-module `M` and every `q`, the cohomology `Hᵠ(X, M)` is a finite-dimensional `ℂ`-vector
space, for the `ℂ`-structure induced by `s`. -/
def CartanSerreFinitenessStatement : Prop :=
  ∀ (X : LocallyRingedSpace.{0}) (s : X ⟶ specField ℂ), IsAnalyticSpaceOver ℂ X s →
    CompactSpace X → T2Space X →
    ∀ (M : X.Modules), SheafOfModules.IsFinitePresentation.{0} M → ∀ q : ℕ,
      letI := LocallyRingedSpace.Modules.cohomologyModule
        (LocallyRingedSpace.structureRingHom s) M q ⊤
      Module.Finite ℂ (M.toAbSheaf.H' q ⊤)

/-- **Cartan's coherence theorem for ideal sheaves of analytic sets** (statement only, germ
form): let `g₁, …, g_r` be holomorphic on an open `U ⊆ ℂⁿ`, `Z = {y ∈ U | g(y) = 0}`, and
`x₀ ∈ U`. There are a neighbourhood `V ⊆ U` of `x₀` and finitely many functions `h_j`
holomorphic on `V` and vanishing on `Z ∩ V` whose germs generate, at every `y ∈ V`, the ideal of
the germs at `y` of the holomorphic functions vanishing on `Z` near `y`. This is finite type;
coherence of the ideal sheaf then follows from Oka's theorem (`AnalyticGeometry.okaCoherence`). -/
def IdealSheafCoherentStatement : Prop :=
  ∀ (n r : ℕ) (U : Set (Fin n → ℂ)) (_ : IsOpen U) (g : Fin r → (Fin n → ℂ) → ℂ)
    (_ : ∀ l, ∀ x ∈ U, AnalyticAt ℂ (g l) x), ∀ x₀ ∈ U,
    ∃ V ∈ 𝓝 x₀, V ⊆ U ∧ ∃ (m : ℕ) (h : Fin m → (Fin n → ℂ) → ℂ)
      (hh : ∀ j, ∀ y ∈ V, AnalyticAt ℂ (h j) y),
      (∀ j, ∀ y ∈ V, (∀ l, g l y = 0) → h j y = 0) ∧
      ∀ (y : Fin n → ℂ) (hy : y ∈ V) (F : (Fin n → ℂ) → ℂ) (hF : AnalyticAt ℂ F y),
        (∀ᶠ z in 𝓝 y, (∀ l, g l z = 0) → F z = 0) →
          germOf F hF ∈ Ideal.span (Set.range fun j ↦ germOf (h j) (hh j y hy))

end AnalyticGeometry
