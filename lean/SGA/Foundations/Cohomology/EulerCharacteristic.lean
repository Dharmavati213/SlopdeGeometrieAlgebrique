/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Statements
import Mathlib.Algebra.Homology.EulerCharacteristic

/-!
# Dimensions of cohomology, Euler characteristic and genus over a field

Let `k` be a field and `f : X ⟶ Spec k`. For an `𝒪_X`-module `M`, the cohomology `Hᵖ(X, M)` is a
`k`-module through `k → Γ(X, 𝒪_X)` (`Scheme.Modules.moduleOver`, EGA III 1.4.1). When `f` is
proper and `M` coherent, these are finite-dimensional
(`AlgebraicGeometry.properFinitenessStatement`, EGA III 3.2.1) and vanish in large degrees, and one
defines (EGA III 2.5; Hartshorne III Ex. 5.1; Stacks Tag 0BEJ)

* `Scheme.Modules.cohomologyGraded f M`: the graded `k`-module `p ↦ Hᵖ(X, M)`;
* `Scheme.Modules.finrankH f M p = hᵖ(X, M) = dim_k Hᵖ(X, M)`;
* `Scheme.Modules.eulerChar f M = χ(X, M) = Σ_p (-1)ᵖ hᵖ(X, M)`, mathlib's
  `GradedObject.eulerChar` of `cohomologyGraded f M`;
* `Scheme.Hom.genus f = h¹(X, 𝒪_X)`. For a smooth proper connected curve over a separably closed
  field this is the genus (Hartshorne IV.1; Stacks Tag 0BY8); in general it is the first Hodge
  number `h^{0,1}`, not the arithmetic genus `(-1)^{dim X} (χ(𝒪_X) - 1)`.

These use the same cohomology (`Scheme.Modules.H`) and the same `k`-module structure
(`Scheme.Modules.moduleOver`) as `ProperFinitenessStatement`. Like mathlib's `Module.finrank` and
`finsum`, they take junk values (`0`) when the cohomology is infinite-dimensional or nonzero in
infinitely many degrees.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

namespace Scheme.Modules

/-- The graded `k`-module `p ↦ Hᵖ(X, M)` of an `𝒪_X`-module `M` on a scheme `X` over `Spec k`,
with the `k`-module structure `Scheme.Modules.moduleOver` (EGA III 1.4.1). -/
noncomputable def cohomologyGraded (f : X ⟶ Spec (.of k)) (M : X.Modules) :
    GradedObject ℕ (ModuleCat.{u} k) :=
  fun p ↦ letI := M.moduleOver f p ⊤; ModuleCat.of k (M.H p)

/-- `hᵖ(X, M) = dim_k Hᵖ(X, M)` for an `𝒪_X`-module `M` on a scheme `X` over `Spec k`
(Hartshorne III Ex. 5.1). It is `0` when `Hᵖ(X, M)` is infinite-dimensional. -/
noncomputable def finrankH (f : X ⟶ Spec (.of k)) (M : X.Modules) (p : ℕ) : ℕ :=
  letI := M.moduleOver f p ⊤
  Module.finrank k (M.H p)

/-- The **Euler characteristic** `χ(X, M) = Σ_p (-1)ᵖ dim_k Hᵖ(X, M)` of an `𝒪_X`-module `M` on a
scheme `X` over `Spec k` (EGA III 2.5; Hartshorne III Ex. 5.1; Stacks Tag 0BEJ), as mathlib's
`GradedObject.eulerChar` of `cohomologyGraded f M`. It is meaningful for `f` proper and `M`
coherent; it is `0` when infinitely many `hᵖ(X, M)` are nonzero. -/
noncomputable def eulerChar (f : X ⟶ Spec (.of k)) (M : X.Modules) : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℕ) (cohomologyGraded f M)

lemma finrank_cohomologyGraded (f : X ⟶ Spec (.of k)) (M : X.Modules) (p : ℕ) :
    Module.finrank k (cohomologyGraded f M p) = finrankH f M p :=
  rfl

lemma eulerChar_def (f : X ⟶ Spec (.of k)) (M : X.Modules) :
    eulerChar f M = ∑ᶠ p : ℕ, (-1 : ℤ) ^ p * (finrankH f M p : ℤ) := by
  simp only [eulerChar, GradedObject.eulerChar, ComplexShape.χ, ComplexShape.eulerCharSignsUpNat_χ,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, finrank_cohomologyGraded]

/-- If `hᵖ(X, M) = 0` for every `p ∉ s`, then `χ(X, M)` is the finite sum over `s`. -/
lemma eulerChar_eq_sum (f : X ⟶ Spec (.of k)) (M : X.Modules) (s : Finset ℕ)
    (hs : ∀ p ∉ s, finrankH f M p = 0) :
    eulerChar f M = ∑ p ∈ s, (-1 : ℤ) ^ p * (finrankH f M p : ℤ) := by
  rw [eulerChar_def, finsum_eq_sum_of_support_subset]
  intro p hp
  by_contra h
  exact hp (by simp [hs p h])

end Scheme.Modules

/-- The **genus** `h¹(X, 𝒪_X) = dim_k H¹(X, 𝒪_X)` of a scheme `X` over `Spec k`. For a smooth
proper connected curve over a separably closed field this is the genus of the curve (Hartshorne
IV.1; Stacks Tag 0BY8: there `H⁰(X, 𝒪_X) = k`, so it is also `1 - χ(X, 𝒪_X)`). For higher
dimensional `X` it is the Hodge number `h^{0,1}`, not the arithmetic genus. -/
noncomputable def Scheme.Hom.genus (f : X ⟶ Spec (.of k)) : ℕ :=
  Scheme.Modules.finrankH f (SheafOfModules.unit X.ringCatSheaf) 1

end AlgebraicGeometry
