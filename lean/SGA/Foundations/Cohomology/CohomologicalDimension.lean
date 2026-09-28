/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.CechVanishing
import SGA.Foundations.Cohomology.ProjectiveSpace

/-!
# Vanishing of cohomology above the number of affines

If a scheme is covered by `n` affine opens all of whose finite intersections are affine (e.g. a
separated scheme covered by `n` affines), the cohomology of quasi-coherent modules vanishes in
degrees `≥ n` (Stacks Project, Tags 01XD and 01FM; Hartshorne III.4.5 and Exercise III.4.8). In
particular `Hᵖ(ℙʳ_A, F) = 0` for `p > r` and every quasi-coherent `F`.
-/

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- **Vanishing above the number of affines** (Stacks Project, Tags 01XD and 01FM): let
`U₀, …, U_{n-1}` be affine opens of a scheme all of whose finite intersections are affine, and `F`
quasi-coherent. Then `Hᵖ(⋃ Uᵢ, F) = 0` for `p ≥ n`. -/
theorem H'_subsingleton_of_card_le [F.IsQuasicoherent] {n : ℕ} (U : Fin n → X.Opens)
    (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    {p : ℕ} (hp : n ≤ p + 1) : Subsingleton (F.H' (p + 1) (⨆ i, U i)) :=
  (TopCat.Sheaf.cechComplex_exactAt_iff_subsingleton_H' (X := X.carrier) U p F.toAbSheaf
    fun x q ↦ F.H'_subsingleton_of_isAffineOpen (hU x) q).mp
    (TopCat.Presheaf.cechComplex_exactAt_of_card_le _ U hp (Nat.succ_pos p))

/-- **Vanishing above the number of affines** (Stacks Project, Tags 01XD and 01FM; Hartshorne
III.4.5 and Exercise III.4.8): on a scheme with affine diagonal (e.g. a separated scheme) covered
by `n` affine opens, `Hᵖ(X, F) = 0` for `p ≥ n` and `F` quasi-coherent. -/
theorem H_subsingleton_of_card_le [IsAffineHom (pullback.diagonal (terminal.from X))]
    [F.IsQuasicoherent] {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) {p : ℕ} (hp : n ≤ p + 1) : Subsingleton (F.H (p + 1)) := by
  have h := F.H'_subsingleton_of_card_le U (isAffineOpen_cechOpen hU) hp
  rw [hcov] at h
  exact h

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.projectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `Hᵖ(ℙʳ_A, F) = 0` for `p > r` and every quasi-coherent `F` on `ℙʳ_A = Proj A[x₀, …, x_r]`
(Hartshorne III.4.5 and Exercise III.4.8; the cover by the `r + 1` affines `D₊(xᵢ)`). -/
theorem H_subsingleton_of_lt (A : CommRingCat.{u}) (r : ℕ) (F : (projectiveSpace A r).Modules)
    [F.IsQuasicoherent] {p : ℕ} (hp : r ≤ p) : Subsingleton (F.H (p + 1)) := by
  have h := F.H'_subsingleton_of_card_le (stdCover (Fin (r + 1)) A) (fun {m} x ↦ by
    have := Proj.isAffineOpen_basicOpen _ _ (prodX_mem (A := A) (Finset.univ.image x))
      (image_nonempty x).card_pos
    rwa [← cechOpen_stdCover] at this)
    (p := p) (by omega)
  have e : (⊤ : (projectiveSpace A r).Opens) = ⨆ i, stdCover (Fin (r + 1)) A i :=
    (iSup_stdCover _ _).symm
  change Subsingleton (F.H' (p + 1) ⊤)
  rw [e]
  exact h

end AlgebraicGeometry.projectiveSpace
