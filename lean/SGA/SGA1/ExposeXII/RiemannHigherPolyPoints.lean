/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigherPolyFamily
import SGA.SGA1.ExposeXII.Points

/-!
# Points of `A[X]` and of `A[X][1/r]`

For a `ℂ`-algebra `A`, the points of `A[X]` are the pairs of a point `w` of `A` and a value `x`
of `X` (`RiemannHigher.polyHomeomorph : Points ℂ A[X] ≃ₜ Points ℂ A × ℂ`), and the points of the
localization `A[X][1/r]` are those with `r_w(x) ≠ 0`
(`RiemannHigher.polyAwayHomeomorph : Points ℂ A[X][1/r] ≃ₜ PolyComplement (w ↦ r_w)`). These are
the families of punctured lines of the induction step of XII.5.1 in higher dimension
(`SGA.SGA1.ExposeXII.RiemannHigher`).
-/
noncomputable section

open Polynomial Topology Set

namespace SGA.SGA1.ExposeXII.RiemannHigher

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The point of `A[X]` with restriction `w` to `A` and value `x` at `X`. -/
def polyPoint (w : Points ℂ A) (x : ℂ) : Points ℂ A[X] :=
  Points.ofAlgHom
    { eval₂RingHom w.toRingHom x with
      commutes' := fun c ↦ by
        change eval₂ w.toRingHom x (C (algebraMap ℂ A c)) = c
        rw [eval₂_C]
        exact w.commutes c }

@[simp]
lemma polyPoint_apply (w : Points ℂ A) (x : ℂ) (p : A[X]) :
    polyPoint w x p = p.eval₂ w.toRingHom x := rfl

/-- A point of `A[X]` is determined by its restriction to `A` and its value at `X`. -/
lemma polyPoint_eq (χ : Points ℂ A[X]) :
    polyPoint (Points.proj A A[X] χ) (χ X) = χ := by
  ext p
  rw [polyPoint_apply]
  conv_rhs => rw [← p.sum_C_mul_X_pow_eq]
  rw [eval₂_eq_sum, Polynomial.sum, Polynomial.sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_pow]
  rfl

/-- The points of `A[X]` are the pairs (point of `A`, value of `X`). -/
def polyHomeomorph : Points ℂ A[X] ≃ₜ Points ℂ A × ℂ where
  toFun χ := (Points.proj A A[X] χ, χ X)
  invFun wx := polyPoint wx.1 wx.2
  left_inv χ := polyPoint_eq χ
  right_inv wx := by
    refine Prod.ext (Points.ext fun a ↦ ?_) ?_
    · change eval₂ wx.1.toRingHom wx.2 (C a) = wx.1 a
      rw [eval₂_C]
      rfl
    · change eval₂ wx.1.toRingHom wx.2 X = wx.2
      rw [eval₂_X]
  continuous_toFun := (Points.continuous_map _).prodMk (Points.continuous_apply _)
  continuous_invFun := by
    refine Points.continuous_iff.mpr fun p ↦ ?_
    change Continuous fun wx : Points ℂ A × ℂ ↦ p.eval₂ wx.1.toRingHom wx.2
    simp_rw [eval₂_eq_sum_range]
    refine continuous_finsetSum _ fun i _ ↦ ?_
    exact ((Points.continuous_apply (p.coeff i)).comp continuous_fst).mul
      (continuous_snd.pow i)

@[simp]
lemma polyHomeomorph_apply (χ : Points ℂ A[X]) :
    polyHomeomorph χ = (Points.proj A A[X] χ, χ X) := rfl

lemma polyHomeomorph_symm_apply (wx : Points ℂ A × ℂ) :
    polyHomeomorph.symm wx = polyPoint wx.1 wx.2 := rfl

/-- The value of an element of `A[X]` at the point `(w, x)` is `p_w(x)`. -/
lemma polyPoint_apply_eq_eval (w : Points ℂ A) (x : ℂ) (p : A[X]) :
    polyPoint w x p = (p.map w.toRingHom).eval x := by
  rw [polyPoint_apply, eval_map]

section Away

variable (r : A[X])

/-- The family of `ℂ` minus the roots of `r_w`, over the points `w` of `A`. -/
abbrev PolyAwayBase : Type _ := PolyComplement (fun w : Points ℂ A ↦ r.map w.toRingHom)

/-- The points of `A[X][1/r]` are the pairs `(w, x)` with `r_w(x) ≠ 0`. -/
def polyAwayHomeomorph : Points ℂ (Localization.Away r) ≃ₜ PolyAwayBase r :=
  have he := Points.isOpenEmbedding_map_of_isLocalizationAway (K := ℂ) (A := A[X])
    (B := Localization.Away r) r
  (he.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr
    (Points.range_map_of_isLocalizationAway r))).trans
    (polyHomeomorph.subtype fun χ ↦ by
      change χ r ≠ 0 ↔ ((r.map (Points.proj A A[X] χ).toRingHom).eval (χ X)) ≠ 0
      rw [← polyPoint_apply_eq_eval, polyPoint_eq])

lemma polyAwayHomeomorph_apply_fst (χ : Points ℂ (Localization.Away r)) :
    (polyAwayHomeomorph r χ).1.1 = Points.proj A (Localization.Away r) χ := rfl

lemma polyAwayHomeomorph_apply_snd (χ : Points ℂ (Localization.Away r)) :
    (polyAwayHomeomorph r χ).1.2 = χ (algebraMap A[X] _ X) := rfl

end Away

end SGA.SGA1.ExposeXII.RiemannHigher
