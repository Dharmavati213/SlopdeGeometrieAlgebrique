/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigherPolyPoints
import SGA.SGA1.ExposeXII.RiemannHigherRootSpace
import SGA.SGA1.ExposeXII.LocalTopologyLPC
import SGA.Foundations.Topology.FiniteCoveringBaseChange

/-!
# Families of presentations of coverings of punctured lines

Let `A` be a `ℂ`-algebra, `r ∈ A[X]` and `T = A[X][1/r]`, whose points are the pairs `(w, x)` with
`r_w(x) ≠ 0` (`polyAwayHomeomorph`). A *presentation datum* over an `A`-algebra `R`
(`RiemannHigher.PresData r R`) consists of `G ∈ R[X]` monic and separable (`V G + V' G' = 1`),
`P ∈ R[X][Y]` monic in `Y` and separable over `R[X][1/G]` (`a P + b ∂_Y P = G^N`), and `U` with
`U r = G^N`. At a point `z` of `R` over `w ∈ A(ℂ)` it gives the covering
`{(x, y) | G_z(x) ≠ 0, P_z(x, y) = 0}` of `{x | G_z(x) ≠ 0} ⊆ {x | r_w(x) ≠ 0}`.

For a finite covering `E` of `T(ℂ)`:

* `RiemannHigher.FibreMatch r E w G₀ P₀`: over `{x | G₀(x) ≠ 0}`, the part of `E` over the fibre
  `w` is homeomorphic to `{(x, y) | P₀(x, y) = 0}`, compatibly with `x`;
* the two coverings of `{(z, x) | G_z(x) ≠ 0}` over `R(ℂ)`: the root space of `P`
  (`PresData.rootCovering`) and the pullback of `E` (`PresData.pullCovering`), and
  `PresData.fibreIso_iff`: they are isomorphic over `z` iff `FibreMatch r E w G_z P_z`;
* `PresData.isClopen_setOf_fibreMatch`: for `R` of finite type over `ℂ`, the set of points `z` of
  `R` at which the datum presents `E` is clopen in `R(ℂ)` (`isClopen_setOf_fibreIso_polyComplement`).

This is the parameter space of the induction step of XII.5.1 in higher dimension
(`SGA.SGA1.ExposeXII.RiemannHigher`, step 1 (b), (c)).
-/
noncomputable section

open Polynomial Topology Set CategoryTheory

namespace SGA.SGA1.ExposeXII.RiemannHigher

/-- The polynomial in `Y` obtained from `P₀ ∈ ℂ[X][Y]` by setting `X = x`. -/
abbrev fibrePoly (P₀ : ℂ[X][X]) (x : ℂ) : ℂ[X] := P₀.map (evalRingHom x)

section Data

variable {A : Type} [CommRing A] [Algebra ℂ A] (r : A[X])

/-- A presentation datum over an `A`-algebra `R`: `G ∈ R[X]` monic and separable, `P ∈ R[X][Y]`
monic in `Y` and separable after inverting `G`, and `r | G^N`. -/
structure PresData (R : Type) [CommRing R] [Algebra A R] where
  /-- The exponent in the certificates. -/
  N : ℕ
  /-- The polynomial whose zeros are removed. -/
  G : R[X]
  /-- The polynomial cutting out the covering. -/
  P : R[X][X]
  /-- Certificate for `r | G^N`. -/
  U : R[X]
  /-- Certificates for the separability of `G`. -/
  V : R[X]
  V' : R[X]
  /-- Certificates for the separability of `P` over `R[X][1/G]`. -/
  a : R[X][X]
  b : R[X][X]
  monic_G : G.Monic
  monic_P : P.Monic
  sep_G : V * G + V' * derivative G = 1
  sep_P : a * P + b * derivative P = C (G ^ N)
  dvd_r : U * r.map (algebraMap A R) = G ^ N

variable {r}

namespace PresData

variable {R : Type} [CommRing R] [Algebra A R]

/-- The image of a presentation datum under an `A`-algebra map. -/
def map (D : PresData r R) {R' : Type} [CommRing R'] [Algebra A R'] (φ : R →ₐ[A] R') :
    PresData r R' where
  N := D.N
  G := D.G.map φ
  P := D.P.map (mapRingHom φ)
  U := D.U.map φ
  V := D.V.map φ
  V' := D.V'.map φ
  a := D.a.map (mapRingHom φ)
  b := D.b.map (mapRingHom φ)
  monic_G := D.monic_G.map _
  monic_P := D.monic_P.map _
  sep_G := by
    rw [derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add,
      D.sep_G, Polynomial.map_one]
  sep_P := by
    rw [derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add,
      D.sep_P, Polynomial.map_C, coe_mapRingHom, Polynomial.map_pow]
  dvd_r := by
    rw [← φ.comp_algebraMap, ← Polynomial.map_map, ← Polynomial.map_mul, D.dvd_r,
      Polynomial.map_pow]

end PresData

/-- A polynomial over a field with `a p + b p' = c ≠ 0` constant is separable. -/
lemma separable_of_mul_add_eq_C {K : Type*} [Field K] {p a b : K[X]} {c : K}
    (h : a * p + b * derivative p = C c) (hc : c ≠ 0) : p.Separable :=
  ⟨C c⁻¹ * a, C c⁻¹ * b, by
    rw [mul_assoc, mul_assoc, ← mul_add, h, ← C_mul, inv_mul_cancel₀ hc, C_1]⟩

/-- `(p_z)(x)` is continuous in `(z, x)`. -/
lemma continuous_eval_map {R : Type*} [CommRing R] [Algebra ℂ R] (p : R[X]) :
    Continuous fun c : Points ℂ R × ℂ ↦ (p.map c.1.toRingHom).eval c.2 := by
  have : (fun c : Points ℂ R × ℂ ↦ (p.map c.1.toRingHom).eval c.2) =
      fun c ↦ polyHomeomorph.symm c p := by
    ext c
    rw [polyHomeomorph_symm_apply, polyPoint_apply_eq_eval]
  rw [this]
  exact (Points.continuous_apply p).comp polyHomeomorph.symm.continuous

namespace PresData

variable {R : Type} [CommRing R] [Algebra ℂ R] [Algebra A R] [IsScalarTower ℂ A R]
  (D : PresData r R)

/-- The family `{(z, x) | G_z(x) ≠ 0}` over the points of `R`. -/
abbrev Base : Type := PolyComplement (fun z : Points ℂ R ↦ D.G.map z.toRingHom)

/-- The polynomial `P_z(x, Y)` over a point `(z, x)` of the base. -/
abbrev rootPoly (c : D.Base) : ℂ[X] := fibrePoly (D.P.map (mapRingHom c.1.1.toRingHom)) c.1.2

omit [Algebra ℂ A] [IsScalarTower ℂ A R] in
lemma monic_rootPoly (c : D.Base) : (D.rootPoly c).Monic := (D.monic_P.map _).map _

omit [Algebra ℂ A] [IsScalarTower ℂ A R] in
lemma natDegree_rootPoly (c : D.Base) : (D.rootPoly c).natDegree = D.P.natDegree := by
  rw [(D.monic_P.map _).natDegree_map, D.monic_P.natDegree_map]

omit [Algebra ℂ A] [IsScalarTower ℂ A R] in
lemma continuous_coeff_rootPoly (i : ℕ) : Continuous fun c : D.Base ↦ (D.rootPoly c).coeff i := by
  have : (fun c : D.Base ↦ (D.rootPoly c).coeff i) =
      fun c ↦ ((D.P.coeff i).map c.1.1.toRingHom).eval c.1.2 := by
    ext c
    simp [rootPoly, fibrePoly, coeff_map]
  rw [this]
  exact (continuous_eval_map (D.P.coeff i)).comp continuous_subtype_val

omit [Algebra ℂ A] [IsScalarTower ℂ A R] in
lemma separable_rootPoly (c : D.Base) : (D.rootPoly c).Separable := by
  refine separable_of_mul_add_eq_C (a := fibrePoly (D.a.map (mapRingHom c.1.1.toRingHom)) c.1.2)
    (b := fibrePoly (D.b.map (mapRingHom c.1.1.toRingHom)) c.1.2) ?_ (pow_ne_zero D.N c.2)
  simp only [fibrePoly, rootPoly]
  rw [derivative_map, derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
    ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, ← Polynomial.map_add,
    D.sep_P, Polynomial.map_C, Polynomial.map_C, coe_mapRingHom, Polynomial.map_pow, coe_evalRingHom,
    eval_pow]

omit [Algebra ℂ A] [IsScalarTower ℂ A R] in
/-- The root space of `P` over the base: a covering. -/
lemma isCoveringMap_rootProj : IsCoveringMap (rootProj D.rootPoly) :=
  isCoveringMap_rootSpace D.monic_rootPoly D.natDegree_rootPoly D.continuous_coeff_rootPoly
    D.separable_rootPoly

omit [Algebra ℂ A] [IsScalarTower ℂ A R] in
lemma finite_rootProj_preimage (c : D.Base) : (rootProj D.rootPoly ⁻¹' {c}).Finite :=
  RiemannHigher.finite_rootProj_preimage (fun c ↦ (D.monic_rootPoly c).ne_zero) c

lemma eval_r_ne_zero (c : D.Base) :
    (r.map (Points.proj A R c.1.1).toRingHom).eval c.1.2 ≠ 0 := by
  have h := congrArg (fun p : R[X] ↦ (p.map c.1.1.toRingHom).eval c.1.2) D.dvd_r
  simp only [Polynomial.map_mul, Polynomial.map_pow, eval_mul, eval_pow, Polynomial.map_map] at h
  intro h0
  refine pow_ne_zero D.N c.2 (h.symm.trans ?_)
  convert mul_zero _
  exact h0

/-- The point of `T = A[X][1/r]` under a point `(z, x)` of the base. -/
def basePoint (c : D.Base) : Points ℂ (Localization.Away r) :=
  (polyAwayHomeomorph r).symm ⟨(Points.proj A R c.1.1, c.1.2), D.eval_r_ne_zero c⟩

lemma continuous_basePoint : Continuous D.basePoint :=
  (polyAwayHomeomorph r).symm.continuous.comp (Continuous.subtype_mk
    (((Points.continuous_map _).comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)) _)

lemma polyAwayHomeomorph_basePoint (c : D.Base) :
    polyAwayHomeomorph r (D.basePoint c) =
      ⟨(Points.proj A R c.1.1, c.1.2), D.eval_r_ne_zero c⟩ :=
  (polyAwayHomeomorph r).apply_symm_apply _

variable (E : TopCat.FiniteCovering (TopCat.of (Points ℂ (Localization.Away r))))

/-- The pullback of `E` to the base. -/
abbrev PullSpace : Type := Function.Pullback D.basePoint E.obj.hom

lemma isCoveringMap_pullSpace :
    IsCoveringMap (Function.Pullback.fst : D.PullSpace E → D.Base) :=
  E.isCoveringMap.pullbackFst D.continuous_basePoint

end PresData

variable (r) in
/-- `E` is presented over the fibre `w`, away from the zeros of `G₀`, by `P₀`: the part of `E` over
`{(w, x) | G₀(x) ≠ 0}` is homeomorphic to `{(x, y) | G₀(x) ≠ 0, P₀(x, y) = 0}`, compatibly with
`x`. -/
def FibreMatch (E : TopCat.FiniteCovering (TopCat.of (Points ℂ (Localization.Away r))))
    (w : Points ℂ A) (G₀ : ℂ[X]) (P₀ : ℂ[X][X]) : Prop :=
  ∃ φ : {e : E.obj.left // (polyAwayHomeomorph r (E.obj.hom e)).1.1 = w ∧
      G₀.eval (polyAwayHomeomorph r (E.obj.hom e)).1.2 ≠ 0} ≃ₜ
      {xy : ℂ × ℂ // G₀.eval xy.1 ≠ 0 ∧ (fibrePoly P₀ xy.1).eval xy.2 = 0},
    ∀ e, (φ e).1.1 = (polyAwayHomeomorph r (E.obj.hom e.1)).1.2

namespace PresData

variable {R : Type} [CommRing R] [Algebra ℂ R] [Algebra A R] [IsScalarTower ℂ A R]
  (D : PresData r R) (E : TopCat.FiniteCovering (TopCat.of (Points ℂ (Localization.Away r))))

omit [Algebra ℂ A] [IsScalarTower ℂ A R] in
/-- The fibre of the root space over `z`. -/
def rootFibreHomeomorph (z : Points ℂ R) :
    FibreSpace (rootProj D.rootPoly) (fun c : D.Base ↦ c.1.1) z ≃ₜ
      {xy : ℂ × ℂ // (D.G.map z.toRingHom).eval xy.1 ≠ 0 ∧
        (fibrePoly (D.P.map (mapRingHom z.toRingHom)) xy.1).eval xy.2 = 0} where
  toFun c := ⟨(c.1.1.1.1.2, c.1.1.2), by
    obtain ⟨⟨⟨⟨⟨z', x⟩, hG⟩, y⟩, hy⟩, hz⟩ := c
    dsimp only at hz
    subst hz
    exact ⟨hG, hy⟩⟩
  invFun xy := ⟨⟨(⟨(z, xy.1.1), xy.2.1⟩, xy.1.2), xy.2.2⟩, rfl⟩
  left_inv c := by
    obtain ⟨⟨⟨⟨⟨z', x⟩, hG⟩, y⟩, hy⟩, hz⟩ := c
    dsimp only at hz
    subst hz
    rfl
  right_inv xy := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The fibre of the pullback of `E` over `z`. -/
def pullFibreHomeomorph (z : Points ℂ R) :
    FibreSpace (Function.Pullback.fst : D.PullSpace E → D.Base) (fun c : D.Base ↦ c.1.1) z ≃ₜ
      {e : E.obj.left // (polyAwayHomeomorph r (E.obj.hom e)).1.1 = Points.proj A R z ∧
        (D.G.map z.toRingHom).eval (polyAwayHomeomorph r (E.obj.hom e)).1.2 ≠ 0} where
  toFun q := ⟨q.1.1.2, by
    obtain ⟨⟨⟨⟨⟨z', x⟩, hG⟩, e⟩, he⟩, hz⟩ := q
    change z' = z at hz
    subst hz
    change D.basePoint _ = E.obj.hom e at he
    rw [← he, polyAwayHomeomorph_basePoint]
    exact ⟨rfl, hG⟩⟩
  invFun e := ⟨⟨(⟨(z, (polyAwayHomeomorph r (E.obj.hom e.1)).1.2), e.2.2⟩, e.1), by
    change (polyAwayHomeomorph r).symm _ = E.obj.hom e.1
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext (Prod.ext e.2.1.symm rfl)⟩, rfl⟩
  left_inv q := by
    obtain ⟨⟨⟨⟨⟨z', x⟩, hG⟩, e⟩, he⟩, hz⟩ := q
    change z' = z at hz
    subst hz
    change D.basePoint _ = E.obj.hom e at he
    refine Subtype.ext (Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl ?_)) rfl))
    change (polyAwayHomeomorph r (E.obj.hom e)).1.2 = x
    rw [← he, polyAwayHomeomorph_basePoint]
  right_inv e := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk
      (Continuous.subtype_mk (continuous_const.prodMk ?_) _) continuous_subtype_val) _) _
    exact continuous_subtype_val.comp ((polyAwayHomeomorph r).continuous.comp
      (E.obj.hom.hom.continuous.comp continuous_subtype_val)) |>.snd

/-- The root space of `P` and the pullback of `E` are isomorphic over the fibre at `z` if and only
if `E` is presented by `P_z` over the fibre at `z`. -/
theorem fibreIso_iff (z : Points ℂ R) :
    FibreIso (rootProj D.rootPoly) (Function.Pullback.fst : D.PullSpace E → D.Base)
      (fun c : D.Base ↦ c.1.1) z ↔
      FibreMatch r E (Points.proj A R z) (D.G.map z.toRingHom)
        (D.P.map (mapRingHom z.toRingHom)) := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨(D.pullFibreHomeomorph E z).symm.trans (φ.symm.trans (D.rootFibreHomeomorph z)),
      fun e ↦ ?_⟩
    have := hφ (φ.symm ((D.pullFibreHomeomorph E z).symm e))
    rw [Homeomorph.apply_symm_apply] at this
    exact (congrArg (fun c : D.Base ↦ c.1.2) this).symm
  · rintro ⟨ψ, hψ⟩
    refine ⟨(D.rootFibreHomeomorph z).trans (ψ.symm.trans (D.pullFibreHomeomorph E z).symm),
      fun c ↦ ?_⟩
    have := hψ (ψ.symm (D.rootFibreHomeomorph z c))
    rw [Homeomorph.apply_symm_apply] at this
    refine Subtype.ext (Prod.ext ?_ this.symm)
    exact c.2.symm

omit [Algebra ℂ A] [IsScalarTower ℂ A R] in
lemma separable_G_map (z : Points ℂ R) : (D.G.map z.toRingHom).Separable :=
  ⟨D.V.map z.toRingHom, D.V'.map z.toRingHom, by
    rw [derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, D.sep_G,
      Polynomial.map_one]⟩

/-- The points of `R` at which the datum presents `E` form a clopen subset of `R(ℂ)`. -/
theorem isClopen_setOf_fibreMatch [Algebra.FiniteType ℂ R] :
    IsClopen {z : Points ℂ R | FibreMatch r E (Points.proj A R z) (D.G.map z.toRingHom)
      (D.P.map (mapRingHom z.toRingHom))} := by
  have h := isClopen_setOf_fibreIso_polyComplement (B := Points ℂ R)
    (G := fun z : Points ℂ R ↦ D.G.map z.toRingHom) (r := D.G.natDegree)
    (fun _ ↦ D.monic_G.map _) (fun _ ↦ D.monic_G.natDegree_map _)
    (fun i ↦ by simpa [coeff_map] using Points.continuous_apply (D.G.coeff i))
    D.separable_G_map D.isCoveringMap_rootProj (D.isCoveringMap_pullSpace E)
  convert h using 1
  ext z
  exact (D.fibreIso_iff E z).symm

end PresData

end Data

end SGA.SGA1.ExposeXII.RiemannHigher
