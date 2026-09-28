/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Projective.ProjectiveSpaceHom

/-!
# Dehomogenization

For a ring `R` and `i ∈ σ`, the degree `0` part `R[xⱼ : j ∈ σ]_(xᵢ)` of the localization of the
polynomial ring at `xᵢ` is the polynomial ring `R[xⱼ / xᵢ : j ≠ i]` (EGA II 2.3.1, Hartshorne
II.2.5 (b)): the inverse maps are `P / xᵢⁿ ↦ P(xᵢ := 1)` and `yⱼ ↦ xⱼ / xᵢ`.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.dehomogenize i : R[σ] →+* R[σ ∖ {i}]`, `P ↦ P(xᵢ := 1)`.
- `AlgebraicGeometry.ProjectiveSpace.awayEquiv i : R[σ]_(xᵢ) ≃+* R[σ ∖ {i}]`.
-/

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.ProjectiveSpace

variable {σ R : Type u} [CommRing R] (i : σ)

open Classical in
/-- Dehomogenization at `xᵢ`: `P ↦ P(xᵢ := 1)`, with values in the polynomial ring in the
other variables. -/
noncomputable def dehomogenize : MvPolynomial σ R →+* MvPolynomial {j // j ≠ i} R :=
  eval₂Hom C fun j ↦ if h : j = i then 1 else X ⟨j, h⟩

@[simp]
lemma dehomogenize_C (r : R) : dehomogenize i (C r : MvPolynomial σ R) = C r :=
  eval₂Hom_C _ _ _

@[simp]
lemma dehomogenize_X_self : dehomogenize i (X i : MvPolynomial σ R) = 1 := by
  simp [dehomogenize]

lemma dehomogenize_X_of_ne {j : σ} (h : j ≠ i) :
    dehomogenize i (X j : MvPolynomial σ R) = X ⟨j, h⟩ := by
  simp [dehomogenize, h]

lemma isUnit_dehomogenize_X_self : IsUnit (dehomogenize i (X i : MvPolynomial σ R)) := by
  rw [dehomogenize_X_self]
  exact isUnit_one

variable {t : MvPolynomial σ R} (ht : t = X i)

include ht in
lemma isUnit_dehomogenize_of_eq : IsUnit (dehomogenize i t) := by
  subst ht
  exact isUnit_dehomogenize_X_self i

include ht in
lemma mem_grading_one_of_eq : t ∈ grading σ R 1 := by
  subst ht
  exact X_mem_grading i

/-- The ring homomorphism `R[σ]_(xᵢ) → R[σ ∖ {i}]`, `P / xᵢⁿ ↦ P(xᵢ := 1)`. It is stated for
an element `t` equal to `xᵢ` to avoid transport along such equalities. -/
noncomputable def awayDehomogenize : Away (grading σ R) t →+* MvPolynomial {j // j ≠ i} R :=
  (IsLocalization.Away.lift (S := Localization.Away t) t
    (isUnit_dehomogenize_of_eq i ht)).comp (algebraMap _ _)

lemma awayDehomogenize_mk (n : ℕ) (a : MvPolynomial σ R) (ha : a ∈ grading σ R (n • 1)) :
    awayDehomogenize i ht (Away.mk (grading σ R) (mem_grading_one_of_eq i ht) n a ha) =
      dehomogenize i a := by
  subst ht
  change (IsLocalization.Away.lift (S := Localization.Away (X i : MvPolynomial σ R)) (X i)
    (isUnit_dehomogenize_of_eq i rfl)) (Away.mk _ (mem_grading_one_of_eq i rfl) n a ha).val = _
  rw [Away.val_mk, Localization.mk_eq_mk']
  refine (IsLocalization.lift_mk'_spec (M := Submonoid.powers (X i : MvPolynomial σ R))
    (S := Localization.Away (X i : MvPolynomial σ R)) _ a _ ⟨X i ^ n, n, rfl⟩).mpr ?_
  simp

/-- The element `xⱼ / xᵢ` of `R[σ]_(xᵢ)`. -/
noncomputable def awayX (j : σ) : Away (grading σ R) t :=
  Away.mk (grading σ R) (mem_grading_one_of_eq i ht) 1 (X j) (by simpa using X_mem_grading j)

variable (t) in
/-- The ring homomorphism `R → R[σ]_(t)`. -/
noncomputable def awayC : R →+* Away (grading σ R) t :=
  (fromZeroRingHom (grading σ R) _).comp (algebraMap R (grading σ R 0))

lemma val_awayC (r : R) : (awayC t r).val = algebraMap _ _ (C r : MvPolynomial σ R) :=
  rfl

/-- The ring homomorphism `R[σ ∖ {i}] → R[σ]_(xᵢ)`, `yⱼ ↦ xⱼ / xᵢ`. -/
noncomputable def awayHomogenize : MvPolynomial {j // j ≠ i} R →+* Away (grading σ R) t :=
  eval₂Hom (awayC t) fun j ↦ awayX i ht j.1

lemma awayDehomogenize_awayC (r : R) : awayDehomogenize i ht (awayC t r) = C r := by
  subst ht
  change (IsLocalization.Away.lift (S := Localization.Away (X i : MvPolynomial σ R)) (X i)
    (isUnit_dehomogenize_of_eq i rfl)) (awayC _ r).val = _
  rw [val_awayC, IsLocalization.Away.lift, IsLocalization.lift_eq, dehomogenize_C]

lemma awayDehomogenize_comp_awayHomogenize :
    (awayDehomogenize i ht).comp (awayHomogenize i ht) =
      RingHom.id (MvPolynomial {j // j ≠ i} R) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
  · simp [awayHomogenize, awayDehomogenize_awayC]
  · simp only [awayHomogenize, RingHom.coe_comp, Function.comp_apply, coe_eval₂Hom, eval₂_X,
      RingHom.id_apply, awayX, awayDehomogenize_mk, dehomogenize_X_of_ne i j.2]

lemma val_awayHomogenize_dehomogenize (a : MvPolynomial σ R) :
    (awayHomogenize i (rfl : (X i : MvPolynomial σ R) = X i) (dehomogenize i a)).val =
      eval₂ (algebraMap R (Localization.Away (X i : MvPolynomial σ R)))
        (fun j ↦ IsLocalization.Away.invSelf (X i : MvPolynomial σ R) *
          algebraMap _ _ (X j : MvPolynomial σ R)) a := by
  let ρ : MvPolynomial σ R →+* Localization.Away (X i : MvPolynomial σ R) :=
    (algebraMap (Away (grading σ R) (X i)) _).comp
      ((awayHomogenize i (rfl : (X i : MvPolynomial σ R) = X i)).comp (dehomogenize i))
  change ρ a = _
  suffices hρ : ρ = eval₂Hom (algebraMap R (Localization.Away (X i : MvPolynomial σ R)))
      (fun j ↦ IsLocalization.Away.invSelf (X i : MvPolynomial σ R) *
        algebraMap _ _ (X j : MvPolynomial σ R)) by
    rw [hρ, coe_eval₂Hom]
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
  · simp only [ρ, RingHom.coe_comp, Function.comp_apply, dehomogenize_C, awayHomogenize,
      coe_eval₂Hom, eval₂_C, eval₂Hom_C]
    rw [HomogeneousLocalization.algebraMap_apply, val_awayC,
      IsScalarTower.algebraMap_apply R (MvPolynomial σ R), MvPolynomial.algebraMap_eq]
  · simp only [ρ, RingHom.coe_comp, Function.comp_apply, eval₂Hom_X']
    by_cases h : j = i
    · subst h
      rw [dehomogenize_X_self, map_one, map_one, mul_comm, IsLocalization.Away.mul_invSelf]
    · rw [dehomogenize_X_of_ne i h, awayHomogenize, eval₂Hom_X',
        HomogeneousLocalization.algebraMap_apply, awayX,
        Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
      simp only [pow_one]
      rfl

lemma awayHomogenize_comp_awayDehomogenize :
    (awayHomogenize i ht).comp (awayDehomogenize i ht) = RingHom.id (Away (grading σ R) t) := by
  subst ht
  ext y
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading σ R) (X_mem_grading i) y
  simp only [RingHom.coe_comp, Function.comp_apply, awayDehomogenize_mk, RingHom.id_apply,
    val_awayHomogenize_dehomogenize, Away.val_mk]
  have hh : a.IsHomogeneous n := by simpa using mem_grading.mp ha
  have e : eval₂ (algebraMap R (Localization.Away (X i : MvPolynomial σ R)))
      (fun j ↦ algebraMap _ _ (X j : MvPolynomial σ R)) a = algebraMap _ _ a := by
    conv_rhs => rw [← MvPolynomial.eval₂_eta a]
    rw [MvPolynomial.eval₂_comp_left]
    congr 1
  rw [hh.eval₂_mul_left, e, eq_comm, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp only [map_pow]
  rw [mul_right_comm, ← mul_pow, mul_comm (IsLocalization.Away.invSelf _),
    IsLocalization.Away.mul_invSelf, one_pow, one_mul]

/-- EGA II 2.3.1: the dehomogenization isomorphism `R[σ]_(xᵢ) ≃ R[σ ∖ {i}]`,
`P / xᵢⁿ ↦ P(xᵢ := 1)`, with inverse `yⱼ ↦ xⱼ / xᵢ`. It is stated for an element `t` equal to
`xᵢ`. -/
noncomputable def awayEquiv : Away (grading σ R) t ≃+* MvPolynomial {j // j ≠ i} R :=
  RingEquiv.ofRingHom (awayDehomogenize i ht) (awayHomogenize i ht)
    (awayDehomogenize_comp_awayHomogenize i ht) (awayHomogenize_comp_awayDehomogenize i ht)

lemma awayEquiv_apply (y : Away (grading σ R) t) : awayEquiv i ht y = awayDehomogenize i ht y :=
  rfl

@[simp]
lemma awayEquiv_awayC (r : R) : awayEquiv i ht (awayC t r) = C r :=
  awayDehomogenize_awayC i ht r

lemma awayEquiv_mk (n : ℕ) (a : MvPolynomial σ R) (ha : a ∈ grading σ R (n • 1)) :
    awayEquiv i ht (Away.mk (grading σ R) (mem_grading_one_of_eq i ht) n a ha) =
      dehomogenize i a :=
  awayDehomogenize_mk i ht n a ha

section map

variable {R' : Type u} [CommRing R'] (φ : R →+* R')

variable (σ) in
/-- The graded ring homomorphism `R[σ] → R'[σ]` induced by `φ : R →+* R'`. -/
noncomputable def gradingMap : grading σ R →+*ᵍ grading σ R' where
  toRingHom := MvPolynomial.map φ
  map_mem hx := mem_grading.mpr ((mem_grading.mp hx).map φ)

@[simp]
lemma gradingMap_apply (p : MvPolynomial σ R) : gradingMap σ φ p = MvPolynomial.map φ p :=
  rfl

lemma dehomogenize_map (a : MvPolynomial σ R) :
    dehomogenize i (MvPolynomial.map φ a) = MvPolynomial.map φ (dehomogenize i a) := by
  change ((dehomogenize i).comp (MvPolynomial.map φ)) a =
    ((MvPolynomial.map φ).comp (dehomogenize i)) a
  congr 1
  refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun j ↦ ?_)
  by_cases h : j = i
  · subst h
    simp
  · simp [dehomogenize_X_of_ne i h]

lemma map_X_eq : gradingMap σ φ (X i) = X i :=
  MvPolynomial.map_X φ i

/-- Dehomogenization commutes with change of rings. -/
lemma awayEquiv_awayMap (y : Away (grading σ R) (X i)) :
    awayEquiv i (map_X_eq i φ) (Away.map (gradingMap σ φ) (X i) y) =
      MvPolynomial.map φ (awayEquiv i rfl y) := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading σ R) (X_mem_grading i) y
  rw [Away.map_mk]
  exact (awayEquiv_mk i _ n _ _).trans ((dehomogenize_map i φ a).trans
    (congrArg _ (awayEquiv_mk i rfl n a ha).symm))

lemma awayMap_awayC (r : R) :
    Away.map (gradingMap σ φ) (X i) (awayC (X i) r) = awayC (gradingMap σ φ (X i)) (φ r) := by
  apply (awayEquiv i (map_X_eq i φ)).injective
  rw [awayEquiv_awayMap, awayEquiv_awayC, awayEquiv_awayC, map_C]

attribute [local instance] MvPolynomial.algebraMvPolynomial in
open CommRingCat in
set_option backward.isDefEq.respectTransparency false in
/-- The homogeneous localization `R[σ]_(xᵢ)` commutes with base change `R → R'`: the square
`R → R[σ]_(xᵢ)`, `R' → R'[σ]_(xᵢ)` is a pushout of commutative rings. -/
lemma isPushout_away :
    IsPushout (ofHom (awayC (X i : MvPolynomial σ R))) (ofHom φ)
      (ofHom (Away.map (gradingMap σ φ) (X i))) (ofHom (awayC (gradingMap σ φ (X i)))) := by
  let := φ.toAlgebra
  have H := CommRingCat.isPushout_of_isPushout R (MvPolynomial {j // j ≠ i} R) R'
    (MvPolynomial {j // j ≠ i} R')
  refine H.of_iso (Iso.refl _) (awayEquiv i rfl).symm.toCommRingCatIso (Iso.refl _)
    (awayEquiv i (map_X_eq i φ)).symm.toCommRingCatIso ?_ ?_ ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    apply (awayEquiv i rfl).injective
    simp [MvPolynomial.algebraMap_eq]
  · rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun p ↦ ?_)
    apply (awayEquiv i (map_X_eq i φ)).injective
    simp only [CommRingCat.hom_comp, hom_ofHom, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toCommRingCatIso_hom, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply,
      awayEquiv_awayMap]
    rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    apply (awayEquiv i (map_X_eq i φ)).injective
    simp [MvPolynomial.algebraMap_eq]

end map

end AlgebraicGeometry.ProjectiveSpace
