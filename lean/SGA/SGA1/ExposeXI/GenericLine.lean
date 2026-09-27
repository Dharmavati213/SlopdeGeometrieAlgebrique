/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Projective.Dehomogenization
import SGA.SGA1.ExposeXI.ProjectiveLineAlgebra

/-!
# The generic line through a point of `ℙʳ` (for XI.1.1)

Let `P = Proj k[xⱼ : j ∈ σ]` and `n ≠ s` two indices. The lines through the point `e = (xₙ = 1,
xⱼ = 0 for j ≠ n)` are `[x₀ : x₁] ↦ (xₙ = x₀, x_s = x₁, xⱼ = wⱼ x₁)`; over the field
`F = k(wⱼ : j ≠ n, s)` this is the *generic line* through `e`. We record it on the rings of the
standard charts `D₊(xₙ)`, `D₊(x_s)`, `D₊(xₙ x_s)` of `P`:

* `lineN : k[σ]_(xₙ) → F[t]`, `xⱼ/xₙ ↦ t` (`j = s`), `wⱼ t` (`j ≠ n, s`);
* `lineS : k[σ]_(x_s) → F[u]`, `xₙ/x_s ↦ u`, `xⱼ/x_s ↦ wⱼ`, a localization (`isLocalization_lineS`);
* `lineNS : k[σ]_(xₙ x_s) → F[t, t⁻¹]`, compatible with both (`lineNS_comp_awayMapN`,
  `lineNS_comp_awayMapS`, with `u = t⁻¹`);
* `pointN : k[σ]_(xₙ) → k`, the point `e`, with `t = 0` over it (`evalZero_comp_lineN`).
-/

universe u

open Polynomial LaurentPolynomial HomogeneousLocalization AlgebraicGeometry.ProjectiveSpace

namespace SGA.SGA1.ExposeXI.GenericLine

section AwayLift

variable {A : Type*} [CommRing A] {σ' : Type*} [SetLike σ' A] [AddSubgroupClass σ' A]
  (𝒜 : ℕ → σ') [GradedRing 𝒜] {R : Type*} [CommRing R]

/-- The ring homomorphism `A_(f) → R`, `a / fᵐ ↦ g(a) / g(f)ᵐ`, for `g : A → R` with `g f` a
unit. -/
noncomputable def awayLift (f : A) (g : A →+* R) (hg : IsUnit (g f)) : Away 𝒜 f →+* R :=
  (IsLocalization.Away.lift (S := Localization.Away f) f hg).comp (algebraMap _ _)

lemma awayLift_mk_mul {d : ℕ} {f : A} (g : A →+* R) (hg : IsUnit (g f)) (hf : f ∈ 𝒜 d)
    (m : ℕ) (a : A) (ha : a ∈ 𝒜 (m • d)) :
    awayLift 𝒜 f g hg (Away.mk 𝒜 hf m a ha) * g f ^ m = g a := by
  change (IsLocalization.Away.lift (S := Localization.Away f) f hg)
    (Away.mk 𝒜 hf m a ha).val * g f ^ m = g a
  have h1 := IsLocalization.Away.lift_eq (S := Localization.Away f) f hg
  rw [Away.val_mk, Localization.mk_eq_mk', ← map_pow, ← h1 (f ^ m), ← map_mul]
  exact (congrArg _ (IsLocalization.mk'_spec (Localization.Away f) a
    ⟨f ^ m, (Submonoid.mem_powers_iff _ _).mpr ⟨m, rfl⟩⟩)).trans (h1 a)

end AwayLift

section Pushout

variable {A A' C C' P P' B B' : Type*} [CommRing A] [CommRing A'] [CommRing C] [CommRing C']
  [CommRing P] [CommRing P'] [CommRing B] [CommRing B']
  [Algebra A A'] [Algebra A C] [Algebra A' C'] [Algebra C C'] [Algebra A C']
  [IsScalarTower A A' C'] [IsScalarTower A C C']
  [Algebra A P] [Algebra A' P'] [Algebra P P'] [Algebra A P']
  [IsScalarTower A A' P'] [IsScalarTower A P P']
  [Algebra A B] [Algebra P B] [Algebra C B] [IsScalarTower A P B] [IsScalarTower A C B]
  [Algebra A' B'] [Algebra P' B'] [Algebra C' B'] [IsScalarTower A' P' B'] [IsScalarTower A' C' B']

/-- Localization commutes with base change: if `A' = A[1/a]`, `C' = C[1/a]` and `P' = P[1/a]`,
`B = P ⊗_A C` and `B' = P' ⊗_{A'} C'` (as pushouts), then `B' = B[1/a]`. -/
theorem isLocalization_of_isPushout (a : A) [IsLocalization.Away a A']
    [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers a)) C']
    [IsLocalization (Algebra.algebraMapSubmonoid P (Submonoid.powers a)) P']
    [Algebra.IsPushout A P C B] [Algebra.IsPushout A' P' C' B'] [Algebra B B']
    (hP : ∀ x : P, algebraMap B B' (algebraMap P B x) = algebraMap P' B' (algebraMap P P' x))
    (hC : ∀ x : C, algebraMap B B' (algebraMap C B x) = algebraMap C' B' (algebraMap C C' x)) :
    IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers a)) B' := by
  let _ : Algebra A B' := ((algebraMap A' B').comp (algebraMap A A')).toAlgebra
  let _ : Algebra P B' := ((algebraMap P' B').comp (algebraMap P P')).toAlgebra
  let _ : Algebra C B' := ((algebraMap C' B').comp (algebraMap C C')).toAlgebra
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap A' B' (algebraMap A A' r) = algebraMap B B' (algebraMap A B r)
    rw [IsScalarTower.algebraMap_apply A P B, hP, ← IsScalarTower.algebraMap_apply A P P',
      IsScalarTower.algebraMap_apply A A' P', ← IsScalarTower.algebraMap_apply A' P' B']
  have : IsScalarTower P P' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower P B B' := IsScalarTower.of_algebraMap_eq fun r ↦ (hP r).symm
  have : IsScalarTower C C' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower C B B' := IsScalarTower.of_algebraMap_eq fun r ↦ (hC r).symm
  have : IsScalarTower A P' B' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap A' B' (algebraMap A A' r) = algebraMap P' B' (algebraMap A P' r)
    rw [IsScalarTower.algebraMap_apply A A' P', ← IsScalarTower.algebraMap_apply A' P' B']
  have : IsScalarTower A C' B' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap A' B' (algebraMap A A' r) = algebraMap C' B' (algebraMap A C' r)
    rw [IsScalarTower.algebraMap_apply A A' C', ← IsScalarTower.algebraMap_apply A' C' B']
  have : IsScalarTower A C B' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap A' B' (algebraMap A A' r) =
      algebraMap C' B' (algebraMap C C' (algebraMap A C r))
    rw [← IsScalarTower.algebraMap_apply A C C', IsScalarTower.algebraMap_apply A A' C',
      ← IsScalarTower.algebraMap_apply A' C' B']
  have h₁ : Algebra.IsPushout A C A' C' :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers a) A' C C'
  have : Algebra.IsPushout A A' C C' := h₁.symm
  have h₂ : Algebra.IsPushout A P' C B' :=
    (Algebra.IsPushout.comp_iff A A' C (S' := C') (T := P') (T' := B')).mpr inferInstance
  have h₃ : Algebra.IsPushout P P' B B' :=
    (Algebra.IsPushout.comp_iff A P C (S' := B) (T := P') (T' := B')).mp h₂
  have h₄ := (Algebra.isLocalization_iff_isPushout
    (Algebra.algebraMapSubmonoid P (Submonoid.powers a)) P' (T := B) (B := B')).mpr h₃.symm
  have heq : Algebra.algebraMapSubmonoid B (Algebra.algebraMapSubmonoid P (Submonoid.powers a)) =
      Algebra.algebraMapSubmonoid B (Submonoid.powers a) := by
    rw [Algebra.algebraMapSubmonoid, Algebra.algebraMapSubmonoid, Algebra.algebraMapSubmonoid,
      Submonoid.map_powers, Submonoid.map_powers, Submonoid.map_powers,
      IsScalarTower.algebraMap_apply A P B]
  rwa [heq] at h₄

end Pushout

section BaseChange

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A A' C C' P P' : Type*} [CommRing A] [CommRing A'] [CommRing C] [CommRing C']
  [CommRing P] [CommRing P']
  [Algebra A A'] [Algebra A C] [Algebra A' C'] [Algebra C C'] [Algebra A C']
  [IsScalarTower A A' C'] [IsScalarTower A C C']
  [Algebra A P] [Algebra A' P'] [Algebra P P'] [Algebra A P']
  [IsScalarTower A A' P'] [IsScalarTower A P P']

variable (A C P) in
/-- The base change map `P ⊗_A C → P' ⊗_{A'} C'`, `p ⊗ c ↦ p ⊗ c`, for `A' = A[1/a]`: it is
`P ⊗_A C → P' ⊗_A C' = P' ⊗_{A'} C'`. -/
noncomputable def baseChangeMap (a : A) [IsLocalization.Away a A'] : P ⊗[A] C →+* P' ⊗[A'] C' :=
  (IsLocalization.algebraTensorEquiv (Submonoid.powers a) A' P' C').symm.toRingHom.comp
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A P P')
      (IsScalarTower.toAlgHom A C C')).toRingHom

lemma baseChangeMap_tmul (a : A) [IsLocalization.Away a A'] (x : P) (y : C) :
    baseChangeMap A C P (A' := A') (C' := C') (P' := P') a (x ⊗ₜ y) =
      algebraMap P P' x ⊗ₜ algebraMap C C' y :=
  rfl

lemma baseChangeMap_algebraMap_left (a : A) [IsLocalization.Away a A'] (x : P) :
    baseChangeMap A C P (A' := A') (C' := C') (P' := P') a (algebraMap P (P ⊗[A] C) x) =
      algebraMap P' (P' ⊗[A'] C') (algebraMap P P' x) := by
  change baseChangeMap A C P (A' := A') (C' := C') (P' := P') a (x ⊗ₜ 1) = algebraMap P P' x ⊗ₜ 1
  rw [baseChangeMap_tmul, map_one]

lemma baseChangeMap_algebraMap_right (a : A) [IsLocalization.Away a A'] (x : C) :
    baseChangeMap A C P (A' := A') (C' := C') (P' := P') a (algebraMap C (P ⊗[A] C) x) =
      algebraMap C' (P' ⊗[A'] C') (algebraMap C C' x) := by
  change baseChangeMap A C P (A' := A') (C' := C') (P' := P') a (1 ⊗ₜ x) = 1 ⊗ₜ algebraMap C C' x
  rw [baseChangeMap_tmul, map_one]

/-- Localization commutes with base change: if `A' = A[1/a]`, `C' = C[1/a]` and `P' = P[1/a]`,
then `P' ⊗_{A'} C'` is the localization of `P ⊗_A C` at `a`. -/
theorem isLocalization_baseChangeMap (a : A) [IsLocalization.Away a A']
    [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers a)) C']
    [IsLocalization (Algebra.algebraMapSubmonoid P (Submonoid.powers a)) P'] :
    letI := (baseChangeMap A C P (A' := A') (C' := C') (P' := P') a).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (P ⊗[A] C) (Submonoid.powers a))
      (P' ⊗[A'] C') := by
  let _ := (baseChangeMap A C P (A' := A') (C' := C') (P' := P') a).toAlgebra
  exact isLocalization_of_isPushout (A := A) (A' := A') (C := C) (C' := C') (P := P) (P' := P')
    (B := P ⊗[A] C) (B' := P' ⊗[A'] C') a (baseChangeMap_algebraMap_left a)
    (baseChangeMap_algebraMap_right a)

variable (A C P) in
/-- If `P` is a localization of `A` at `M`, then `P ⊗_A C` is the localization of `C` at `M`. -/
lemma isLocalization_tensorProduct_right (M : Submonoid A) [IsLocalization M P] :
    IsLocalization (Algebra.algebraMapSubmonoid C M) (P ⊗[A] C) :=
  (Algebra.isLocalization_iff_isPushout M P).mpr inferInstance

end BaseChange

/-- A nontrivial localization of a domain is a domain. -/
lemma isDomain_of_isLocalization {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [Nontrivial S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] : IsDomain S := by
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (M := M) S fun x hx ↦ ?_
  refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ?_
  have := IsLocalization.map_units S ⟨x, hx⟩
  simp only [h0, map_zero, isUnit_zero_iff] at this
  exact zero_ne_one this



variable (k : Type u) [Field k] {σ : Type u} [DecidableEq σ] (n s : σ)

/-- The indices other than `n` and `s`: the coordinates of the direction of the line. -/
abbrev Dir : Type u := {j : σ // j ≠ n ∧ j ≠ s}

/-- The field `F = k(wⱼ : j ≠ n, s)` of the generic line. -/
abbrev LineField : Type u := FractionRing (MvPolynomial (Dir n s) k)

variable {k n s}

/-- The coordinate `wⱼ ∈ F`. -/
noncomputable abbrev w (j : Dir n s) : LineField k n s :=
  algebraMap (MvPolynomial (Dir n s) k) _ (MvPolynomial.X j)

variable (k n s)

/-- The generic line on the chart `D₊(xₙ) = Spec k[xⱼ/xₙ]`: `x_s/xₙ ↦ t`, `xⱼ/xₙ ↦ wⱼ t`. -/
noncomputable def psiN : MvPolynomial {j // j ≠ n} k →+* (LineField k n s)[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap k _)) fun j ↦
    if h : j.1 = s then Polynomial.X else Polynomial.C (w ⟨j.1, j.2, h⟩) * Polynomial.X

/-- The bijection `{j ≠ s} ≃ Option {j ≠ n, s}`, `n ↦ none`. -/
def dirEquiv (hns : n ≠ s) : {j // j ≠ s} ≃ Option (Dir n s) where
  toFun j := if h : j.1 = n then none else some ⟨j.1, h, j.2⟩
  invFun o := o.elim ⟨n, hns⟩ fun j ↦ ⟨j.1, j.2.2⟩
  left_inv j := by
    by_cases h : j.1 = n
    · simp only [h, dite_true, Option.elim_none]
      exact Subtype.ext h.symm
    · simp [h]
  right_inv o := by
    cases o with
    | none => simp
    | some j => simp [j.2.1]

/-- The generic line on the chart `D₊(x_s) = Spec k[xⱼ/x_s]`: `xₙ/x_s ↦ u`, `xⱼ/x_s ↦ wⱼ`. It is
`k[w][u] → F[u]`. -/
noncomputable def psiS (hns : n ≠ s) : MvPolynomial {j // j ≠ s} k →+* (LineField k n s)[X] :=
  (Polynomial.mapRingHom (algebraMap (MvPolynomial (Dir n s) k) (LineField k n s))).comp
    ((MvPolynomial.optionEquivLeft k (Dir n s)).toRingEquiv.toRingHom.comp
      (MvPolynomial.renameEquiv k (dirEquiv n s hns)).toRingEquiv.toRingHom)

variable {k n s}

section Values

variable (hns : n ≠ s)

@[simp] lemma psiN_C (r : k) :
    psiN k n s (MvPolynomial.C r) = Polynomial.C (algebraMap k (LineField k n s) r) := by
  simp [psiN]

include hns in
lemma psiN_X_s : psiN k n s (MvPolynomial.X ⟨s, hns.symm⟩) = Polynomial.X := by
  simp [psiN]

lemma psiN_X_of_ne {j : σ} (hjn : j ≠ n) (hjs : j ≠ s) :
    psiN k n s (MvPolynomial.X ⟨j, hjn⟩) = Polynomial.C (w ⟨j, hjn, hjs⟩) * Polynomial.X := by
  simp [psiN, hjs]

@[simp] lemma psiS_C (r : k) :
    psiS k n s hns (MvPolynomial.C r) = Polynomial.C (algebraMap k (LineField k n s) r) := by
  simp [psiS, MvPolynomial.optionEquivLeft_C, Polynomial.map_C]
  rfl

lemma psiS_X_n : psiS k n s hns (MvPolynomial.X ⟨n, hns⟩) = Polynomial.X := by
  simp [psiS, dirEquiv, MvPolynomial.optionEquivLeft_X_none]

lemma psiS_X_of_ne {j : σ} (hjn : j ≠ n) (hjs : j ≠ s) :
    psiS k n s hns (MvPolynomial.X ⟨j, hjs⟩) = Polynomial.C (w ⟨j, hjn, hjs⟩) := by
  simp [psiS, dirEquiv, hjn, MvPolynomial.optionEquivLeft_X_some]

variable (k n s) in
/-- The generic line on `k[σ]`, dehomogenized at `xₙ`. -/
noncomputable def gN : MvPolynomial σ k →+* (LineField k n s)[X] :=
  (psiN k n s).comp (dehomogenize n)

variable (k n s) in
/-- The generic line on `k[σ]`, dehomogenized at `x_s`. -/
noncomputable def gS : MvPolynomial σ k →+* (LineField k n s)[X] :=
  (psiS k n s hns).comp (dehomogenize s)

lemma gN_X_n : gN k n s (MvPolynomial.X n) = 1 := by
  simp [gN]

include hns in
lemma gN_X_s : gN k n s (MvPolynomial.X s) = Polynomial.X := by
  rw [gN, RingHom.comp_apply, dehomogenize_X_of_ne n hns.symm, psiN_X_s hns]

lemma gS_X_s : gS k n s hns (MvPolynomial.X s) = 1 := by
  simp [gS]

lemma gS_X_n : gS k n s hns (MvPolynomial.X n) = Polynomial.X := by
  rw [gS, RingHom.comp_apply, dehomogenize_X_of_ne s hns, psiS_X_n hns]

end Values

section Charts

variable (hns : n ≠ s)

omit [DecidableEq σ] in
lemma X_mem_grading_one (j : σ) : (MvPolynomial.X j : MvPolynomial σ k) ∈ grading σ k 1 :=
  X_mem_grading j

variable (k n s) in
/-- The generic line on the chart `D₊(xₙ)`: `k[σ]_(xₙ) = k[xⱼ/xₙ] → F[t]`. -/
noncomputable def lineN : Away (grading σ k) (MvPolynomial.X n) →+* (LineField k n s)[X] :=
  (psiN k n s).comp (awayEquiv n rfl).toRingHom

variable (k n s) in
/-- The generic line on the chart `D₊(x_s)`: `k[σ]_(x_s) = k[xⱼ/x_s] → F[u]`. -/
noncomputable def lineS : Away (grading σ k) (MvPolynomial.X s) →+* (LineField k n s)[X] :=
  (psiS k n s hns).comp (awayEquiv s rfl).toRingHom

variable (k n) in
/-- The point `e = (xₙ = 1, xⱼ = 0)` on the chart `D₊(xₙ)`. -/
noncomputable def pointN : Away (grading σ k) (MvPolynomial.X n) →+* k :=
  MvPolynomial.constantCoeff.comp (awayEquiv n rfl).toRingHom

include hns in
lemma gN_mul_isUnit : IsUnit ((toLaurent.comp (gN k n s))
    (MvPolynomial.X n * MvPolynomial.X s : MvPolynomial σ k)) := by
  rw [RingHom.comp_apply, map_mul, gN_X_n, gN_X_s hns, one_mul, toLaurent_X]
  exact isUnit_T 1

variable (k n s) in
/-- The generic line on the chart `D₊(xₙ x_s)`: `k[σ]_(xₙ x_s) → F[t, t⁻¹]`. -/
noncomputable def lineNS : Away (grading σ k) (MvPolynomial.X n * MvPolynomial.X s) →+*
    (LineField k n s)[T;T⁻¹] :=
  awayLift (grading σ k) _ (toLaurent.comp (gN k n s)) (gN_mul_isUnit hns)

lemma lineN_mk (m : ℕ) (a : MvPolynomial σ k) (ha : a ∈ grading σ k (m • 1)) :
    lineN k n s (Away.mk (grading σ k) (X_mem_grading_one n) m a ha) = gN k n s a := by
  change psiN k n s (awayEquiv n rfl (Away.mk _ (mem_grading_one_of_eq n rfl) m a ha)) = _
  rw [awayEquiv_mk]
  rfl

lemma lineS_mk (m : ℕ) (a : MvPolynomial σ k) (ha : a ∈ grading σ k (m • 1)) :
    lineS k n s hns (Away.mk (grading σ k) (X_mem_grading_one s) m a ha) = gS k n s hns a := by
  change psiS k n s hns (awayEquiv s rfl (Away.mk _ (mem_grading_one_of_eq s rfl) m a ha)) = _
  rw [awayEquiv_mk]
  rfl

/-- Over the point `e`, the coordinate `t` of the generic line vanishes. -/
lemma evalZero_comp_lineN :
    (Polynomial.evalRingHom 0).comp (lineN k n s) = (algebraMap k _).comp (pointN k n) := by
  ext y
  obtain ⟨p, rfl⟩ :=
    (awayEquiv n (rfl : (MvPolynomial.X n : MvPolynomial σ k) = _)).symm.surjective y
  change Polynomial.eval 0 (psiN k n s (awayEquiv n rfl ((awayEquiv n rfl).symm p))) =
    algebraMap k _ (MvPolynomial.constantCoeff (awayEquiv n rfl ((awayEquiv n rfl).symm p)))
  rw [RingEquiv.apply_symm_apply]
  change ((Polynomial.evalRingHom 0).comp (psiN k n s)) p =
    ((algebraMap k _).comp MvPolynomial.constantCoeff) p
  congr 1
  refine MvPolynomial.ringHom_ext (fun r ↦ by simp) fun j ↦ ?_
  by_cases h : j.1 = s
  · obtain ⟨j, hj⟩ := j
    subst h
    simp [psiN_X_s hj.symm]
  · obtain ⟨j, hj⟩ := j
    simp [psiN_X_of_ne hj h]

include hns in
lemma lineN_isLocalizationElem :
    lineN k n s (Away.isLocalizationElem (X_mem_grading_one (k := k) n)
      (X_mem_grading_one (k := k) s)) = Polynomial.X := by
  rw [Away.isLocalizationElem, lineN_mk, pow_one, gN_X_s hns]

lemma lineS_isLocalizationElem :
    lineS k n s hns (Away.isLocalizationElem (X_mem_grading_one (k := k) s)
      (X_mem_grading_one (k := k) n)) = Polynomial.X := by
  rw [Away.isLocalizationElem, lineS_mk, pow_one, gS_X_n hns]

include hns in
lemma lineNS_mk_mul {d : ℕ} (hf : MvPolynomial.X n * MvPolynomial.X s ∈ grading σ k d) (m : ℕ)
    (b : MvPolynomial σ k) (hb : b ∈ grading σ k (m • d)) :
    lineNS k n s hns (Away.mk (grading σ k) hf m b hb) * T m = toLaurent (gN k n s b) := by
  have h := awayLift_mk_mul (grading σ k) (toLaurent.comp (gN k n s)) (gN_mul_isUnit hns) hf m b hb
  rw [RingHom.comp_apply, map_mul, gN_X_n, gN_X_s hns, one_mul, toLaurent_X, T_pow,
    mul_one] at h
  exact h

include hns in
lemma lineNS_comp_awayMapN :
    (lineNS k n s hns).comp (awayMap (grading σ k) (X_mem_grading_one (k := k) s)
      (rfl : (MvPolynomial.X n * MvPolynomial.X s : MvPolynomial σ k) = _)) =
      toLaurent.comp (lineN k n s) := by
  refine RingHom.ext fun y ↦ ?_
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective (grading σ k) (X_mem_grading_one (k := k) n) y
  rw [RingHom.comp_apply, awayMap_mk, RingHom.comp_apply, lineN_mk,
    ← (isUnit_T (m : ℤ)).mul_left_inj, lineNS_mk_mul hns, map_mul, map_mul, map_pow, gN_X_s hns,
    map_pow, toLaurent_X, T_pow, mul_one]

/-- The generic line is homogeneous: `t^m · a(u, 1, w) = a(1, t, w t)` for `a` homogeneous of
degree `m`, with `u = t⁻¹`. -/
lemma toLaurent_gN_eq {m : ℕ} {a : MvPolynomial σ k} (ha : a.IsHomogeneous m) :
    toLaurent (gN k n s a) = T m * toLaurentInv _ (gS k n s hns a) := by
  let c : k →+* (LineField k n s)[T;T⁻¹] := LaurentPolynomial.C.comp (algebraMap k _)
  let vS : σ → (LineField k n s)[T;T⁻¹] := fun j ↦ toLaurentInv _ (gS k n s hns (MvPolynomial.X j))
  have e₂ : (toLaurentInv (LineField k n s)).toRingHom.comp (gS k n s hns) =
      MvPolynomial.eval₂Hom c vS := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) fun j ↦ (MvPolynomial.eval₂Hom_X' c vS j).symm
    simp [c, gS, toLaurentInv_apply, Polynomial.toLaurent_C]
  have e₁ : toLaurent.comp (gN k n s) = MvPolynomial.eval₂Hom c (fun j ↦ T 1 * vS j) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) fun j ↦ ?_
    · simp [c, gN, Polynomial.toLaurent_C]
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', vS]
      by_cases hjn : j = n
      · subst hjn
        rw [gN_X_n, gS_X_n hns, map_one, toLaurentInv_apply, Polynomial.toLaurent_X, invert_T,
          ← T_add]
        simp
      · by_cases hjs : j = s
        · subst hjs
          rw [gN_X_s hns, gS_X_s hns, map_one, mul_one, Polynomial.toLaurent_X]
        · rw [gN, gS, RingHom.comp_apply, RingHom.comp_apply, dehomogenize_X_of_ne n hjn,
            dehomogenize_X_of_ne s hjs, psiN_X_of_ne hjn hjs, psiS_X_of_ne hns hjn hjs,
            map_mul, Polynomial.toLaurent_X, Polynomial.toLaurent_C, toLaurentInv_apply,
            Polynomial.toLaurent_C, invert_C, mul_comm]
  have := congrArg (fun φ ↦ φ a) e₁
  simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom] at this
  rw [this, MvPolynomial.IsHomogeneous.eval₂_mul_left ha, T_pow, mul_one]
  have := congrArg (fun φ ↦ φ a) e₂
  simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom] at this
  rw [← this]
  rfl

lemma lineNS_comp_awayMapS :
    (lineNS k n s hns).comp (awayMap (grading σ k) (X_mem_grading_one (k := k) n)
      (mul_comm _ _ : (MvPolynomial.X n * MvPolynomial.X s : MvPolynomial σ k) =
        MvPolynomial.X s * MvPolynomial.X n)) =
      (toLaurentInv (LineField k n s)).toRingHom.comp (lineS k n s hns) := by
  refine RingHom.ext fun y ↦ ?_
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective (grading σ k) (X_mem_grading_one (k := k) s) y
  have hm : a.IsHomogeneous m := by simpa using mem_grading.mp ha
  rw [RingHom.comp_apply, awayMap_mk, RingHom.comp_apply, lineS_mk,
    ← (isUnit_T (m : ℤ)).mul_left_inj, lineNS_mk_mul hns, map_mul, map_pow, gN_X_n, one_pow,
    mul_one, toLaurent_gN_eq hns hm, mul_comm]
  rfl

/-- On the chart `D₊(x_s) = Spec k[w][u]`, the generic line `k[w][u] → F[u]` is a localization. -/
lemma isLocalization_lineS :
    letI := (lineS k n s hns).toAlgebra
    ∃ M : Submonoid (Away (grading σ k) (MvPolynomial.X s)),
      IsLocalization M (LineField k n s)[X] := by
  let e : Polynomial (MvPolynomial (Dir n s) k) ≃+* Away (grading σ k) (MvPolynomial.X s) :=
    ((awayEquiv s rfl).trans ((MvPolynomial.renameEquiv k (dirEquiv n s hns)).toRingEquiv.trans
      (MvPolynomial.optionEquivLeft k (Dir n s)).toRingEquiv)).symm
  let _ : Algebra (Polynomial (MvPolynomial (Dir n s) k)) (LineField k n s)[X] :=
    Polynomial.algebra (MvPolynomial (Dir n s) k) (LineField k n s)
  have h1 : IsLocalization ((nonZeroDivisors (MvPolynomial (Dir n s) k)).map Polynomial.C)
      (LineField k n s)[X] := Polynomial.isLocalization _ _
  have h2 := IsLocalization.isLocalization_of_base_ringEquiv
    ((nonZeroDivisors (MvPolynomial (Dir n s) k)).map Polynomial.C) (LineField k n s)[X] e
  let _ := (lineS k n s hns).toAlgebra
  refine ⟨(((nonZeroDivisors (MvPolynomial (Dir n s) k)).map Polynomial.C).map e), ?_⟩
  convert h2 using 1
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

end Charts

end SGA.SGA1.ExposeXI.GenericLine
