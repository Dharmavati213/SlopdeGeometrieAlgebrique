/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.TensorProduct.Decomposition
import Mathlib.RingTheory.GradedAlgebra.TensorProduct

/-!
# Base change of `Proj`

For a graded `R`-algebra `A = ⨁ 𝒜 i` and an arbitrary `R`-algebra `R'`, the tensor product
`R' ⊗[R] A` is graded by `(𝒜 i).baseChange R'` (`GradedAlgebra.baseChange`). We prove
(EGA II 2.8.10) that `Proj (R' ⊗[R] A)` is the base change of `Proj A` along `Spec R' ⟶ Spec R`.

The algebraic input is that homogeneous localization commutes with base change:
`R' ⊗[R] A_(s) ≃ (R' ⊗[R] A)_(1 ⊗ s)` for homogeneous `s`
(`AlgebraicGeometry.Proj.awayBaseChangeEquiv`). No flatness is needed, since every graded piece
`𝒜 i` is a direct summand of `A`.

## Main definitions and results

- `HomogeneousLocalization.algebraOfGradedAlgebra`: `A_(x)` is an `R`-algebra.
- `AlgebraicGeometry.Proj.toSpecBase`: the structure morphism `Proj A ⟶ Spec R`.
- `AlgebraicGeometry.Proj.baseChangeGradedHom`: the graded map `A → R' ⊗[R] A`.
- `AlgebraicGeometry.Proj.awayBaseChangeEquiv`: `R' ⊗[R] A_(s) ≃ₐ[R'] (R' ⊗[R] A)_(1 ⊗ s)`.
- `AlgebraicGeometry.Proj.isPullback_map_baseChange`: the cartesian square
  `Proj (R' ⊗[R] A) ⟶ Proj A` over `Spec R' ⟶ Spec R`.
-/

universe u

open CategoryTheory Limits HomogeneousLocalization TensorProduct

namespace HomogeneousLocalization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜] (x : Submonoid A)

/-- For a graded `R`-algebra `A`, the homogeneous localization `A_(x)` is an `R`-algebra, the
scalar action being the one of `HomogeneousLocalization.instSMul`. -/
instance algebraOfGradedAlgebra : Algebra R (HomogeneousLocalization 𝒜 x) where
  algebraMap := (fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0))
  commutes' _ _ := mul_comm _ _
  smul_def' r y := by
    ext
    rw [val_smul, val_mul, Algebra.smul_def]
    rfl

lemma val_algebraMap (r : R) :
    (algebraMap R (HomogeneousLocalization 𝒜 x) r).val = algebraMap R (Localization x) r :=
  rfl

variable {d : ℕ} {s : A} (hs : s ∈ 𝒜 d)

/-- The `R`-linear map `𝒜 (n • d) → A_(s)`, `a ↦ a / s ^ n`. -/
noncomputable def Away.mkLinear (n : ℕ) : 𝒜 (n • d) →ₗ[R] Away 𝒜 s where
  toFun a := Away.mk 𝒜 hs n a a.2
  map_add' a b := by ext; simp [Localization.add_mk_self]
  map_smul' r a := by ext; simp [val_smul, Localization.smul_mk]

@[simp]
lemma Away.mkLinear_apply (n : ℕ) (a : 𝒜 (n • d)) : Away.mkLinear 𝒜 hs n a = Away.mk 𝒜 hs n a a.2 :=
  rfl

/-- Multiplication by `s ^ m`, as an `R`-linear map `𝒜 (n • d) → 𝒜 ((n + m) • d)`. -/
noncomputable def Away.mulPowLinear (n m : ℕ) : 𝒜 (n • d) →ₗ[R] 𝒜 ((n + m) • d) :=
  (LinearMap.mulLeft R (s ^ m)).restrict fun a ha ↦ by
    rw [add_smul, add_comm]
    exact SetLike.mul_mem_graded (SetLike.pow_mem_graded m hs) ha

@[simp]
lemma Away.coe_mulPowLinear_apply (n m : ℕ) (a : 𝒜 (n • d)) :
    (Away.mulPowLinear 𝒜 hs n m a : A) = s ^ m * a :=
  rfl

lemma Away.mkLinear_comp_mulPowLinear (n m : ℕ) :
    Away.mkLinear 𝒜 hs (n + m) ∘ₗ Away.mulPowLinear 𝒜 hs n m = Away.mkLinear 𝒜 hs n := by
  ext a
  simp only [LinearMap.coe_comp, Function.comp_apply, Away.mkLinear_apply, Away.val_mk,
    Away.coe_mulPowLinear_apply]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [pow_add]; ring⟩

lemma Away.exists_mkLinear_eq_of_le {n N : ℕ} (h : n ≤ N) (a : 𝒜 (n • d)) :
    ∃ b : 𝒜 (N • d), Away.mkLinear 𝒜 hs N b = Away.mkLinear 𝒜 hs n a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨Away.mulPowLinear 𝒜 hs n m a, by rw [← Away.mkLinear_comp_mulPowLinear 𝒜 hs n m]; rfl⟩


end HomogeneousLocalization

namespace AlgebraicGeometry.Proj

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (ℰ : ℕ → Submodule R A)
  [GradedAlgebra ℰ]

/-- The structure morphism `Proj A ⟶ Spec R` of the projective spectrum of a graded
`R`-algebra `A`. -/
noncomputable def toSpecBase : Proj ℰ ⟶ Spec (.of R) :=
  toSpecZero ℰ ≫ Spec.map (CommRingCat.ofHom (algebraMap R (ℰ 0)))

@[reassoc]
lemma awayι_toSpecBase {s : A} {d : ℕ} (hs : s ∈ ℰ d) (hd : 0 < d) :
    awayι ℰ s hs hd ≫ toSpecBase ℰ = Spec.map (CommRingCat.ofHom (algebraMap R (Away ℰ s))) := by
  rw [toSpecBase, awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

end

variable {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A] [Algebra R R'] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

variable (R') in
/-- The graded ring homomorphism `A → R' ⊗[R] A`, `a ↦ 1 ⊗ a`. -/
def baseChangeGradedHom : 𝒜 →+*ᵍ fun i ↦ (𝒜 i).baseChange R' where
  toRingHom := Algebra.TensorProduct.includeRight.toRingHom
  map_mem hx := Submodule.tmul_mem_baseChange_of_mem _ hx

omit [GradedAlgebra 𝒜] in
@[simp]
lemma baseChangeGradedHom_apply (a : A) : baseChangeGradedHom R' 𝒜 a = 1 ⊗ₜ a :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma irrelevant_baseChange_le :
    HomogeneousIdeal.irrelevant (fun i ↦ (𝒜 i).baseChange R') ≤
      (HomogeneousIdeal.irrelevant 𝒜).map (baseChangeGradedHom R' 𝒜) := by
  classical
  rw [← toIdeal_le_toIdeal_iff]
  intro x hx
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hx
  rw [← DirectSum.sum_support_decompose (fun i ↦ (𝒜 i).baseChange R') x]
  refine Ideal.sum_mem _ fun i hi ↦ ?_
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact (DFinsupp.mem_support_iff.mp hi) (Subtype.ext hx)
  have hc : (DirectSum.decompose (fun i ↦ (𝒜 i).baseChange R') x i : R' ⊗[R] A) ∈
      Submodule.span R' ((𝒜 i).map (TensorProduct.mk R R' A 1) : Set (R' ⊗[R] A)) := by
    rw [← Submodule.baseChange_eq_span]
    exact SetLike.coe_mem _
  change _ ∈ Ideal.map (baseChangeGradedHom R' 𝒜) (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  generalize (DirectSum.decompose (fun i ↦ (𝒜 i).baseChange R') x i : R' ⊗[R] A) = y at hc ⊢
  induction hc using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    refine Ideal.mem_map_of_mem _ ?_
    rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_ne _ ha hi0]
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul r y _ hy =>
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ hy

set_option hygiene false in
local notation3 "ℬ" => fun (i : ℕ) ↦ Submodule.baseChange R' (𝒜 i)

variable (R') in
/-- The map `A_(s) → (R' ⊗[R] A)_(1 ⊗ s)` induced by `a ↦ 1 ⊗ a`. -/
noncomputable def awayMapBaseChange (s : A) : Away 𝒜 s →+* Away ℬ (1 ⊗ₜ[R] s) :=
  Away.map (baseChangeGradedHom R' 𝒜) s

lemma awayMapBaseChange_mk {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayMapBaseChange R' 𝒜 s (Away.mk 𝒜 hs n a ha) =
      Away.mk ℬ (Submodule.tmul_mem_baseChange_of_mem _ hs) n (1 ⊗ₜ a)
        (Submodule.tmul_mem_baseChange_of_mem _ ha) :=
  Away.map_mk _ _ hs n a ha

variable (R') in
/-- The comparison map `R' ⊗[R] A_(s) → (R' ⊗[R] A)_(1 ⊗ s)`. -/
noncomputable def awayBaseChange (s : A) : R' ⊗[R] Away 𝒜 s →ₐ[R'] Away ℬ (1 ⊗ₜ[R] s) :=
  letI : Algebra R (Away ℬ (1 ⊗ₜ[R] s)) := ((algebraMap R' _).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' (Away ℬ (1 ⊗ₜ[R] s)) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := R') (A := Away ℬ (1 ⊗ₜ[R] s)) fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId R' _)
    { awayMapBaseChange R' 𝒜 s with
      commutes' r := by
        ext
        change (Away.map (baseChangeGradedHom R' 𝒜) s
          (HomogeneousLocalization.mk ⟨0, algebraMap R (𝒜 0) r, 1, one_mem _⟩)).val =
          (HomogeneousLocalization.mk ⟨0, algebraMap R' (ℬ 0) (algebraMap R R' r), 1, one_mem _⟩ :
            Away ℬ (1 ⊗ₜ[R] s)).val
        rw [Away.map, map_mk, val_mk, val_mk]
        simp only [Algebra.algebraMap_eq_smul_one]
        congr 1
        change (1 : R') ⊗ₜ[R] (r • (1 : A)) = (r • (1 : R')) • (1 : R' ⊗[R] A)
        rw [Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one, smul_tmul] }
    fun _ _ ↦ .all _ _


@[simp]
lemma awayBaseChange_tmul (s : A) (r : R') (x : Away 𝒜 s) :
    awayBaseChange R' 𝒜 s (r ⊗ₜ x) = r • awayMapBaseChange R' 𝒜 s x := by
  change algebraMap R' _ r * awayMapBaseChange R' 𝒜 s x = _
  exact (Algebra.smul_def r _).symm

variable {d : ℕ} {s : A} (hs : s ∈ 𝒜 d)

omit [GradedAlgebra 𝒜] in
include hs in
lemma one_tmul_mem_baseChange : (1 : R') ⊗ₜ[R] s ∈ ℬ d :=
  Submodule.tmul_mem_baseChange_of_mem _ hs

lemma awayBaseChange_baseChange_mkLinear (n : ℕ) (w : R' ⊗[R] 𝒜 (n • d)) :
    awayBaseChange R' 𝒜 s ((Away.mkLinear 𝒜 hs n).baseChange R' w) =
      Away.mkLinear ℬ (one_tmul_mem_baseChange 𝒜 hs) n ((𝒜 (n • d)).toBaseChange R' w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r a =>
    rw [LinearMap.baseChange_tmul, awayBaseChange_tmul, Away.mkLinear_apply, awayMapBaseChange_mk]
    ext
    simp only [Away.mkLinear_apply, val_smul, Away.val_mk, Localization.smul_mk,
      Submodule.coe_toBaseChange_tmul, Algebra.TensorProduct.tmul_pow,
      one_pow, smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

include hs in
lemma awayBaseChange_surjective : Function.Surjective (awayBaseChange R' 𝒜 s) := by
  intro y
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (one_tmul_mem_baseChange 𝒜 hs) y
  obtain ⟨w, rfl⟩ := (𝒜 (n • d)).toBaseChange_surjective' R' hb
  exact ⟨_, awayBaseChange_baseChange_mkLinear 𝒜 hs n w⟩

lemma exists_eq_baseChange_mkLinear (z : R' ⊗[R] Away 𝒜 s) :
    ∃ (n : ℕ) (w : R' ⊗[R] 𝒜 (n • d)), (Away.mkLinear 𝒜 hs n).baseChange R' w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, map_zero _⟩
  | tmul r x =>
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
    exact ⟨n, r ⊗ₜ ⟨a, ha⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨n₁, w₁, rfl⟩ := hx
    obtain ⟨n₂, w₂, rfl⟩ := hy
    have key : ∀ n N, n ≤ N → ∀ w : R' ⊗[R] 𝒜 (n • d), ∃ w' : R' ⊗[R] 𝒜 (N • d),
        (Away.mkLinear 𝒜 hs N).baseChange R' w' = (Away.mkLinear 𝒜 hs n).baseChange R' w := by
      intro n N h w
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
      refine ⟨(Away.mulPowLinear 𝒜 hs n m).baseChange R' w, ?_⟩
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, Away.mkLinear_comp_mulPowLinear]
    obtain ⟨w₁', hw₁⟩ := key n₁ (n₁ + n₂) (Nat.le_add_right _ _) w₁
    obtain ⟨w₂', hw₂⟩ := key n₂ (n₁ + n₂) (Nat.le_add_left _ _) w₂
    exact ⟨n₁ + n₂, w₁' + w₂', by rw [map_add, hw₁, hw₂]⟩

lemma pow_mul_toBaseChange (n m : ℕ) (w : R' ⊗[R] 𝒜 (n • d)) :
    ((1 : R') ⊗ₜ[R] s) ^ m * ((𝒜 (n • d)).toBaseChange R' w : R' ⊗[R] A) =
      (𝒜 ((n + m) • d)).toBaseChange R' ((Away.mulPowLinear 𝒜 hs n m).baseChange R' w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    simp [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp only [map_add, Submodule.coe_add, mul_add, hx, hy]

include hs in
lemma awayBaseChange_injective : Function.Injective (awayBaseChange R' 𝒜 s) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, w, rfl⟩ := exists_eq_baseChange_mkLinear 𝒜 hs z
  rw [awayBaseChange_baseChange_mkLinear] at hz
  have h := congrArg HomogeneousLocalization.val hz
  rw [Away.mkLinear_apply, Away.val_mk, val_zero, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_zero_iff] at h
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := h
  rw [pow_mul_toBaseChange 𝒜 hs] at hm
  have h0 : (Away.mulPowLinear 𝒜 hs n m).baseChange R' w = 0 :=
    DirectSum.toBaseChange_injective 𝒜 _ (by rw [map_zero]; exact Subtype.ext hm)
  rw [← Away.mkLinear_comp_mulPowLinear 𝒜 hs n m, LinearMap.baseChange_comp,
    LinearMap.comp_apply, h0, map_zero]

include hs in
lemma awayBaseChange_bijective : Function.Bijective (awayBaseChange R' 𝒜 s) :=
  ⟨awayBaseChange_injective 𝒜 hs, awayBaseChange_surjective 𝒜 hs⟩


variable (R') in
/-- EGA II 2.8.10 (affine case): `(R' ⊗[R] A)_(1 ⊗ s) ≅ R' ⊗[R] A_(s)`. -/
noncomputable def awayBaseChangeEquiv : R' ⊗[R] Away 𝒜 s ≃ₐ[R'] Away ℬ (1 ⊗ₜ[R] s) :=
  AlgEquiv.ofBijective (awayBaseChange R' 𝒜 s) (awayBaseChange_bijective 𝒜 hs)

@[simp]
lemma awayBaseChangeEquiv_apply (z : R' ⊗[R] Away 𝒜 s) :
    awayBaseChangeEquiv R' 𝒜 hs z = awayBaseChange R' 𝒜 s z :=
  rfl

include hs in
/-- The square of rings `R → A_(s)`, `R' → (R' ⊗[R] A)_(1 ⊗ s)` is a pushout. -/
lemma isPushout_away :
    IsPushout (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom (algebraMap R (Away 𝒜 s)))
      (CommRingCat.ofHom (algebraMap R' (Away ℬ (1 ⊗ₜ[R] s))))
      (CommRingCat.ofHom (awayMapBaseChange R' 𝒜 s)) := by
  refine (CommRingCat.isPushout_tensorProduct R R' (Away 𝒜 s)).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (awayBaseChangeEquiv R' 𝒜 hs).toRingEquiv.toCommRingCatIso (by simp) (by simp)
    ?_ ?_
  · ext r
    simp [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.algebraMap_eq_smul_one]
  · ext x
    simp

set_option backward.isDefEq.respectTransparency.types false in
/-- EGA II 2.8.10: for a graded `R`-algebra `A` and any `R`-algebra `R'`,
`Proj (R' ⊗[R] A) = Spec R' ×_{Spec R} Proj A`. -/
theorem isPullback_map_baseChange :
    IsPullback (Proj.map (baseChangeGradedHom R' 𝒜) (irrelevant_baseChange_le 𝒜))
      (toSpecBase ℬ) (toSpecBase 𝒜) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (Proj.affineOpenCover 𝒜).openCover fun i ↦ ?_
  let s : A := i.2
  have hs : s ∈ 𝒜 i.1 := i.2.2
  have hk : 0 < (i.1 : ℕ) := i.1.2
  let f := baseChangeGradedHom R' 𝒜
  have P1 : IsPullback (Spec.map (CommRingCat.ofHom (Away.map f s)))
      (awayι ℬ (f s) (f.2 hs) hk) (awayι 𝒜 s hs hk) (Proj.map f (irrelevant_baseChange_le 𝒜)) :=
    IsOpenImmersion.isPullback _ _ _ _ (awayι_comp_map _ _ _ _ _)
      (by rw [opensRange_awayι, opensRange_awayι]; rfl)
  have Q0 := (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_away 𝒜 (R' := R') hs)).flip
  have Q : IsPullback (Spec.map (CommRingCat.ofHom (Away.map f s)))
      (awayι ℬ (f s) (f.2 hs) hk ≫ toSpecBase ℬ) (awayι 𝒜 s hs hk ≫ toSpecBase 𝒜)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Q0.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp; rfl)
      (by rw [awayι_toSpecBase]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
      (by rw [awayι_toSpecBase]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
      (by simp)
  refine Q.of_iso P1.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by exact (Category.comp_id _).trans (Category.id_comp _).symm) (by simp)
  · exact (Category.comp_id _).trans (IsPullback.isoPullback_hom_snd P1.flip).symm
  · exact (Category.comp_id _).trans
      ((congrArg (· ≫ toSpecBase ℬ) (IsPullback.isoPullback_hom_fst P1.flip)).symm.trans
        (Category.assoc _ _ _))

end AlgebraicGeometry.Proj
