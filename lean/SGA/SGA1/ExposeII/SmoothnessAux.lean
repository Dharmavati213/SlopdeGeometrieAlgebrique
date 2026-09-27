/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeII.RegularImmersion
import SGA.SGA1.ExposeIV.LocalCriterion

/-!
# SGA 1, Exposé II: auxiliary lemmas for the converse of II.4.15

General commutative algebra used in `SGA.SGA1.ExposeII.RegularImmersionSmooth`. These lemmas do
not depend on SGA and belong in `SGA.Foundations` (or mathlib):

* `IsRegularSystemOfGenerators.units_mul`: multiplying a regular system of generators by units;
* `grMapInjective_idealOfVars`: if the images in `P` of the variables of `R[t₁,…,tₙ]` form a
  regular system of generators, the canonical map `gr⁰(P) ⊗ gr(R[t]) → gr(P)` for the ideal of
  the variables is an isomorphism (the hypothesis of the local flatness criterion IV.5.6 (iii));
* `flat_of_surjective_algebraMap`: flatness over `R` gives flatness over a quotient of `R`;
* `flat_of_formallySmooth_of_isLocalization`, `flat_of_formallySmooth_of_essFiniteType`: a
  formally smooth quotient of a localization of an algebra of finite type over a noetherian ring
  is flat (smooth implies flat, essentially of finite type version of
  `Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing`);
* `formallySmooth_tensorProduct_of_quotient`,
  `formallySmooth_tensorProduct_of_formallySmooth_quotient`: `K ⊗_A P = K ⊗_{A/I} (P / IP)` is
  formally smooth over `K` when `P / IP` is formally smooth over `A / I` and `IK = 0`.
-/

universe u

open MvPolynomial IsLocalRing Algebra
open scoped TensorProduct

namespace SGA.SGA1.ExposeII

section Units

variable {A : Type*} [CommRing A] {ι : Type*} {x : ι → A}

lemma span_range_units_mul (u : ι → Aˣ) :
    Ideal.span (Set.range fun i ↦ (u i : A) * x i) = Ideal.span (Set.range x) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have : x i = (((u i)⁻¹ : Aˣ) : A) * ((u i : A) * x i) := by simp
    rw [SetLike.mem_coe, this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- Multiplying the members of a regular system of generators by units gives a regular system
of generators. -/
theorem IsRegularSystemOfGenerators.units_mul (hx : IsRegularSystemOfGenerators x)
    (u : ι → Aˣ) : IsRegularSystemOfGenerators (fun i ↦ (u i : A) * x i) := by
  classical
  intro d F hF hmem μ
  rw [span_range_units_mul] at hmem ⊢
  let w : (ι →₀ ℕ) → A := fun ν ↦ ν.prod fun i e ↦ (u i : A) ^ e
  have hw (ν : ι →₀ ℕ) : IsUnit (w ν) :=
    Finset.prod_induction _ IsUnit (fun _ _ ha hb ↦ ha.mul hb) isUnit_one
      fun i _ ↦ (u i).isUnit.pow _
  let F' : MvPolynomial ι A := ∑ ν ∈ F.support, monomial ν (F.coeff ν * w ν)
  have hcoeff (m : ι →₀ ℕ) : F'.coeff m = F.coeff m * w m := by
    simp only [F', coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single m (fun b _ hb ↦ by simp [hb]) fun hm ↦ by
      simp [notMem_support_iff.mp hm]]
    simp
  have hF' : F'.IsHomogeneous d :=
    IsHomogeneous.sum _ _ _ fun ν hν ↦ isHomogeneous_monomial _ (by
      rw [Finsupp.degree_eq_weight_one]; exact hF (mem_support_iff.mp hν))
  have heval : eval x F' = eval (fun i ↦ (u i : A) * x i) F := by
    rw [eval_eq _ F]
    simp only [F', map_sum, eval_monomial]
    refine Finset.sum_congr rfl fun ν _ ↦ ?_
    simp only [w, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, mul_assoc]
  have := hx d F' hF' (heval ▸ hmem) μ
  rw [hcoeff] at this
  exact (Ideal.mul_unit_mem_iff_mem _ (hw μ)).mp this

end Units

section Graded

open SGA.SGA1.ExposeIV

variable {σ R P : Type*} [Finite σ] [CommRing R] [CommRing P] [Algebra (MvPolynomial σ R) P]

/-- If the images `yᵢ` in `P` of the variables of `R[t₁,…,tₙ]` form a regular system of
generators, then the canonical map `gr⁰(P) ⊗ gr(R[t]) → gr(P)` for the ideal of the variables is
an isomorphism in every degree. -/
theorem grMapInjective_idealOfVars
    (h : IsRegularSystemOfGenerators fun i : σ ↦ algebraMap (MvPolynomial σ R) P (X i)) :
    GrMapInjective (idealOfVars σ R) P := by
  classical
  have := Fintype.ofFinite σ
  set A := MvPolynomial σ R
  set I := idealOfVars σ R
  set y : σ → P := fun i ↦ algebraMap A P (X i)
  set J := Ideal.span (Set.range y)
  intro d
  have hmon (ν : σ →₀ ℕ) (hν : ν.degree = d) : (monomial ν 1 : A) ∈ I ^ d := by
    rw [pow_idealOfVars_eq_span]
    exact Ideal.subset_span ⟨ν, hν, rfl⟩
  let e : (σ →₀ ℕ) → GrPiece I d := fun ν ↦
    if hν : ν.degree = d then Submodule.Quotient.mk ⟨monomial ν 1, hmon ν hν⟩ else 0
  let Φ : ((σ →₀ ℕ) →₀ P) →ₗ[A] GrPiece I d ⊗[A] P :=
    Finsupp.lsum A fun ν ↦ TensorProduct.mk A (GrPiece I d) P (e ν)
  have hΦ (c : (σ →₀ ℕ) →₀ P) : Φ c = c.sum fun ν p ↦ e ν ⊗ₜ p := rfl
  -- `Φ` is surjective
  have hsurj : ∀ z, z ∈ LinearMap.range Φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add a b ha hb => exact add_mem ha hb
    | tmul q m =>
      obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      suffices H : ∀ a, a ∈ Submodule.span A ((monomial · 1) '' Finsupp.degree ⁻¹' {d}) →
          ∀ (ha : a ∈ I ^ d) (m : P),
            (Submodule.Quotient.mk (⟨a, ha⟩ : ↥(I ^ d)) : GrPiece I d) ⊗ₜ[A] m ∈
              LinearMap.range Φ from
        H a (by have := ha; rwa [pow_idealOfVars_eq_span] at this) ha m
      intro a ha'
      induction ha' using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨ν, hν, rfl⟩ := hz
        intro ha m
        refine ⟨Finsupp.single ν m, ?_⟩
        rw [hΦ, Finsupp.sum_single_index (by simp)]
        have hν' : ν.degree = d := by simpa using hν
        simp only [e, hν', ↓reduceDIte]
      | zero =>
        intro ha m
        have : (Submodule.Quotient.mk (⟨0, ha⟩ : ↥(I ^ d)) : GrPiece I d) = 0 := by
          rw [Submodule.Quotient.mk_eq_zero]; exact zero_mem _
        rw [this, TensorProduct.zero_tmul]
        exact zero_mem _
      | add a b ha hb iha ihb =>
        intro hab m
        have ha' : a ∈ I ^ d := by rw [pow_idealOfVars_eq_span]; exact ha
        have hb' : b ∈ I ^ d := by rw [pow_idealOfVars_eq_span]; exact hb
        have : (Submodule.Quotient.mk (⟨a + b, hab⟩ : ↥(I ^ d)) : GrPiece I d) =
            Submodule.Quotient.mk ⟨a, ha'⟩ + Submodule.Quotient.mk ⟨b, hb'⟩ := rfl
        rw [this, TensorProduct.add_tmul]
        exact add_mem (iha ha' m) (ihb hb' m)
      | smul b a ha iha =>
        intro hba m
        have ha' : a ∈ I ^ d := by rw [pow_idealOfVars_eq_span]; exact ha
        have : (Submodule.Quotient.mk (⟨b • a, hba⟩ : ↥(I ^ d)) : GrPiece I d) =
            b • Submodule.Quotient.mk ⟨a, ha'⟩ := rfl
        rw [this, ← TensorProduct.smul_tmul']
        exact Submodule.smul_mem _ _ (iha ha' m)
  -- the image of the ideal of the variables is `J`
  have hIJ : I.map (algebraMap A P) = J := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  -- value of a monomial
  have hval (ν : σ →₀ ℕ) : algebraMap A P (monomial ν 1) = ν.prod fun i e ↦ y i ^ e := by
    rw [monomial_eq, map_one, one_mul, Finsupp.prod, Finsupp.prod, map_prod]
    simp [y]
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨c, rfl⟩ := hsurj z
  set s := c.support.filter fun ν ↦ ν.degree = d
  let F : MvPolynomial σ P := ∑ ν ∈ s, monomial ν (c ν)
  have hFc (ν : σ →₀ ℕ) (hν : ν ∈ s) : F.coeff ν = c ν := by
    simp only [F, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single ν (fun b _ hb ↦ by simp [hb]) fun h ↦ (h hν).elim]
    simp
  have hF : F.IsHomogeneous d :=
    IsHomogeneous.sum _ _ _ fun ν hν ↦ isHomogeneous_monomial _ (Finset.mem_filter.mp hν).2
  have hgr : grMap I P d (Φ c) = Submodule.Quotient.mk (eval y F) := by
    rw [hΦ, Finsupp.sum, map_sum]
    simp only [F, map_sum, eval_monomial]
    rw [← Finset.sum_filter_add_sum_filter_not c.support (fun ν ↦ ν.degree = d)]
    rw [Finset.sum_eq_zero (s := c.support.filter fun ν ↦ ¬ ν.degree = d) fun ν hν ↦ by
      simp [e, (Finset.mem_filter.mp hν).2], add_zero]
    change _ = Submodule.mkQ _ _
    rw [map_sum]
    refine Finset.sum_congr rfl fun ν hν ↦ ?_
    simp only [e, (Finset.mem_filter.mp hν).2, ↓reduceDIte]
    rw [grMap_tmul, Submodule.mkQ_apply]
    congr 1
    rw [Algebra.smul_def]
    erw [hval]
    ring
  rw [hgr, Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
    Ideal.map_pow, hIJ] at hz
  have hcJ (ν : σ →₀ ℕ) (hν : ν ∈ s) : c ν ∈ J := hFc ν hν ▸ h d F hF hz ν
  rw [hΦ, Finsupp.sum]
  refine Finset.sum_eq_zero fun ν hν ↦ ?_
  by_cases hd : ν.degree = d
  swap
  · simp [e, hd]
  obtain ⟨f, hf⟩ := Submodule.mem_span_range_iff_exists_fun P |>.mp
    (hcJ ν (Finset.mem_filter.mpr ⟨hν, hd⟩))
  rw [← hf, TensorProduct.tmul_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have : f i • y i = (X i : A) • f i := by
    rw [smul_eq_mul, Algebra.smul_def, mul_comm]
  rw [this, ← TensorProduct.smul_tmul]
  have hzero : (X i : A) • e ν = 0 := by
    simp only [e, hd, ↓reduceDIte]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    change (X i : A) * monomial ν 1 ∈ I ^ (d + 1)
    rw [pow_succ']
    exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (hmon ν hd)
  rw [hzero, TensorProduct.zero_tmul]

end Graded

section Flat

/-- Flatness over `R` gives flatness over a quotient `S` of `R`, for modules over `S`. -/
theorem flat_of_surjective_algebraMap {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (h : Function.Surjective (algebraMap R S)) [Module.Flat R M] : Module.Flat S M := by
  have hsurj := TensorProduct.mk_surjective R M S h
  let g : S ⊗[R] M →ₗ[S] M := LinearMap.liftBaseChange S LinearMap.id
  have hg : Function.Bijective g := by
    refine ⟨fun a b hab ↦ ?_, fun m ↦ ⟨1 ⊗ₜ m, by simp [g]⟩⟩
    obtain ⟨a, rfl⟩ := hsurj a
    obtain ⟨b, rfl⟩ := hsurj b
    simp only [g, TensorProduct.mk_apply, LinearMap.liftBaseChange_tmul, LinearMap.id_apply,
      one_smul] at hab
    rw [hab]
  exact Module.Flat.isBaseChange R S M M (f := LinearMap.id)
    (IsBaseChange.of_equiv (LinearEquiv.ofBijective g hg) fun m ↦ by simp [g])

/-- A formally smooth quotient of a localization of an algebra of finite type over a noetherian
ring is flat (smooth implies flat, for essentially finite type algebras). -/
theorem flat_of_formallySmooth_of_isLocalization {R T L' L : Type*} [CommRing R] [CommRing T]
    [CommRing L'] [CommRing L] [Algebra R T] [Algebra T L'] [Algebra R L'] [IsScalarTower R T L']
    [Algebra R L] [IsNoetherianRing R] [FiniteType R T] (M : Submonoid T) [IsLocalization M L']
    (f : L' →ₐ[R] L) (hf : Function.Surjective f) [FormallySmooth R L] : Module.Flat R L := by
  obtain ⟨n, f₀, hf₀⟩ := FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : FiniteType R T)
  let M' := M.comap f₀
  let P' := Localization M'
  let fP : P' →ₐ[R] L' := IsLocalization.liftAlgHom (M := M')
      (f := (IsScalarTower.toAlgHom R T L').comp f₀) fun x ↦ by
    simpa using IsLocalization.map_units (M := M) L' ⟨f₀ x.1, x.2⟩
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := M') _ x ⟨s, hs⟩, ?_⟩
    simp [fP, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight]
  have : IsNoetherianRing P' := IsLocalization.isNoetherianRing M' P' inferInstance
  have : Module.Flat (MvPolynomial (Fin n) R) P' := IsLocalization.flat P' M'
  have : Module.Flat R P' := .trans R (MvPolynomial (Fin n) R) P'
  exact FormallySmooth.flat_of_algHom_of_isNoetherianRing (f.comp fP) (hf.comp hf₁)

/-- A formally smooth algebra essentially of finite type over a noetherian ring is flat. -/
theorem flat_of_formallySmooth_of_essFiniteType {R L : Type*} [CommRing R] [CommRing L]
    [Algebra R L] [IsNoetherianRing R] [EssFiniteType R L] [FormallySmooth R L] :
    Module.Flat R L :=
  flat_of_formallySmooth_of_isLocalization (T := EssFiniteType.subalgebra R L)
    (EssFiniteType.submonoid R L) (AlgHom.id R L) Function.surjective_id

end Flat

section Fibre

/-- Let `A` be an `R`-algebra and `I` an ideal of `A` with `R → A/I` surjective, `P` an
`A`-algebra with `P / IP` formally smooth over `R`, and `K` an `A`-algebra killed by `I`. Then
`K ⊗_A P = K ⊗_R (P / IP)` is formally smooth over `K`. -/
theorem formallySmooth_tensorProduct_of_quotient {R A P : Type*} [CommRing R] [CommRing A]
    [CommRing P] [Algebra R A] [Algebra A P] [Algebra R P] [IsScalarTower R A P] (I : Ideal A)
    (hI : ∀ b : A, ∃ r : R, b - algebraMap R A r ∈ I) (K : Type*) [CommRing K] [Algebra A K]
    [Algebra R K] [IsScalarTower R A K] (hK : ∀ b ∈ I, algebraMap A K b = 0)
    [FormallySmooth R (P ⧸ I.map (algebraMap A P))] : FormallySmooth K (K ⊗[A] P) := by
  set J := I.map (algebraMap A P)
  choose c hc using hI
  have hκ (b : A) : algebraMap A K b = algebraMap R K (c b) := by
    rw [IsScalarTower.algebraMap_apply R A K, ← sub_eq_zero, ← map_sub]
    exact hK _ (hc b)
  have hPJ (b : A) : Ideal.Quotient.mk J (algebraMap A P b) = algebraMap R (P ⧸ J) (c b) := by
    rw [← Ideal.Quotient.mk_algebraMap, IsScalarTower.algebraMap_apply R A P, Ideal.Quotient.eq,
      ← map_sub]
    exact Ideal.mem_map_of_mem _ (hc b)
  let g : P →ₐ[A] K ⊗[R] (P ⧸ J) :=
    { (Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ R J)).toRingHom with
      commutes' := fun b ↦ by
        change (1 : K) ⊗ₜ[R] Ideal.Quotient.mk J (algebraMap A P b) = _
        rw [hPJ, Algebra.TensorProduct.algebraMap_apply, hκ]
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := R) (A := K) (B := P ⧸ J)
          (c b)).symm }
  have hg (y : P) : g y = 1 ⊗ₜ Ideal.Quotient.mk J y := rfl
  let φ : K ⊗[A] P →ₐ[K] K ⊗[R] (P ⧸ J) :=
    Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft g fun _ _ ↦ .all _ _
  have hφ (k : K) (y : P) : φ (k ⊗ₜ y) = k ⊗ₜ Ideal.Quotient.mk J y := by
    simp [φ, hg]
  have hJker : J ≤ RingHom.ker (Algebra.TensorProduct.includeRight.restrictScalars R :
      P →ₐ[R] K ⊗[A] P) := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change Algebra.TensorProduct.includeRight (algebraMap A P b) = 0
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, hK b hb, TensorProduct.zero_tmul]
  let ψ : K ⊗[R] (P ⧸ J) →ₐ[K] K ⊗[A] P :=
    Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
      (Ideal.Quotient.liftₐ J _ fun y hy ↦ hJker hy) fun _ _ ↦ .all _ _
  have hψ (k : K) (y : P) : ψ (k ⊗ₜ Ideal.Quotient.mk J y) = k ⊗ₜ y := by
    have : (Ideal.Quotient.liftₐ J _ fun y hy ↦ hJker hy) (Ideal.Quotient.mk J y) =
        (1 : K) ⊗ₜ[A] y := rfl
    simp only [ψ, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply, this,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let e : K ⊗[R] (P ⧸ J) ≃ₐ[K] K ⊗[A] P :=
    AlgEquiv.ofAlgHom ψ φ
      (Algebra.TensorProduct.ext' fun k y ↦ by simp [hφ, hψ])
      (Algebra.TensorProduct.ext' fun k y ↦ by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        simp [hφ, hψ])
  exact .of_equiv e

/-- If `P / IP` is formally smooth over `A / I` and `K` is an `A`-algebra killed by `I`, then
`K ⊗_A P = K ⊗_{A/I} (P / IP)` is formally smooth over `K`. -/
theorem formallySmooth_tensorProduct_of_formallySmooth_quotient {A P : Type*} [CommRing A]
    [CommRing P] [Algebra A P] (I : Ideal A)
    [FormallySmooth (A ⧸ I) (P ⧸ I.map (algebraMap A P))] (K : Type*) [CommRing K]
    [Algebra A K] (hK : ∀ b ∈ I, algebraMap A K b = 0) : FormallySmooth K (K ⊗[A] P) := by
  let : Algebra (A ⧸ I) K := (Ideal.Quotient.lift I (algebraMap A K) hK).toAlgebra
  have : IsScalarTower A (A ⧸ I) K := .of_algebraMap_eq fun _ ↦ rfl
  have : FormallySmooth (A ⧸ I) ((A ⧸ I) ⊗[A] P) :=
    .of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor P I)
  exact .of_equiv (Algebra.TensorProduct.cancelBaseChange A (A ⧸ I) K K P)

end Fibre

end SGA.SGA1.ExposeII
