/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.FormallySmooth

/-!
# SGA 1, Exposé III, 1.4 (ii): descent of formal smoothness along a finite free extension

Proposition III.1.4 (ii): if `A'` is finite, free and local over `A` and `A' ⊗[A] B` is formally
smooth over `A'`, then `B` is formally smooth over `A`. We prove it for the lifting property
`AdicFormallySmooth` (III.2.1 (iii)), for any `A`-algebra `A'` with an `A`-linear retraction
`π : A' → A`, `π 1 = 1`, which exists when `A` is local and `A'` finite free and nonzero.

SGA's argument (in the proof of III.2.1, (i) ⇒ (iii)) descends the solvability of a system of
linear equations along `A → A'`. We use instead that `π ⊗ C : A' ⊗ C → C` is `C`-linear, hence
multiplicative on lifts through a square-zero ideal.
-/

universe u

namespace SGA.SGA1.ExposeIII

open TensorProduct

/-- A nonzero finite free algebra `A'` over a local ring `A` has an `A`-linear retraction
`π : A' → A` with `π 1 = 1`: some coordinate of `1` in a basis is a unit, by Nakayama's lemma. -/
theorem exists_retraction_of_free (A : Type*) [CommRing A] [IsLocalRing A] (A' : Type*)
    [CommRing A'] [Algebra A A'] [Module.Free A A'] [Module.Finite A A'] [Nontrivial A'] :
    ∃ π : A' →ₗ[A] A, π 1 = 1 := by
  let b := Module.Free.chooseBasis A A'
  by_cases h : ∃ i, IsUnit (b.coord i 1)
  · obtain ⟨i, hi⟩ := h
    exact ⟨(hi.unit⁻¹ : Aˣ) • b.coord i, by simp [Units.smul_def]⟩
  · push Not at h
    exfalso
    -- otherwise `1 ∈ 𝔪 A'`, so `A' = 𝔪 A'` and `A' = 0` by Nakayama
    have h1 : (1 : A') ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A A') := by
      rw [← b.sum_repr 1]
      exact Submodule.sum_mem _ fun i _ ↦
        Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).2 (h i)) trivial
    have htop : (⊤ : Submodule A A') ≤ IsLocalRing.maximalIdeal A • ⊤ := by
      intro x _
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] at h1 ⊢
      simpa using Ideal.mul_mem_left _ x h1
    have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal A) ⊤
      Module.Finite.fg_top htop (IsLocalRing.maximalIdeal_le_jacobson _)
    exact top_ne_bot this

namespace AdicFormallySmooth

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {I : Ideal B}

section Descent

variable {A' C : Type u} [CommRing A'] [Algebra A A'] [CommRing C] [Algebra A C]
  (π : A' →ₗ[A] A)

/-- The `C`-linear map `A' ⊗[A] C → C` induced by `π : A' → A`. -/
noncomputable def retractionTensor : A' ⊗[A] C →ₗ[A] C :=
  TensorProduct.lid A C ∘ₗ π.rTensor C

lemma retractionTensor_tmul (a : A') (c : C) : retractionTensor π (a ⊗ₜ c) = π a • c := by
  simp [retractionTensor]

lemma retractionTensor_includeRight_mul (c : C) (y : A' ⊗[A] C) :
    retractionTensor π (Algebra.TensorProduct.includeRight c * y) = c * retractionTensor π y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c' =>
    simp only [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, retractionTensor_tmul, mul_smul_comm]
  | add y y' h h' => rw [mul_add, map_add, map_add, h, h', mul_add]

lemma retractionTensor_mem {J : Ideal C} {y : A' ⊗[A] C}
    (hy : y ∈ J.map (Algebra.TensorProduct.includeRight : C →ₐ[A] A' ⊗[A] C)) :
    retractionTensor π y ∈ J := by
  suffices ∀ r, retractionTensor π (r * y) ∈ J by simpa using this 1
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        retractionTensor_tmul]
      rw [Algebra.smul_def]
      exact J.mul_mem_left _ (J.mul_mem_left c hj)
    | add r r' h h' => rw [add_mul, map_add]; exact J.add_mem h h'
  | zero => simp
  | add y y' _ _ h h' => intro r; rw [mul_add, map_add]; exact J.add_mem (h r) (h' r)
  | smul z y _ h => intro r; rw [smul_eq_mul, ← mul_assoc]; exact h _

lemma retractionTensor_includeRight (hπ : π 1 = 1) (c : C) :
    retractionTensor π (Algebra.TensorProduct.includeRight c) = c := by
  rw [Algebra.TensorProduct.includeRight_apply, retractionTensor_tmul, hπ, one_smul]

end Descent

/-- III.1.4 (ii), for the adic lifting property: let `A'` be an `A`-algebra admitting an `A`-linear
retraction `π : A' → A`, `π 1 = 1` (e.g. `A'` finite free over the local ring `A`,
`exists_retraction_of_free`). If `A' ⊗[A] B` is formally smooth over `A'` for the topology
defined by `I`, then `B` is formally smooth over `A` for the `I`-adic topology.

This is the descent step of SGA's proof of III.2.1, (i) ⇒ (iii) ("a system of linear equations
... has a solution if and only if the corresponding system over `A'` has one"). Instead of
solving linear equations we apply `π ⊗ C : A' ⊗ C → C` to a lift over `A'`: it is `C`-linear, so
it is multiplicative on lifts of a map to `C ⧸ J` with `J² = 0`. SGA states III.1.4 (ii) with the
localizations of `A' ⊗ B` at its maximal ideals; here the hypothesis is on `A' ⊗ B` itself. -/
theorem of_baseChange (A' : Type u) [CommRing A'] [Algebra A A'] (π : A' →ₗ[A] A) (hπ : π 1 = 1)
    (h : AdicFormallySmooth A' (I.map (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B))) :
    AdicFormallySmooth A I := by
  refine of_sq_zero fun C _ _ J hJ f ⟨n, hn⟩ ↦ ?_
  -- base change to `A'`
  let ι : C →ₐ[A] A' ⊗[A] C := Algebra.TensorProduct.includeRight
  let J' := J.map ι
  have hJ'2 : J' ^ 2 = ⊥ := by rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  let q : C ⧸ J →ₐ[A] (A' ⊗[A] C) ⧸ J' := Ideal.quotientMapₐ J' ι Ideal.le_comap_map
  let f' : A' ⊗[A] B →ₐ[A'] (A' ⊗[A] C) ⧸ J' :=
    Algebra.TensorProduct.lift (Algebra.ofId A' _) (q.comp f) fun _ _ ↦ Commute.all _ _
  have hf' (x : B) : f' (1 ⊗ₜ x) = q (f x) := by simp [f']
  obtain ⟨g', hg'⟩ := h J' ⟨2, hJ'2⟩ f' ⟨n, by
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change f' (1 ⊗ₜ x) = 0
    rw [hf', RingHom.mem_ker.1 (hn hx), map_zero]⟩
  let g₁ : B →ₐ[A] A' ⊗[A] C := (g'.restrictScalars A).comp Algebra.TensorProduct.includeRight
  -- `g₁ x` is `ι c` modulo `J'`, for any lift `c` of `f x`
  have key (x : B) : ∃ c : C, Ideal.Quotient.mk J c = f x ∧ g₁ x - ι c ∈ J' := by
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (f x)
    refine ⟨c, hc, Ideal.Quotient.eq.1 ?_⟩
    have := congr($hg' (1 ⊗ₜ x))
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hf'] at this
    change Ideal.Quotient.mk J' (g' (1 ⊗ₜ x)) = _
    rw [this, ← hc]
    rfl
  let v₀ := retractionTensor (C := C) π
  have hv₀ (c : C) (y : A' ⊗[A] C) : v₀ (ι c * y) = c * v₀ y :=
    retractionTensor_includeRight_mul π c y
  have hv₀ι (c : C) : v₀ (ι c) = c := retractionTensor_includeRight π hπ c
  have hJJ {a b : C} (ha : a ∈ J) (hb : b ∈ J) : a * b = 0 := by
    have : a * b ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rwa [hJ, Ideal.mem_bot] at this
  have hJJ' {a b : A' ⊗[A] C} (ha : a ∈ J') (hb : b ∈ J') : a * b = 0 := by
    have : a * b ∈ J' ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rwa [hJ'2, Ideal.mem_bot] at this
  let v : B →ₐ[A] C := AlgHom.ofLinearMap (v₀ ∘ₗ g₁.toLinearMap)
    (by simpa [map_one] using hv₀ι 1) fun x y ↦ by
      obtain ⟨c, -, hc⟩ := key x
      obtain ⟨d, -, hd⟩ := key y
      set α := g₁ x - ι c
      set β := g₁ y - ι d
      have hx : g₁ x = ι c + α := by simp [α]
      have hy : g₁ y = ι d + β := by simp [β]
      have hxy : g₁ x * g₁ y = ι (c * d) + ι c * β + ι d * α + α * β := by
        rw [hx, hy, map_mul]; ring
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_mul]
      rw [hxy, hJJ' hc hd, add_zero, map_add, map_add, hv₀, hv₀, hv₀ι, hx, hy, map_add, map_add,
        hv₀ι, hv₀ι]
      have h0 : v₀ α * v₀ β = 0 := hJJ (retractionTensor_mem π hc) (retractionTensor_mem π hd)
      linear_combination -h0
  refine ⟨v, AlgHom.ext fun x ↦ ?_⟩
  obtain ⟨c, hcx, hc⟩ := key x
  have : v x = c + v₀ (g₁ x - ι c) := by
    change v₀ (g₁ x) = _
    rw [map_sub, hv₀ι]
    ring
  rw [AlgHom.comp_apply, this, Ideal.Quotient.mkₐ_eq_mk, map_add,
    Ideal.Quotient.eq_zero_iff_mem.2 (retractionTensor_mem π hc), add_zero, hcx]

/-- III.1.4 (ii), for a finite free local extension (SGA's setting): if `A` is local, `A'` is
finite free over `A` and nonzero, and `A' ⊗[A] B` is formally smooth over `A'`, then `B` is
formally smooth over `A`. -/
theorem of_baseChange_of_free [IsLocalRing A] (A' : Type u) [CommRing A'] [Algebra A A']
    [Module.Free A A'] [Module.Finite A A'] [Nontrivial A']
    (h : AdicFormallySmooth A' (I.map (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B))) :
    AdicFormallySmooth A I :=
  have ⟨π, hπ⟩ := exists_retraction_of_free A A'
  of_baseChange A' π hπ h

end AdicFormallySmooth

end SGA.SGA1.ExposeIII
