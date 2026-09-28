/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.MvPowerSeries.Equiv
import SGA.SGA1.ExposeII.RegularSequence

/-!
# SGA 1, Exposé II, II.4.14 and II.4.17 (iii): regular systems of generators and completions

Let `A` be a `B`-algebra and `J = (x₁,…,xₙ)` an ideal with `A/J ≅ B`. SGA characterises the regular
systems of generators by the `J`-adic completion: `B[[t₁,…,tₙ]] → Â` is an isomorphism (it is
always surjective). We first prove the statement at every finite level: the maps
`B[t]/(t)^m → A/J^m`, `tᵢ ↦ xᵢ`, are surjective, and they are injective for all `m` iff the `xᵢ`
form a regular system of generators
(`isRegularSystemOfGenerators_iff_forall_injective_truncatedMap`). Passing to the inverse limit,
the `xᵢ` form a regular system of generators iff `B[[t₁,…,tₙ]] → Â` is bijective
(`isRegularSystemOfGenerators_iff_bijective_powerSeriesMap`); for a section of
`Spec A → Spec B` this is II.4.17, (ii) ⇔ (iii)
(`isRegularSystemOfGenerators_iff_bijective_powerSeriesMap_of_section`). SGA's (iii) asks for an
abstract isomorphism of augmented `B`-algebras; we use the canonical map `tᵢ ↦ xᵢ`.
-/

open MvPolynomial

namespace SGA.SGA1.ExposeII

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A] {σ : Type*} (x : σ → A)

/-- `t ↦ x` maps `(t)^m` into `J^m`, `J = (xᵢ)`. -/
lemma map_aeval_pow_idealOfVars_le (m : ℕ) :
    (idealOfVars σ B ^ m).map (aeval x : MvPolynomial σ B →ₐ[B] A) ≤
      Ideal.span (Set.range x) ^ m := by
  rw [Ideal.map_pow]
  refine Ideal.pow_right_mono ?_ m |>.trans le_rfl
  rw [idealOfVars, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact Ideal.subset_span ⟨i, by simp⟩

/-- The map `B[t]/(t)^m → A/J^m` defined by `t ↦ x`. -/
noncomputable def truncatedMap (m : ℕ) :
    MvPolynomial σ B ⧸ idealOfVars σ B ^ m →+* A ⧸ Ideal.span (Set.range x) ^ m :=
  Ideal.quotientMap _ (aeval x : MvPolynomial σ B →ₐ[B] A).toRingHom
    (Ideal.map_le_iff_le_comap.mp (map_aeval_pow_idealOfVars_le x m))

variable {x}

/-- Splitting the coefficients of a polynomial over `A` along `A = B + J`. -/
private lemma exists_split (hB : Function.Surjective (algebraMap B (A ⧸ Ideal.span (Set.range x))))
    (F : MvPolynomial σ A) {d : ℕ} (hF : F.IsHomogeneous d) :
    ∃ (G : MvPolynomial σ B) (H : MvPolynomial σ A), G.IsHomogeneous d ∧ H.IsHomogeneous d ∧
      (∀ ν, H.coeff ν ∈ Ideal.span (Set.range x)) ∧ F = map (algebraMap B A) G + H := by
  classical
  choose c hc using fun a : A ↦ hB (Ideal.Quotient.mk _ a)
  refine ⟨∑ ν ∈ F.support, monomial ν (c (F.coeff ν)),
    F - map (algebraMap B A) (∑ ν ∈ F.support, monomial ν (c (F.coeff ν))), ?_, ?_, ?_, by ring⟩
  · exact IsHomogeneous.sum _ _ _ fun ν hν ↦ isHomogeneous_monomial _ (by
      rw [Finsupp.degree_eq_weight_one]; exact hF (mem_support_iff.mp hν))
  · refine hF.sub (IsHomogeneous.map ?_ _)
    exact IsHomogeneous.sum _ _ _ fun ν hν ↦ isHomogeneous_monomial _ (by
      rw [Finsupp.degree_eq_weight_one]; exact hF (mem_support_iff.mp hν))
  · intro ν
    rw [coeff_sub, coeff_map, coeff_sum]
    simp only [coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply, hc, Ideal.Quotient.algebraMap_eq, sub_self]
    · simp [notMem_support_iff.mp h]

variable (x) in
/-- A homogeneous polynomial of degree `d` with coefficients in `J` takes a value in `J^{d+1}`. -/
private lemma eval_mem_pow_succ {H : MvPolynomial σ A} {d : ℕ} (hH : H.IsHomogeneous d)
    (hHJ : ∀ ν, H.coeff ν ∈ Ideal.span (Set.range x)) :
    eval x H ∈ Ideal.span (Set.range x) ^ (d + 1) := by
  classical
  rw [eval_eq]
  refine Ideal.sum_mem _ fun ν hν ↦ ?_
  have hdeg : ν.degree = d := by
    rw [Finsupp.degree_eq_weight_one]; exact hH (mem_support_iff.mp hν)
  have hmon : ∏ i ∈ ν.support, x i ^ ν i ∈ Ideal.span (Set.range x) ^ d := by
    refine (mem_span_pow_iff_exists x d _).mpr ⟨monomial ν 1, ?_, ?_⟩
    · rw [mem_pow_idealOfVars_iff]
      intro μ hμ
      rw [Finset.mem_singleton.mp (support_monomial_subset hμ), hdeg]
    · simp [eval_monomial, Finsupp.prod]
  rw [pow_succ']
  exact Ideal.mul_mem_mul (hHJ ν) hmon

/-- II.4.14: the map `B[t]/(t)^m → A/J^m` is always surjective (when `B → A/J` is). -/
theorem truncatedMap_surjective
    (hB : Function.Surjective (algebraMap B (A ⧸ Ideal.span (Set.range x)))) (m : ℕ) :
    Function.Surjective (truncatedMap (B := B) x m) := by
  have key : ∀ a : A, ∃ F : MvPolynomial σ B,
      a - aeval x F ∈ Ideal.span (Set.range x) ^ m := by
    induction m with
    | zero => exact fun a ↦ ⟨0, by simp⟩
    | succ m ih =>
      intro a
      obtain ⟨F, hF⟩ := ih a
      obtain ⟨W, hW, hWe⟩ := (mem_span_pow_iff_exists_isHomogeneous x m _).mp hF
      obtain ⟨G, H, -, hH, hHJ, rfl⟩ := exists_split hB W hW
      refine ⟨F + G, ?_⟩
      have := eval_mem_pow_succ x hH hHJ
      rw [eval_add, eval_map, ← aeval_def] at hWe
      convert this using 1
      rw [map_add]
      linear_combination (-1 : A) * hWe
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨F, hF⟩ := key a
  refine ⟨Ideal.Quotient.mk _ F, ?_⟩
  change Ideal.Quotient.mk _ (aeval x F) = _
  rw [Ideal.Quotient.eq]
  rw [← neg_mem_iff, neg_sub]
  exact hF

/-- II.4.14, the characterisation by the `J`-adic filtration: let `A` be a `B`-algebra and
`J = (x₁,…,xₙ)` an ideal with `A/J ≅ B` (as `B`-algebras). Then the `xᵢ` form a regular system of
generators of `J` iff the maps `B[t₁,…,tₙ]/(t)^m → A/J^m` defined by `tᵢ ↦ xᵢ` are injective (hence
bijective) for all `m`. Passing to the inverse limit this is SGA's statement that
`B[[t₁,…,tₙ]] → Â` is an isomorphism; that completed form is
`isRegularSystemOfGenerators_iff_bijective_powerSeriesMap`. -/
theorem isRegularSystemOfGenerators_iff_forall_injective_truncatedMap
    (hB : Function.Bijective (algebraMap B (A ⧸ Ideal.span (Set.range x)))) :
    IsRegularSystemOfGenerators x ↔ ∀ m, Function.Injective (truncatedMap (B := B) x m) := by
  classical
  constructor
  · intro hx m
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk _ (aeval x F) = 0 at hz
    rw [Ideal.Quotient.eq_zero_iff_mem] at hz
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_pow_idealOfVars_iff']
    suffices H : ∀ d, d < m → ∀ ν : σ →₀ ℕ, ν.degree = d → F.coeff ν = 0 from
      fun ν hν ↦ H _ hν ν rfl
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
    intro hdm ν hν
    have hFd : F - homogeneousComponent d F ∈ idealOfVars σ B ^ (d + 1) := by
      rw [mem_pow_idealOfVars_iff']
      intro μ hμ
      rw [coeff_sub, coeff_homogeneousComponent]
      by_cases hμd : μ.degree = d
      · simp [hμd]
      · simp only [hμd, ↓reduceIte, sub_zero]
        exact IH _ (by omega) (by omega) μ rfl
    have h1 := map_aeval_pow_idealOfVars_le (B := B) x (d + 1) (Ideal.mem_map_of_mem _ hFd)
    have h2 : aeval x F ∈ Ideal.span (Set.range x) ^ (d + 1) :=
      Ideal.pow_le_pow_right (by omega) hz
    have h3 : eval x (map (algebraMap B A) (homogeneousComponent d F)) ∈
        Ideal.span (Set.range x) ^ (d + 1) := by
      rw [eval_map, ← aeval_def]
      have := sub_mem h2 h1
      rwa [map_sub, sub_sub_cancel] at this
    have h4 := hx d _ ((homogeneousComponent_isHomogeneous d F).map _) h3 ν
    rw [coeff_map, coeff_homogeneousComponent] at h4
    simp only [hν, ↓reduceIte] at h4
    rw [← Ideal.Quotient.eq_zero_iff_mem,
      ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply] at h4
    exact hB.1 (h4.trans (map_zero _).symm)
  · intro h d F hF hmem μ
    obtain ⟨G, H, hG, hH, hHJ, rfl⟩ := exists_split hB.2 F hF
    have hHmem := eval_mem_pow_succ x hH hHJ
    rw [eval_add, eval_map, ← aeval_def] at hmem
    have hG1 : aeval x G ∈ Ideal.span (Set.range x) ^ (d + 1) := by
      have := sub_mem hmem hHmem
      rwa [add_sub_cancel_right] at this
    have hG0 : G = 0 := by
      have := h (d + 1) (a₁ := Ideal.Quotient.mk _ G) (a₂ := 0) (by
        change Ideal.Quotient.mk _ (aeval x G) = Ideal.Quotient.mk _ (aeval x 0)
        rw [map_zero, map_zero, Ideal.Quotient.eq_zero_iff_mem]
        exact hG1)
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_pow_idealOfVars_iff'] at this
      ext ν
      by_cases hν : ν.degree = d
      · exact this ν (by omega)
      · exact hG.coeff_eq_zero hν
    rw [hG0, map_zero, zero_add]
    exact hHJ μ

/-- If `J = ker σA` for a retraction `σA : A → B`, then `B → A/J` is bijective. -/
lemma bijective_algebraMap_quotient_of_section (σA : A →ₐ[B] B)
    (hx : Ideal.span (Set.range x) = RingHom.ker σA) :
    Function.Bijective (algebraMap B (A ⧸ Ideal.span (Set.range x))) := by
  have hsurj : Function.Surjective σA := fun b ↦ ⟨algebraMap B A b, σA.commutes b⟩
  let e : (A ⧸ Ideal.span (Set.range x)) ≃ₐ[B] B :=
    (Ideal.quotientEquivAlgOfEq B hx).trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  have : algebraMap B (A ⧸ Ideal.span (Set.range x)) = e.symm.toRingEquiv.toRingHom := by
    ext b
    exact (e.symm.commutes b).symm
  rw [this]
  exact e.symm.bijective

/-- II.4.17, (ii) ⇔ (iii), levelwise form: let `σ : A → B` be a `B`-algebra retraction (a section
of `Spec A → Spec B`) whose ideal `J = ker σ` is generated by `x₁,…,xₙ`. Then the `xᵢ` form a
regular system of generators of `J` iff `B[t₁,…,tₙ]/(t)^m ≅ A/J^m` via `tᵢ ↦ xᵢ` for all `m`, i.e.
(passing to the limit) the `J`-adic completion of `A` is `B[[t₁,…,tₙ]]`. -/
theorem isRegularSystemOfGenerators_iff_forall_bijective_of_section (σA : A →ₐ[B] B)
    (hx : Ideal.span (Set.range x) = RingHom.ker σA) :
    IsRegularSystemOfGenerators x ↔ ∀ m, Function.Bijective (truncatedMap (B := B) x m) := by
  have hB := bijective_algebraMap_quotient_of_section σA hx
  rw [isRegularSystemOfGenerators_iff_forall_injective_truncatedMap hB]
  exact forall_congr' fun m ↦ ⟨fun h ↦ ⟨h, truncatedMap_surjective hB.2 m⟩, And.left⟩

section

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The projections `R̂ → R/Iⁿ` are compatible with the transition maps. -/
lemma factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (z : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n z) = AdicCompletion.evalₐ I m z := by
  obtain ⟨z, rfl⟩ := AdicCompletion.mk_surjective I R z
  simp only [AdicCompletion.evalₐ_mk]
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  have := AdicCompletion.AdicCauchySequence.mk_eq_mk hle z
  rw [Submodule.Quotient.eq] at this
  simpa using this

end

variable (x)

lemma factorPow_comp_truncatedMap {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span (Set.range x)) hle).comp (truncatedMap (B := B) x n) =
      (truncatedMap x m).comp (Ideal.Quotient.factorPow (idealOfVars σ B) hle) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p ↦ ?_)
  rfl

/-- The map `B[t]^ → Â` induced by `tᵢ ↦ xᵢ` on the completions for the `(t)`-adic and the
`J`-adic topologies, `J = (xᵢ)`. -/
lemma truncatedMap_comp_evalₐ_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span (Set.range x)) hle).comp
        ((truncatedMap (B := B) x n).comp (AdicCompletion.evalₐ (idealOfVars σ B) n).toRingHom) =
      (truncatedMap x m).comp (AdicCompletion.evalₐ (idealOfVars σ B) m).toRingHom := by
  rw [← RingHom.comp_assoc, factorPow_comp_truncatedMap, RingHom.comp_assoc]
  congr 1
  ext z
  exact factorPow_evalₐ _ hle z

/-- The map `B[t]^ → Â` induced by `tᵢ ↦ xᵢ` on the completions for the `(t)`-adic and the
`J`-adic topologies, `J = (xᵢ)`. -/
noncomputable def completedMap :
    AdicCompletion (idealOfVars σ B) (MvPolynomial σ B) →+*
      AdicCompletion (Ideal.span (Set.range x)) A :=
  AdicCompletion.liftRingHom (Ideal.span (Set.range x))
    (fun n ↦ (truncatedMap x n).comp (AdicCompletion.evalₐ (idealOfVars σ B) n).toRingHom)
    (truncatedMap_comp_evalₐ_compat x)

@[simp]
lemma evalₐ_completedMap (n : ℕ) (z : AdicCompletion (idealOfVars σ B) (MvPolynomial σ B)) :
    AdicCompletion.evalₐ _ n (completedMap x z) =
      truncatedMap x n (AdicCompletion.evalₐ _ n z) :=
  AdicCompletion.evalₐ_liftRingHom _ _ (truncatedMap_comp_evalₐ_compat x) n z

lemma completedMap_algebraMap (p : MvPolynomial σ B) :
    completedMap x (algebraMap _ (AdicCompletion (idealOfVars σ B) (MvPolynomial σ B)) p) =
      algebraMap A (AdicCompletion (Ideal.span (Set.range x)) A) (aeval x p) :=
  AdicCompletion.ext_evalₐ fun n ↦ by
    rw [evalₐ_completedMap, AlgHom.commutes, AlgHom.commutes]
    rfl

variable {x}

/-- If all the truncated maps `B[t]/(t)^n → A/Jⁿ` are bijective, so is the map of completions. -/
theorem bijective_completedMap_of_forall_bijective
    (h : ∀ n, Function.Bijective (truncatedMap (B := B) x n)) :
    Function.Bijective (completedMap (B := B) x) := by
  refine ⟨fun z₁ z₂ hz ↦ AdicCompletion.ext_evalₐ fun n ↦ (h n).1 ?_, fun w ↦ ?_⟩
  · rw [← evalₐ_completedMap, ← evalₐ_completedMap, hz]
  · let e (n : ℕ) := RingEquiv.ofBijective _ (h n)
    let ψ := AdicCompletion.liftRingHom (idealOfVars σ B)
      (fun n ↦ (e n).symm.toRingHom.comp
        (AdicCompletion.evalₐ (Ideal.span (Set.range x)) n).toRingHom)
      (fun {m n} hle ↦ RingHom.ext fun w ↦ (h m).1 (by
        simp only [RingHom.comp_apply]
        rw [← RingHom.comp_apply (truncatedMap x m), ← factorPow_comp_truncatedMap x hle,
          RingHom.comp_apply]
        change Ideal.Quotient.factorPow _ hle (e n ((e n).symm _)) = e m ((e m).symm _)
        rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
        exact factorPow_evalₐ _ hle w))
    refine ⟨ψ w, AdicCompletion.ext_evalₐ fun n ↦ ?_⟩
    rw [evalₐ_completedMap, AdicCompletion.evalₐ_liftRingHom]
    exact (e n).apply_symm_apply _

/-- If the map of completions is bijective, the truncated maps are injective. -/
theorem injective_truncatedMap_of_bijective_completedMap
    (h : Function.Bijective (completedMap (B := B) x)) (n : ℕ) :
    Function.Injective (truncatedMap (B := B) x n) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hp : aeval x p ∈ Ideal.span (Set.range x) ^ n := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hz
  obtain ⟨W, hW, hWp⟩ := (mem_span_pow_iff_exists_isHomogeneous x n _).mp hp
  choose c hc using fun a : A ↦
    h.2 (algebraMap A (AdicCompletion (Ideal.span (Set.range x)) A) a)
  have hw : completedMap x (∑ α ∈ W.support, c (W.coeff α) *
      algebraMap (MvPolynomial σ B) (AdicCompletion (idealOfVars σ B) (MvPolynomial σ B))
        (monomial α (1 : B))) =
      completedMap x (algebraMap (MvPolynomial σ B)
        (AdicCompletion (idealOfVars σ B) (MvPolynomial σ B)) p) := by
    rw [completedMap_algebraMap, ← hWp, map_sum]
    conv_rhs => rw [W.as_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [map_mul, hc, completedMap_algebraMap, ← map_mul, aeval_monomial, eval_monomial]
    simp
  have := congrArg (AdicCompletion.evalₐ _ n) (h.1 hw)
  rw [AlgHom.commutes] at this
  change algebraMap _ (MvPolynomial σ B ⧸ idealOfVars σ B ^ n) p = 0
  rw [← this, map_sum]
  refine Finset.sum_eq_zero fun α hα ↦ ?_
  have hmem : monomial α (1 : B) ∈ idealOfVars σ B ^ n := by
    rw [pow_idealOfVars_eq_span]
    refine Ideal.subset_span ⟨α, ?_, rfl⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff, Finsupp.degree_eq_weight_one]
    exact hW (mem_support_iff.mp hα)
  rw [map_mul, AlgHom.commutes]
  change _ * Ideal.Quotient.mk _ _ = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, mul_zero]

/-- II.4.14, completion form: let `J = (x₁,…,xₙ)` with `B → A/J` bijective. The `xᵢ` form a
regular system of generators of `J` iff the map of completions `B[t]^ → Â`, `tᵢ ↦ xᵢ`, is an
isomorphism. -/
theorem isRegularSystemOfGenerators_iff_bijective_completedMap
    (hB : Function.Bijective (algebraMap B (A ⧸ Ideal.span (Set.range x)))) :
    IsRegularSystemOfGenerators x ↔ Function.Bijective (completedMap (B := B) x) := by
  rw [isRegularSystemOfGenerators_iff_forall_injective_truncatedMap hB]
  exact ⟨fun h ↦ bijective_completedMap_of_forall_bijective fun n ↦
      ⟨h n, truncatedMap_surjective hB.2 n⟩,
    injective_truncatedMap_of_bijective_completedMap⟩

variable (x) in
/-- The map `B[[t₁,…,tₙ]] → Â`, `tᵢ ↦ xᵢ`, to the `J`-adic completion of `A`, `J = (xᵢ)`. -/
noncomputable def powerSeriesMap [Finite σ] :
    MvPowerSeries σ B →+* AdicCompletion (Ideal.span (Set.range x)) A :=
  (completedMap x).comp (MvPowerSeries.toAdicCompletionAlgEquiv σ B).toRingEquiv.toRingHom

/-- II.4.14, completion form: let `J = (x₁,…,xₙ)` with `B → A/J` bijective. The `xᵢ` form a
regular system of generators of `J` iff `B[[t₁,…,tₙ]] → Â`, `tᵢ ↦ xᵢ`, is an isomorphism onto the
`J`-adic completion of `A`. -/
theorem isRegularSystemOfGenerators_iff_bijective_powerSeriesMap [Finite σ]
    (hB : Function.Bijective (algebraMap B (A ⧸ Ideal.span (Set.range x)))) :
    IsRegularSystemOfGenerators x ↔ Function.Bijective (powerSeriesMap (B := B) x) := by
  rw [isRegularSystemOfGenerators_iff_bijective_completedMap hB, powerSeriesMap,
    RingHom.coe_comp]
  exact (Function.Bijective.of_comp_iff _
    (MvPowerSeries.toAdicCompletionAlgEquiv σ B).bijective).symm

/-- II.4.17, (ii) ⇔ (iii), for a section `σA : A → B` of `B → A` with ideal `J = ker σA`
generated by `x₁,…,xₙ`: the `xᵢ` form a regular system of generators of `J` iff the `J`-adic
completion of `A` is `B[[t₁,…,tₙ]]`, through `tᵢ ↦ xᵢ`. -/
theorem isRegularSystemOfGenerators_iff_bijective_powerSeriesMap_of_section [Finite σ]
    (σA : A →ₐ[B] B) (hx : Ideal.span (Set.range x) = RingHom.ker σA) :
    IsRegularSystemOfGenerators x ↔ Function.Bijective (powerSeriesMap (B := B) x) :=
  isRegularSystemOfGenerators_iff_bijective_powerSeriesMap
    (bijective_algebraMap_quotient_of_section σA hx)

end SGA.SGA1.ExposeII
