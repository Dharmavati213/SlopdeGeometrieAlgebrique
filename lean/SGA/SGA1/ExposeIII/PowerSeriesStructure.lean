/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.PowerSeries
import SGA.SGA1.ExposeIII.PowerSeriesCompletion
import SGA.SGA1.ExposeIII.Descent

/-!
# SGA 1, Exposé III, 1.5 and 2.2: formally smooth algebras with trivial residue extension

Let `A → B` be a local homomorphism of complete noetherian local rings with trivial residue
extension. Corollary III.2.2, (iv ter) ⇒ (v) ⇒ (i): if `B` has the lifting property, a basis
`x₁, …, xₙ` of the relative cotangent space `𝔫/(𝔫² + 𝔪B)` gives a map
`B → B₁/(𝔫₁² + 𝔪B₁)`, `B₁ = A⟦t₁, …, tₙ⟧`, which lifts to `u : B → B₁` because `B₁` is complete;
by III.2.3 (`bijective_of_cotangent`) `u` is an isomorphism. We obtain, for the lifting property
`AdicFormallySmooth` (III.2.1 (iii)):

* `exists_cotangent_bijective_of_adicFormallySmooth`: III.2.2, (iii) ⇒ (v);
* `adicFormallySmooth_iff_exists_algEquiv`: `B` is formally smooth iff `B ≅ A⟦t₁, …, tₙ⟧`
  (III.1.5, and III.2.1 (iii) ⇔ (i) in this case);
* `formallySmoothLocal_of_adicFormallySmooth`: III.2.1, (iii) ⇒ (i);
* `adicFormallySmooth_of_formallySmoothLocal`: III.2.1, (i) ⇒ (iii), by descent along the finite
  free extension `A'` of Definition III.1.1 (`A' ⊗ B` is local, `isLocalRing_tensorProduct`);
* `formallySmoothLocal_iff_exists_algEquiv`: III.1.5, for Definition III.1.1;
* `exists_cotangent_bijective_of_artinianLiftingProperty`: III.2.2, (iv ter) ⇒ (v), for the
  lifting property with local artinian test rings (`ArtinianLiftingProperty`);
* `formallySmooth_tfae`: the equivalence of (i), (iii), (iv ter), (v) of III.2.1 and III.2.2 and of
  `B ≅ A⟦t₁, …, tₙ⟧`.

SGA reduces III.2.1 to the case of a trivial residue extension, which is the case treated here;
the general case (finite residue extension) is in `LocalComponents.lean` and `LiftingCriteria.lean`.
-/

universe u

open IsLocalRing MvPowerSeries TensorProduct

namespace SGA.SGA1.ExposeIII

section Cotangent

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

/-- A family `x` of elements of `𝔫` spanning `𝔫` modulo `𝔫² + 𝔪B`. -/
def IsCotangentFamily {n : ℕ} (x : Fin n → B) : Prop :=
  (∀ i, x i ∈ maximalIdeal B) ∧ maximalIdeal B ≤ Ideal.span (Set.range x) ⊔
    (maximalIdeal B ^ 2 ⊔ (maximalIdeal A).map (algebraMap A B))

omit [IsLocalHom (algebraMap A B)] in
/-- If some `xᵢ` has a unit coefficient in a relation modulo `𝔫² + 𝔪B`, it can be dropped. -/
lemma isCotangentFamily_succAbove {n : ℕ} {x : Fin (n + 1) → B} (hx : IsCotangentFamily (A := A) x)
    (a : Fin (n + 1) → A) (ha : ∑ i, algebraMap A B (a i) * x i ∈
      maximalIdeal B ^ 2 ⊔ (maximalIdeal A).map (algebraMap A B))
    (i : Fin (n + 1)) (hai : IsUnit (a i)) : IsCotangentFamily (A := A) (x ∘ i.succAbove) := by
  set Q := maximalIdeal B ^ 2 ⊔ (maximalIdeal A).map (algebraMap A B)
  refine ⟨fun k ↦ hx.1 _, ?_⟩
  have hxi : x i ∈ Ideal.span (Set.range (x ∘ i.succAbove)) ⊔ Q := by
    rw [Fin.sum_univ_succAbove _ i] at ha
    obtain ⟨u, hu⟩ := (hai.map (algebraMap A B))
    have hT : ∑ k, algebraMap A B (a (i.succAbove k)) * x (i.succAbove k) ∈
        Ideal.span (Set.range (x ∘ i.succAbove)) :=
      Ideal.sum_mem _ fun k _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
    have : x i = (u⁻¹ : Bˣ) * ((algebraMap A B (a i) * x i +
        ∑ k, algebraMap A B (a (i.succAbove k)) * x (i.succAbove k)) -
          ∑ k, algebraMap A B (a (i.succAbove k)) * x (i.succAbove k)) := by
      rw [add_sub_cancel_right, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ (Submodule.mem_sup_right ha)
      (Submodule.mem_sup_left hT))
  refine hx.2.trans (sup_le (Ideal.span_le.2 ?_) le_sup_right)
  rintro _ ⟨j, rfl⟩
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · exact hxi
  · exact Submodule.mem_sup_left (Ideal.subset_span ⟨k, rfl⟩)

omit [IsLocalHom (algebraMap A B)] in
lemma mem_maximalIdeal_of_minimal {n : ℕ} {x : Fin n → B} (hx : IsCotangentFamily (A := A) x)
    (hmin : ∀ m < n, ∀ y : Fin m → B, ¬ IsCotangentFamily (A := A) y) (a : Fin n → A)
    (ha : ∑ i, algebraMap A B (a i) * x i ∈
      maximalIdeal B ^ 2 ⊔ (maximalIdeal A).map (algebraMap A B)) (i : Fin n) :
    a i ∈ maximalIdeal A := by
  by_contra hai
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  exact hmin m (Nat.lt_succ_self m) _
    (isCotangentFamily_succAbove hx a ha i (notMem_maximalIdeal.1 hai))

omit [IsLocalHom (algebraMap A B)] in
/-- There is a family `x₁, …, xₙ` of elements of `𝔫` spanning `𝔫` modulo `𝔫² + 𝔪B` which is
linearly independent over the residue field: a relation `∑ aᵢ xᵢ ∈ 𝔫² + 𝔪B` with `aᵢ ∈ A` has
all `aᵢ ∈ 𝔪`. (Take a family of minimal length.) -/
lemma exists_isCotangentFamily [IsNoetherianRing B] :
    ∃ (n : ℕ) (x : Fin n → B), IsCotangentFamily (A := A) x ∧
      ∀ a : Fin n → A, ∑ i, algebraMap A B (a i) * x i ∈
        maximalIdeal B ^ 2 ⊔ (maximalIdeal A).map (algebraMap A B) →
          ∀ i, a i ∈ maximalIdeal A := by
  classical
  have hP : ∃ n, ∃ x : Fin n → B, IsCotangentFamily (A := A) x := by
    obtain ⟨n, s, hs⟩ :=
      Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian (maximalIdeal B))
    refine ⟨n, s, fun i ↦ ?_, ?_⟩
    · rw [← hs]; exact Ideal.subset_span ⟨i, rfl⟩
    · rw [← hs]; exact le_sup_left
  obtain ⟨x, hx⟩ := Nat.find_spec hP
  exact ⟨_, x, hx, mem_maximalIdeal_of_minimal hx fun m hm y hy ↦ Nat.find_min hP hm ⟨y, hy⟩⟩

end Cotangent

section Linear

variable {A : Type u} [CommRing A] {n : ℕ}

/-- A power series whose coefficients vanish in total degree `< m` lies in `(X)ᵐ`. -/
lemma mem_pow_span_X_of_coeff_eq_zero {σ : Type*} [Finite σ] {m : ℕ} {G : MvPowerSeries σ A}
    (hG : ∀ e : σ →₀ ℕ, e.degree < m → coeff e G = 0) :
    G ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ A)) ^ m := by
  have h0 : truncTotal m G = 0 := by
    ext e
    rw [coeff_truncTotal_eq_ite, MvPolynomial.coeff_zero]
    split_ifs with h
    · exact hG e h
    · rfl
  simpa [h0] using sub_truncTotal_mem_pow_span_X m G

/-- A multidegree of total degree one is that of a single variable. -/
lemma exists_eq_single_of_degree_eq_one {σ : Type*} {e : σ →₀ ℕ} (he : e.degree = 1) :
    ∃ j, e = Finsupp.single j 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, e j ≠ 0 := by
    by_contra! h
    have : e = 0 := Finsupp.ext h
    rw [this, map_zero] at he
    exact zero_ne_one he
  have hle : Finsupp.single j (e j) ≤ e := by
    intro i
    rw [Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · exact Nat.zero_le _
  obtain ⟨r, hr⟩ := le_iff_exists_add.1 hle
  have hdeg : e.degree = e j + r.degree := by
    conv_lhs => rw [hr]
    rw [map_add, Finsupp.degree_single]
  have hej : e j = 1 := by omega
  have hr0 : r = 0 := (Finsupp.degree_eq_zero_iff r).1 (by omega)
  exact ⟨j, by rw [hr, hr0, add_zero, hej]⟩

/-- The linear part of a power series: `F - (F₀ + ∑ Fᵢ tᵢ) ∈ (t)²`. -/
lemma sub_linearPart_mem_pow_span_X (F : MvPowerSeries (Fin n) A) :
    F - (C (constantCoeff F) + ∑ i, C (coeff (Finsupp.single i 1) F) * X i) ∈
      Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) A)) ^ 2 := by
  classical
  refine mem_pow_span_X_of_coeff_eq_zero fun e he ↦ ?_
  rw [map_sub, map_add, map_sum]
  simp_rw [coeff_C_mul, coeff_X, coeff_C]
  rcases (Nat.lt_succ_iff.1 he).lt_or_eq with h | h
  · rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at h
    subst h
    simp [coeff_zero_eq_constantCoeff_apply, eq_comm (a := (0 : Fin n →₀ ℕ))]
  · obtain ⟨j, rfl⟩ := exists_eq_single_of_degree_eq_one h
    simp [Finsupp.single_left_inj one_ne_zero]

end Linear

section CotangentMap

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B] in
/-- The ideal `𝔫² + 𝔪B` defining the relative cotangent space `𝔫 / (𝔫² + 𝔪B)`. -/
abbrev relCotangentIdeal : Ideal B := maximalIdeal B ^ 2 ⊔ (maximalIdeal A).map (algebraMap A B)

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  {n : ℕ} (x : Fin n → B) (hx : ∀ i, x i ∈ maximalIdeal B)
include hx

lemma aeval_mk_eq_zero_of_mem (p : MvPolynomial (Fin n) A)
    (hp : p ∈ MvPolynomial.idealOfVars (Fin n) A ^ 2) :
    MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk (relCotangentIdeal A B) (x i)) p = 0 := by
  set Q := relCotangentIdeal A B
  have hle : Ideal.span (Set.range fun i ↦ Ideal.Quotient.mk Q (x i)) ≤
      (maximalIdeal B).map (Ideal.Quotient.mk Q) :=
    Ideal.span_le.2 (Set.range_subset_iff.2 fun i ↦ Ideal.mem_map_of_mem _ (hx i))
  have hbot : (MvPolynomial.idealOfVars (Fin n) A ^ 2).map
      (MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk Q (x i))) ≤ ⊥ := by
    rw [Ideal.map_pow, MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
    simp only [Function.comp_def, MvPolynomial.aeval_X]
    refine (Ideal.pow_right_mono hle 2).trans ?_
    rw [← Ideal.map_pow]
    calc ((maximalIdeal B) ^ 2).map (Ideal.Quotient.mk Q) ≤ Q.map (Ideal.Quotient.mk Q) :=
          Ideal.map_mono le_sup_left
      _ = ⊥ := Ideal.map_quotient_self Q
  exact (Ideal.mem_bot).1 (hbot (Ideal.mem_map_of_mem _ hp))

/-- The `A`-algebra map `A⟦t₁, …, tₙ⟧ → B ⧸ (𝔫² + 𝔪B)` sending `tᵢ` to `xᵢ`, for `xᵢ ∈ 𝔫`. -/
noncomputable def cotangentMap : MvPowerSeries (Fin n) A →ₐ[A] B ⧸ relCotangentIdeal A B :=
  (Ideal.Quotient.liftₐ (MvPolynomial.idealOfVars (Fin n) A ^ 2)
    (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk (relCotangentIdeal A B) (x i))
      (aeval_mk_eq_zero_of_mem x hx)).comp ((truncTotalAlgHom (Fin n) A 2).restrictScalars A)

lemma cotangentMap_X (i : Fin n) :
    cotangentMap x hx (X i) = Ideal.Quotient.mk (relCotangentIdeal A B) (x i) := by
  simp only [cotangentMap, AlgHom.comp_apply, AlgHom.coe_restrictScalars', truncTotalAlgHom_X,
    Ideal.Quotient.liftₐ_apply]
  exact MvPolynomial.aeval_X _ i

lemma cotangentMap_C (a : A) :
    cotangentMap x hx (C a) = Ideal.Quotient.mk (relCotangentIdeal A B) (algebraMap A B a) := by
  rw [MvPowerSeries.c_eq_algebraMap, AlgHom.commutes, Ideal.Quotient.mk_algebraMap]

lemma cotangentMap_eq_zero_of_mem {H : MvPowerSeries (Fin n) A}
    (hH : H ∈ Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) A)) ^ 2) :
    cotangentMap x hx H = 0 := by
  rw [← ker_truncTotalAlgHom, RingHom.mem_ker] at hH
  simp only [cotangentMap, AlgHom.comp_apply, AlgHom.coe_restrictScalars']
  rw [show (truncTotalAlgHom (Fin n) A 2) H = 0 from hH, map_zero]

lemma cotangentMap_linear (a₀ : A) (a : Fin n → A) :
    cotangentMap x hx (C a₀ + ∑ i, C (a i) * X i) = Ideal.Quotient.mk (relCotangentIdeal A B)
      (algebraMap A B a₀ + ∑ i, algebraMap A B (a i) * x i) := by
  simp only [map_add, map_sum, map_mul, cotangentMap_C, cotangentMap_X]

lemma cotangentMap_apply (F : MvPowerSeries (Fin n) A) :
    cotangentMap x hx F = Ideal.Quotient.mk (relCotangentIdeal A B)
      (algebraMap A B (constantCoeff F) +
        ∑ i, algebraMap A B (coeff (Finsupp.single i 1) F) * x i) := by
  rw [← cotangentMap_linear x hx, ← sub_eq_zero, ← map_sub]
  exact cotangentMap_eq_zero_of_mem x hx (sub_linearPart_mem_pow_span_X F)

end CotangentMap

section Construction

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

lemma algebraMap_mem_maximalIdeal_iff {a : A} :
    algebraMap A B a ∈ maximalIdeal B ↔ a ∈ maximalIdeal A := by
  simp only [mem_maximalIdeal, mem_nonunits_iff]
  exact ⟨fun h ha ↦ h (ha.map _), fun h ha ↦ h (isUnit_of_map_unit _ _ ha)⟩

omit [IsLocalHom (algebraMap A B)] in
lemma constantCoeff_mem_maximalIdeal_iff {F : MvPowerSeries (Fin n) A} :
    constantCoeff F ∈ maximalIdeal A ↔ F ∈ maximalIdeal (MvPowerSeries (Fin n) A) := by
  simp only [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff]

lemma relCotangentIdeal_le : relCotangentIdeal A B ≤ maximalIdeal B :=
  sup_le (Ideal.pow_le_self two_ne_zero) (Ideal.map_le_iff_le_comap.2 fun _ ha ↦
    algebraMap_mem_maximalIdeal_iff.2 ha)

variable {n : ℕ} {x : Fin n → B} (hx : IsCotangentFamily (A := A) x)
include hx

/-- The linear combination `a₀ + ∑ aᵢ xᵢ` lies in `𝔫` if and only if `a₀ ∈ 𝔪`. -/
lemma linear_mem_maximalIdeal_iff (a₀ : A) (a : Fin n → A) :
    algebraMap A B a₀ + ∑ i, algebraMap A B (a i) * x i ∈ maximalIdeal B ↔
      a₀ ∈ maximalIdeal A := by
  have hsum : ∑ i, algebraMap A B (a i) * x i ∈ maximalIdeal B :=
    Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hx.1 i)
  constructor
  · intro h
    exact (algebraMap_mem_maximalIdeal_iff (B := B)).1 (by simpa using sub_mem h hsum)
  · intro h
    exact add_mem ((algebraMap_mem_maximalIdeal_iff (B := B)).2 h) hsum

omit [IsLocalHom (algebraMap A B)] in
/-- `A⟦t⟧ → B ⧸ (𝔫² + 𝔪B)` is surjective when the residue extension is trivial. -/
lemma cotangentMap_surjective (htriv : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B) :
    Function.Surjective (cotangentMap (A := A) x hx.1) := by
  classical
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a₀, ha₀⟩ := htriv b
  obtain ⟨s, hs, q, hq, hsq⟩ := Submodule.mem_sup.1 (hx.2 ha₀)
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hs
  choose a ha using fun i ↦ htriv (c i)
  refine ⟨C a₀ + ∑ i, C (a i) * X i, ?_⟩
  rw [cotangentMap_linear, Ideal.Quotient.eq]
  have : algebraMap A B a₀ + ∑ i, algebraMap A B (a i) * x i - b =
      -(∑ i, (c i - algebraMap A B (a i)) * x i + q) := by
    have hb : b = algebraMap A B a₀ + (∑ i, c i • x i + q) := by rw [hsq]; ring
    rw [hb]
    simp only [smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [this]
  refine neg_mem (add_mem (Ideal.sum_mem _ fun i _ ↦ ?_) hq)
  exact Submodule.mem_sup_left (by rw [pow_two]; exact Ideal.mul_mem_mul (ha i) (hx.1 i))

/-- The kernel of `A⟦t⟧ → B ⧸ (𝔫² + 𝔪B)` is `𝔫₁² + 𝔪 A⟦t⟧`, when the `xᵢ` are independent
modulo `𝔫² + 𝔪B`. -/
lemma ker_cotangentMap (hind : ∀ a : Fin n → A, ∑ i, algebraMap A B (a i) * x i ∈
      relCotangentIdeal A B → ∀ i, a i ∈ maximalIdeal A) :
    RingHom.ker (cotangentMap (A := A) x hx.1) = relCotangentIdeal A (MvPowerSeries (Fin n) A) := by
  set B₁ := MvPowerSeries (Fin n) A
  set Q := relCotangentIdeal A B
  refine le_antisymm (fun F hF ↦ ?_) (sup_le ?_ ?_)
  · rw [RingHom.mem_ker, cotangentMap_apply, Ideal.Quotient.eq_zero_iff_mem] at hF
    have h₀ : constantCoeff F ∈ maximalIdeal A :=
      (linear_mem_maximalIdeal_iff hx _ _).1 (relCotangentIdeal_le hF)
    have hsum : ∑ i, algebraMap A B (coeff (Finsupp.single i 1) F) * x i ∈ Q := by
      have := sub_mem hF (Submodule.mem_sup_right (Ideal.mem_map_of_mem (algebraMap A B) h₀) :
        algebraMap A B (constantCoeff F) ∈ Q)
      simpa using this
    have hi := hind _ hsum
    have hlin : C (constantCoeff F) + ∑ i, C (coeff (Finsupp.single i 1) F) * X i ∈
        (maximalIdeal A).map (algebraMap A B₁) := by
      refine add_mem ?_ (Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_right _ _ ?_)
      · rw [MvPowerSeries.c_eq_algebraMap]; exact Ideal.mem_map_of_mem _ h₀
      · rw [MvPowerSeries.c_eq_algebraMap]; exact Ideal.mem_map_of_mem _ (hi i)
    have hH := Ideal.pow_right_mono span_X_le_maximalIdeal 2 (sub_linearPart_mem_pow_span_X F)
    rw [show F = (F - (C (constantCoeff F) + ∑ i, C (coeff (Finsupp.single i 1) F) * X i)) +
      (C (constantCoeff F) + ∑ i, C (coeff (Finsupp.single i 1) F) * X i) by ring]
    exact add_mem (Submodule.mem_sup_left hH) (Submodule.mem_sup_right hlin)
  · -- `𝔫₁` maps into `𝔫 ⧸ Q`, whose square vanishes
    have hmap : (maximalIdeal B₁).map (cotangentMap (A := A) x hx.1) ≤
        (maximalIdeal B).map (Ideal.Quotient.mk Q) := by
      rw [Ideal.map_le_iff_le_comap]
      intro F hF
      rw [Ideal.mem_comap, cotangentMap_apply]
      exact Ideal.mem_map_of_mem _ ((linear_mem_maximalIdeal_iff hx _ _).2
        (constantCoeff_mem_maximalIdeal_iff.2 hF))
    rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, eq_bot_iff]
    refine (Ideal.pow_right_mono hmap 2).trans ?_
    rw [← Ideal.map_pow, ← Ideal.map_quotient_self Q]
    exact Ideal.map_mono le_sup_left
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change cotangentMap (A := A) x hx.1 (algebraMap A B₁ a) = 0
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A B (B ⧸ Q), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Submodule.mem_sup_right (Ideal.mem_map_of_mem _ ha)

end Construction

instance isLocalHom_algebraMap_mvPowerSeries {A : Type u} [CommRing A] {σ : Type*} :
    IsLocalHom (algebraMap A (MvPowerSeries σ A)) :=
  ⟨fun a ha ↦ by
    rw [isUnit_iff_constantCoeff, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, constantCoeff_C] at ha
    exact ha⟩

section Main

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

/-- III.2.2, (iv ter) ⇒ (v), the construction: let `A → B` be a local homomorphism of local
rings with trivial residue extension, `A` complete and `B` noetherian. If maps from `B` lift
through the test rings `A⟦t₁, …, tₙ⟧ ⧸ 𝔫₁ᵠ⁺¹` (`LiftsModPow`), there is a local `A`-homomorphism
`u : B → B₁ = A⟦t₁, …, tₙ⟧` inducing a bijection `𝔫/(𝔫² + 𝔪B) → 𝔫₁/(𝔫₁² + 𝔪B₁)` (in the form
used by `bijective_of_cotangent`).

As in SGA, a basis `x₁, …, xₙ` of `𝔫/(𝔫² + 𝔪B)` gives `B → B₁/(𝔫₁² + 𝔪B₁)`, which is lifted
step by step to `B → B₁ ⧸ 𝔫₁ᵠ`, and then to `B → B₁` using the completeness of `B₁` for its
maximal ideal (`isAdicComplete_maximalIdeal`). -/
theorem exists_cotangent_bijective_of_liftsModPow [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal A) A]
    (htriv : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B)
    (h : ∀ n, AdicFormallySmooth.LiftsModPow A (maximalIdeal B)
      (maximalIdeal (MvPowerSeries (Fin n) A))) :
    ∃ (n : ℕ) (u : B →ₐ[A] MvPowerSeries (Fin n) A), IsLocalHom u ∧
      (∀ y ∈ maximalIdeal (MvPowerSeries (Fin n) A), ∃ x ∈ maximalIdeal B,
        u x - y ∈ maximalIdeal (MvPowerSeries (Fin n) A) ^ 2 ⊔
          (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin n) A))) ∧
      (∀ x ∈ maximalIdeal B, u x ∈ maximalIdeal (MvPowerSeries (Fin n) A) ^ 2 ⊔
          (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin n) A)) →
        x ∈ maximalIdeal B ^ 2 ⊔ (maximalIdeal A).map (algebraMap A B)) := by
  obtain ⟨n, x, hx, hind⟩ := exists_isCotangentFamily (A := A) (B := B)
  set B₁ := MvPowerSeries (Fin n) A
  set Q := relCotangentIdeal A B
  set J₁ := relCotangentIdeal A B₁
  set w := cotangentMap (A := A) x hx.1
  have hw := cotangentMap_surjective hx htriv
  have hker : RingHom.ker w = J₁ := ker_cotangentMap hx hind
  let e : (B₁ ⧸ J₁) ≃ₐ[A] B ⧸ Q :=
    (Ideal.quotientEquivAlgOfEq A hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hw)
  have he (F : B₁) : e (Ideal.Quotient.mk J₁ F) = w F := rfl
  let u₀ : B →ₐ[A] B₁ ⧸ J₁ := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ A Q)
  have hu₀e (b : B) : e (u₀ b) = Ideal.Quotient.mk Q b := by simp [u₀]
  have hJ₁ : J₁ ≤ maximalIdeal B₁ := relCotangentIdeal_le
  have : IsAdicComplete (maximalIdeal B₁) B₁ := isAdicComplete_maximalIdeal
  -- `u₀` maps `𝔫` into `𝔫₁`
  have hu₀ (b : B) (hb : b ∈ maximalIdeal B) :
      ∃ F ∈ maximalIdeal B₁, u₀ b = Ideal.Quotient.mk J₁ F := by
    obtain ⟨F, hF⟩ := Ideal.Quotient.mk_surjective (u₀ b)
    refine ⟨F, ?_, hF.symm⟩
    have hwF : w F = Ideal.Quotient.mk Q b := by rw [← he, hF, hu₀e]
    rw [cotangentMap_apply, Ideal.Quotient.eq] at hwF
    rw [← constantCoeff_mem_maximalIdeal_iff, ← linear_mem_maximalIdeal_iff hx]
    simpa using add_mem (relCotangentIdeal_le hwF) hb
  obtain ⟨u, hu⟩ := AdicFormallySmooth.exists_lift_of_liftsModPow (maximalIdeal B₁) (h n) hJ₁
    (fun c hc ↦ by
      have := hc 2
      rwa [sup_eq_left.2 (le_sup_left : maximalIdeal B₁ ^ 2 ≤ J₁)] at this) u₀ (by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      obtain ⟨F, hF, hFb⟩ := hu₀ b hb
      rw [Ideal.mem_comap]
      rw [hFb]
      exact Ideal.mem_map_of_mem _ hF)
  have hu' (b : B) : Ideal.Quotient.mk J₁ (u b) = u₀ b := congr($hu b)
  -- `u` maps `𝔫` into `𝔫₁`
  have hu𝔫 (b : B) (hb : b ∈ maximalIdeal B) : u b ∈ maximalIdeal B₁ := by
    obtain ⟨F, hF, hFb⟩ := hu₀ b hb
    have : u b - F ∈ J₁ := by rw [← Ideal.Quotient.eq, hu', hFb]
    simpa using add_mem (hJ₁ this) hF
  refine ⟨n, u, ⟨fun b hb ↦ ?_⟩, fun y hy ↦ ?_, fun b hb hub ↦ ?_⟩
  · by_contra hb'
    exact ((mem_maximalIdeal _).1 (hu𝔫 b ((mem_maximalIdeal _).2 hb'))) hb
  · refine ⟨algebraMap A B (constantCoeff y) +
      ∑ i, algebraMap A B (coeff (Finsupp.single i 1) y) * x i,
      (linear_mem_maximalIdeal_iff hx _ _).2 (constantCoeff_mem_maximalIdeal_iff.2 hy), ?_⟩
    rw [← Ideal.Quotient.eq, hu']
    apply e.injective
    rw [hu₀e, he, cotangentMap_apply]
  · have h0 : e (u₀ b) = 0 := by
      rw [← hu', Ideal.Quotient.eq_zero_iff_mem.2 hub, map_zero]
    rwa [hu₀e, Ideal.Quotient.eq_zero_iff_mem] at h0

/-- III.2.2, (iii) ⇒ (v): under the hypotheses of `exists_cotangent_bijective_of_liftsModPow`,
if `B` is formally smooth over `A` for its `𝔫`-adic topology (III.2.1 (iii)), there is a local
`A`-homomorphism `u : B → A⟦t₁, …, tₙ⟧` inducing a bijection of relative cotangent spaces. -/
theorem exists_cotangent_bijective_of_adicFormallySmooth [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal A) A]
    (htriv : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B)
    (h : AdicFormallySmooth A (maximalIdeal B)) :
    ∃ (n : ℕ) (u : B →ₐ[A] MvPowerSeries (Fin n) A), IsLocalHom u ∧
      (∀ y ∈ maximalIdeal (MvPowerSeries (Fin n) A), ∃ x ∈ maximalIdeal B,
        u x - y ∈ maximalIdeal (MvPowerSeries (Fin n) A) ^ 2 ⊔
          (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin n) A))) ∧
      (∀ x ∈ maximalIdeal B, u x ∈ maximalIdeal (MvPowerSeries (Fin n) A) ^ 2 ⊔
          (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin n) A)) →
        x ∈ maximalIdeal B ^ 2 ⊔ (maximalIdeal A).map (algebraMap A B)) :=
  exists_cotangent_bijective_of_liftsModPow htriv fun _ ↦ h.liftsModPow _

/-- III.2.2, (iii) ⇒ (v) ⇒ (i), and III.1.5 for the lifting property: let `A → B` be a local
homomorphism of complete noetherian local rings with trivial residue extension. If `B` is formally
smooth over `A` for its `𝔫`-adic topology, then `B` is `A`-isomorphic to a power series ring
`A⟦t₁, …, tₙ⟧`. -/
theorem exists_algEquiv_mvPowerSeries_of_adicFormallySmooth [IsNoetherianRing A]
    [IsNoetherianRing B] [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]
    (htriv : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B)
    (h : AdicFormallySmooth A (maximalIdeal B)) :
    ∃ n, Nonempty (B ≃ₐ[A] MvPowerSeries (Fin n) A) := by
  obtain ⟨n, u, hloc, hsurj, hinj⟩ := exists_cotangent_bijective_of_adicFormallySmooth htriv h
  exact ⟨n, ⟨algEquivOfCotangent u hsurj hinj⟩⟩

omit [IsLocalHom (algebraMap A B)] in
/-- Conversely (III.1.5, sufficiency, for the lifting property): a local `A`-algebra isomorphic to
a power series ring over `A` is formally smooth for its adic topology. -/
theorem adicFormallySmooth_of_algEquiv_mvPowerSeries {n : ℕ}
    (e : B ≃ₐ[A] MvPowerSeries (Fin n) A) : AdicFormallySmooth A (maximalIdeal B) := by
  have h := (adicFormallySmooth_mvPowerSeries (R := A) (σ := Fin n)).mono span_X_le_maximalIdeal
  have hcomap : (maximalIdeal (MvPowerSeries (Fin n) A)).comap e = maximalIdeal B := by
    have : ((maximalIdeal (MvPowerSeries (Fin n) A)).comap e).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ e.surjective
    exact IsLocalRing.eq_maximalIdeal this
  rw [← hcomap]
  exact h.of_algEquiv e

/-- III.2.1, (iii) ⇔ (i) and III.1.5, for a local homomorphism of complete noetherian local
rings with trivial residue extension: `B` is formally smooth over `A` for its `𝔫`-adic topology
if and only if it is isomorphic to a power series ring over `A`. -/
theorem adicFormallySmooth_iff_exists_algEquiv [IsNoetherianRing A]
    [IsNoetherianRing B] [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]
    (htriv : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B) :
    AdicFormallySmooth A (maximalIdeal B) ↔ ∃ n, Nonempty (B ≃ₐ[A] MvPowerSeries (Fin n) A) :=
  ⟨exists_algEquiv_mvPowerSeries_of_adicFormallySmooth htriv,
    fun ⟨_, ⟨e⟩⟩ ↦ adicFormallySmooth_of_algEquiv_mvPowerSeries e⟩

omit [IsLocalHom (algebraMap A B)] in
/-- Definition III.1.1 holds (with `A' = A`) for a local `A`-algebra isomorphic to a power series
ring over `A`. -/
theorem formallySmoothLocal_of_algEquiv {n : ℕ} (e : B ≃ₐ[A] MvPowerSeries (Fin n) A) :
    FormallySmoothLocal A B := by
  open scoped TensorProduct in
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun P _ ↦ ⟨n, ⟨?_⟩⟩⟩
  have : Nontrivial (A ⊗[A] B) := (Algebra.TensorProduct.lid A B).toRingEquiv.nontrivial
  have : IsLocalRing (A ⊗[A] B) :=
    .of_surjective' (Algebra.TensorProduct.lid A B).symm.toRingHom
      (Algebra.TensorProduct.lid A B).symm.surjective
  have hP : P = maximalIdeal _ := IsLocalRing.eq_maximalIdeal ‹_›
  have hunit : P.primeCompl ≤ IsUnit.submonoid (A ⊗[A] B) := by
    intro y hy
    have hy' : y ∉ maximalIdeal _ := hP ▸ hy
    exact (notMem_maximalIdeal.mp hy' : IsUnit y)
  exact ((IsLocalization.atUnits (A ⊗[A] B) P.primeCompl hunit).symm.restrictScalars A).trans
    ((Algebra.TensorProduct.lid A B).trans e)

/-- III.2.1, (iii) ⇒ (i), for a local homomorphism of complete noetherian local rings with trivial
residue extension: if `B` is formally smooth over `A` for its `𝔫`-adic topology, it is formally
smooth in the sense of Definition III.1.1 (with `A' = A`). -/
theorem formallySmoothLocal_of_adicFormallySmooth [IsNoetherianRing A]
    [IsNoetherianRing B] [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]
    (htriv : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B)
    (h : AdicFormallySmooth A (maximalIdeal B)) : FormallySmoothLocal A B :=
  have ⟨_, ⟨e⟩⟩ := exists_algEquiv_mvPowerSeries_of_adicFormallySmooth htriv h
  formallySmoothLocal_of_algEquiv e

end Main

section TensorLocal

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)] (A' : Type u) [CommRing A'] [Algebra A A'] [IsLocalRing A']
  [Module.Finite A A']

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] [IsLocalRing A'] [Module.Finite A A'] in
/-- With trivial residue extension, every element of `A' ⊗[A] B` is congruent to some `a' ⊗ 1`
modulo `𝔫 (A' ⊗ B)`. -/
lemma exists_sub_tmul_one_mem
    (htriv : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B) (r : A' ⊗[A] B) :
    ∃ a' : A', r - a' ⊗ₜ 1 ∈
      (maximalIdeal B).map (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B) := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a' b =>
    obtain ⟨a, ha⟩ := htriv b
    refine ⟨a • a', ?_⟩
    have : a' ⊗ₜ[A] b - (a • a') ⊗ₜ[A] (1 : B) =
        (a' ⊗ₜ[A] (1 : B)) * Algebra.TensorProduct.includeRight (b - algebraMap A B a) := by
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        mul_one, tmul_sub, smul_tmul, Algebra.algebraMap_eq_smul_one]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ha)
  | add r s hr hs =>
    obtain ⟨a', ha'⟩ := hr
    obtain ⟨b', hb'⟩ := hs
    refine ⟨a' + b', ?_⟩
    rw [add_tmul, show r + s - (a' ⊗ₜ 1 + b' ⊗ₜ 1) = (r - a' ⊗ₜ 1) + (s - b' ⊗ₜ 1) by ring]
    exact add_mem ha' hb'

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsLocalRing A'] in
/-- `A' ⊗[A] B` is integral over `B` when `A'` is finite over `A`. -/
lemma isIntegral_includeRight :
    (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom.IsIntegral := by
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := A') (B := B)
  have hint : Algebra.IsIntegral B (A' ⊗[A] B) := by
    refine ⟨fun r ↦ ?_⟩
    induction r using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul a' b =>
      have h1 : IsIntegral B (a' ⊗ₜ[A] (1 : B)) := by
        have : IsIntegral A
            ((Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] B) a') :=
          (Algebra.IsIntegral.isIntegral a').map _
        exact this.tower_top
      have : a' ⊗ₜ[A] b = (a' ⊗ₜ[A] (1 : B)) * algebraMap B (A' ⊗[A] B) b := by
        rw [Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
      rw [this]
      exact h1.mul isIntegral_algebraMap
    | add r s hr hs => exact hr.add hs
  exact hint.1

omit [IsLocalRing A] [IsLocalRing A'] [Module.Finite A A'] [IsLocalHom (algebraMap A B)] in
lemma sup_pow_le {R : Type*} [CommRing R] (K L : Ideal R) (n : ℕ) : (K ⊔ L) ^ n ≤ K ⊔ L ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le (le_sup_of_le_left Ideal.mul_le_left)
      (le_sup_of_le_left Ideal.mul_le_left)) (sup_le (le_sup_of_le_left Ideal.mul_le_right)
      le_sup_right)

variable [Module.Free A A'] (htriv : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B)
include htriv

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] [Module.Free A A'] in
/-- With trivial residue extension, the maximal ideals of `A' ⊗[A] B` all equal
`𝔫 (A' ⊗ B) + 𝔪_{A'} (A' ⊗ B)`. -/
lemma eq_sup_of_isMaximal (M : Ideal (A' ⊗[A] B)) [M.IsMaximal] :
    M = (maximalIdeal B).map (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B) ⊔
      (maximalIdeal A').map (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] B) := by
  set φ : A' →ₐ[A] A' ⊗[A] B := Algebra.TensorProduct.includeLeft
  set K := (maximalIdeal B).map (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B)
  have hK : K ≤ M := by
    rw [Ideal.map_le_iff_le_comap]
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ (isIntegral_includeRight A') M
    exact (IsLocalRing.eq_maximalIdeal this).ge
  have hc : M.comap φ = maximalIdeal A' := by
    let := Ideal.Quotient.field M
    have hsurj : Function.Surjective ((Ideal.Quotient.mk M).comp (φ : A' →+* A' ⊗[A] B)) := by
      intro y
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨a', ha'⟩ := exists_sub_tmul_one_mem A' htriv r
      exact ⟨a', (Ideal.Quotient.eq.2 (hK ha')).symm⟩
    have : (M.comap φ).IsMaximal := by
      have h := RingHom.ker_isMaximal_of_surjective _ hsurj
      have heq : M.comap φ = RingHom.ker ((Ideal.Quotient.mk M).comp (φ : A' →+* A' ⊗[A] B)) :=
        Ideal.ext fun a ↦ by simp [Ideal.Quotient.eq_zero_iff_mem]
      rwa [heq]
    exact IsLocalRing.eq_maximalIdeal this
  refine le_antisymm (fun r hr ↦ ?_) (sup_le hK (Ideal.map_le_iff_le_comap.2 hc.ge))
  obtain ⟨a', ha'⟩ := exists_sub_tmul_one_mem A' htriv r
  have hφ : φ a' ∈ M := by
    have := M.sub_mem hr (hK ha')
    simpa [φ] using this
  have : a' ∈ maximalIdeal A' := hc ▸ hφ
  rw [show r = (r - a' ⊗ₜ 1) + φ a' by simp [φ]]
  exact add_mem (Submodule.mem_sup_left ha') (Submodule.mem_sup_right (Ideal.mem_map_of_mem _ this))

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] in
/-- With trivial residue extension, `A' ⊗[A] B` is a local ring, for `A'` finite, free and
local over `A` (this is used in SGA's proof of III.1.5: "this algebra is local, since the residual
extension of `B` over `A` is trivial"). -/
theorem isLocalRing_tensorProduct : IsLocalRing (A' ⊗[A] B) := by
  have : Nontrivial (A' ⊗[A] B) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right A A').2 inferInstance
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (A' ⊗[A] B)
  exact .of_unique_max_ideal ⟨M, hM, fun M' hM' ↦
    (eq_sup_of_isMaximal A' htriv M').trans (eq_sup_of_isMaximal A' htriv M).symm⟩

/-- A power of the maximal ideal of `A' ⊗[A] B` lies in `𝔫 (A' ⊗ B)`. -/
theorem exists_pow_maximalIdeal_le [IsNoetherianRing A] :
    have := isLocalRing_tensorProduct A' htriv
    ∃ N, maximalIdeal (A' ⊗[A] B) ^ N ≤
      (maximalIdeal B).map (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B) := by
  have := isLocalRing_tensorProduct A' htriv
  set φ : A' →ₐ[A] A' ⊗[A] B := Algebra.TensorProduct.includeLeft
  set K := (maximalIdeal B).map (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B)
  have : IsNoetherianRing A' := IsNoetherianRing.of_finite A A'
  -- `𝔪_{A'}` is the radical of `𝔪 A'`
  have hrad : maximalIdeal A' ≤ ((maximalIdeal A).map (algebraMap A A')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P ⟨hP, hPp⟩ ↦ ?_
    have hPc : P.comap (algebraMap A A') = maximalIdeal A :=
      ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.comap _).ne_top
        (Ideal.map_le_iff_le_comap.1 hP)).symm
    have : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P
      (hPc ▸ IsLocalRing.maximalIdeal.isMaximal A)
    exact (IsLocalRing.eq_maximalIdeal this).ge
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (IsNoetherian.noetherian (maximalIdeal A'))
  refine ⟨N, ?_⟩
  rw [eq_sup_of_isMaximal A' htriv (maximalIdeal _)]
  refine (sup_pow_le _ _ N).trans (sup_le le_rfl ?_)
  rw [← Ideal.map_pow]
  refine (Ideal.map_mono hN).trans ?_
  rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap]
  have : φ (algebraMap A A' a) = Algebra.TensorProduct.includeRight (algebraMap A B a) := by
    simp [φ, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact Ideal.mem_map_of_mem _ ((algebraMap_mem_maximalIdeal_iff (B := B)).2 ha)

end TensorLocal

section FormallySmooth

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)] [IsNoetherianRing A]
  (htriv : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B)
include htriv

/-- III.2.1, (i) ⇒ (iii), with trivial residue extension: if `B` is formally smooth over `A` in
the sense of Definition III.1.1, it is formally smooth for its `𝔫`-adic topology. As in SGA, the
lifting property holds after the finite free extension `A'` (for power series rings) and descends
to `B` (`AdicFormallySmooth.of_baseChange_of_free`). SGA reduces III.2.1 to the case of a trivial
residue extension, which is the one treated here. -/
theorem adicFormallySmooth_of_formallySmoothLocal (h : FormallySmoothLocal A B) :
    AdicFormallySmooth A (maximalIdeal B) := by
  obtain ⟨A', _, _, _, _, _, hA'⟩ := h
  have := isLocalRing_tensorProduct A' htriv
  obtain ⟨n, ⟨e⟩⟩ := hA' (maximalIdeal (A' ⊗[A] B))
  have hunit : (maximalIdeal (A' ⊗[A] B)).primeCompl ≤ IsUnit.submonoid (A' ⊗[A] B) :=
    fun y hy ↦ (notMem_maximalIdeal.mp hy : IsUnit y)
  let e' : A' ⊗[A] B ≃ₐ[A'] MvPowerSeries (Fin n) A' :=
    ((IsLocalization.atUnits (A' ⊗[A] B) _ hunit).restrictScalars A').trans e
  obtain ⟨N, hN⟩ := exists_pow_maximalIdeal_le A' htriv
  exact AdicFormallySmooth.of_baseChange_of_free A'
    ((adicFormallySmooth_of_algEquiv_mvPowerSeries e').of_pow_le N hN)

variable [IsNoetherianRing B] [IsAdicComplete (maximalIdeal A) A]
  [IsAdicComplete (maximalIdeal B) B]

/-- III.2.1, (i) ⇔ (iii), with trivial residue extension, for complete noetherian local rings. -/
theorem formallySmoothLocal_iff_adicFormallySmooth :
    FormallySmoothLocal A B ↔ AdicFormallySmooth A (maximalIdeal B) :=
  ⟨adicFormallySmooth_of_formallySmoothLocal htriv,
    formallySmoothLocal_of_adicFormallySmooth htriv⟩

/-- III.1.5: let `A → B` be a local homomorphism of complete noetherian local rings with trivial
residue extension. Then `B` is formally smooth over `A` (Definition III.1.1) if and only if it is
isomorphic to a power series ring `A⟦t₁, …, tₙ⟧`. (SGA states it for the completions `Â`, `B̂`.) -/
theorem formallySmoothLocal_iff_exists_algEquiv :
    FormallySmoothLocal A B ↔ ∃ n, Nonempty (B ≃ₐ[A] MvPowerSeries (Fin n) A) := by
  rw [formallySmoothLocal_iff_adicFormallySmooth htriv,
    adicFormallySmooth_iff_exists_algEquiv htriv]

end FormallySmooth

section TestRings

variable {A : Type u} [CommRing A] [IsLocalRing A] {n : ℕ} (q : ℕ)

lemma pow_succ_maximalIdeal_ne_top :
    maximalIdeal (MvPowerSeries (Fin n) A) ^ (q + 1) ≠ ⊤ :=
  fun h ↦ (maximalIdeal.isMaximal _).ne_top (eq_top_iff.2 (h ▸ Ideal.pow_le_self q.succ_ne_zero))

instance :
    Nontrivial (MvPowerSeries (Fin n) A ⧸ maximalIdeal (MvPowerSeries (Fin n) A) ^ (q + 1)) :=
  Ideal.Quotient.nontrivial_iff.2 (pow_succ_maximalIdeal_ne_top q)

instance :
    IsLocalRing (MvPowerSeries (Fin n) A ⧸ maximalIdeal (MvPowerSeries (Fin n) A) ^ (q + 1)) :=
  .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

lemma mk_mem_maximalIdeal_iff {F : MvPowerSeries (Fin n) A} :
    Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin n) A) ^ (q + 1)) F ∈ maximalIdeal _ ↔
      F ∈ maximalIdeal (MvPowerSeries (Fin n) A) := by
  simp only [mem_maximalIdeal, mem_nonunits_iff]
  refine ⟨fun h hF ↦ h (hF.map _), fun hF hunit ↦ hF ?_⟩
  obtain ⟨g, hg⟩ := hunit.exists_right_inv
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective g
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at hg
  by_contra hF'
  have h1 : F * G ∈ maximalIdeal (MvPowerSeries (Fin n) A) :=
    Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).2 hF')
  have := sub_mem h1 (Ideal.pow_le_self q.succ_ne_zero hg)
  rw [sub_sub_cancel] at this
  exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 this)

lemma maximalIdeal_quotient_le :
    maximalIdeal (MvPowerSeries (Fin n) A ⧸ maximalIdeal (MvPowerSeries (Fin n) A) ^ (q + 1)) ≤
      (maximalIdeal (MvPowerSeries (Fin n) A)).map (Ideal.Quotient.mk _) := by
  intro y hy
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact Ideal.mem_map_of_mem _ ((mk_mem_maximalIdeal_iff q).1 hy)

instance [IsNoetherianRing A] :
    IsArtinianRing
      (MvPowerSeries (Fin n) A ⧸ maximalIdeal (MvPowerSeries (Fin n) A) ^ (q + 1)) := by
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨q + 1, eq_bot_iff.2 ((Ideal.pow_right_mono (maximalIdeal_quotient_le q) _).trans ?_)⟩
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

instance : Module.Finite A
    (MvPowerSeries (Fin n) A ⧸ maximalIdeal (MvPowerSeries (Fin n) A) ^ (q + 1)) := by
  classical
  set M := maximalIdeal (MvPowerSeries (Fin n) A) ^ (q + 1)
  let S : Finset (MvPowerSeries (Fin n) A ⧸ M) :=
    (Finsupp.finite_of_degree_lt (σ := Fin n) (q + 1)).toFinset.image
      fun e ↦ Ideal.Quotient.mk M (monomial e 1)
  refine ⟨⟨S, eq_top_iff.2 fun y _ ↦ ?_⟩⟩
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hsub : F - (truncTotal (q + 1) F : MvPowerSeries (Fin n) A) ∈ M :=
    Ideal.pow_right_mono span_X_le_maximalIdeal _ (sub_truncTotal_mem_pow_span_X (q + 1) F)
  rw [show Ideal.Quotient.mk M F = Ideal.Quotient.mk M (truncTotal (q + 1) F) from
    Ideal.Quotient.eq.2 hsub]
  rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, (truncTotal (q + 1) F).as_sum, map_sum,
    map_sum]
  refine Submodule.sum_mem _ fun e he ↦ ?_
  have hlt : e.degree < q + 1 := by
    by_contra h
    exact MvPolynomial.mem_support_iff.1 he (coeff_truncTotal_eq_zero _ (not_lt.1 h))
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial,
    show monomial e (MvPolynomial.coeff e (truncTotal (q + 1) F)) =
      MvPolynomial.coeff e (truncTotal (q + 1) F) • monomial e (1 : A) by
      rw [smul_eq_C_mul, ← monomial_zero_eq_C_apply, monomial_mul_monomial, zero_add, mul_one],
    ← Ideal.Quotient.mkₐ_eq_mk A, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image.2
    ⟨e, (Set.Finite.mem_toFinset _).2 hlt, rfl⟩))

lemma exists_sub_algebraMap_mem_maximalIdeal
    (c : MvPowerSeries (Fin n) A ⧸ maximalIdeal (MvPowerSeries (Fin n) A) ^ (q + 1)) :
    ∃ a : A, c - algebraMap A _ a ∈ maximalIdeal _ := by
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨constantCoeff F, ?_⟩
  rw [IsScalarTower.algebraMap_apply A (MvPowerSeries (Fin n) A), Ideal.Quotient.algebraMap_eq,
    ← map_sub, mk_mem_maximalIdeal_iff, ← constantCoeff_mem_maximalIdeal_iff, map_sub,
    MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_C,
    sub_self]
  exact zero_mem _

end TestRings

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] in
/-- III.2.1 (iv), in the form (iv ter) of III.2.2: maps from `B` lift through square-zero ideals
of local artinian `A`-algebras `C`, finite over `A`, with the residue field of `A`. -/
def ArtinianLiftingProperty : Prop :=
  ∀ ⦃C : Type u⦄ [CommRing C] [Algebra A C] [IsLocalRing C] [IsArtinianRing C]
    [Module.Finite A C], (∀ c : C, ∃ a : A, c - algebraMap A C a ∈ maximalIdeal C) →
      ∀ J : Ideal C, J ^ 2 = ⊥ → ∀ f : B →ₐ[A] C ⧸ J, IsLocalHom f →
        ∃ g : B →ₐ[A] C, (Ideal.Quotient.mkₐ A J).comp g = f

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]

omit [IsLocalRing A] in
/-- III.2.1, (iii) ⇒ (iv): formal smoothness for the adic topology gives the lifting property
for local artinian test rings (a local map to a local artinian ring kills a power of `𝔫`). -/
theorem AdicFormallySmooth.artinianLiftingProperty (h : AdicFormallySmooth A (maximalIdeal B)) :
    ArtinianLiftingProperty A B := by
  intro C _ _ _ _ _ _ J hJ f hf
  have : Nontrivial (C ⧸ J) := by
    by_contra hC
    rw [not_nontrivial_iff_subsingleton] at hC
    exact not_isUnit_zero (isUnit_of_map_unit f 0 (isUnit_of_subsingleton _))
  have : IsLocalRing (C ⧸ J) := .of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  obtain ⟨N, hN⟩ : IsNilpotent (maximalIdeal (C ⧸ J)) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  refine h J ⟨2, hJ⟩ f ⟨N, ?_⟩
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, eq_bot_iff, ← Ideal.zero_eq_bot, ← hN]
  refine Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun b hb ↦ ?_) N
  exact map_nonunit (f : B →+* C ⧸ J) b hb

/-- III.2.1 (iv ter) gives the lifting property for the test rings `A⟦t₁, …, tₙ⟧ ⧸ 𝔫₁ᵠ⁺¹` used
in the proof of III.2.2, (iv ter) ⇒ (v): these are local artinian, finite over `A`, with the
residue field of `A`. -/
theorem liftsModPow_of_artinianLiftingProperty [IsNoetherianRing A]
    (h : ArtinianLiftingProperty A B) (n : ℕ) :
    AdicFormallySmooth.LiftsModPow A (maximalIdeal B)
      (maximalIdeal (MvPowerSeries (Fin n) A)) := by
  intro q J' hle hJ' hsq w ⟨k, hk⟩
  set C := MvPowerSeries (Fin n) A ⧸ maximalIdeal (MvPowerSeries (Fin n) A) ^ (q + 1)
  set J'' := RingHom.ker (Ideal.Quotient.factorₐ A hle)
  let e : (C ⧸ J'') ≃ₐ[A] MvPowerSeries (Fin n) A ⧸ J' :=
    Ideal.quotientKerAlgEquivOfSurjective (Ideal.Quotient.factor_surjective hle)
  have he (c : C) : e (Ideal.Quotient.mk J'' c) = Ideal.Quotient.factorₐ A hle c := rfl
  have : Nontrivial (MvPowerSeries (Fin n) A ⧸ J') :=
    Ideal.Quotient.nontrivial_iff.2 fun h ↦
      (maximalIdeal.isMaximal _).ne_top (eq_top_iff.2 (h ▸ hJ'))
  let f : B →ₐ[A] C ⧸ J'' := e.symm.toAlgHom.comp w
  have hf : IsLocalHom f := ⟨fun b hb ↦ by
    by_contra hb'
    have hbk : b ^ k ∈ RingHom.ker w := hk (Ideal.pow_mem_pow ((mem_maximalIdeal _).2 hb') k)
    have hnil : IsNilpotent (f b) := ⟨k, by
      rw [← map_pow]
      simp [f, RingHom.mem_ker.1 hbk]⟩
    have : Nontrivial (C ⧸ J'') := e.toEquiv.nontrivial
    exact hnil.not_isUnit hb⟩
  obtain ⟨g, hg⟩ := h (exists_sub_algebraMap_mem_maximalIdeal q) J'' hsq f hf
  refine ⟨g, AlgHom.ext fun b ↦ ?_⟩
  have := congr(e ($hg b))
  simpa [f, he] using this

variable [IsLocalHom (algebraMap A B)]

/-- III.2.2, (iv ter) ⇒ (v): with trivial residue extension, `A` complete and `B` noetherian, the
lifting property for local artinian test rings with the residue field of `A` gives a local
`A`-homomorphism `u : B → A⟦t₁, …, tₙ⟧` inducing a bijection of relative cotangent spaces. -/
theorem exists_cotangent_bijective_of_artinianLiftingProperty [IsNoetherianRing A]
    [IsNoetherianRing B] [IsAdicComplete (maximalIdeal A) A]
    (htriv : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B)
    (h : ArtinianLiftingProperty A B) :
    ∃ (n : ℕ) (u : B →ₐ[A] MvPowerSeries (Fin n) A), IsLocalHom u ∧
      (∀ y ∈ maximalIdeal (MvPowerSeries (Fin n) A), ∃ x ∈ maximalIdeal B,
        u x - y ∈ maximalIdeal (MvPowerSeries (Fin n) A) ^ 2 ⊔
          (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin n) A))) ∧
      (∀ x ∈ maximalIdeal B, u x ∈ maximalIdeal (MvPowerSeries (Fin n) A) ^ 2 ⊔
          (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin n) A)) →
        x ∈ maximalIdeal B ^ 2 ⊔ (maximalIdeal A).map (algebraMap A B)) :=
  exists_cotangent_bijective_of_liftsModPow htriv (liftsModPow_of_artinianLiftingProperty h)

/-- III.2.1 and III.2.2, for a local homomorphism `A → B` of complete noetherian local rings with
trivial residue extension (the case to which SGA reduces III.2.1). The following are equivalent:
(i) `B` is formally smooth over `A` (Definition III.1.1); (iii) `B` is formally smooth for its
`𝔫`-adic topology; (iv ter) the lifting property for local artinian test rings, finite over `A`,
with the residue field of `A`; (v) there is a local `A`-homomorphism `B → A⟦t₁, …, tₙ⟧` inducing
a bijection of relative cotangent spaces; and `B ≅ A⟦t₁, …, tₙ⟧` (III.1.5, III.2.3). -/
theorem formallySmooth_tfae [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]
    (htriv : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B) :
    List.TFAE [FormallySmoothLocal A B, AdicFormallySmooth A (maximalIdeal B),
      ArtinianLiftingProperty A B,
      ∃ (n : ℕ) (u : B →ₐ[A] MvPowerSeries (Fin n) A), IsLocalHom u ∧
        (∀ y ∈ maximalIdeal (MvPowerSeries (Fin n) A), ∃ x ∈ maximalIdeal B,
          u x - y ∈ maximalIdeal (MvPowerSeries (Fin n) A) ^ 2 ⊔
            (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin n) A))) ∧
        (∀ x ∈ maximalIdeal B, u x ∈ maximalIdeal (MvPowerSeries (Fin n) A) ^ 2 ⊔
            (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin n) A)) →
          x ∈ maximalIdeal B ^ 2 ⊔ (maximalIdeal A).map (algebraMap A B)),
      ∃ n, Nonempty (B ≃ₐ[A] MvPowerSeries (Fin n) A)] := by
  tfae_have 1 ↔ 2 := formallySmoothLocal_iff_adicFormallySmooth htriv
  tfae_have 2 → 3 := AdicFormallySmooth.artinianLiftingProperty
  tfae_have 3 → 4 := exists_cotangent_bijective_of_artinianLiftingProperty htriv
  tfae_have 4 → 5 := fun ⟨n, u, _, hsurj, hinj⟩ ↦ ⟨n, ⟨algEquivOfCotangent u hsurj hinj⟩⟩
  tfae_have 5 → 2 := fun ⟨_, ⟨e⟩⟩ ↦ adicFormallySmooth_of_algEquiv_mvPowerSeries e
  tfae_finish

end SGA.SGA1.ExposeIII
