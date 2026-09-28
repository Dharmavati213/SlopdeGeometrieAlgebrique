/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.Finite
import SGA.SGA1.ExposeV.DecompositionInertia

/-!
# SGA 1, Exposé V, §2: free actions, étaleness and principal coverings (V.2.3–V.2.8)

Let a finite group `G` act on a ring `A` with `B = A^G`. SGA proves V.2.3 (trivial inertia
implies étale) through completions (V.2.2). We use instead the argument of Chase, Harrison and
Rosenberg (Mem. AMS 52, 1965, Thm. 1.3), which needs no noetherian hypothesis: if all inertia
groups are trivial there are `x_i, y_i ∈ A` with `∑ x_i σ(y_i) = δ_{σ,1}`
(`exists_galois_elements`). They form a dual basis for the trace `A → B`, so `A` is finite
projective over `B`, and `∑ x_i ⊗ y_i` is a separability idempotent, so `A` is unramified.

* V.2.3: trivial inertia implies `A` finite étale over `B` (`etale_of_inertia_eq_bot`); local
  form: trivial inertia at `Q` implies étale over a neighbourhood of the image of `Q`.
* V.2.4: for `Spec A` connected and `G` faithful, étale iff trivial inertia, and then every
  `B`-automorphism of `A` comes from `G`. The input is I.5.4 in ring form
  (`algHom_eq_of_separability`).
* V.2.5: the example `Y × E` with the permutation group of `E`.
* V.2.6: (i) ⇔ (iii) (`isPrincipalCovering_iff`), (i) ⇒ (ii bis) with `Y₁ = X`, (iii) ⇒ (ii),
  and (ii) ⇒ (i) for any faithfully flat `B → B'`; all for `Y` affine.
* V.2.7: a principal covering with a section is trivial.
* V.2.8: principal coverings (`IsPrincipalCovering`), affine case.

V.2.3 and V.2.4 for non-affine `X` are in `InertiaGroups.lean`, V.2.6 ((i) ⇒ (iii)) and V.2.7
for non-affine `X` in `QuotientPrincipal.lean`, and V.2.6 for arbitrary schemes (all four
conditions) in `QuotientDescent.lean` (`principalCovering_tfae`). V.2.2 is proved in
`InertiaEtale.lean`.
-/

open TensorProduct
open scoped Pointwise

namespace SGA.SGA1.ExposeV

section

variable {A : Type*} [CommRing A] {G : Type*} [Group G] [MulSemiringAction G A]

lemma exists_sum_mul_smul_sub {g : G} (hg : ∀ m : Ideal A, m.IsMaximal → g ∈ m.inertia G → g = 1)
    (hg1 : g ≠ 1) : ∃ (n : ℕ) (a b : Fin n → A), ∑ i, a i * b i = 1 ∧ ∑ i, a i * g • b i = 0 := by
  have htop : Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    exact hg1 (hg m hm fun a ↦ hle (Ideal.subset_span ⟨a, rfl⟩))
  have h1 : (1 : A) ∈ Ideal.span (Set.range fun a : A ↦ g • a - a) := htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp h1
  -- index the support of `c` by `Fin k`
  let k := c.support.card
  let e := c.support.equivFin
  let a' : Fin k → A := fun i ↦ (e.symm i : A)
  refine ⟨k + 1, Fin.cons (∑ i, c (a' i) * g • a' i) fun i ↦ -c (a' i),
    Fin.cons 1 a', ?_, ?_⟩
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, mul_one, neg_mul, Finset.sum_neg_distrib]
    rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib, ← hc, Finsupp.sum]
    rw [← Finset.sum_coe_sort c.support, ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [smul_eq_mul, a']
    ring
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_one, mul_one, neg_mul, Finset.sum_neg_distrib,
      add_neg_cancel]

end

section

variable {A : Type*} [CommRing A] {G : Type*} [Group G] [MulSemiringAction G A]

/-- The elements of Chase–Harrison–Rosenberg: if `G` acts without inertia, there are
`x_i, y_i` with `∑ x_i y_i = 1` and `∑ x_i σ(y_i) = 0` for `σ ≠ 1`. -/
theorem exists_galois_elements [Finite G]
    (hfree : ∀ m : Ideal A, m.IsMaximal → ∀ g ∈ m.inertia G, g = 1) :
    ∃ (n : ℕ) (x y : Fin n → A), ∑ i, x i * y i = 1 ∧
      ∀ σ : G, σ ≠ 1 → ∑ i, x i * σ • y i = 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hg : ∀ g : G, ∃ (n : ℕ) (a b : Fin n → A), ∑ i, a i * b i = 1 ∧
      (g ≠ 1 → ∑ i, a i * g • b i = 0) := by
    intro g
    by_cases hg1 : g = 1
    · exact ⟨1, fun _ ↦ 1, fun _ ↦ 1, by simp, fun h ↦ (h hg1).elim⟩
    · obtain ⟨n, a, b, h1, h2⟩ := exists_sum_mul_smul_sub (fun m hm h ↦ hfree m hm _ h) hg1
      exact ⟨n, a, b, h1, fun _ ↦ h2⟩
  choose n a b h1 h2 using hg
  let J := (g : G) → Fin (n g)
  let e := Fintype.equivFin J
  have key : ∀ σ : G, ∑ j, (∏ g, a g (e.symm j g)) * σ • ∏ g, b g (e.symm j g) =
      ∏ g, ∑ i, a g i * σ • b g i := by
    intro σ
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.smul_prod', ← Finset.prod_mul_distrib]
  refine ⟨Fintype.card J, fun j ↦ ∏ g, a g (e.symm j g), fun j ↦ ∏ g, b g (e.symm j g),
    ?_, fun σ hσ ↦ ?_⟩
  · have := key 1
    simp only [one_smul] at this
    rw [this]
    exact Finset.prod_eq_one fun g _ ↦ h1 g
  · rw [key]
    exact Finset.prod_eq_zero (Finset.mem_univ σ) (h2 σ hσ)

end

section

variable {A : Type*} [CommRing A] {G : Type*} [Group G] [MulSemiringAction G A]
  (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A] [Fintype G]
  [Algebra.IsInvariant B A G]

lemma smul_sum_smul (g : G) (a : A) : g • ∑ σ : G, σ • a = ∑ σ : G, σ • a := by
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun _ ↦ rfl

variable {B}

omit [SMulCommClass G B A] in
variable (G) in
lemma exists_algebraMap_eq_sum_smul (a : A) : ∃ b : B, algebraMap B A b = ∑ σ : G, σ • a :=
  Algebra.IsInvariant.isInvariant (∑ σ : G, σ • a) fun g ↦ smul_sum_smul g a

/-- The trace `a ↦ ∑ σ • a`, as a `B`-linear map `A → B = A^G`. -/
noncomputable def invTrace (hinj : Function.Injective (algebraMap B A)) : A →ₗ[B] B where
  toFun a := (exists_algebraMap_eq_sum_smul (B := B) G a).choose
  map_add' a a' := hinj <| by
    rw [map_add, (exists_algebraMap_eq_sum_smul G _).choose_spec,
      (exists_algebraMap_eq_sum_smul G _).choose_spec,
      (exists_algebraMap_eq_sum_smul G _).choose_spec, ← Finset.sum_add_distrib]
    simp only [smul_add]
  map_smul' b a := hinj <| by
    rw [RingHom.id_apply, smul_eq_mul, map_mul, (exists_algebraMap_eq_sum_smul G _).choose_spec,
      (exists_algebraMap_eq_sum_smul G _).choose_spec, Finset.mul_sum]
    simp only [Algebra.smul_def, smul_mul', smul_algebraMap]

lemma algebraMap_invTrace (hinj : Function.Injective (algebraMap B A)) (a : A) :
    algebraMap B A (invTrace (G := G) hinj a) = ∑ σ : G, σ • a :=
  (exists_algebraMap_eq_sum_smul G a).choose_spec

/-- The dual basis property of the Chase–Harrison–Rosenberg elements. -/
lemma sum_mul_invTrace (hinj : Function.Injective (algebraMap B A)) {n : ℕ} {x y : Fin n → A}
    (h1 : ∑ i, x i * y i = 1) (h2 : ∀ σ : G, σ ≠ 1 → ∑ i, x i * σ • y i = 0) (a : A) :
    ∑ i, x i * algebraMap B A (invTrace (G := G) hinj (y i * a)) = a := by
  simp_rw [algebraMap_invTrace, Finset.mul_sum, smul_mul', ← mul_assoc]
  rw [Finset.sum_comm, Finset.sum_eq_single (1 : G)]
  · simp_rw [one_smul, ← Finset.sum_mul, h1, one_mul]
  · intro σ _ hσ
    rw [← Finset.sum_mul, h2 σ hσ, zero_mul]
  · simp

end

section

variable {A : Type*} [CommRing A] {G : Type*} [Group G] [MulSemiringAction G A]
  {B : Type*} [CommRing B] [Algebra B A] [SMulCommClass G B A] [Fintype G]
  [Algebra.IsInvariant B A G]

omit [Fintype G] in
/-- The Chase–Harrison–Rosenberg elements make `A` a direct summand of `B^n`. -/
theorem finite_and_projective_of_galois [Finite G] (hinj : Function.Injective (algebraMap B A))
    {n : ℕ} {x y : Fin n → A} (h1 : ∑ i, x i * y i = 1)
    (h2 : ∀ σ : G, σ ≠ 1 → ∑ i, x i * σ • y i = 0) :
    Module.Finite B A ∧ Module.Projective B A := by
  have : Fintype G := Fintype.ofFinite G
  let i : A →ₗ[B] (Fin n → B) :=
    LinearMap.pi fun k ↦ invTrace (G := G) hinj ∘ₗ LinearMap.mulLeft B (y k)
  let s : (Fin n → B) →ₗ[B] A := Fintype.linearCombination B x
  have hsi : s ∘ₗ i = LinearMap.id := by
    ext a
    simp only [LinearMap.comp_apply, Fintype.linearCombination_apply, LinearMap.pi_apply,
      LinearMap.mulLeft_apply, LinearMap.id_apply, s, i, Algebra.smul_def]
    conv_rhs => rw [← sum_mul_invTrace hinj h1 h2 a]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  exact ⟨Module.Finite.of_surjective s fun a ↦ ⟨i a, congr($hsi a)⟩,
    Module.Projective.of_split i s hsi⟩

omit [SMulCommClass G B A] [Algebra.IsInvariant B A G] [Fintype G] in
lemma sum_smul_mul_eq_zero {n : ℕ} {x y : Fin n → A}
    (h2 : ∀ σ : G, σ ≠ 1 → ∑ i, x i * σ • y i = 0) {σ : G} (hσ : σ ≠ 1) :
    ∑ i, σ • x i * y i = 0 := by
  have := congr_arg (σ • ·) (h2 σ⁻¹ (inv_ne_one.mpr hσ))
  simpa [Finset.smul_sum, smul_mul', smul_inv_smul] using this

lemma sum_invTrace_mul (hinj : Function.Injective (algebraMap B A)) {n : ℕ} {x y : Fin n → A}
    (h1 : ∑ i, x i * y i = 1) (h2 : ∀ σ : G, σ ≠ 1 → ∑ i, x i * σ • y i = 0) (a : A) :
    ∑ i, algebraMap B A (invTrace (G := G) hinj (a * x i)) * y i = a := by
  simp_rw [algebraMap_invTrace, Finset.sum_mul, smul_mul', mul_assoc]
  rw [Finset.sum_comm, Finset.sum_eq_single (1 : G)]
  · simp_rw [one_smul, ← Finset.mul_sum, h1, mul_one]
  · intro σ _ hσ
    rw [← Finset.mul_sum, sum_smul_mul_eq_zero h2 hσ, mul_zero]
  · simp

omit [Fintype G] in
/-- The element `t = ∑ x_i ⊗ y_i` of `A ⊗_B A` is a separability idempotent. -/
lemma galois_tensor_spec [Finite G] (hinj : Function.Injective (algebraMap B A)) {n : ℕ}
    {x y : Fin n → A} (h1 : ∑ i, x i * y i = 1) (h2 : ∀ σ : G, σ ≠ 1 → ∑ i, x i * σ • y i = 0) :
    (∀ s : A, ((1 : A) ⊗ₜ[B] s - s ⊗ₜ[B] (1 : A)) * ∑ i, x i ⊗ₜ[B] y i = 0) ∧
      Algebra.TensorProduct.lmul' B (∑ i, x i ⊗ₜ[B] y i) = 1 := by
  have : Fintype G := Fintype.ofFinite G
  refine ⟨fun s ↦ ?_, ?_⟩
  · have key : ∑ i, (s * x i) ⊗ₜ[B] y i = ∑ k, x k ⊗ₜ[B] (y k * s) := by
      conv_lhs => enter [2, i]; rw [← sum_mul_invTrace (G := G) hinj h1 h2 (s * x i)]
      simp_rw [TensorProduct.sum_tmul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp_rw [mul_comm (x k), ← Algebra.smul_def, TensorProduct.smul_tmul,
        ← TensorProduct.tmul_sum, Algebra.smul_def, ← mul_assoc]
      rw [sum_invTrace_mul hinj h1 h2]
    rw [Finset.mul_sum]
    simp_rw [sub_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [Finset.sum_sub_distrib, sub_eq_zero, key]
    simp_rw [mul_comm s]
  · simp [Algebra.TensorProduct.lmul'_apply_tmul, h1]

omit [Fintype G] in
theorem formallyUnramified_of_galois [Finite G] (hinj : Function.Injective (algebraMap B A))
    {n : ℕ} {x y : Fin n → A} (h1 : ∑ i, x i * y i = 1)
    (h2 : ∀ σ : G, σ ≠ 1 → ∑ i, x i * σ • y i = 0) :
    Algebra.FormallyUnramified B A := by
  have := (finite_and_projective_of_galois hinj h1 h2).1
  rw [Algebra.FormallyUnramified.iff_exists_tensorProduct]
  exact ⟨_, galois_tensor_spec hinj h1 h2⟩

omit [Fintype G] in
/-- V.2.3: if `G` acts on `A` without inertia (trivial inertia at every maximal ideal), then `A`
is finite, projective and étale over `B = A^G`. -/
theorem etale_of_inertia_eq_bot [Finite G] (hinj : Function.Injective (algebraMap B A))
    (hfree : ∀ m : Ideal A, m.IsMaximal → ∀ g ∈ m.inertia G, g = 1) :
    Algebra.Etale B A ∧ Module.Finite B A ∧ Module.Projective B A := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨n, x, y, h1, h2⟩ := exists_galois_elements hfree
  obtain ⟨_, _⟩ := finite_and_projective_of_galois hinj h1 h2
  have := formallyUnramified_of_galois hinj h1 h2
  have : Module.FinitePresentation B A := Module.finitePresentation_of_projective B A
  exact ⟨.of_formallyUnramified_of_flat, inferInstance, inferInstance⟩

end

section

section Unramified

variable {B A C : Type*} [CommRing B] [CommRing A] [CommRing C] [Algebra B A] [Algebra B C]
  {t : A ⊗[B] A} (ht₁ : ∀ s : A, ((1 : A) ⊗ₜ[B] s - s ⊗ₜ[B] (1 : A)) * t = 0)
  (ht₂ : Algebra.TensorProduct.lmul' B t = 1)

include ht₁ in
lemma mul_eq_lmul'_tmul_mul (z : A ⊗[B] A) :
    z * t = (Algebra.TensorProduct.lmul' B z ⊗ₜ[B] (1 : A)) * t := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have hb : ((1 : A) ⊗ₜ[B] b) * t = (b ⊗ₜ[B] (1 : A)) * t := sub_eq_zero.mp (by
      rw [← sub_mul]; exact ht₁ b)
    rw [Algebra.TensorProduct.lmul'_apply_tmul,
      show a ⊗ₜ[B] b = (a ⊗ₜ[B] (1 : A)) * ((1 : A) ⊗ₜ[B] b) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
      mul_assoc, hb, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | add x y hx hy => rw [add_mul, hx, hy, map_add, TensorProduct.add_tmul, add_mul]

include ht₁ ht₂ in
/-- A separability element `t` is idempotent. -/
lemma isIdempotentElem_of_separability : IsIdempotentElem t := by
  rw [IsIdempotentElem, mul_eq_lmul'_tmul_mul ht₁ t, ht₂, ← Algebra.TensorProduct.one_def,
    one_mul]

include ht₁ in
lemma mul_productMap_eq_zero (σ τ : A →ₐ[B] C) (s : A) :
    (τ s - σ s) * Algebra.TensorProduct.productMap σ τ t = 0 := by
  have := congr_arg (Algebra.TensorProduct.productMap σ τ) (ht₁ s)
  rwa [map_mul, map_sub, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, map_one, one_mul, mul_one,
    map_zero] at this

include ht₁ ht₂ in
/-- I.5.4 in ring form (used in V.2.4): let `A` be unramified over `B`, with separability element
`t`. Two `B`-algebra maps `σ τ : A → C`, into a ring without nontrivial idempotents, which agree
modulo a proper ideal `I` (i.e. at a point, with the same residue map) are equal. -/
theorem algHom_eq_of_separability (hC : ∀ c : C, IsIdempotentElem c → c = 0 ∨ c = 1)
    (σ τ : A →ₐ[B] C) (I : Ideal C) (hI : I ≠ ⊤) (hστ : ∀ a, σ a - τ a ∈ I) : σ = τ := by
  set c := Algebra.TensorProduct.productMap σ τ t
  have hc : IsIdempotentElem c := (isIdempotentElem_of_separability ht₁ ht₂).map _
  have hmod : ∀ z : A ⊗[B] A, Ideal.Quotient.mk I (Algebra.TensorProduct.productMap σ τ z) =
      Ideal.Quotient.mk I (σ (Algebra.TensorProduct.lmul' B z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
        map_mul, map_mul, map_mul, Ideal.Quotient.eq.mpr (show τ b - σ b ∈ I from by
          rw [← neg_sub]; exact I.neg_mem_iff.mpr (hστ b))]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add]
  have hc0 : c ≠ 0 := by
    intro h
    have := hmod t
    rw [ht₂, map_one, map_one] at this
    change Ideal.Quotient.mk I c = 1 at this
    rw [h, map_zero] at this
    exact hI (Ideal.Quotient.zero_eq_one_iff.mp this)
  have hc1 : c = 1 := (hC c hc).resolve_left hc0
  ext s
  have := mul_productMap_eq_zero ht₁ σ τ s
  rw [← sub_eq_zero, ← neg_sub, neg_eq_zero]
  change (τ s - σ s) * c = 0 at this
  rwa [hc1, mul_one] at this

end Unramified


end

section

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra B A]
  {G : Type*} [Group G] [MulSemiringAction G A] [SMulCommClass G B A]

section Connected

/-- V.2.4, first assertion (necessity): if `A` is unramified over `B`, `Spec A` is connected and
`G` acts faithfully, then every inertia group is trivial. -/
theorem eq_one_of_mem_inertia [Algebra.FormallyUnramified B A] [Algebra.EssFiniteType B A]
    (hA : ∀ c : A, IsIdempotentElem c → c = 0 ∨ c = 1)
    (hfaith : ∀ g : G, (∀ a : A, g • a = a) → g = 1) (Q : Ideal A) (hQ : Q ≠ ⊤) (g : G)
    (hg : g ∈ Q.inertia G) : g = 1 := by
  obtain ⟨t, ht₁, ht₂⟩ := Algebra.FormallyUnramified.iff_exists_tensorProduct.mp ‹_›
  have := algHom_eq_of_separability ht₁ ht₂ hA (MulSemiringAction.toAlgHom B A g)
    (AlgHom.id B A) Q hQ fun a ↦ hg a
  exact hfaith g fun a ↦ congr($this a)

variable [Finite G] [Algebra.IsInvariant B A G]

/-- V.2.4, first assertion: if `Spec A` is connected and `G` acts faithfully, then `A` is étale
over `A^G` iff all inertia groups are trivial. -/
theorem etale_iff_inertia_eq_bot (hinj : Function.Injective (algebraMap B A))
    (hA : ∀ c : A, IsIdempotentElem c → c = 0 ∨ c = 1)
    (hfaith : ∀ g : G, (∀ a : A, g • a = a) → g = 1) :
    Algebra.Etale B A ↔ ∀ Q : Ideal A, Q.IsPrime → ∀ g ∈ Q.inertia G, g = 1 := by
  refine ⟨fun _ Q hQ g hg ↦ eq_one_of_mem_inertia (B := B) hA hfaith Q hQ.ne_top g hg,
    fun h ↦ ?_⟩
  exact (etale_of_inertia_eq_bot hinj fun m hm ↦ h m hm.isPrime).1

/-- V.2.4, second assertion: if `G` acts without inertia and `Spec A` is connected, every
`B`-automorphism of `A` is given by an element of `G`. -/
theorem exists_smul_eq_of_algEquiv [Nontrivial A] (hinj : Function.Injective (algebraMap B A))
    (hfree : ∀ m : Ideal A, m.IsMaximal → ∀ g ∈ m.inertia G, g = 1)
    (hA : ∀ c : A, IsIdempotentElem c → c = 0 ∨ c = 1) (u : A ≃ₐ[B] A) :
    ∃ g : G, ∀ a, g • a = u a := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨n, x, y, h1, h2⟩ := exists_galois_elements hfree
  obtain ⟨ht₁, ht₂⟩ := galois_tensor_spec (G := G) hinj h1 h2
  set t := ∑ i, x i ⊗ₜ[B] y i
  let φ : G → (A ⊗[B] A →ₐ[B] A) := fun h ↦ Algebra.TensorProduct.productMap (AlgHom.id B A)
    (u.toAlgHom.comp (MulSemiringAction.toAlgHom B A h))
  have hφ : ∀ h, φ h t = ∑ i, x i * u (h • y i) := fun h ↦ by
    simp [t, φ, Algebra.TensorProduct.productMap_apply_tmul]
  have hsum : ∑ h : G, φ h t = 1 := by
    simp_rw [hφ]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← map_sum, ← algebraMap_invTrace (B := B) hinj, AlgEquiv.commutes]
    conv_rhs => rw [← sum_mul_invTrace (G := G) hinj h1 h2 1]
    simp
  obtain ⟨h, hh⟩ : ∃ h, φ h t = 1 := by
    by_contra! hne
    have : ∀ h ∈ Finset.univ, φ h t = 0 := fun h _ ↦
      (hA _ ((isIdempotentElem_of_separability ht₁ ht₂).map (φ h))).resolve_right (hne h)
    rw [Finset.sum_eq_zero this] at hsum
    exact zero_ne_one hsum
  refine ⟨h⁻¹, fun a ↦ ?_⟩
  have := mul_productMap_eq_zero ht₁ (AlgHom.id B A)
    (u.toAlgHom.comp (MulSemiringAction.toAlgHom B A h)) (h⁻¹ • a)
  change _ * φ h t = 0 at this
  rw [hh, mul_one, sub_eq_zero] at this
  simpa using this.symm

end Connected


section Galois

variable (B G) in
/-- The map `A ⊗_B A → ∏_{σ ∈ G} A`, `a ⊗ a' ↦ (a · σ(a'))_σ`: on rings, the morphism
`X × G = X ×_Y G_Y → X ×_Y X` of V.2.6 (iii). It is `A`-linear for the first factor. -/
noncomputable def galoisMap : A ⊗[B] A →ₐ[A] (G → A) :=
  AlgHom.pi fun σ ↦
    Algebra.TensorProduct.productLeftAlgHom (AlgHom.id A A) (MulSemiringAction.toAlgHom B A σ)

lemma galoisMap_tmul (a a' : A) (σ : G) : galoisMap B G (a ⊗ₜ[B] a') σ = a * σ • a' := by
  simp [galoisMap]

variable [Finite G] [Algebra.IsInvariant B A G]

/-- V.2.6, (i) ⇒ (iii): if `G` acts without inertia, `X ×_Y X ≅ X × G`, i.e. `X` is formally
principal homogeneous under `G_Y`: the map `A ⊗_B A → ∏_G A` is bijective. -/
theorem galoisMap_bijective (hinj : Function.Injective (algebraMap B A))
    (hfree : ∀ m : Ideal A, m.IsMaximal → ∀ g ∈ m.inertia G, g = 1) :
    Function.Bijective (galoisMap B G (A := A)) := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨n, x, y, h1, h2⟩ := exists_galois_elements hfree
  -- the inverse on the image
  let E : (G → A) → A ⊗[B] A := fun f ↦ ∑ k, (∑ σ : G, σ • y k * f σ) ⊗ₜ[B] x k
  have hE : ∀ z, E (galoisMap B G z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [E]
    | tmul u v =>
      simp only [E, galoisMap_tmul]
      have : ∀ k, ∑ σ : G, σ • y k * (u * σ • v) = u * algebraMap B A
          (invTrace (G := G) hinj (y k * v)) := fun k ↦ by
        rw [algebraMap_invTrace, Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ ↦ by rw [smul_mul']; ring
      simp_rw [this, mul_comm u, ← Algebra.smul_def, TensorProduct.smul_tmul,
        ← TensorProduct.tmul_sum, Algebra.smul_def, mul_comm (algebraMap B A _)]
      rw [sum_mul_invTrace hinj h1 h2]
    | add z z' hz hz' =>
      conv_rhs => rw [← hz, ← hz']
      simp only [E, map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib,
        TensorProduct.add_tmul]
  refine ⟨fun z z' hzz' ↦ by rw [← hE z, ← hE z', hzz'], fun f ↦ ?_⟩
  refine ⟨∑ h : G, ∑ i, (f h * x i) ⊗ₜ[B] (h⁻¹ • y i), funext fun σ ↦ ?_⟩
  simp only [map_sum, Finset.sum_apply, galoisMap_tmul, smul_smul, mul_assoc,
    ← Finset.mul_sum]
  rw [Finset.sum_eq_single σ]
  · simp [h1]
  · intro h _ hh
    rw [h2 _ (mul_inv_eq_one.not.mpr (Ne.symm hh)), mul_zero]
  · simp

/-- V.2.6, (i) ⇒ (iii): if `G` acts without inertia, `A` is faithfully flat over `A^G`. -/
theorem faithfullyFlat_of_inertia_eq_bot (hinj : Function.Injective (algebraMap B A))
    (hfree : ∀ m : Ideal A, m.IsMaximal → ∀ g ∈ m.inertia G, g = 1) :
    Module.FaithfullyFlat B A := by
  obtain ⟨-, -, _⟩ := etale_of_inertia_eq_bot hinj hfree
  exact .of_comap_surjective
    (RingHom.IsIntegral.comap_surjective (Algebra.IsInvariant.isIntegral B A G).1 hinj)

/-- V.2.7: if `G` acts without inertia and `X` has a section `s` over `Y` (a `B`-algebra map
`A → B`), then `X` is trivial: `a ↦ (s(σ • a))_σ` is a `G`-equivariant isomorphism
`A ≅ ∏_G B`, i.e. `X ≅ Y × G`. -/
theorem bijective_of_section (hinj : Function.Injective (algebraMap B A))
    (hfree : ∀ m : Ideal A, m.IsMaximal → ∀ g ∈ m.inertia G, g = 1) (s : A →ₐ[B] B) :
    Function.Bijective fun a : A ↦ fun σ : G ↦ s (σ • a) := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨n, x, y, h1, h2⟩ := exists_galois_elements hfree
  have hs : ∀ b : B, s (algebraMap B A b) = b := s.commutes
  refine ⟨fun a a' h ↦ ?_, fun f ↦ ?_⟩
  · rw [← sum_mul_invTrace (G := G) hinj h1 h2 a, ← sum_mul_invTrace (G := G) hinj h1 h2 a']
    refine Finset.sum_congr rfl fun k _ ↦ congr_arg _ (congr_arg _ ?_)
    rw [← hs (invTrace hinj (y k * a)), ← hs (invTrace hinj (y k * a')), algebraMap_invTrace,
      algebraMap_invTrace, map_sum, map_sum]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    have hσ : s (σ • a) = s (σ • a') := congr_fun h σ
    rw [smul_mul', smul_mul', map_mul, map_mul, hσ]
  · classical
    let e : A := ∑ j, algebraMap B A (s (x j)) * y j
    have he : ∀ τ : G, s (τ • e) = if τ = 1 then 1 else 0 := by
      intro τ
      have : s (τ • e) = s (∑ j, x j * τ • y j) := by
        simp only [e, Finset.smul_sum, smul_mul', smul_algebraMap, map_sum, map_mul, hs]
      rw [this]
      split_ifs with hτ
      · rw [hτ]; simp [h1]
      · rw [h2 τ hτ, map_zero]
    refine ⟨∑ h : G, algebraMap B A (f h) * (h⁻¹ • e), funext fun σ ↦ ?_⟩
    simp only [Finset.smul_sum, smul_mul', smul_algebraMap, smul_smul, map_sum, map_mul, hs, he]
    rw [Finset.sum_eq_single σ]
    · simp
    · intro h _ hh
      simp [mul_inv_eq_one, Ne.symm hh]
    · simp

end Galois

end

section PrincipalCovering

variable (B A G : Type*) [CommRing B] [CommRing A] [Algebra B A] [Group G]
  [MulSemiringAction G A] [SMulCommClass G B A]

/-- V.2: `A` is trivial if it is `G`-equivariantly isomorphic to `∏_G B`, on which `G` acts by
right translations `(τ • f)(σ) = f (σ τ)`; i.e. `X ≅ Y × G`. -/
def IsTrivial : Prop :=
  ∃ e : A ≃ₐ[B] (G → B), ∀ (τ : G) (a : A) (σ : G), e (τ • a) σ = e a (σ * τ)

/-- V.2.8: `A` is a principal covering of `B` with Galois group `G`, in the affine case: the
conditions V.2.6 (i), i.e. `A` finite over `B`, `B = A^G`, and all inertia groups trivial. -/
structure IsPrincipalCovering : Prop where
  finite : Module.Finite B A
  injective : Function.Injective (algebraMap B A)
  isInvariant : Algebra.IsInvariant B A G
  inertia_eq_bot : ∀ Q : Ideal A, Q.IsPrime → ∀ g ∈ Q.inertia G, g = 1

variable {B A G} [Finite G]

lemma IsPrincipalCovering.of_inertia_eq_bot [Algebra.IsInvariant B A G]
    (hinj : Function.Injective (algebraMap B A))
    (hfree : ∀ Q : Ideal A, Q.IsPrime → ∀ g ∈ Q.inertia G, g = 1) :
    IsPrincipalCovering B A G :=
  ⟨(etale_of_inertia_eq_bot hinj fun m hm ↦ hfree m hm.isPrime).2.1, hinj, ‹_›, hfree⟩

/-- V.2.3 for a principal covering: `A` is finite étale over `B`. -/
theorem IsPrincipalCovering.etale (h : IsPrincipalCovering B A G) : Algebra.Etale B A :=
  have := h.isInvariant
  (etale_of_inertia_eq_bot h.injective fun m hm ↦ h.inertia_eq_bot m hm.isPrime).1

/-- V.2.6, (i) ⇒ (iii): a principal covering is formally principal homogeneous
(`A ⊗_B A ≅ ∏_G A`) and faithfully flat. -/
theorem IsPrincipalCovering.galoisMap_bijective_and_faithfullyFlat
    (h : IsPrincipalCovering B A G) :
    Function.Bijective (galoisMap B G (A := A)) ∧ Module.FaithfullyFlat B A :=
  have := h.isInvariant
  ⟨galoisMap_bijective h.injective fun m hm ↦ h.inertia_eq_bot m hm.isPrime,
    faithfullyFlat_of_inertia_eq_bot h.injective fun m hm ↦ h.inertia_eq_bot m hm.isPrime⟩

omit [Finite G] in
lemma galoisMap_smul (τ : G) (z : A ⊗[B] A) (σ : G) :
    letI := tensorAction (B := B) (A := A) A G
    galoisMap B G (τ • z) σ = galoisMap B G z (σ * τ) := by
  let := tensorAction (B := B) (A := A) A G
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a a' =>
    rw [tensorAction_tmul, galoisMap_tmul, galoisMap_tmul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hx, hy]

/-- V.2.6, (i) ⇒ (ii bis): after the finite étale surjective change of base `A/B` itself, a
principal covering becomes trivial: `A ⊗_B A ≅ ∏_G A`, `G`-equivariantly. -/
theorem IsPrincipalCovering.isTrivial_tensorProduct_self (h : IsPrincipalCovering B A G) :
    letI := tensorAction (B := B) (A := A) A G
    IsTrivial A (A ⊗[B] A) G := by
  let := tensorAction (B := B) (A := A) A G
  exact ⟨AlgEquiv.ofBijective _ h.galoisMap_bijective_and_faithfullyFlat.1,
    fun τ z σ ↦ galoisMap_smul τ z σ⟩

/-- V.2.7: a principal covering with a section `A → B` is trivial. -/
theorem IsPrincipalCovering.isTrivial_of_section (h : IsPrincipalCovering B A G)
    (s : A →ₐ[B] B) : IsTrivial B A G := by
  have := h.isInvariant
  let f : A →ₐ[B] (G → B) := AlgHom.pi fun σ ↦ s.comp (MulSemiringAction.toAlgHom B A σ)
  have hf : Function.Bijective f :=
    bijective_of_section h.injective (fun m hm ↦ h.inertia_eq_bot m hm.isPrime) s
  refine ⟨AlgEquiv.ofBijective f hf, fun τ a σ ↦ ?_⟩
  simp [f, mul_smul]

omit [Finite G] in
/-- V.2.6, (iii) ⇒ (ii): if `X` is formally principal homogeneous, i.e. `A ⊗_B A → ∏_G A` is
bijective, then `X` becomes trivial after the change of base `A/B`. -/
theorem isTrivial_tensorProduct_self_of_bijective
    (h : Function.Bijective (galoisMap B G (A := A))) :
    letI := tensorAction (B := B) (A := A) A G
    IsTrivial A (A ⊗[B] A) G := by
  let := tensorAction (B := B) (A := A) A G
  exact ⟨AlgEquiv.ofBijective _ h, fun τ z σ ↦ galoisMap_smul τ z σ⟩

/-- V.2.6, (ii) ⇒ (i): if `X` becomes trivial after a faithfully flat change of base `B → B'`,
then `X` is a principal covering. -/
theorem IsPrincipalCovering.of_isTrivial_tensorProduct (B' : Type*) [CommRing B'] [Algebra B B']
    [Module.FaithfullyFlat B B']
    (htriv : letI := tensorAction (B := B) (A := A) B' G; IsTrivial B' (B' ⊗[B] A) G) :
    IsPrincipalCovering B A G := by
  let := tensorAction (B := B) (A := A) B' G
  obtain ⟨e, he⟩ := htriv
  -- finiteness descends
  have : Module.Finite B' (B' ⊗[B] A) := Module.Finite.equiv e.symm.toLinearEquiv
  have hfin : Module.Finite B A := .of_finite_tensorProduct_of_faithfullyFlat B'
  -- `B' ⊗ A` has invariants `B'`
  have hinj' : Function.Injective (algebraMap B' (B' ⊗[B] A)) := by
    intro b b' hbb'
    have := congr_fun ((e.commutes b).symm.trans ((congr_arg e hbb').trans (e.commutes b'))) 1
    simpa using this
  have hinv' : Algebra.IsInvariant B' (B' ⊗[B] A) G := ⟨fun x hx ↦ ⟨e x 1, e.injective ?_⟩⟩
  · obtain ⟨hinj, hinv⟩ := isInvariant_of_tensorProduct B' G hinj' hinv'
    refine ⟨hfin, hinj, hinv, fun Q hQ g hg ↦ ?_⟩
    -- a prime of `B' ⊗ A` over `Q`
    obtain ⟨⟨Q'', hQ''⟩, hQ''Q⟩ :=
      PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := A ⊗[B] B') ⟨Q, hQ⟩
    let c : B' ⊗[B] A ≃ₐ[B] A ⊗[B] B' := Algebra.TensorProduct.comm B B' A
    let Q' : Ideal (B' ⊗[B] A) := Q''.comap c.toRingHom
    have hQ' : Q'.IsPrime := Ideal.comap_isPrime _ _
    have hQ'Q : Q'.comap (Algebra.TensorProduct.includeRight : A →ₐ[B] B' ⊗[B] A) = Q := by
      have := congr_arg PrimeSpectrum.asIdeal hQ''Q
      simp only [PrimeSpectrum.comap_asIdeal] at this
      rw [← this]
      ext a
      simp [Q', c, Algebra.TensorProduct.algebraMap_apply]
    have hg' : g ∈ Q'.inertia G := by rwa [inertia_tensorProduct G B' Q', hQ'Q]
    by_contra hg1
    classical
    have : Fintype G := Fintype.ofFinite G
    let ε : G → B' ⊗[B] A := fun σ ↦ e.symm (Pi.single σ 1)
    have hsum : ∑ σ, ε σ = 1 := by
      simp only [ε, ← map_sum, Finset.univ_sum_single]
      exact map_one e.symm
    obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, ε σ₀ ∉ Q' := by
      by_contra! h
      exact hQ'.ne_top ((Ideal.eq_top_iff_one _).mpr (hsum ▸ Q'.sum_mem fun σ _ ↦ h σ))
    have hmul : g • ε σ₀ * ε σ₀ = 0 := by
      apply e.injective
      ext σ
      rw [map_mul, Pi.mul_apply, he, map_zero, Pi.zero_apply]
      simp only [ε, AlgEquiv.apply_symm_apply, Pi.single_apply]
      split_ifs with h₁ h₂ <;> simp_all
    have hidem : ε σ₀ * ε σ₀ = ε σ₀ := by
      rw [← map_mul, ← Pi.single_mul, mul_one]
    have := Q'.mul_mem_right (ε σ₀) (hg' (ε σ₀))
    rw [sub_mul, hmul, hidem, zero_sub, Q'.neg_mem_iff] at this
    exact hσ₀ this
  · have h1 : ∀ σ, e x σ = e x 1 := fun σ ↦ by
      have := he σ x 1
      rw [hx, one_mul] at this
      exact this.symm
    ext σ
    rw [AlgEquiv.commutes]
    simp [h1 σ]

/-- V.2.6, (i) ⇔ (iii), affine case: `A` is a principal covering of `B` with group `G` iff it is
formally principal homogeneous (`A ⊗_B A ≅ ∏_G A`) and faithfully flat over `B`. -/
theorem isPrincipalCovering_iff :
    IsPrincipalCovering B A G ↔
      Function.Bijective (galoisMap B G (A := A)) ∧ Module.FaithfullyFlat B A :=
  ⟨fun h ↦ h.galoisMap_bijective_and_faithfullyFlat, fun ⟨h, _⟩ ↦
    .of_isTrivial_tensorProduct A (isTrivial_tensorProduct_self_of_bijective h)⟩

end PrincipalCovering

section Local

variable {B A G : Type*} [CommRing B] [CommRing A] [Algebra B A] [Group G] [Finite G]
  [MulSemiringAction G A] [SMulCommClass G B A] [Algebra.IsInvariant B A G]

omit [Finite G] [Algebra.IsInvariant B A G] in
lemma mem_inertia_iff_span_le (g : G) (m : Ideal A) :
    g ∈ m.inertia G ↔ Ideal.span (Set.range fun a : A ↦ g • a - a) ≤ m := by
  rw [Ideal.span_le, Set.range_subset_iff]
  rfl

/-- If `G_i(Q) = 1`, then for `g ≠ 1` some `s ∈ B` outside `P = Q ∩ B` lies in every ideal whose
inertia group contains `g`. -/
lemma exists_not_mem_of_inertia_eq_bot (Q : Ideal A) [Q.IsPrime]
    (hQ : ∀ g ∈ Q.inertia G, g = 1) {g : G} (hg : g ≠ 1) :
    ∃ s : B, s ∉ Q.comap (algebraMap B A) ∧
      algebraMap B A s ∈ Ideal.span (Set.range fun a : A ↦ g • a - a) := by
  have := Algebra.IsInvariant.isIntegral B A G
  by_contra! h
  obtain ⟨Q', hle, hQ', hQ'P⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (Q.comap (algebraMap B A)) (Ideal.span (Set.range fun a : A ↦ g • a - a))
    fun s hs ↦ by_contra fun hsP ↦ h s hsP hs
  obtain ⟨h, rfl⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B A G Q Q' hQ'P.symm
  have hgQ' : g ∈ (h • Q).inertia G := (mem_inertia_iff_span_le g _).mpr hle
  rw [Ideal.inertia_smul, Subgroup.mem_map] at hgQ'
  obtain ⟨k, hk, rfl⟩ := hgQ'
  exact hg (by rw [hQ k hk, map_one])

/-- V.2.3, local form: if the inertia group of `Q` is trivial, then `X = Spec A` is étale over a
neighbourhood `D(s)` of the image `y` of `Q`: `B_s → B_s ⊗_B A` is étale. (In particular `X` is
étale over `Y` at `Q`, as in SGA; here all inertia groups over `y` are conjugate, so trivial.) -/
theorem exists_etale_localization_of_inertia_eq_bot (hinj : Function.Injective (algebraMap B A))
    (Q : Ideal A) [Q.IsPrime] (hQ : ∀ g ∈ Q.inertia G, g = 1) :
    ∃ s : B, s ∉ Q.comap (algebraMap B A) ∧
      Algebra.Etale (Localization.Away s) (Localization.Away s ⊗[B] A) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hs : ∀ g : G, ∃ s : B, s ∉ Q.comap (algebraMap B A) ∧ (g ≠ 1 →
      algebraMap B A s ∈ Ideal.span (Set.range fun a : A ↦ g • a - a)) := by
    intro g
    by_cases hg : g = 1
    · exact ⟨1, (Ideal.IsPrime.ne_top inferInstance) ∘ (Ideal.eq_top_iff_one _).mpr,
        fun h ↦ (h hg).elim⟩
    · obtain ⟨s, hs, hsI⟩ := exists_not_mem_of_inertia_eq_bot (B := B) Q hQ hg
      exact ⟨s, hs, fun _ ↦ hsI⟩
  choose t ht htI using hs
  let s := ∏ g, t g
  have hsP : s ∉ Q.comap (algebraMap B A) :=
    Ideal.IsPrime.prod_mem_iff.not.mpr fun ⟨g, _, hg⟩ ↦ ht g hg
  refine ⟨s, hsP, ?_⟩
  let B' := Localization.Away s
  let := tensorAction (B := B) (A := A) B' G
  have := tensorAction_smulCommClass (B := B) (A := A) B' G
  obtain ⟨hinj', hinv'⟩ := isInvariant_tensorProduct B' G hinj
  refine (etale_of_inertia_eq_bot (G := G) hinj' fun m hm g hg ↦ ?_).1
  by_contra hg1
  have hgm : g ∈ (m.comap (Algebra.TensorProduct.includeRight : A →ₐ[B] B' ⊗[B] A)).inertia G := by
    rw [← inertia_tensorProduct G B' m]
    exact hg
  have hmem := (mem_inertia_iff_span_le g _).mp hgm (htI g hg1)
  rw [Ideal.mem_comap, Algebra.TensorProduct.includeRight_apply, ← mul_one (algebraMap B A _),
    ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one] at hmem
  have hunit : IsUnit (algebraMap B B' (t g)) := by
    refine isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem t (Finset.mem_univ g)))
      (IsLocalization.Away.algebraMap_isUnit s)
  have hunit' := hunit.map (Algebra.TensorProduct.includeLeft : B' →ₐ[B] B' ⊗[B] A)
  exact hm.ne_top (Ideal.eq_top_of_isUnit_mem m hmem
    (by simpa [Algebra.TensorProduct.algebraMap_apply] using hunit'))

end Local

section Remark

variable (B E : Type*) [CommRing B]

/-- The permutation action of `Equiv.Perm E` on `E → B`, i.e. on `Y × E`:
`(σ • f) e = f (σ⁻¹ e)`. -/
@[instance_reducible]
def permAction : MulSemiringAction (Equiv.Perm E) (E → B) where
  smul σ f e := f (σ⁻¹ e)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

attribute [local instance] permAction

lemma permAction_apply (σ : Equiv.Perm E) (f : E → B) (e : E) : (σ • f) e = f (σ⁻¹ e) := rfl

instance : SMulCommClass (Equiv.Perm E) B (E → B) := ⟨fun _ _ _ ↦ rfl⟩

variable {B E}

/-- V.2.5: for a subgroup `G` of the permutations of a set `E` acting transitively, the
invariants of `Y × E` are `Y`: `(E → B)^G = B`. -/
theorem isInvariant_pi_of_transitive (G : Subgroup (Equiv.Perm E))
    (hG : ∀ e e' : E, ∃ σ ∈ G, σ e = e') [Nonempty E] :
    Algebra.IsInvariant B (E → B) G := by
  refine ⟨fun f hf ↦ ⟨f (Classical.arbitrary E), funext fun e ↦ ?_⟩⟩
  obtain ⟨σ, hσ, he⟩ := hG e (Classical.arbitrary E)
  have := congr_fun (hf ⟨σ⁻¹, G.inv_mem hσ⟩) e
  change f (σ e) = f e at this
  rw [he] at this
  simpa only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using this

/-- V.2.5: the permutation group of a finite set `E` with at least three elements acts on the
étale covering `Y × E` of `Y = (Y × E)/G` with nontrivial inertia at every point: the hypothesis
that `X` be connected cannot be dropped from V.2.4. -/
theorem exists_ne_one_mem_inertia_pi [Nontrivial B] {a b c : E} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) [Finite E] (Q : Ideal (E → B)) [hQ : Q.IsPrime] :
    ∃ g : Equiv.Perm E, g ≠ 1 ∧ g ∈ Q.inertia (Equiv.Perm E) := by
  classical
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨e, he⟩ : ∃ e : E, Pi.single e (1 : B) ∉ Q := by
    by_contra! h
    exact hQ.ne_top ((Ideal.eq_top_iff_one _).mpr (by
      rw [← Finset.univ_sum_single (1 : E → B)]
      exact Q.sum_mem fun e _ ↦ by simpa using h e))
  -- a transposition fixing `e`
  obtain ⟨x, y, hxy, hxe, hye⟩ : ∃ x y : E, x ≠ y ∧ x ≠ e ∧ y ≠ e := by
    by_cases hae : a = e
    · exact ⟨b, c, hbc, hae ▸ hab.symm, hae ▸ hac.symm⟩
    by_cases hbe : b = e
    · exact ⟨a, c, hac, hbe ▸ hab, hbe ▸ hbc.symm⟩
    · exact ⟨a, b, hab, hae, hbe⟩
  have hswap : Equiv.swap x y ≠ 1 := fun h ↦ hxy (by
    have := congr($h x)
    rw [Equiv.swap_apply_left, Equiv.Perm.one_apply] at this
    exact this.symm)
  refine ⟨Equiv.swap x y, hswap, fun f ↦ ?_⟩
  have h0 : (Equiv.swap x y • f - f) * Pi.single e 1 = 0 := by
    ext e'
    by_cases h : e' = e
    · subst h
      simp [permAction_apply, Equiv.swap_apply_of_ne_of_ne hxe.symm hye.symm]
    · simp [Pi.single_eq_of_ne h]
  exact (hQ.mem_or_mem (h0 ▸ Q.zero_mem)).resolve_right he

/-- V.2.5: `E → B` is étale over `B` (a finite product of copies of `B`). -/
example [Finite E] : Algebra.Etale B (E → B) := inferInstance

/-- V.2.5: if `G` is a proper subgroup of the permutations of `E`, some `B`-automorphism of
`Y × E` does not come from `G` (so `G` is not the full automorphism group, although it may act
transitively). -/
theorem exists_algEquiv_not_mem_pi [Nontrivial B] (G : Subgroup (Equiv.Perm E)) (hG : G ≠ ⊤) :
    ∃ u : (E → B) ≃ₐ[B] (E → B), ∀ g ∈ G, ∃ f : E → B, g • f ≠ u f := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ, σ ∉ G := by
    by_contra! h
    exact hG (eq_top_iff.mpr fun σ _ ↦ h σ)
  refine ⟨MulSemiringAction.toAlgEquiv B (E → B) σ, fun g hg ↦ ?_⟩
  by_contra! h
  have hσg : σ = g := by
    ext x
    have := congr_fun (h (Pi.single x 1)) (g x)
    have hgx : g⁻¹ (g x) = x := by simp
    simp only [permAction_apply, MulSemiringAction.toAlgEquiv_apply, hgx,
      Pi.single_eq_same] at this
    by_contra hne
    have h1 : σ⁻¹ (g x) ≠ x := fun h' ↦ hne (by
      have := congr_arg σ h'
      rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at this
      exact this.symm)
    rw [Pi.single_eq_of_ne h1] at this
    exact one_ne_zero this
  exact hσ (hσg ▸ hg)

end Remark

end SGA.SGA1.ExposeV
