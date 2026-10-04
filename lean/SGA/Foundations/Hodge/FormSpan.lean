/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.KahlerPositivity
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Forms of type `(p, q)` in the coordinates `ζ_I ∧ ζ̄_J`

Let `u` be a complex basis of the finite-dimensional complex vector space `E`, with coordinates
`ζⱼ` and conjugates `ζ̄ⱼ` (`Hodge.coordForm`, `Hodge.conjCoordForm`), real `1`-forms with complex
values, i.e. elements of `V = E →L[ℝ] ℂ`. In mathlib's exterior algebra `⋀ V` write
`ζ_I = ζ_{i₀} ∧ ⋯` and `ζ̄_J` for finite sets `I`, `J` of indices listed in increasing order
(`Hodge.zetaMulti`, `Hodge.zetaBarMulti`).

* `Hodge.eq_sum_coordForm_conjCoordForm`: every `φ ∈ V` is `∑ⱼ aⱼ ζⱼ + bⱼ ζ̄ⱼ`;
* `ContinuousAlternatingMap.exists_toForms_eq`: every real alternating `ℂ`-valued `k`-form is
  `toForms y` for some `y ∈ ⋀ᵏ V` (expansion in a real basis);
* `Hodge.exteriorPower_le_span_zetaMulti`: `⋀ᵏ V` is spanned by the `ζ_I ∧ ζ̄_J`, `|I| + |J| = k`;
* `Hodge.isOfType_toForms_zetaMulti_mul`: `ζ_I ∧ ζ̄_J` has type `(|I|, |J|)`;
* `Hodge.IsOfType.eq_sum_of_eq_sum`: **type projection**. If a form of type `(p, q)` is a
  combination of forms of types `(aᵢ, bᵢ)` with `aᵢ + bᵢ = p + q`, it is the combination of the
  terms with `aᵢ = p` (average over roots of unity);
* `Hodge.IsOfType.exists_eq_toForms_sum`: **a form of type `(p, q)` is
  `∑_{|I| = p, |J| = q} c_{IJ} ζ_I ∧ ζ̄_J`**.

Reference: D. Huybrechts, *Complex geometry*, §1.2.
-/

noncomputable section

open ComplexConjugate ContinuousAlternatingMap ExteriorAlgebra

namespace Hodge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {n : ℕ}
  (u : Module.Basis (Fin n) ℂ E)

/-! ### `1`-forms -/

/-- Every real `1`-form with complex values is `∑ⱼ aⱼ ζⱼ + bⱼ ζ̄ⱼ`, with
`aⱼ = (φ(uⱼ) - i φ(i uⱼ)) / 2` and `bⱼ = (φ(uⱼ) + i φ(i uⱼ)) / 2`. -/
theorem eq_sum_coordForm_conjCoordForm (φ : E →L[ℝ] ℂ) :
    φ = ∑ j, ((φ (u j) - Complex.I * φ (Complex.I • u j)) / 2) • coordForm u j +
      ∑ j, ((φ (u j) + Complex.I * φ (Complex.I • u j)) / 2) • conjCoordForm u j := by
  have aux : ∀ x y c : ℂ, (c.re : ℂ) * x + (c.im : ℂ) * y =
      (x - Complex.I * y) / 2 * c + (x + Complex.I * y) / 2 * conj c := by
    intro x y c
    conv_rhs => rw [← Complex.re_add_im c]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring
  ext v
  simp only [_root_.add_apply, _root_.sum_apply, _root_.smul_apply, coordForm_apply,
    conjCoordForm_apply, smul_eq_mul]
  conv_lhs => rw [← u.sum_repr v]
  rw [_root_.map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  set c := u.repr v j
  have hc : c • u j = c.re • u j + c.im • (Complex.I • u j) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [Module.Basis.coord_apply, hc, map_add, map_smul, map_smul, Complex.real_smul,
    Complex.real_smul]
  exact aux _ _ c

/-! ### Products `ζ_I ∧ ζ̄_J` -/

/-- `ζ_I = ζ_{i₀} ∧ ⋯ ∧ ζ_{i_{p-1}}` for `I = {i₀ < ⋯ < i_{p-1}}`. -/
def zetaMulti (I : Finset (Fin n)) : ExteriorAlgebra ℂ (E →L[ℝ] ℂ) :=
  ιMulti ℂ I.card (coordForm u ∘ I.orderEmbOfFin rfl)

/-- `ζ̄_J = ζ̄_{j₀} ∧ ⋯ ∧ ζ̄_{j_{q-1}}` for `J = {j₀ < ⋯ < j_{q-1}}`. -/
def zetaBarMulti (J : Finset (Fin n)) : ExteriorAlgebra ℂ (E →L[ℝ] ℂ) :=
  ιMulti ℂ J.card (conjCoordForm u ∘ J.orderEmbOfFin rfl)

omit [FiniteDimensional ℂ E] in
lemma ιMulti_family_eq {k : ℕ} (v : Fin n → E →L[ℝ] ℂ) (s : Set.powersetCard (Fin n) k) :
    ExteriorAlgebra.ιMulti_family ℂ k v s =
      ιMulti ℂ (s.val.card) (v ∘ s.val.orderEmbOfFin rfl) := by
  obtain ⟨s, hs⟩ := s
  have hs' : s.card = k := hs
  subst hs'
  rfl

lemma zetaMulti_eq_ιMulti_family {k : ℕ} (s : Set.powersetCard (Fin n) k) :
    zetaMulti u s.val = ExteriorAlgebra.ιMulti_family ℂ k (coordForm u) s :=
  (ιMulti_family_eq _ s).symm

lemma zetaBarMulti_eq_ιMulti_family {k : ℕ} (s : Set.powersetCard (Fin n) k) :
    zetaBarMulti u s.val = ExteriorAlgebra.ιMulti_family ℂ k (conjCoordForm u) s :=
  (ιMulti_family_eq _ s).symm

lemma zetaMulti_mem (I : Finset (Fin n)) : zetaMulti u I ∈ ⋀[ℂ]^(I.card) (E →L[ℝ] ℂ) :=
  ιMulti_mem_exteriorPower _

lemma zetaBarMulti_mem (J : Finset (Fin n)) :
    zetaBarMulti u J ∈ ⋀[ℂ]^(J.card) (E →L[ℝ] ℂ) :=
  ιMulti_mem_exteriorPower _

lemma zetaMulti_empty : zetaMulti u ∅ = 1 :=
  ιMulti_zero_apply _

lemma zetaBarMulti_empty : zetaBarMulti u ∅ = 1 :=
  ιMulti_zero_apply _

lemma ι_coordForm_eq (j : Fin n) : ι ℂ (coordForm u j) = zetaMulti u {j} := by
  simp only [zetaMulti, ιMulti_apply, Finset.card_singleton, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one, Function.comp_apply]
  congr 2
  exact (Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)).symm

lemma ι_conjCoordForm_eq (j : Fin n) : ι ℂ (conjCoordForm u j) = zetaBarMulti u {j} := by
  simp only [zetaBarMulti, ιMulti_apply, Finset.card_singleton, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one, Function.comp_apply]
  congr 2
  exact (Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)).symm

/-- `ζⱼ ∧ ζ_I = 0` if `j ∈ I`. -/
lemma ι_mul_zetaMulti_of_mem {j : Fin n} {I : Finset (Fin n)} (hj : j ∈ I) :
    ι ℂ (coordForm u j) * zetaMulti u I = 0 := by
  rw [ι_coordForm_eq]
  let sj : Set.powersetCard (Fin n) 1 := ⟨{j}, by simp⟩
  let sI : Set.powersetCard (Fin n) I.card := ⟨I, rfl⟩
  rw [show zetaMulti u {j} = zetaMulti u sj.val from rfl,
    show zetaMulti u I = zetaMulti u sI.val from rfl, zetaMulti_eq_ιMulti_family,
    zetaMulti_eq_ιMulti_family]
  exact ιMulti_family_mul_of_not_disjoint ℂ _ _ _ (by
    rw [Finset.not_disjoint_iff]
    exact ⟨j, Finset.mem_singleton_self j, hj⟩)

/-- `ζⱼ ∧ ζ_I = ± ζ_{I ∪ {j}}` if `j ∉ I`. -/
lemma ι_mul_zetaMulti_of_notMem {j : Fin n} {I : Finset (Fin n)} (hj : j ∉ I) :
    ∃ s : ℤˣ, ι ℂ (coordForm u j) * zetaMulti u I = s • zetaMulti u (insert j I) := by
  rw [ι_coordForm_eq]
  let sj : Set.powersetCard (Fin n) 1 := ⟨{j}, by simp⟩
  let sI : Set.powersetCard (Fin n) I.card := ⟨I, rfl⟩
  rw [show zetaMulti u {j} = zetaMulti u sj.val from rfl,
    show zetaMulti u I = zetaMulti u sI.val from rfl, zetaMulti_eq_ιMulti_family,
    zetaMulti_eq_ιMulti_family]
  have hd : Disjoint sj.val sI.val := Finset.disjoint_singleton_left.2 hj
  refine ⟨(Set.powersetCard.permOfDisjoint hd).sign, ?_⟩
  rw [ιMulti_family_mul_of_disjoint ℂ _ _ _ hd, ← zetaMulti_eq_ιMulti_family]
  congr 2
  ext x
  simp [Set.powersetCard.coe_disjUnion, sj, sI]

/-- `ζ̄ⱼ ∧ ζ̄_J = 0` if `j ∈ J`. -/
lemma ι_mul_zetaBarMulti_of_mem {j : Fin n} {J : Finset (Fin n)} (hj : j ∈ J) :
    ι ℂ (conjCoordForm u j) * zetaBarMulti u J = 0 := by
  rw [ι_conjCoordForm_eq]
  let sj : Set.powersetCard (Fin n) 1 := ⟨{j}, by simp⟩
  let sJ : Set.powersetCard (Fin n) J.card := ⟨J, rfl⟩
  rw [show zetaBarMulti u {j} = zetaBarMulti u sj.val from rfl,
    show zetaBarMulti u J = zetaBarMulti u sJ.val from rfl, zetaBarMulti_eq_ιMulti_family,
    zetaBarMulti_eq_ιMulti_family]
  exact ιMulti_family_mul_of_not_disjoint ℂ _ _ _ (by
    rw [Finset.not_disjoint_iff]
    exact ⟨j, Finset.mem_singleton_self j, hj⟩)

/-- `ζ̄ⱼ ∧ ζ̄_J = ± ζ̄_{J ∪ {j}}` if `j ∉ J`. -/
lemma ι_mul_zetaBarMulti_of_notMem {j : Fin n} {J : Finset (Fin n)} (hj : j ∉ J) :
    ∃ s : ℤˣ, ι ℂ (conjCoordForm u j) * zetaBarMulti u J = s • zetaBarMulti u (insert j J) := by
  rw [ι_conjCoordForm_eq]
  let sj : Set.powersetCard (Fin n) 1 := ⟨{j}, by simp⟩
  let sJ : Set.powersetCard (Fin n) J.card := ⟨J, rfl⟩
  rw [show zetaBarMulti u {j} = zetaBarMulti u sj.val from rfl,
    show zetaBarMulti u J = zetaBarMulti u sJ.val from rfl, zetaBarMulti_eq_ιMulti_family,
    zetaBarMulti_eq_ιMulti_family]
  have hd : Disjoint sj.val sJ.val := Finset.disjoint_singleton_left.2 hj
  refine ⟨(Set.powersetCard.permOfDisjoint hd).sign, ?_⟩
  rw [ιMulti_family_mul_of_disjoint ℂ _ _ _ hd, ← zetaBarMulti_eq_ιMulti_family]
  congr 2
  ext x
  simp [Set.powersetCard.coe_disjUnion, sj, sJ]

omit [FiniteDimensional ℂ E] in
/-- `ι w ∧ x = (-1)ᵏ x ∧ ι w` for `x = ιMulti v` of degree `k`. -/
lemma ι_mul_ιMulti_comm {k : ℕ} (w : E →L[ℝ] ℂ) (v : Fin k → E →L[ℝ] ℂ) :
    ι ℂ w * ιMulti ℂ k v = ((-1 : ℂ) ^ k) • (ιMulti ℂ k v * ι ℂ w) := by
  rw [ιMulti_mul_ι, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

/-- The products `ζ_I ∧ ζ̄_J` with `|I| + |J| = k`. -/
def zetaProdSet (k : ℕ) : Set (ExteriorAlgebra ℂ (E →L[ℝ] ℂ)) :=
  {x | ∃ I J : Finset (Fin n), I.card + J.card = k ∧ x = zetaMulti u I * zetaBarMulti u J}

/-- **`⋀ᵏ V` is spanned by the `ζ_I ∧ ζ̄_J`, `|I| + |J| = k`.** -/
theorem exteriorPower_le_span_zetaMulti (k : ℕ) :
    ⋀[ℂ]^k (E →L[ℝ] ℂ) ≤ Submodule.span ℂ (zetaProdSet u k) := by
  induction k with
  | zero =>
    change LinearMap.range (ι ℂ : (E →L[ℝ] ℂ) →ₗ[ℂ] _) ^ 0 ≤ _
    rw [pow_zero, Submodule.one_eq_span, Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨∅, ∅, rfl, by rw [zetaMulti_empty, zetaBarMulti_empty, one_mul]⟩
  | succ k ih =>
    change LinearMap.range (ι ℂ : (E →L[ℝ] ℂ) →ₗ[ℂ] _) ^ (k + 1) ≤ _
    rw [pow_succ']
    refine Submodule.mul_le.2 fun a ha b hb ↦ ?_
    obtain ⟨φ, rfl⟩ := ha
    have hb' := ih hb
    clear hb
    -- it suffices to treat generators `b = ζ_I ζ̄_J`
    induction hb' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨I, J, hIJ, rfl⟩ := hx
      rw [eq_sum_coordForm_conjCoordForm u φ, map_add, _root_.map_sum, _root_.map_sum,
        add_mul, Finset.sum_mul, Finset.sum_mul]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun j _ ↦ ?_)
        (Submodule.sum_mem _ fun j _ ↦ ?_)
      · rw [map_smul, smul_mul_assoc]
        refine Submodule.smul_mem _ _ ?_
        rw [← mul_assoc]
        by_cases hj : j ∈ I
        · rw [ι_mul_zetaMulti_of_mem u hj, zero_mul]
          exact Submodule.zero_mem _
        · obtain ⟨s, hs⟩ := ι_mul_zetaMulti_of_notMem u hj
          rw [hs, smul_mul_assoc, Units.smul_def]
          refine Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ?_)
          refine ⟨insert j I, J, ?_, rfl⟩
          rw [Finset.card_insert_of_notMem hj]
          omega
      · rw [map_smul, smul_mul_assoc]
        refine Submodule.smul_mem _ _ ?_
        rw [← mul_assoc, show zetaMulti u I = ιMulti ℂ I.card _ from rfl, ι_mul_ιMulti_comm,
          smul_mul_assoc, mul_assoc]
        refine Submodule.smul_mem _ _ ?_
        by_cases hj : j ∈ J
        · rw [ι_mul_zetaBarMulti_of_mem u hj, mul_zero]
          exact Submodule.zero_mem _
        · obtain ⟨s, hs⟩ := ι_mul_zetaBarMulti_of_notMem u hj
          rw [hs, mul_smul_comm, Units.smul_def]
          refine Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ?_)
          refine ⟨I, insert j J, ?_, rfl⟩
          rw [Finset.card_insert_of_notMem hj]
          omega
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-! ### Expansion in a real basis; surjectivity of `toForms` -/

section Real

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {d : ℕ}

/-- The `i`-th coordinate of a real basis, as a real `1`-form with complex values. -/
def realCoordForm (e : Module.Basis (Fin d) ℝ F) (i : Fin d) : F →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (e.coord i).toContinuousLinearMap

/-- **Expansion of a real alternating `ℂ`-valued `k`-form in a real basis**:
`α = ∑_{|S| = k} α (e_S) ξ_S` with `ξ` the coordinates of `e`. -/
theorem eq_sum_detForm_realCoordForm (e : Module.Basis (Fin d) ℝ F) {k : ℕ}
    (α : F [⋀^Fin k]→L[ℝ] ℂ) :
    α = ∑ S : Set.powersetCard (Fin d) k,
      α (e ∘ Set.powersetCard.ofFinEmbEquiv.symm S) •
        detForm (realCoordForm e ∘ Set.powersetCard.ofFinEmbEquiv.symm S) := by
  let G : ⋀[ℝ]^k F →ₗ[ℝ] ℂ := exteriorPower.alternatingMapLinearEquiv α.toAlternatingMap
  let B := e.exteriorPower k
  ext v
  have hG : G (exteriorPower.ιMulti ℝ k v) = α v := by
    simp [G, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rw [← hG, ← B.sum_repr (exteriorPower.ιMulti ℝ k v), _root_.map_sum,
    ContinuousAlternatingMap.sum_apply]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [map_smul, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    ContinuousAlternatingMap.smul_apply, detForm_apply_eq_det, smul_eq_mul, Complex.real_smul,
    mul_comm]
  congr 1
  · simp [G, B, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  · exact (RingHom.map_det Complex.ofRealHom _).trans rfl

end Real

/-- **Every real alternating `ℂ`-valued `k`-form is `toForms y` for some `y ∈ ⋀ᵏ V`.** -/
theorem exists_toForms_eq {k : ℕ} (α : E [⋀^Fin k]→L[ℝ] ℂ) :
    ∃ y ∈ ⋀[ℂ]^k (E →L[ℝ] ℂ), toForms E ℂ y k = α := by
  let e := Module.finBasis ℝ E
  refine ⟨∑ S : Set.powersetCard (Fin (Module.finrank ℝ E)) k,
    α (e ∘ Set.powersetCard.ofFinEmbEquiv.symm S) •
      ιMulti ℂ k (realCoordForm e ∘ Set.powersetCard.ofFinEmbEquiv.symm S),
    Submodule.sum_mem _ fun S _ ↦ Submodule.smul_mem _ _ (ιMulti_mem_exteriorPower _), ?_⟩
  conv_rhs => rw [eq_sum_detForm_realCoordForm e α]
  simp only [_root_.map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, toForms_ιMulti_self]

/-! ### Types of `ζ_I ∧ ζ̄_J` -/

omit [FiniteDimensional ℂ E] in
/-- `φ₀ ∧ ⋯ ∧ φ_{k-1}` has type `(k, 0)` if every `φᵢ` is complex linear. -/
lemma isOfType_detForm_of_linear {k : ℕ} {φ : Fin k → E →L[ℝ] ℂ}
    (hφ : ∀ i (c : ℂ) v, φ i (c • v) = c * φ i v) : IsOfType k 0 (detForm φ) := by
  intro c v
  simp only [detForm_apply, pow_zero, mul_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp only [Pi.smul_apply, hφ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Units.smul_def, zsmul_eq_mul]
  ring

omit [FiniteDimensional ℂ E] in
/-- `φ₀ ∧ ⋯ ∧ φ_{k-1}` has type `(0, k)` if every `φᵢ` is complex antilinear. -/
lemma isOfType_detForm_of_antilinear {k : ℕ} {φ : Fin k → E →L[ℝ] ℂ}
    (hφ : ∀ i (c : ℂ) v, φ i (c • v) = conj c * φ i v) : IsOfType 0 k (detForm φ) := by
  intro c v
  simp only [detForm_apply, pow_zero, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp only [Pi.smul_apply, hφ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Units.smul_def, zsmul_eq_mul]
  ring

lemma toForms_zetaMulti_mul (I J : Finset (Fin n)) :
    toForms E ℂ (zetaMulti u I * zetaBarMulti u J) (I.card + J.card) =
      detForm (coordForm u ∘ I.orderEmbOfFin rfl) ⋏
        detForm (conjCoordForm u ∘ J.orderEmbOfFin rfl) := by
  rw [toForms_mul (zetaMulti_mem u I) (zetaBarMulti_mem u J), zetaMulti, zetaBarMulti,
    toForms_ιMulti_self, toForms_ιMulti_self]

/-- `ζ_I ∧ ζ̄_J` has type `(|I|, |J|)`. -/
theorem isOfType_toForms_zetaMulti_mul (I J : Finset (Fin n)) :
    IsOfType I.card J.card (toForms E ℂ (zetaMulti u I * zetaBarMulti u J) (I.card + J.card)) := by
  rw [toForms_zetaMulti_mul]
  have h1 : IsOfType I.card 0 (detForm (coordForm u ∘ I.orderEmbOfFin rfl)) :=
    isOfType_detForm_of_linear fun i c v ↦ by simp
  have h2 : IsOfType 0 J.card (detForm (conjCoordForm u ∘ J.orderEmbOfFin rfl)) :=
    isOfType_detForm_of_antilinear fun i c v ↦ by simp
  simpa using h1.wedge h2

/-! ### Type projection -/

omit [FiniteDimensional ℂ E] in
/-- **Type projection**: if a form of type `(p, q)` is a combination `∑ᵢ cᵢ tᵢ` of forms `tᵢ` of
types `(aᵢ, bᵢ)` with `aᵢ + bᵢ = p + q`, it equals the sum of the terms with `aᵢ = p`. -/
theorem IsOfType.eq_sum_filter {k p q : ℕ} (hk : p + q = k) {α : E [⋀^Fin k]→L[ℝ] ℂ}
    (hα : IsOfType p q α) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (t : ι → E [⋀^Fin k]→L[ℝ] ℂ) (a b : ι → ℕ) (ht : ∀ i, IsOfType (a i) (b i) (t i))
    (hab : ∀ i, a i + b i = k) (h : α = ∑ i ∈ s, c i • t i) :
    α = ∑ i ∈ s with a i = p, c i • t i := by
  classical
  set N := 2 * k + 1 with hN
  have hN0 : N ≠ 0 := by omega
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hN0
  have hω0 : ω ≠ 0 := hω.ne_zero hN0
  have hconj : conj ω = ω⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hω.norm'_eq_one hN0]
    simp
  -- scaling a form of type `(a, b)` by `ωʲ`
  have hscale : ∀ (a' b' : ℕ) (t' : E [⋀^Fin k]→L[ℝ] ℂ), IsOfType a' b' t' → ∀ (j : ℕ) v,
      t' ((ω ^ j) • v) = ω ^ ((j : ℤ) * ((a' : ℤ) - b')) * t' v := by
    intro a' b' t' ht' j v
    rw [ht', map_pow, hconj, show ((j : ℤ) * ((a' : ℤ) - b')) = ((j * a' : ℕ) : ℤ) - (j * b' : ℕ) by
      push_cast; ring, zpow_sub₀ hω0, zpow_natCast, zpow_natCast, inv_pow, pow_mul, pow_mul,
      div_eq_mul_inv, inv_pow]
  -- the geometric sums
  have hgeom : ∀ d : ℤ, |d| < N →
      ∑ j ∈ Finset.range N, ω ^ ((j : ℤ) * d) = if d = 0 then (N : ℂ) else 0 := by
    intro d hd
    split_ifs with hd0
    · simp [hd0]
    · have hne : ω ^ d ≠ 1 := by
        rw [Ne, hω.zpow_eq_one_iff_dvd]
        intro hdvd
        have := Int.le_of_dvd (abs_pos.2 hd0) ((dvd_abs _ _).2 hdvd)
        omega
      have : ∑ j ∈ Finset.range N, ω ^ ((j : ℤ) * d) = ∑ j ∈ Finset.range N, (ω ^ d) ^ j := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [mul_comm, zpow_mul, zpow_natCast]
      rw [this, geom_sum_eq hne, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hω.pow_eq_one, one_zpow, sub_self, zero_div]
  ext v
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  apply mul_left_cancel₀ hN'
  have hα' : ∀ j : ℕ, α ((ω ^ j) • v) = ω ^ ((j : ℤ) * ((p : ℤ) - q)) * α v :=
    fun j ↦ hscale p q α hα j v
  calc (N : ℂ) * α v
      = ∑ j ∈ Finset.range N, ω ^ (-((j : ℤ) * ((p : ℤ) - q))) * α ((ω ^ j) • v) := by
        simp only [hα', ← mul_assoc, ← zpow_add₀ hω0, neg_add_cancel, zpow_zero, one_mul,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ∑ i ∈ s, c i * (∑ j ∈ Finset.range N,
          ω ^ ((j : ℤ) * (((a i : ℤ) - b i) - ((p : ℤ) - q)))) * t i v := by
        rw [h]
        simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul, Finset.mul_sum, hscale _ _ _ (ht _)]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [show ((j : ℤ) * (((a i : ℤ) - b i) - ((p : ℤ) - q))) =
          (j : ℤ) * ((a i : ℤ) - b i) + (-((j : ℤ) * ((p : ℤ) - q))) by ring, zpow_add₀ hω0]
        ring
    _ = ∑ i ∈ s, c i * (if a i = p then (N : ℂ) else 0) * t i v := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hi := hab i
        rw [hgeom _ (by rw [abs_lt]; constructor <;> omega)]
        congr 2
        apply if_congr _ rfl rfl
        constructor <;> intro h' <;> omega
    _ = (N : ℂ) * (∑ i ∈ s with a i = p, c i • t i) v := by
        rw [ContinuousAlternatingMap.sum_apply, Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        split_ifs
        · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
          ring
        · simp

/-! ### Forms of type `(p, q)` -/

/-- `toForms (ζ_I ∧ ζ̄_J)` in a degree `k = |I| + |J|` has type `(|I|, |J|)`. -/
theorem isOfType_toForms_zetaMulti_mul' {k : ℕ} (I J : Finset (Fin n)) (h : I.card + J.card = k) :
    IsOfType I.card J.card (toForms E ℂ (zetaMulti u I * zetaBarMulti u J) k) := by
  rw [toForms_congr_degree _ h]
  exact (isOfType_toForms_zetaMulti_mul u I J).domDomCongr _

/-- **A form of type `(p, q)` is `∑_{|I| = p, |J| = q} c_{IJ} ζ_I ∧ ζ̄_J`.** -/
theorem IsOfType.exists_eq_toForms_sum {p q k : ℕ} (hk : p + q = k) {α : E [⋀^Fin k]→L[ℝ] ℂ}
    (hα : IsOfType p q α) :
    ∃ c : Set.powersetCard (Fin n) p → Set.powersetCard (Fin n) q → ℂ,
      α = toForms E ℂ (∑ I, ∑ J, c I J • (zetaMulti u I.val * zetaBarMulti u J.val)) k := by
  classical
  obtain ⟨y, hy, rfl⟩ := exists_toForms_eq (E := E) α
  let X := {IJ : Finset (Fin n) × Finset (Fin n) // IJ.1.card + IJ.2.card = k}
  let v : X → ExteriorAlgebra ℂ (E →L[ℝ] ℂ) := fun x ↦ zetaMulti u x.1.1 * zetaBarMulti u x.1.2
  have hrange : zetaProdSet u k = Set.range v := by
    ext z
    constructor
    · rintro ⟨I, J, hIJ, rfl⟩
      exact ⟨⟨(I, J), hIJ⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1.1, x.1.2, x.2, rfl⟩
  have hy' := exteriorPower_le_span_zetaMulti u k hy
  rw [hrange, Submodule.mem_span_range_iff_exists_fun] at hy'
  obtain ⟨c, hc⟩ := hy'
  have hsum : toForms E ℂ y k = ∑ x : X, c x • toForms E ℂ (v x) k := by
    rw [← hc, _root_.map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply]
  have hproj := (show IsOfType p q (toForms E ℂ y k) from hα).eq_sum_filter hk Finset.univ c
    (fun x ↦ toForms E ℂ (v x) k) (fun x ↦ x.1.1.card) (fun x ↦ x.1.2.card)
    (fun x ↦ isOfType_toForms_zetaMulti_mul' u x.1.1 x.1.2 x.2) (fun x ↦ x.2) hsum
  refine ⟨fun I J ↦ c ⟨(I.val, J.val), by simp only [Set.powersetCard.card_eq]; exact hk⟩, ?_⟩
  rw [hproj, _root_.map_sum, Finset.sum_apply]
  simp only [_root_.map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  rw [← Finset.sum_product']
  refine Finset.sum_bij' (fun x hx ↦ (⟨x.1.1, by
      rw [Set.powersetCard.mem_iff]; exact (Finset.mem_filter.1 hx).2⟩,
      ⟨x.1.2, by
      rw [Set.powersetCard.mem_iff]; have := x.2; have := (Finset.mem_filter.1 hx).2; omega⟩))
    (fun IJ _ ↦ ⟨(IJ.1.val, IJ.2.val), by simp only [Set.powersetCard.card_eq]; exact hk⟩)
    (fun _ _ ↦ Finset.mem_univ _) (fun IJ _ ↦ ?_) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, Set.powersetCard.card_eq IJ.1⟩

end Hodge
