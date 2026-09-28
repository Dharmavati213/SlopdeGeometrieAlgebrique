/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Regular.RegularSequence
import SGA.SGA1.ExposeII.RegularImmersion

/-!
# SGA 1, Exposé II, II.4.14: regular sequences are regular systems of generators

The remarks II.4.14 recall that, in a local ring, `x₁,…,xₙ ∈ 𝔪` is a regular system of
generators iff it is an `A`-sequence in the sense of Serre (a regular sequence). We prove the
direction valid in every ring (Matsumura, *Commutative Ring Theory*, Thm 16.2 (i); Stacks 061M):
a weakly regular sequence (mathlib's `RingTheory.Sequence.IsWeaklyRegular`) is a regular system
of generators; and the converse in a noetherian local ring (Matsumura, Thm 16.3):
`isRegularSystemOfGenerators_iff_isWeaklyRegular`. For the converse, `x₁` is a nonzerodivisor by
Krull's intersection theorem, and the images of `x₂,…,xₙ` form a regular system of generators
modulo `x₁`.
-/

open MvPolynomial
open scoped Pointwise

namespace SGA.SGA1.ExposeII

variable {A : Type*} [CommRing A] {ι : Type*}

/-- `J^d` consists of the values at `x` of the homogeneous polynomials of degree `d`. -/
lemma mem_span_pow_iff_exists_isHomogeneous (x : ι → A) (d : ℕ) (z : A) :
    z ∈ Ideal.span (Set.range x) ^ d ↔
      ∃ W : MvPolynomial ι A, W.IsHomogeneous d ∧ eval x W = z := by
  constructor
  · intro hz
    rw [← map_eval_idealOfVars, ← Ideal.map_pow, pow_idealOfVars_eq_span, Ideal.map_span] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨_, ⟨m, hm, rfl⟩, rfl⟩ := hz
      exact ⟨monomial m 1, isHomogeneous_monomial _ hm, rfl⟩
    | zero => exact ⟨0, isHomogeneous_zero _ _ _, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨W, hW, rfl⟩ := ha
      obtain ⟨W', hW', rfl⟩ := hb
      exact ⟨W + W', hW.add hW', map_add _ _ _⟩
    | smul a b _ hb =>
      obtain ⟨W, hW, rfl⟩ := hb
      exact ⟨C a * W, hW.C_mul a, by simp⟩
  · rintro ⟨W, hW, rfl⟩
    refine (mem_span_pow_iff_exists x d _).mpr ⟨W, ?_, rfl⟩
    rw [mem_pow_idealOfVars_iff]
    intro m hm
    have := hW (mem_support_iff.mp hm)
    rw [Finsupp.degree_eq_weight_one]
    exact this.ge

/-- `(a + b)^{k+1} ⊆ a^{k+1} + b (a + b)^k`. -/
private lemma sup_pow_succ_le (a b : Ideal A) (k : ℕ) :
    (a ⊔ b) ^ (k + 1) ≤ a ^ (k + 1) ⊔ b * (a ⊔ b) ^ k := by
  induction k with
  | zero => simp [Ideal.mul_top]
  | succ k ih =>
    have h₁ : a ^ (k + 1) * (a ⊔ b) ≤ a ^ (k + 1 + 1) ⊔ b * (a ⊔ b) ^ (k + 1) := by
      rw [Ideal.mul_sup, ← pow_succ]
      refine sup_le_sup_left ?_ _
      rw [mul_comm]
      exact Ideal.mul_mono_right (Ideal.pow_right_mono le_sup_left _)
    have h₂ : b * (a ⊔ b) ^ k * (a ⊔ b) = b * (a ⊔ b) ^ (k + 1) := by
      rw [mul_assoc, ← pow_succ]
    calc (a ⊔ b) ^ (k + 1 + 1) = (a ⊔ b) ^ (k + 1) * (a ⊔ b) := pow_succ _ _
      _ ≤ (a ^ (k + 1) ⊔ b * (a ⊔ b) ^ k) * (a ⊔ b) := Ideal.mul_mono_left ih
      _ = a ^ (k + 1) * (a ⊔ b) ⊔ b * (a ⊔ b) ^ k * (a ⊔ b) := Ideal.sup_mul _ _ _
      _ ≤ a ^ (k + 1 + 1) ⊔ b * (a ⊔ b) ^ (k + 1) := by
        rw [h₂]
        exact sup_le h₁ le_sup_right


private lemma degree_option (n : Option ι →₀ ℕ) : n.degree = n none + n.some.degree :=
  Finsupp.sum_option_index n (fun _ e ↦ e) (fun _ ↦ rfl) fun _ _ _ ↦ rfl

/-- The value at `x` of a homogeneous polynomial of degree `0` is its constant coefficient. -/
lemma eval_eq_coeff_zero_of_isHomogeneous_zero (x : ι → A) {W : MvPolynomial ι A}
    (hW : W.IsHomogeneous 0) : eval x W = W.coeff 0 := by
  classical
  rw [eval_eq, Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0
    exact absurd (hW.coeff_eq_zero fun h ↦ hb0 ((Finsupp.degree_eq_zero_iff b).mp h))
      (mem_support_iff.mp hb)
  · intro h
    simp [notMem_support_iff.mp h]

variable {x : ι → A} {y : A}

/-- If `x` is a regular system of generators of `I'` and `y` is a nonzerodivisor modulo `I'`,
then `y` is a nonzerodivisor modulo every power of `I'`. -/
lemma mem_pow_of_mul_mem_pow (hx : IsRegularSystemOfGenerators x)
    (hy : ∀ m, y * m ∈ Ideal.span (Set.range x) → m ∈ Ideal.span (Set.range x)) (d : ℕ) (m : A)
    (hm : y * m ∈ Ideal.span (Set.range x) ^ d) : m ∈ Ideal.span (Set.range x) ^ d := by
  classical
  induction d generalizing m with
  | zero => simp
  | succ d ih =>
    set I' := Ideal.span (Set.range x)
    obtain ⟨W, hW, rfl⟩ := (mem_span_pow_iff_exists_isHomogeneous x d m).mp
      (ih m (Ideal.pow_le_pow_right d.le_succ hm))
    have hcoeff (μ : ι →₀ ℕ) : W.coeff μ ∈ I' := by
      apply hy
      have := hx d (C y * W) (hW.C_mul y) (by simpa using hm) μ
      simpa [coeff_C_mul] using this
    rw [eval_eq, pow_succ']
    refine Ideal.sum_mem _ fun μ hμ ↦ Ideal.mul_mem_mul (hcoeff μ) ?_
    have hdeg : μ.degree = d := by
      have := hW (mem_support_iff.mp hμ)
      rw [Finsupp.degree_eq_weight_one]
      exact this
    have := (mem_span_pow_iff_exists_isHomogeneous x d _).mpr
      ⟨monomial μ 1, isHomogeneous_monomial _ hdeg, rfl⟩
    simpa [eval_monomial, Finsupp.prod] using this


/-- The heart of the proof that regular sequences are quasi-regular (Matsumura, Thm 16.2):
decomposing a homogeneous polynomial in `(t, tₙ)` along the powers of `tₙ`. -/
lemma coeff_mem_of_sum_mem (hx : IsRegularSystemOfGenerators x)
    (hy : ∀ m, y * m ∈ Ideal.span (Set.range x) → m ∈ Ideal.span (Set.range x)) (D : ℕ)
    (G : ℕ → MvPolynomial ι A) (hG : ∀ k ≤ D, (G k).IsHomogeneous (D - k))
    (hmem : ∑ k ∈ Finset.range (D + 1), y ^ k * eval x (G k) ∈
      (Ideal.span (Set.range x) ⊔ Ideal.span {y}) ^ (D + 1)) :
    ∀ k ≤ D, ∀ μ, (G k).coeff μ ∈ Ideal.span (Set.range x) ⊔ Ideal.span {y} := by
  set I' := Ideal.span (Set.range x)
  set I := I' ⊔ Ideal.span {y}
  induction D generalizing G with
  | zero =>
    intro k hk μ
    obtain rfl : k = 0 := by omega
    have h0 := hG 0 le_rfl
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, pow_one,
      eval_eq_coeff_zero_of_isHomogeneous_zero x h0] at hmem
    by_cases hμ : μ = 0
    · rwa [hμ]
    · rw [h0.coeff_eq_zero fun h ↦ hμ ((Finsupp.degree_eq_zero_iff μ).mp h)]
      exact zero_mem _
  | succ D ih =>
    set s := ∑ j ∈ Finset.range (D + 1), y ^ j * eval x (G (j + 1)) with hs
    have htot : ∑ k ∈ Finset.range (D + 1 + 1), y ^ k * eval x (G k) = eval x (G 0) + y * s := by
      rw [Finset.sum_range_succ', hs, Finset.mul_sum, add_comm]
      simp [pow_succ, mul_assoc, mul_comm]
    rw [htot] at hmem
    obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.mp (sup_pow_succ_le I' _ (D + 1) hmem)
    obtain ⟨v, hv, rfl⟩ := Ideal.mem_span_singleton_mul.mp ht
    have hG0 : eval x (G 0) ∈ I' ^ (D + 1) :=
      (mem_span_pow_iff_exists_isHomogeneous x (D + 1) _).mpr ⟨G 0, hG 0 (by omega), rfl⟩
    have hw : s - v ∈ I' ^ (D + 1) := by
      refine mem_pow_of_mul_mem_pow hx hy (D + 1) _ ?_
      have : y * (s - v) = u - eval x (G 0) := by linear_combination -hut
      rw [this]
      exact sub_mem (Ideal.pow_le_pow_right (by omega) hu) hG0
    have hsI : s ∈ I ^ (D + 1) := by
      have : s = v + (s - v) := by ring
      rw [this]
      exact add_mem hv (Ideal.pow_right_mono le_sup_left _ hw)
    have ih' := ih (fun j ↦ G (j + 1)) (fun j hj ↦ by simpa using hG (j + 1) (by omega)) hsI
    obtain ⟨W, hW, hWeq⟩ := (mem_span_pow_iff_exists_isHomogeneous x (D + 1) _).mp hw
    have hsum : eval x (G 0 + C y * W) ∈ I' ^ (D + 1 + 1) := by
      have : eval x (G 0 + C y * W) = u := by
        simp only [map_add, map_mul, eval_C, hWeq]
        linear_combination -hut
      rwa [this]
    have hGW := hx (D + 1) (G 0 + C y * W) ((hG 0 (by omega)).add ((hW).C_mul y)) hsum
    intro k hk μ
    rcases k with _ | j
    · have h := hGW μ
      rw [coeff_add, coeff_C_mul] at h
      have : (G 0).coeff μ = ((G 0).coeff μ + y * W.coeff μ) - y * W.coeff μ := by ring
      rw [this]
      exact sub_mem (le_sup_left (a := I') h)
        (Ideal.mul_mem_right _ _ (le_sup_right (a := I') (Ideal.mem_span_singleton_self y)))
    · exact ih' j (by omega) μ


/-- If `x` is a regular system of generators and `y` is a nonzerodivisor modulo `(x)`, then
`(x, y)` is a regular system of generators (Matsumura, Thm 16.2 (i), induction step). -/
theorem IsRegularSystemOfGenerators.option_elim (hx : IsRegularSystemOfGenerators x)
    (hy : ∀ m, y * m ∈ Ideal.span (Set.range x) → m ∈ Ideal.span (Set.range x)) :
    IsRegularSystemOfGenerators (fun o : Option ι ↦ o.elim y x) := by
  classical
  intro D F hF hmem μ
  have hspan : Ideal.span (Set.range fun o : Option ι ↦ o.elim y x) =
      Ideal.span (Set.range x) ⊔ Ideal.span {y} := by
    have : (Set.range fun o : Option ι ↦ o.elim y x) = insert y (Set.range x) := by
      ext z
      simp [Option.exists, eq_comm]
    rw [this, Ideal.span_insert, sup_comm]
  rw [hspan] at hmem ⊢
  set P := optionEquivLeft A ι F
  have hcoeff (k : ℕ) (d : ι →₀ ℕ) : (P.coeff k).coeff d = F.coeff (d.optionElim k) :=
    optionEquivLeft_coeff_coeff (p := F) (m := k) (d := d)
  have hdeg (k : ℕ) (d : ι →₀ ℕ) : (d.optionElim k).degree = k + d.degree := by
    rw [degree_option, Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
  have hFdeg {n : Option ι →₀ ℕ} (hn : F.coeff n ≠ 0) : n.degree = D := by
    have := hF hn
    rw [Finsupp.degree_eq_weight_one]
    exact this
  have hGhom : ∀ k ≤ D, (P.coeff k).IsHomogeneous (D - k) := by
    intro k hk d hd
    rw [hcoeff] at hd
    have h := hFdeg hd
    rw [hdeg] at h
    have h' : d.degree = D - k := by omega
    rw [Finsupp.degree_eq_weight_one] at h'
    exact h'
  have hvanish (k : ℕ) (hk : D < k) : P.coeff k = 0 := by
    ext d
    rw [hcoeff, coeff_zero]
    by_contra h
    have := hFdeg h
    rw [hdeg] at this
    omega
  have heval : eval (fun o : Option ι ↦ o.elim y x) F =
      ∑ k ∈ Finset.range (D + 1), y ^ k * eval x (P.coeff k) := by
    have hnat : (Polynomial.map (eval x) P).natDegree < D + 1 := by
      refine Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_)
      rw [Polynomial.coeff_map, hvanish N (by exact_mod_cast hN), map_zero]
    rw [optionEquivLeft_elim_eval, Polynomial.eval_eq_sum_range' hnat]
    simp [Polynomial.coeff_map, mul_comm]
  rw [heval] at hmem
  have key := coeff_mem_of_sum_mem hx hy D (fun k ↦ P.coeff k) hGhom hmem
  rw [← optionEquivLeft_coeff_some_coeff_none]
  by_cases h : μ none ≤ D
  · exact key _ h _
  · rw [hvanish _ (by omega), coeff_zero]
    exact zero_mem _


/-- Regular systems of generators can be reindexed. -/
theorem IsRegularSystemOfGenerators.comp_equiv {κ : Type*} (e : κ ≃ ι)
    (hx : IsRegularSystemOfGenerators x) : IsRegularSystemOfGenerators (x ∘ e) := by
  intro d F hF hmem μ
  have hspan : Ideal.span (Set.range (x ∘ e)) = Ideal.span (Set.range x) := by
    rw [e.surjective.range_comp]
  rw [hspan] at hmem ⊢
  have := hx d (rename e F) hF.rename_isHomogeneous (by rwa [eval_rename])
    (μ.mapDomain e)
  rwa [coeff_rename_mapDomain _ e.injective] at this

omit [CommRing A] in
/-- The empty family is a regular system of generators of the zero ideal. -/
theorem isRegularSystemOfGenerators_of_isEmpty {A : Type*} [CommRing A] [IsEmpty ι]
    (x : ι → A) : IsRegularSystemOfGenerators x := by
  intro d F _ hmem μ
  have hrange : Set.range x = ∅ := Set.range_eq_empty x
  rw [hrange, Ideal.span_empty] at hmem ⊢
  rw [F.eq_C_of_isEmpty, eval_C, Ideal.bot_pow (by omega), Ideal.mem_bot] at hmem
  rw [Subsingleton.elim μ 0, hmem]
  exact zero_mem _

open RingTheory.Sequence in
/-- II.4.14 (the direction valid in any ring, Matsumura Thm 16.2 (i)): a (weakly) regular
sequence `x₁,…,xₙ` (an `A`-sequence in the sense of Serre) is a regular system of generators
of the ideal it generates. -/
theorem isRegularSystemOfGenerators_of_isWeaklyRegular {A : Type*} [CommRing A] (rs : List A)
    (h : IsWeaklyRegular A rs) : IsRegularSystemOfGenerators fun i : Fin rs.length ↦ rs[i] := by
  induction rs using List.reverseRecOn with
  | nil =>
    have : IsEmpty (Fin ([] : List A).length) := inferInstanceAs (IsEmpty (Fin 0))
    exact isRegularSystemOfGenerators_of_isEmpty _
  | append_singleton rs y ih =>
    rw [isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at h
    have hI : (Ideal.ofList rs • ⊤ : Submodule A A) =
        Ideal.span (Set.range fun i : Fin rs.length ↦ rs[i]) := by
      rw [smul_eq_mul, Ideal.mul_top]
      change Ideal.span {r | r ∈ rs} = _
      congr 1
      ext z
      simp [List.mem_iff_getElem, Fin.exists_iff]
    have hy : ∀ m, y * m ∈ Ideal.span (Set.range fun i : Fin rs.length ↦ rs[i]) →
        m ∈ Ideal.span (Set.range fun i : Fin rs.length ↦ rs[i]) := by
      intro m hm
      rw [← hI] at hm ⊢
      have h0 : y • (Submodule.Quotient.mk m : A ⧸ (Ideal.ofList rs • ⊤ : Submodule A A)) =
          y • 0 := by
        rw [smul_zero, ← Submodule.Quotient.mk_smul, smul_eq_mul, Submodule.Quotient.mk_eq_zero]
        exact hm
      exact (Submodule.Quotient.mk_eq_zero _).mp (h.2 h0)
    have := ((ih h.1).option_elim hy).comp_equiv
      ((finCongr (by simp : (rs ++ [y]).length = rs.length + 1)).trans finSuccEquivLast)
    convert this using 1
    ext ⟨i, hi⟩
    have hi' : i < rs.length + 1 := lt_of_lt_of_eq hi (by simp)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | rfl
    · have h2 : finSuccEquivLast (⟨i, hi'⟩ : Fin (rs.length + 1)) = some ⟨i, hlt⟩ :=
        finSuccEquivLast_castSucc ⟨i, hlt⟩
      simp [h2, List.getElem_append_left hlt]
    · have h2 : finSuccEquivLast (⟨rs.length, hi'⟩ : Fin (rs.length + 1)) = none :=
        finSuccEquivLast_last
      simp [h2]

/-- A homogeneous polynomial of degree `d` with coefficients in `J = (xᵢ)` takes a value in
`J^{d+1}` at `x`. -/
lemma eval_mem_pow_succ_of_coeff_mem {ι : Type*} (x : ι → A) {d : ℕ} {W : MvPolynomial ι A}
    (hW : W.IsHomogeneous d) (hc : ∀ μ, W.coeff μ ∈ Ideal.span (Set.range x)) :
    eval x W ∈ Ideal.span (Set.range x) ^ (d + 1) := by
  classical
  rw [eval_eq, pow_succ']
  refine Ideal.sum_mem _ fun μ hμ ↦ Ideal.mul_mem_mul (hc μ) ?_
  have hdeg : μ.degree = d := by
    have := hW (mem_support_iff.mp hμ)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  have := (mem_span_pow_iff_exists_isHomogeneous x d _).mpr
    ⟨monomial μ 1, isHomogeneous_monomial _ hdeg, rfl⟩
  simpa [eval_monomial, Finsupp.prod] using this

/-- If `x₀, x₁, …` is a regular system of generators of `J` and `x₀ b ∈ J^{d+1}`, then
`b ∈ J^d`. -/
lemma mem_pow_of_mul_mem_pow_succ {n : ℕ} {x : Fin (n + 1) → A}
    (hx : IsRegularSystemOfGenerators x) {d : ℕ} {b : A}
    (h : x 0 * b ∈ Ideal.span (Set.range x) ^ (d + 1)) : b ∈ Ideal.span (Set.range x) ^ d := by
  classical
  set J := Ideal.span (Set.range x)
  by_contra hb
  have hex : ∃ k, b ∉ J ^ k := ⟨d, hb⟩
  set k := Nat.find hex with hk
  have hkb : b ∉ J ^ k := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Ideal.one_eq_top] at hkb
    exact hkb Submodule.mem_top
  have hkd : k ≤ d := Nat.find_min' hex hb
  have hbk : b ∈ J ^ (k - 1) := by
    by_contra h'
    exact Nat.find_min hex (by omega) h'
  obtain ⟨W, hW, rfl⟩ := (mem_span_pow_iff_exists_isHomogeneous x (k - 1) b).mp hbk
  have hG : (W * X 0).IsHomogeneous k := by
    have := hW.mul (isHomogeneous_X A (0 : Fin (n + 1)))
    rwa [show k - 1 + 1 = k by omega] at this
  have hmem : eval x (W * X 0) ∈ J ^ (k + 1) := by
    rw [map_mul, eval_X, mul_comm]
    exact Ideal.pow_le_pow_right (by omega) h
  have hc := hx k (W * X 0) hG hmem
  have hcW (μ) : W.coeff μ ∈ J := by
    have := hc (μ + Finsupp.single 0 1)
    rwa [coeff_mul_X] at this
  have := eval_mem_pow_succ_of_coeff_mem x hW hcW
  rw [show k - 1 + 1 = k by omega] at this
  exact hkb this

/-- In a noetherian local ring, the first element of a regular system of generators of a proper
ideal is a nonzerodivisor (Krull's intersection theorem). -/
lemma isSMulRegular_of_isRegularSystemOfGenerators [IsNoetherianRing A] [IsLocalRing A]
    {n : ℕ} {x : Fin (n + 1) → A} (hx : IsRegularSystemOfGenerators x)
    (hJ : Ideal.span (Set.range x) ≠ ⊤) : IsSMulRegular A (x 0) := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro a ha
  have hmem : ∀ d, a ∈ Ideal.span (Set.range x) ^ d := fun d ↦
    mem_pow_of_mul_mem_pow_succ hx (by rw [← smul_eq_mul, ha]; exact zero_mem _)
  have := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJ
  rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]
  exact hmem

/-- If `x₀, x₁, …, xₙ` is a regular system of generators, the images of `x₁, …, xₙ` form a
regular system of generators in `A ⧸ (x₀)` (Matsumura, Thm 16.3, induction step). -/
lemma isRegularSystemOfGenerators_quotient {n : ℕ} {x : Fin (n + 1) → A}
    (hx : IsRegularSystemOfGenerators x) :
    IsRegularSystemOfGenerators
      (fun i : Fin n ↦ Ideal.Quotient.mk (Ideal.span {x 0}) (x i.succ)) := by
  classical
  set I₀ := Ideal.span {x 0}
  set J := Ideal.span (Set.range x)
  set mk := Ideal.Quotient.mk I₀
  have hspan : Ideal.span (Set.range fun i : Fin n ↦ mk (x i.succ)) = J.map mk := by
    rw [Ideal.map_span]
    refine le_antisymm (Ideal.span_mono ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨i, rfl⟩
      exact ⟨x i.succ, ⟨i.succ, rfl⟩, rfl⟩
    · rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      cases j using Fin.cases with
      | zero =>
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
        exact zero_mem _
      | succ i => exact Ideal.subset_span ⟨i, rfl⟩
  intro d Fb hFb hmem μ
  rw [hspan] at hmem ⊢
  -- lift `Fb` to `A`
  choose c hc using Ideal.Quotient.mk_surjective (I := I₀)
  set F : MvPolynomial (Fin n) A := ∑ ν ∈ Fb.support, monomial ν (c (Fb.coeff ν))
  have hFc (ν) : mk (F.coeff ν) = Fb.coeff ν := by
    simp only [F, coeff_sum, coeff_monomial, map_sum]
    rw [Finset.sum_eq_single ν (fun _ _ h ↦ by simp [h]) (fun h ↦ by
      simp only [↓reduceIte]
      exact (hc _).trans (notMem_support_iff.mp h))]
    simp only [↓reduceIte]
    exact hc _
  have hFhom : F.IsHomogeneous d := IsHomogeneous.sum _ _ _ fun ν hν ↦
    isHomogeneous_monomial _ (by
      rw [Finsupp.degree_eq_weight_one]; exact hFb (mem_support_iff.mp hν))
  have hFmap : map mk F = Fb := by
    ext ν
    rw [coeff_map, hFc]
  have heval : eval (fun i : Fin n ↦ mk (x i.succ)) Fb = mk (eval (fun i ↦ x i.succ) F) := by
    have key : ∀ G : MvPolynomial (Fin n) A,
        eval (fun i : Fin n ↦ mk (x i.succ)) (map mk G) = mk (eval (fun i ↦ x i.succ) G) := by
      intro G
      induction G using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p i hp => simp only [map_mul, hp, map_X, eval_X]
    rw [← hFmap, key]
  rw [heval, ← Ideal.map_pow] at hmem
  have hmem' : eval (fun i ↦ x i.succ) F ∈ J ^ (d + 1) ⊔ I₀ := by
    have := Ideal.mem_comap.mpr hmem
    rwa [Ideal.comap_map_of_surjective' mk Ideal.Quotient.mk_surjective, Ideal.mk_ker] at this
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hmem'
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hv
  rw [← hFc μ]
  rcases d with _ | e
  · -- degree zero: `F` is the constant `u + b x₀`
    by_cases hμ : μ = 0
    · subst hμ
      rw [← eval_eq_coeff_zero_of_isHomogeneous_zero _ hFhom, ← huv, map_add, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (x 0)), mul_zero,
        add_zero]
      exact Ideal.mem_map_of_mem mk (by simpa using hu)
    · rw [hFhom.coeff_eq_zero fun h ↦ hμ ((Finsupp.degree_eq_zero_iff μ).mp h), map_zero]
      exact zero_mem _
  · -- write `b = B(x)` with `B` homogeneous of degree `e`
    have hevF : eval (fun i ↦ x i.succ) F ∈ J ^ (e + 1) :=
      (mem_span_pow_iff_exists_isHomogeneous x (e + 1) _).mpr
        ⟨rename Fin.succ F, hFhom.rename_isHomogeneous, by rw [eval_rename]; rfl⟩
    have hb : x 0 * b ∈ J ^ (e + 1) := by
      have : x 0 * b = eval (fun i ↦ x i.succ) F - u := by linear_combination huv
      rw [this]
      exact sub_mem hevF (Ideal.pow_le_pow_right (by omega) hu)
    obtain ⟨B, hB, rfl⟩ := (mem_span_pow_iff_exists_isHomogeneous x e b).mp
      (mem_pow_of_mul_mem_pow_succ hx hb)
    have hG : (rename Fin.succ F - B * X 0).IsHomogeneous (e + 1) :=
      hFhom.rename_isHomogeneous.sub (hB.mul (isHomogeneous_X A (0 : Fin (n + 1))))
    have hGeval : eval x (rename Fin.succ F - B * X 0) = u := by
      rw [map_sub, eval_rename, map_mul, eval_X]
      change eval (fun i ↦ x i.succ) F - _ = u
      linear_combination -huv
    have hc := hx (e + 1) _ hG (by rw [hGeval]; exact hu) (Finsupp.mapDomain Fin.succ μ)
    have hnot : (0 : Fin (n + 1)) ∉ (Finsupp.mapDomain Fin.succ μ).support := by
      rw [Finsupp.mem_support_iff, Finsupp.mapDomain_of_notMem_range]
      · exact fun h ↦ h rfl
      · rintro ⟨i, hi⟩
        exact Fin.succ_ne_zero i hi
    rw [coeff_sub, coeff_rename_mapDomain _ (Fin.succ_injective _), coeff_mul_X'] at hc
    simp only [hnot, ↓reduceIte, sub_zero] at hc
    exact Ideal.mem_map_of_mem mk hc

open RingTheory.Sequence in
/-- II.4.14, converse (Matsumura, Thm 16.3): in a noetherian local ring, a regular system of
generators `x₁,…,xₙ` of a proper ideal is an `A`-sequence (a weakly regular sequence). -/
theorem isWeaklyRegular_of_isRegularSystemOfGenerators {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {n : ℕ} (x : Fin n → A)
    (hJ : Ideal.span (Set.range x) ≠ ⊤) (hx : IsRegularSystemOfGenerators x) :
    IsWeaklyRegular A (List.ofFn x) := by
  induction n generalizing A with
  | zero =>
    rw [List.ofFn_zero]
    exact IsWeaklyRegular.nil A A
  | succ n ih =>
    rw [List.ofFn_succ, isWeaklyRegular_cons_iff]
    refine ⟨isSMulRegular_of_isRegularSystemOfGenerators hx hJ, ?_⟩
    set I₀ := Ideal.span {x 0}
    have hx0 : x 0 ∈ Ideal.span (Set.range x) := Ideal.subset_span ⟨0, rfl⟩
    have hI₀ : I₀ ≠ ⊤ := fun h ↦ hJ (_root_.eq_top_iff.mpr (h ▸ Ideal.span_le.mpr
      (Set.singleton_subset_iff.mpr hx0)))
    have : Nontrivial (A ⧸ I₀) := Ideal.Quotient.nontrivial_iff.mpr hI₀
    have : IsLocalRing (A ⧸ I₀) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have hx' := isRegularSystemOfGenerators_quotient hx
    have hJ' : Ideal.span (Set.range fun i : Fin n ↦ Ideal.Quotient.mk I₀ (x i.succ)) ≠ ⊤ := by
      intro h
      apply hJ
      have hle : Ideal.span (Set.range fun i : Fin n ↦ Ideal.Quotient.mk I₀ (x i.succ)) ≤
          (Ideal.span (Set.range x)).map (Ideal.Quotient.mk I₀) := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i.succ, rfl⟩)
      rw [h, top_le_iff] at hle
      have := congrArg (Ideal.comap (Ideal.Quotient.mk I₀)) hle
      rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        Ideal.comap_top, sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx0))]
        at this
    have h' := ih (fun i : Fin n ↦ Ideal.Quotient.mk I₀ (x i.succ)) hJ' hx'
    have hmap : (List.ofFn fun i : Fin n ↦ x i.succ).map (algebraMap A (A ⧸ I₀)) =
        List.ofFn fun i : Fin n ↦ Ideal.Quotient.mk I₀ (x i.succ) := by
      rw [List.map_ofFn]
      rfl
    rw [← hmap, isWeaklyRegular_map_algebraMap_iff] at h'
    have hsmul : (x 0 • ⊤ : Submodule A A) = I₀ := by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
    exact (LinearEquiv.isWeaklyRegular_congr (Submodule.quotEquivOfEq _ _ hsmul) _).mpr h'

open RingTheory.Sequence in
/-- II.4.14 (remarks): in a noetherian local ring, `x₁,…,xₙ` generating a proper ideal form a
regular system of generators iff they form an `A`-sequence in the sense of Serre. -/
theorem isRegularSystemOfGenerators_iff_isWeaklyRegular {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {n : ℕ} (x : Fin n → A)
    (hJ : Ideal.span (Set.range x) ≠ ⊤) :
    IsRegularSystemOfGenerators x ↔ IsWeaklyRegular A (List.ofFn x) := by
  refine ⟨isWeaklyRegular_of_isRegularSystemOfGenerators x hJ, fun h ↦ ?_⟩
  have := (isRegularSystemOfGenerators_of_isWeaklyRegular _ h).comp_equiv
    (finCongr (List.length_ofFn (f := x)).symm)
  convert this using 1
  ext i
  simp

end SGA.SGA1.ExposeII
