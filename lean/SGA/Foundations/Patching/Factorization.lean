/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Simultaneous factorization of matrices (Cartan's lemma for patching)

Let `f₁ : R₁ → R₀` and `f₂ : R₂ → R₀` be ring maps and `t₁ ∈ R₁`, `t₂ ∈ R₂` with the same image
`t ∈ R₀`. Assume that `R₁` is `t₁`-adically complete, `R₂` is `t₂`-adically complete, `R₀` is
`t`-adically Hausdorff, and that every element of `R₀` is congruent modulo `t` to a sum
`f₁ a + f₂ b`. Then every matrix `M ≡ 1 mod t` over `R₀` factors as `M = f₁(A) · f₂(B)` with
`A ≡ 1 mod t₁` over `R₁` and `B ≡ 1 mod t₂` over `R₂` (`Matrix.exists_eq_map_mul_map`); such
`A` and `B` are invertible (`Matrix.isUnit_of_eq_one_add_smul`).

This is the factorization step of formal patching (Harbater) and of patching over fields
(Harbater–Hartmann, *Patching over fields*, Israel J. Math. 176 (2010); Haran–Völklein,
*Galois groups over complete valued fields*, Israel J. Math. 93 (1996); Jarden, *Algebraic
patching*, Springer 2011, where it is called Cartan's lemma). The typical case is
`R₀ = k((y))⟦t⟧`, `R₁ = k[y⁻¹]⟦t⟧`, `R₂ = k⟦y⟧⟦t⟧`, where `k((y)) = k[y⁻¹] + k⟦y⟧`.

The proof is successive approximation: if `M ≡ f₁(A) f₂(B) mod t^{m+1}` with `A`, `B ≡ 1`,
write `M - f₁(A) f₂(B) = t^{m+1} E` and `E ≡ f₁(a) + f₂(b) mod t`; then
`A + t₁^{m+1} a` and `B + t₂^{m+1} b` give a factorization modulo `t^{m+2}`.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Limit

variable {R : Type*} [CommRing R] (t : R)

/-- `x ≡ y` modulo `(t)^m` in the sense of `SModEq` iff `t^m ∣ x - y`. -/
private lemma smodEq_iff_dvd_pow {x y : R} {m : ℕ} :
    x ≡ y [SMOD ((Ideal.span {t}) ^ m • ⊤ : Submodule R R)] ↔ t ^ m ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

omit [Fintype n] [DecidableEq n] in
/-- In a `t`-adically complete ring, a sequence of matrices whose `m`-th difference is divisible
by `t^{m+1}` has a limit `L` with `L - A m` divisible by `t^{m+1}`. -/
lemma exists_limit_of_isAdicComplete [IsAdicComplete (Ideal.span {t}) R] (A : ℕ → Matrix n n R)
    (hA : ∀ m, ∃ E : Matrix n n R, A (m + 1) - A m = t ^ (m + 1) • E) :
    ∃ L : Matrix n n R, ∀ m, ∃ E : Matrix n n R, L - A m = t ^ (m + 1) • E := by
  classical
  choose E hE using hA
  -- the differences `A (m + d) - A m` are divisible by `t^{m+1}`
  have hdiff : ∀ m d i j, t ^ (m + 1) ∣ A (m + d) i j - A m i j := by
    intro m d i j
    induction d with
    | zero => simp
    | succ d ih =>
      have h := congrFun (congrFun (hE (m + d)) i) j
      simp only [sub_apply, smul_apply, smul_eq_mul] at h
      have h' : t ^ (m + 1) ∣ A (m + d + 1) i j - A (m + d) i j :=
        h ▸ (pow_dvd_pow t (by omega)).mul_right _
      have := dvd_add h' ih
      rw [sub_add_sub_cancel] at this
      rwa [← add_assoc]
  have hentry : ∀ i j, ∃ L : R, ∀ m, t ^ (m + 1) ∣ L - A m i j := by
    intro i j
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {t}) inferInstance
      (f := fun m ↦ A m i j) (fun {m k} hmk ↦ by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmk
        rw [smodEq_iff_dvd_pow, ← neg_sub, dvd_neg]
        exact (pow_dvd_pow t (Nat.le_succ m)).trans (hdiff m d i j))
    refine ⟨L, fun m ↦ ?_⟩
    have h1 := (smodEq_iff_dvd_pow t).mp (hL (m + 1))
    have := dvd_sub (hdiff m 1 i j) h1
    rwa [sub_sub_sub_cancel_left] at this
  choose L hL using hentry
  refine ⟨Matrix.of L, fun m ↦ ?_⟩
  choose F hF using fun i j ↦ hL i j m
  exact ⟨Matrix.of F, by ext i j; simp [hF i j]⟩

end Limit

section Units

variable {R : Type*} [CommRing R] (t : R)

/-- In a `t`-adically complete ring, a matrix congruent to `1` modulo `t` is invertible. -/
lemma isUnit_of_eq_one_add_smul [IsAdicComplete (Ideal.span {t}) R] {A E : Matrix n n R}
    (h : A = 1 + t • E) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det]
  let π := Ideal.Quotient.mk (Ideal.span {t})
  have hπ : π.mapMatrix A = 1 := by
    have ht : π t = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
    rw [h, map_add, map_one]
    ext i j
    simp [ht]
  have hdet : A.det - 1 ∈ Ideal.span {t} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, hπ, det_one,
      sub_self]
  exact Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (IsAdicComplete.le_jacobson_bot _ hdet)

end Units

section Factorization

variable {R₀ R₁ R₂ : Type*} [CommRing R₀] [CommRing R₁] [CommRing R₂]
  (f₁ : R₁ →+* R₀) (f₂ : R₂ →+* R₀) {t₁ : R₁} {t₂ : R₂} {t : R₀}

omit [Fintype n] [DecidableEq n] in
/-- Matrix form of the additive decomposition `R₀ = f₁(R₁) + f₂(R₂) + t R₀`. -/
private lemma exists_eq_map_add_map_add_smul
    (hdecomp : ∀ r : R₀, ∃ a b c, r = f₁ a + f₂ b + t * c) (E : Matrix n n R₀) :
    ∃ (a : Matrix n n R₁) (b : Matrix n n R₂) (c : Matrix n n R₀),
      E = a.map f₁ + b.map f₂ + t • c := by
  choose a b c h using hdecomp
  exact ⟨E.map a, E.map b, E.map c, by ext i j; simp [← h]⟩

variable {f₁ f₂}

/-- One step of the approximation: a factorization of `M` modulo `t^{m+1}` with factors `≡ 1`
improves to one modulo `t^{m+2}`, changing the factors only modulo `t^{m+1}`. -/
private lemma exists_step (h₁ : f₁ t₁ = t) (h₂ : f₂ t₂ = t)
    (hdecomp : ∀ r : R₀, ∃ a b c, r = f₁ a + f₂ b + t * c) (M : Matrix n n R₀) (m : ℕ)
    {A : Matrix n n R₁} {B : Matrix n n R₂} {α : Matrix n n R₁} {β : Matrix n n R₂}
    (hA : A = 1 + t₁ • α) (hB : B = 1 + t₂ • β) {E : Matrix n n R₀}
    (hE : M - A.map f₁ * B.map f₂ = t ^ (m + 1) • E) :
    ∃ (a : Matrix n n R₁) (b : Matrix n n R₂) (E' : Matrix n n R₀),
      M - (A + t₁ ^ (m + 1) • a).map f₁ * (B + t₂ ^ (m + 1) • b).map f₂ =
        t ^ (m + 2) • E' := by
  obtain ⟨a, b, c, hc⟩ := exists_eq_map_add_map_add_smul f₁ f₂ hdecomp E
  refine ⟨a, b, c - a.map f₁ * β.map f₂ - α.map f₁ * b.map f₂ -
    t ^ m • (a.map f₁ * b.map f₂), ?_⟩
  have hmap₁ : ∀ (k : ℕ) (X : Matrix n n R₁), (t₁ ^ k • X).map f₁ = t ^ k • X.map f₁ := by
    intro k X
    ext i j
    simp [h₁]
  have hmap₂ : ∀ (k : ℕ) (X : Matrix n n R₂), (t₂ ^ k • X).map f₂ = t ^ k • X.map f₂ := by
    intro k X
    ext i j
    simp [h₂]
  have hA' : A.map f₁ = 1 + t • α.map f₁ := by
    rw [hA, Matrix.map_add _ (map_add f₁),
      Matrix.map_one _ (map_zero f₁) (map_one f₁), ← pow_one t₁, hmap₁, pow_one]
  have hB' : B.map f₂ = 1 + t • β.map f₂ := by
    rw [hB, Matrix.map_add _ (map_add f₂),
      Matrix.map_one _ (map_zero f₂) (map_one f₂), ← pow_one t₂, hmap₂, pow_one]
  have hM : M = A.map f₁ * B.map f₂ + t ^ (m + 1) • E := by rw [← hE]; abel
  rw [Matrix.map_add _ (map_add f₁), Matrix.map_add _ (map_add f₂), hmap₁, hmap₂, hM, hc]
  rw [hA', hB']
  simp only [add_mul, mul_add, smul_add, smul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul,
    mul_one, smul_smul, ← pow_add, ← pow_succ, ← pow_succ']
  rw [show m + 1 + (m + 1) = m + 2 + m by omega, pow_add]
  simp only [← smul_smul]
  abel

/-- **Simultaneous factorization** (Cartan's lemma for patching): with `R₁` complete for `t₁`,
`R₂` complete for `t₂`, `R₀` Hausdorff for `t = f₁ t₁ = f₂ t₂`, and `R₀ = f₁(R₁) + f₂(R₂) + t R₀`,
every matrix `M ≡ 1 mod t` over `R₀` is a product `f₁(A) f₂(B)` with `A ≡ 1 mod t₁` and
`B ≡ 1 mod t₂`. -/
theorem exists_eq_map_mul_map [IsAdicComplete (Ideal.span {t₁}) R₁]
    [IsAdicComplete (Ideal.span {t₂}) R₂] [IsHausdorff (Ideal.span {t}) R₀]
    (h₁ : f₁ t₁ = t) (h₂ : f₂ t₂ = t) (hdecomp : ∀ r : R₀, ∃ a b c, r = f₁ a + f₂ b + t * c)
    (M : Matrix n n R₀) (hM : ∃ E, M = 1 + t • E) :
    ∃ (A : Matrix n n R₁) (B : Matrix n n R₂), (∃ α, A = 1 + t₁ • α) ∧ (∃ β, B = 1 + t₂ • β) ∧
      M = A.map f₁ * B.map f₂ := by
  classical
  -- the invariant at stage `m`
  let Inv : ℕ → Matrix n n R₁ × Matrix n n R₂ → Prop := fun m AB ↦
    (∃ α, AB.1 = 1 + t₁ • α) ∧ (∃ β, AB.2 = 1 + t₂ • β) ∧
      ∃ E, M - AB.1.map f₁ * AB.2.map f₂ = t ^ (m + 1) • E
  have hstep : ∀ m (AB : Matrix n n R₁ × Matrix n n R₂), Inv m AB →
      ∃ AB' : Matrix n n R₁ × Matrix n n R₂, Inv (m + 1) AB' ∧
        (∃ a, AB'.1 - AB.1 = t₁ ^ (m + 1) • a) ∧ (∃ b, AB'.2 - AB.2 = t₂ ^ (m + 1) • b) := by
    rintro m ⟨A, B⟩ ⟨⟨α, hA⟩, ⟨β, hB⟩, ⟨E, hE⟩⟩
    dsimp only at hA hB hE
    obtain ⟨a, b, E', hE'⟩ := exists_step h₁ h₂ hdecomp M m hA hB hE
    refine ⟨(A + t₁ ^ (m + 1) • a, B + t₂ ^ (m + 1) • b), ⟨⟨α + t₁ ^ m • a, ?_⟩,
      ⟨β + t₂ ^ m • b, ?_⟩, ⟨E', hE'⟩⟩, ⟨a, by simp⟩, ⟨b, by simp⟩⟩
    · dsimp only
      rw [hA, smul_add, smul_smul, ← pow_succ']
      abel
    · dsimp only
      rw [hB, smul_add, smul_smul, ← pow_succ']
      abel
  choose next hnext using hstep
  have h0 : Inv 0 (1, 1) := by
    obtain ⟨E, hE⟩ := hM
    exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩, ⟨E, by simp [hE]⟩⟩
  let seq : (m : ℕ) → {AB // Inv m AB} := fun m ↦ Nat.rec ⟨(1, 1), h0⟩
    (fun m AB ↦ ⟨next m AB.1 AB.2, (hnext m AB.1 AB.2).1⟩) m
  have hseq : ∀ m, (seq (m + 1)).1 = next m (seq m).1 (seq m).2 := fun _ ↦ rfl
  obtain ⟨A, hA⟩ := exists_limit_of_isAdicComplete t₁ (fun m ↦ (seq m).1.1) fun m ↦ by
    rw [hseq]
    exact (hnext m _ _).2.1
  obtain ⟨B, hB⟩ := exists_limit_of_isAdicComplete t₂ (fun m ↦ (seq m).1.2) fun m ↦ by
    rw [hseq]
    exact (hnext m _ _).2.2
  have hseq0 : (seq 0).1 = (1, 1) := rfl
  refine ⟨A, B, ?_, ?_, ?_⟩
  · obtain ⟨α, hα⟩ := hA 0
    rw [hseq0, zero_add, pow_one] at hα
    exact ⟨α, by rw [← hα]; abel⟩
  · obtain ⟨β, hβ⟩ := hB 0
    rw [hseq0, zero_add, pow_one] at hβ
    exact ⟨β, by rw [← hβ]; abel⟩
  -- `M - f₁(A) f₂(B)` is divisible by every power of `t`
  rw [← sub_eq_zero]
  ext i j
  refine IsHausdorff.haus (I := Ideal.span {t}) inferInstance _ fun m ↦ ?_
  rw [smodEq_iff_dvd_pow, sub_zero]
  refine (pow_dvd_pow t (Nat.le_succ m)).trans ?_
  obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨E, hE⟩⟩ := (seq m).2
  obtain ⟨a, ha⟩ := hA m
  obtain ⟨b, hb⟩ := hB m
  set Am := (seq m).1.1
  set Bm := (seq m).1.2
  have hAeq : A.map f₁ = Am.map f₁ + t ^ (m + 1) • a.map f₁ := by
    rw [← sub_eq_iff_eq_add', ← Matrix.map_sub _ (map_sub f₁), ha]
    ext i j
    simp [h₁]
  have hBeq : B.map f₂ = Bm.map f₂ + t ^ (m + 1) • b.map f₂ := by
    rw [← sub_eq_iff_eq_add', ← Matrix.map_sub _ (map_sub f₂), hb]
    ext i j
    simp [h₂]
  have hM' : M = Am.map f₁ * Bm.map f₂ + t ^ (m + 1) • E := by rw [← hE]; abel
  have key : M - A.map f₁ * B.map f₂ = t ^ (m + 1) • (E - a.map f₁ * B.map f₂ -
      Am.map f₁ * b.map f₂) := by
    rw [hM', hAeq, hBeq]
    simp only [add_mul, mul_add, sub_eq_add_neg, neg_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_neg, smul_smul]
    abel
  rw [key]
  exact ⟨_, rfl⟩

/-- `exists_eq_map_mul_map` with invertible factors. -/
theorem exists_eq_map_mul_map_of_isUnit [IsAdicComplete (Ideal.span {t₁}) R₁]
    [IsAdicComplete (Ideal.span {t₂}) R₂] [IsHausdorff (Ideal.span {t}) R₀]
    (h₁ : f₁ t₁ = t) (h₂ : f₂ t₂ = t) (hdecomp : ∀ r : R₀, ∃ a b c, r = f₁ a + f₂ b + t * c)
    (M : Matrix n n R₀) (hM : ∃ E, M = 1 + t • E) :
    ∃ (A : Matrix n n R₁) (B : Matrix n n R₂), IsUnit A ∧ IsUnit B ∧ M = A.map f₁ * B.map f₂ := by
  obtain ⟨A, B, ⟨α, hA⟩, ⟨β, hB⟩, h⟩ := exists_eq_map_mul_map h₁ h₂ hdecomp M hM
  exact ⟨A, B, isUnit_of_eq_one_add_smul t₁ hA, isUnit_of_eq_one_add_smul t₂ hB, h⟩

end Factorization

end Matrix
