/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import SGA.Foundations.Formal.NoetherianOfComplete

/-!
# Limits of adic inverse systems of rings

Let `⋯ → A₂ → A₁ → A₀` be an inverse system of rings with surjective transition maps
`πₙ : Aₙ₊₁ → Aₙ`, and let `Jₙ = ker (Aₙ → A₀)`. The system is *adic* if `ker πₙ = Jₙ₊₁ⁿ⁺¹` for
all `n`; then also `Jₙⁿ⁺¹ = 0`. EGA 0_I, 7.2.7: if moreover `J₁ = ker π₀` is finitely generated,
then the limit `A = lim Aₙ` is complete and separated for the `J`-adic topology, where
`J = ker (A → A₀)`; `J` is finitely generated and `ker (A → Aₙ) = Jⁿ⁺¹`, so `A ⧸ Jⁿ⁺¹ ≅ Aₙ`.
If `A₀` is noetherian, so is `A`.

## Main definitions and results

* `Ring.inverseLimit π`: the inverse limit, as a subring of `∀ n, A n`, with projections
  `Ring.inverseLimit.proj π n`, which are surjective if the `πₙ` are
  (`Ring.inverseLimit.proj_surjective`).
* `Ring.IsAdicInverseSystem π`: the adic condition above; for instance the system `R ⧸ Iⁿ⁺¹`
  (`Ring.isAdicInverseSystem_quotientPow`).
* `Ring.IsAdicInverseSystem.ker_proj_eq`, `fg_ker_proj_zero`, `isAdicComplete`,
  `quotientEquiv`, `isNoetherianRing`: EGA 0_I, 7.2.7.

The proof: lift generators of `J₁` to `t₁, …, tᵣ ∈ J`, and let `T = (t₁, …, tᵣ)`. By Nakayama's
lemma for the nilpotent ideals `Jₘ`, the image of `T` in `Aₘ` is `Jₘ`. An element of
`ker (A → Aₙ)` is then written as a combination of generators of `Tⁿ⁺¹` by successive
approximation, the coefficients converging in `A`.
-/

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

/-- Nakayama's lemma for a nilpotent ideal: if `I ⊆ T + I²` and `Iᵏ = 0`, then `I ⊆ T`. -/
theorem le_of_le_sup_sq_of_pow_eq_bot {I T : Ideal R} (h : I ≤ T ⊔ I ^ 2) {k : ℕ}
    (hk : I ^ k = ⊥) : I ≤ T := by
  have key (i : ℕ) : I ≤ T ⊔ I ^ (i + 1) := by
    induction i with
    | zero => rw [zero_add, pow_one]; exact le_sup_right
    | succ i ih =>
      calc I ≤ T ⊔ I * I := by rw [← sq]; exact h
        _ ≤ T ⊔ I * (T ⊔ I ^ (i + 1)) := sup_le_sup_left (Ideal.mul_mono_right ih) _
        _ ≤ T ⊔ I ^ (i + 1 + 1) := by
          rw [Ideal.mul_sup, pow_succ' I (i + 1)]
          exact sup_le le_sup_left
            (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)
  have hk' : I ^ (k + 1) = ⊥ := eq_bot_iff.mpr ((Ideal.pow_le_pow_right k.le_succ).trans hk.le)
  simpa [hk'] using key k

end Ideal

namespace Ring

/-- Every element of `Xₙ` extends to a compatible sequence `(xₖ)` with `fₖ xₖ₊₁ = xₖ`, when the
transition maps `fₖ : Xₖ₊₁ → Xₖ` are surjective. -/
lemma exists_compatible_seq_eq : ∀ (n : ℕ) {X : ℕ → Type v} (f : ∀ k, X (k + 1) → X k),
    (∀ k, Function.Surjective (f k)) → ∀ a : X n,
      ∃ x : ∀ k, X k, (∀ k, f k (x (k + 1)) = x k) ∧ x n = a
  | 0, X, f, hf, a => by
    let x : ∀ k, X k := fun k ↦ Nat.rec (motive := X) a (fun k xk ↦ (hf k xk).choose) k
    exact ⟨x, fun k ↦ (hf k (x k)).choose_spec, rfl⟩
  | n + 1, X, f, hf, a => by
    obtain ⟨y, hy, rfl⟩ := exists_compatible_seq_eq n (X := fun k ↦ X (k + 1))
      (fun k ↦ f (k + 1)) (fun k ↦ hf (k + 1)) a
    refine ⟨fun k ↦ Nat.casesOn (motive := X) k (f 0 (y 0)) y, fun k ↦ ?_, rfl⟩
    cases k with
    | zero => rfl
    | succ k => exact hy k

variable {A : ℕ → Type u} [∀ n, CommRing (A n)] (π : ∀ n, A (n + 1) →+* A n)

/-- The inverse limit `lim Aₙ` of a sequence of rings `⋯ → A₂ → A₁ → A₀`, as the subring of
compatible sequences in the product. -/
def inverseLimit : Subring (∀ n, A n) where
  carrier := {x | ∀ n, π n (x (n + 1)) = x n}
  mul_mem' {x y} hx hy n := by
    change π n (x (n + 1) * y (n + 1)) = x n * y n
    rw [map_mul, hx n, hy n]
  one_mem' n := map_one (π n)
  add_mem' {x y} hx hy n := by
    change π n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  zero_mem' n := map_zero (π n)
  neg_mem' {x} hx n := by
    change π n (-x (n + 1)) = -x n
    rw [map_neg, hx n]

namespace inverseLimit

/-- The projection `lim Aₖ → Aₙ`. -/
def proj (n : ℕ) : inverseLimit π →+* A n :=
  (Pi.evalRingHom A n).comp (inverseLimit π).subtype

@[simp]
lemma proj_apply (n : ℕ) (x : inverseLimit π) : proj π n x = (x : ∀ n, A n) n := rfl

@[simp]
lemma π_proj (n : ℕ) (x : inverseLimit π) : π n (proj π (n + 1) x) = proj π n x := x.2 n

lemma π_comp_proj (n : ℕ) : (π n).comp (proj π (n + 1)) = proj π n :=
  RingHom.ext (π_proj π n)

@[ext]
lemma ext {x y : inverseLimit π} (h : ∀ n, proj π n x = proj π n y) : x = y :=
  Subtype.ext (funext h)

lemma proj_surjective (hπ : ∀ n, Function.Surjective (π n)) (n : ℕ) :
    Function.Surjective (proj π n) := fun a ↦ by
  obtain ⟨x, hx, rfl⟩ := exists_compatible_seq_eq n (fun k ↦ π k) hπ a
  exact ⟨⟨x, hx⟩, rfl⟩

lemma ker_proj_succ_le (n : ℕ) : RingHom.ker (proj π (n + 1)) ≤ RingHom.ker (proj π n) :=
  fun x hx ↦ by
    rw [RingHom.mem_ker] at hx ⊢
    rw [← π_proj, hx, map_zero]

lemma ker_proj_antitone : Antitone fun n ↦ RingHom.ker (proj π n) :=
  antitone_nat_of_succ_le (ker_proj_succ_le π)

/-- The composite `Aₙ → A₀` of the transition maps. -/
def toZero : ∀ n, A n →+* A 0
  | 0 => RingHom.id _
  | n + 1 => (toZero n).comp (π n)

@[simp]
lemma toZero_proj (n : ℕ) (x : inverseLimit π) : toZero π n (proj π n x) = proj π 0 x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [toZero, RingHom.comp_apply, π_proj, ih]

lemma ker_toZero_succ (n : ℕ) :
    RingHom.ker (toZero π (n + 1)) = (RingHom.ker (toZero π n)).comap (π n) :=
  (RingHom.comap_ker _ _).symm

lemma ker_toZero_one : RingHom.ker (toZero π 1) = RingHom.ker (π 0) :=
  Ideal.ext fun _ ↦ Iff.rfl

lemma map_ker_proj_zero_le (n : ℕ) :
    (RingHom.ker (proj π 0)).map (proj π n) ≤ RingHom.ker (toZero π n) :=
  Ideal.map_le_iff_le_comap.mpr fun x hx ↦ by
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker, toZero_proj, hx]

end inverseLimit

open inverseLimit

/-- An inverse system of rings `⋯ → A₂ → A₁ → A₀` is *adic* (EGA 0_I, 7.2.7) if the transition
maps `πₙ` are surjective and `ker πₙ = Jₙ₊₁ⁿ⁺¹`, where `Jₙ = ker (Aₙ → A₀)`. For instance
`Aₙ = A ⧸ Iⁿ⁺¹`. -/
structure IsAdicInverseSystem : Prop where
  surjective (n : ℕ) : Function.Surjective (π n)
  ker_eq (n : ℕ) : RingHom.ker (π n) = RingHom.ker (toZero π (n + 1)) ^ (n + 1)

namespace IsAdicInverseSystem

variable {π} (h : IsAdicInverseSystem π)
include h

lemma map_ker_toZero_succ (n : ℕ) :
    (RingHom.ker (toZero π (n + 1))).map (π n) = RingHom.ker (toZero π n) := by
  rw [ker_toZero_succ, Ideal.map_comap_of_surjective _ (h.surjective n)]

/-- In an adic inverse system, `Jₙⁿ⁺¹ = 0`. -/
lemma ker_toZero_pow_eq_bot (n : ℕ) : RingHom.ker (toZero π n) ^ (n + 1) = ⊥ := by
  rw [← h.map_ker_toZero_succ n, ← Ideal.map_pow, ← h.ker_eq n]
  exact (Ideal.map_eq_bot_iff_le_ker _).mpr le_rfl

lemma pow_le_ker_proj (n : ℕ) : RingHom.ker (proj π 0) ^ (n + 1) ≤ RingHom.ker (proj π n) := by
  rw [RingHom.ker_eq_comap_bot (proj π n), ← Ideal.map_le_iff_le_comap, Ideal.map_pow,
    ← h.ker_toZero_pow_eq_bot n]
  exact Ideal.pow_right_mono (map_ker_proj_zero_le π n) _

/-- EGA 0_I, 7.2.7, main step: there is a finitely generated ideal `T` of `lim Aₙ` with
`ker (lim Aₖ → Aₙ) = Tⁿ⁺¹` for all `n`. -/
theorem exists_fg_ker_proj_eq (hJ : (RingHom.ker (π 0)).FG) :
    ∃ T : Ideal (inverseLimit π), T.FG ∧ ∀ n, RingHom.ker (proj π n) = T ^ (n + 1) := by
  obtain ⟨r, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJ
  choose t ht using fun i ↦ proj_surjective π h.surjective 1 (s i)
  let T : Ideal (inverseLimit π) := Ideal.span (Set.range t)
  have hTfg : T.FG := Submodule.fg_span (Set.finite_range t)
  have hT0 : T ≤ RingHom.ker (proj π 0) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have : s i ∈ RingHom.ker (π 0) := hs ▸ Submodule.subset_span ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, ← π_proj, ht, ← RingHom.mem_ker]
    exact this
  have hTm (m : ℕ) : T.map (proj π (m + 1)) = RingHom.ker (toZero π (m + 1)) := by
    induction m with
    | zero =>
      rw [ker_toZero_one, ← hs, Ideal.map_span, ← Set.range_comp]
      congr 2
      exact funext ht
    | succ m ih =>
      refine le_antisymm ((Ideal.map_mono hT0).trans (map_ker_proj_zero_le π _)) ?_
      refine Ideal.le_of_le_sup_sq_of_pow_eq_bot ?_ (h.ker_toZero_pow_eq_bot (m + 2))
      intro x hx
      rw [ker_toZero_succ, Ideal.mem_comap, ← ih, ← π_comp_proj, ← Ideal.map_map] at hx
      obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective _ (h.surjective _)).mp hx
      have hxy' : x - y ∈ RingHom.ker (toZero π (m + 2)) ^ 2 := by
        have : x - y ∈ RingHom.ker (π (m + 1)) := by
          rw [RingHom.mem_ker, map_sub, hxy, sub_self]
        rw [h.ker_eq] at this
        exact Ideal.pow_le_pow_right (by lia) this
      rw [← add_sub_cancel y x]
      exact Submodule.add_mem_sup hy hxy'
  have hTpow (n : ℕ) : T ^ (n + 1) ≤ RingHom.ker (proj π n) :=
    (Ideal.pow_right_mono hT0 _).trans (h.pow_le_ker_proj n)
  refine ⟨T, hTfg, fun n ↦ le_antisymm (fun x hx ↦ ?_) (hTpow n)⟩
  obtain ⟨N, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.FG.pow (n := n + 1) hTfg)
  -- one approximation step
  have step (k : ℕ) (y : inverseLimit π) (hy : y ∈ RingHom.ker (proj π (n + k))) :
      ∃ c : Fin N → inverseLimit π, (∀ j, c j ∈ T ^ k) ∧
        y - ∑ j, c j * g j ∈ RingHom.ker (proj π (n + k + 1)) := by
    have h₁ : proj π (n + k + 1) y ∈ RingHom.ker (π (n + k)) := by
      rw [RingHom.mem_ker, π_proj]
      exact hy
    rw [h.ker_eq, ← hTm (n + k), ← Ideal.map_pow] at h₁
    obtain ⟨z, hz, hzy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ (proj_surjective π h.surjective _)).mp h₁
    have hz' : z ∈ T ^ k • Submodule.span (inverseLimit π) (Set.range g) := by
      rw [hg, smul_eq_mul, ← pow_add]
      convert hz using 2
      lia
    obtain ⟨a, ha, rfl⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum _ g z).mp hz'
    refine ⟨fun j ↦ a j, ha, ?_⟩
    rw [Finsupp.sum_fintype a (fun i c ↦ c • g i) (fun i ↦ zero_smul _ _)] at hzy
    rw [RingHom.mem_ker, map_sub, ← hzy, sub_eq_zero]
    simp only [smul_eq_mul]
  choose! c hcT hc using step
  let ys : ℕ → inverseLimit π := fun k ↦ Nat.rec x (fun k yk ↦ yk - ∑ j, c k yk j * g j) k
  have hys (k : ℕ) : ys k ∈ RingHom.ker (proj π (n + k)) := by
    induction k with
    | zero => exact hx
    | succ k ih => exact hc k (ys k) ih
  let P : ℕ → Fin N → inverseLimit π := fun M j ↦ ∑ k ∈ Finset.range M, c k (ys k) j
  have htel (M : ℕ) : x - ∑ j, P M j * g j = ys M := by
    induction M with
    | zero => simp [P, ys]
    | succ M ih =>
      simp only [P, Finset.sum_range_succ, add_mul, Finset.sum_add_distrib]
      rw [← sub_sub, ih]
  have hTker (m : ℕ) : T ^ (m + 1) ≤ RingHom.ker (proj π m) := hTpow m
  have hcompat (j : Fin N) (m : ℕ) :
      π m (proj π (m + 1) (P (m + 2) j)) = proj π m (P (m + 1) j) := by
    rw [π_proj]
    simp only [P]
    rw [Finset.sum_range_succ _ (m + 1), map_add, add_eq_left]
    exact hTker m (hcT (m + 1) (ys (m + 1)) (hys (m + 1)) j)
  let C : Fin N → inverseLimit π := fun j ↦
    ⟨fun m ↦ proj π m (P (m + 1) j), fun m ↦ hcompat j m⟩
  have hxC : x = ∑ j, C j * g j := by
    refine ext π fun m ↦ ?_
    have h₀ : proj π m (ys (m + 1)) = 0 :=
      ker_proj_antitone π (show m ≤ n + (m + 1) by lia) (hys (m + 1))
    rw [← htel (m + 1), map_sub, sub_eq_zero] at h₀
    rw [h₀, map_sum, map_sum]
    simp only [map_mul]
    rfl
  rw [hxC, ← hg]
  exact Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- EGA 0_I, 7.2.7: for an adic inverse system with `ker (A₁ → A₀)` finitely generated,
`ker (lim Aₖ → Aₙ) = Jⁿ⁺¹` with `J = ker (lim Aₖ → A₀)`. -/
theorem ker_proj_eq (hJ : (RingHom.ker (π 0)).FG) (n : ℕ) :
    RingHom.ker (proj π n) = RingHom.ker (proj π 0) ^ (n + 1) := by
  obtain ⟨T, -, hT⟩ := h.exists_fg_ker_proj_eq hJ
  rw [hT, hT 0, zero_add, pow_one]

/-- EGA 0_I, 7.2.7: the ideal `J = ker (lim Aₖ → A₀)` is finitely generated. -/
theorem fg_ker_proj_zero (hJ : (RingHom.ker (π 0)).FG) : (RingHom.ker (proj π 0)).FG := by
  obtain ⟨T, hTfg, hT⟩ := h.exists_fg_ker_proj_eq hJ
  rw [hT 0, zero_add, pow_one]
  exact hTfg

/-- EGA 0_I, 7.2.7: `lim Aₙ ⧸ Jⁿ⁺¹ ≅ Aₙ`. -/
noncomputable def quotientEquiv (hJ : (RingHom.ker (π 0)).FG) (n : ℕ) :
    inverseLimit π ⧸ RingHom.ker (proj π 0) ^ (n + 1) ≃+* A n :=
  (Ideal.quotEquivOfEq (h.ker_proj_eq hJ n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (proj_surjective π h.surjective n))

@[simp]
lemma quotientEquiv_mk (hJ : (RingHom.ker (π 0)).FG) (n : ℕ) (x : inverseLimit π) :
    h.quotientEquiv hJ n (Ideal.Quotient.mk _ x) = proj π n x :=
  rfl

/-- EGA 0_I, 7.2.7: `lim Aₙ` is complete and separated for the `J`-adic topology. -/
theorem isAdicComplete (hJ : (RingHom.ker (π 0)).FG) :
    IsAdicComplete (RingHom.ker (proj π 0)) (inverseLimit π) := by
  have hker := h.ker_proj_eq hJ
  have hpow (m : ℕ) : (RingHom.ker (proj π 0) ^ m • ⊤ : Submodule (inverseLimit π)
      (inverseLimit π)) = RingHom.ker (proj π 0) ^ m := by
    rw [smul_eq_mul, Ideal.mul_top]
  refine { haus' := fun x hx ↦ ext π fun m ↦ ?_, prec' := fun f hf ↦ ?_ }
  · have := hx (m + 1)
    rw [SModEq.zero, hpow, ← hker, RingHom.mem_ker] at this
    rw [this, map_zero]
  · have hf' {a b : ℕ} (hab : a ≤ b) : f a - f b ∈ RingHom.ker (proj π 0) ^ a := by
      have := hf hab
      rwa [SModEq.sub_mem, hpow] at this
    refine ⟨⟨fun m ↦ proj π m (f (m + 1)), fun m ↦ ?_⟩, fun n ↦ ?_⟩
    · change π m (proj π (m + 1) (f (m + 1 + 1))) = proj π m (f (m + 1))
      rw [π_proj]
      have := hf' (show m + 1 ≤ m + 1 + 1 by lia)
      rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero] at this
      exact this.symm
    · rw [SModEq.sub_mem, hpow]
      cases n with
      | zero => rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
      | succ m =>
        rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
        rfl

/-- EGA 0_I, 7.2.7: the limit of an adic inverse system of rings with `A₀` noetherian and
`ker (A₁ → A₀)` finitely generated is noetherian. -/
theorem isNoetherianRing (hJ : (RingHom.ker (π 0)).FG) [IsNoetherianRing (A 0)] :
    IsNoetherianRing (inverseLimit π) := by
  have := h.isAdicComplete hJ
  have : IsNoetherianRing (inverseLimit π ⧸ RingHom.ker (proj π 0)) :=
    isNoetherianRing_of_ringEquiv (A 0)
      (RingHom.quotientKerEquivOfSurjective (proj_surjective π h.surjective 0)).symm
  exact Ideal.isNoetherianRing_of_isAdicComplete _ (h.fg_ker_proj_zero hJ)

end IsAdicInverseSystem

section QuotientPow

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The inverse system `⋯ → R ⧸ I³ → R ⧸ I² → R ⧸ I`. -/
abbrev quotientPowSystem (n : ℕ) : R ⧸ I ^ (n + 1 + 1) →+* R ⧸ I ^ (n + 1) :=
  Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))

lemma toZero_quotientPowSystem (n : ℕ) :
    toZero (A := fun n ↦ R ⧸ I ^ (n + 1)) (quotientPowSystem I) n =
      Ideal.Quotient.factorPow I (Nat.succ_le_succ (Nat.zero_le n)) := by
  induction n with
  | zero => ext; rfl
  | succ n ih =>
    rw [toZero, ih]
    ext
    rfl

/-- The inverse system `R ⧸ Iⁿ⁺¹` is adic. -/
theorem isAdicInverseSystem_quotientPow :
    IsAdicInverseSystem (A := fun n ↦ R ⧸ I ^ (n + 1)) (quotientPowSystem I) where
  surjective _ := Ideal.Quotient.factor_surjective _
  ker_eq n := by
    rw [toZero_quotientPowSystem, Ideal.Quotient.factor_ker, Ideal.Quotient.factor_ker,
      ← Ideal.map_pow, ← pow_mul]
    simp only [Nat.succ_eq_add_one, zero_add, one_mul]

end QuotientPow

end Ring
