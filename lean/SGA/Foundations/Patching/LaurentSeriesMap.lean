/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Henselian
import SGA.Foundations.Patching.ProjectiveLine

/-!
# Coefficientwise maps of Hahn series and Laurent series

For a ring homomorphism `f : R →+* S`, `HahnSeries.mapRingHom Γ f : R⟦Γ⟧ →+* S⟦Γ⟧` applies `f` to
the coefficients (mathlib has the underlying map `HahnSeries.map` and its multiplicativity
`HahnSeries.map_mul`, but not the ring homomorphism). For Laurent series (`Γ = ℤ`) and a field
extension `k → K`, this is the map `k((y)) → K((y))`, and it is compatible with the local
coordinate `x ↦ y⁻¹` at `∞` (`PatchingProjectiveLine.mapRingHom_comp_invX`):

  `k[x] → k((y)) → K((y))` equals `k[x] → K[x] → K((y))`.

For `m ≥ 1`, `LaurentSeries.expand k m : k((y)) →+* k((y))` is `y ↦ yᵐ` (the extension
`k((y)) ⊆ k((y^{1/m}))`); it is compatible with `Polynomial.expand` through `x ↦ y⁻¹`
(`PatchingProjectiveLine.expand_comp_invX`). Over an algebraically closed field `k`, units of
`k⟦y⟧` have `n`-th roots for `n` invertible in `k` (Hensel's lemma,
`PowerSeries.exists_pow_eq_of_constantCoeff_ne_zero`), so that every Laurent series becomes an
`n`-th power in `k((y^{1/m}))` when `n ∣ m` (`LaurentSeries.exists_expand_eq_pow`).

## References

* [Stacks Project, Tag 0BHW] (Laurent series rings)
-/

universe u

namespace HahnSeries

variable (Γ : Type*) {R S T : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [Semiring R] [Semiring S] [Semiring T]

/-- The ring homomorphism `R⟦Γ⟧ →+* S⟦Γ⟧` applying `f : R →+* S` to the coefficients. -/
def mapRingHom (f : R →+* S) : R⟦Γ⟧ →+* S⟦Γ⟧ where
  toFun x := x.map f
  map_one' := by
    ext g
    by_cases h : g = 0 <;> simp [h, coeff_one]
  map_mul' _ _ := HahnSeries.map_mul (f : R →ₙ+* S)
  map_zero' := HahnSeries.map_zero (f : ZeroHom R S)
  map_add' _ _ := HahnSeries.map_add (f : R →+ S)

@[simp]
lemma coeff_mapRingHom (f : R →+* S) (x : R⟦Γ⟧) (g : Γ) :
    (mapRingHom Γ f x).coeff g = f (x.coeff g) :=
  rfl

lemma mapRingHom_apply (f : R →+* S) (x : R⟦Γ⟧) : mapRingHom Γ f x = x.map f :=
  rfl

lemma mapRingHom_single (f : R →+* S) (g : Γ) (a : R) :
    mapRingHom Γ f (single g a) = single g (f a) := by
  ext g'
  by_cases h : g' = g <;> simp [h]

lemma mapRingHom_C (f : R →+* S) (a : R) : mapRingHom Γ f (C a) = C (f a) :=
  map_C a f

lemma mapRingHom_comp_C (f : R →+* S) : (mapRingHom Γ f).comp C = C.comp f :=
  RingHom.ext (mapRingHom_C Γ f)

lemma mapRingHom_comp (f : R →+* S) (g : S →+* T) :
    mapRingHom Γ (g.comp f) = (mapRingHom Γ g).comp (mapRingHom Γ f) := by
  ext x a
  rfl

@[simp]
lemma mapRingHom_id : mapRingHom Γ (RingHom.id R) = RingHom.id _ := by
  ext x a
  rfl

lemma mapRingHom_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (mapRingHom Γ f) := by
  intro x y h
  ext g
  exact hf (by simpa using congrArg (coeff · g) h)

end HahnSeries

namespace PowerSeries

variable {k : Type u} [Field k]

/-- Hensel's lemma for `n`-th roots in `k⟦y⟧`: over an algebraically closed field `k`, a power
series with nonzero constant term is an `n`-th power when `n` is invertible in `k`. -/
theorem exists_pow_eq_of_constantCoeff_ne_zero [IsAlgClosed k] {n : ℕ} (hn : (n : k) ≠ 0)
    {u : k⟦X⟧} (hu : constantCoeff u ≠ 0) : ∃ v : k⟦X⟧, v ^ n = u := by
  have hn0 : n ≠ 0 := fun h ↦ hn (by simp [h])
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (constantCoeff u) (Nat.pos_of_ne_zero hn0)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hu (by rw [← hc, zero_pow hn0])
  let f : Polynomial k⟦X⟧ := Polynomial.X ^ n - Polynomial.C u
  have hf : f.Monic := Polynomial.monic_X_pow_sub_C u hn0
  have hmem : ∀ w : k⟦X⟧, constantCoeff w = 0 → w ∈ Ideal.span {(X : k⟦X⟧)} := fun w hw ↦ by
    rw [Ideal.mem_span_singleton]
    exact X_dvd_iff.mpr hw
  have h₁ : f.eval (C c) ∈ Ideal.span {(X : k⟦X⟧)} := hmem _ (by
    simp [f, hc])
  have h₂ : IsUnit (Ideal.Quotient.mk (Ideal.span {(X : k⟦X⟧)}) (f.derivative.eval (C c))) := by
    have hunit : IsUnit (f.derivative.eval (C c)) := by
      rw [isUnit_iff_constantCoeff]
      simp only [f, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
        Polynomial.derivative_C, sub_zero, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, map_mul, map_pow, constantCoeff_C]
      simp only [Polynomial.eval_natCast, map_natCast]
      exact (IsUnit.mk0 _ hn).mul ((IsUnit.mk0 c hc0).pow _)
    exact hunit.map _
  obtain ⟨v, hv, -⟩ := HenselianRing.is_henselian f hf (C c) h₁ h₂
  exact ⟨v, sub_eq_zero.mp (by simpa [f] using hv)⟩

end PowerSeries

namespace LaurentSeries

variable (k : Type u) [Field k]

/-- `y ↦ yᵐ` on Laurent series, for `m ≥ 1` (the inclusion `k((y)) ⊆ k((w))`, `y = wᵐ`). -/
noncomputable def expand (m : ℕ) [NeZero m] : k⸨X⸩ →+* k⸨X⸩ :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (m : ℤ))
    (mul_right_injective₀ (by exact_mod_cast NeZero.ne m))
    (fun _ _ ↦ mul_le_mul_iff_right₀ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)))

variable {k}

@[simp]
lemma expand_single (m : ℕ) [NeZero m] (j : ℤ) (c : k) :
    expand k m (HahnSeries.single j c) = HahnSeries.single ((m : ℤ) * j) c := by
  simp [expand, HahnSeries.embDomainRingHom]

@[simp]
lemma expand_C (m : ℕ) [NeZero m] (c : k) : expand k m (HahnSeries.C c) = HahnSeries.C c := by
  rw [HahnSeries.C_apply, expand_single, mul_zero]

/-- Over an algebraically closed field `k`, every Laurent series becomes an `n`-th power in
`k((y^{1/m}))` when `n ∣ m` and `n` is invertible in `k`: `y^j u = (y^{(m/n) j} v)ⁿ` with `vⁿ = u`
(`PowerSeries.exists_pow_eq_of_constantCoeff_ne_zero`). -/
theorem exists_expand_eq_pow [IsAlgClosed k] {m n : ℕ} [NeZero m] (hnm : n ∣ m)
    (hn : (n : k) ≠ 0) (a : k⸨X⸩) : ∃ b : k⸨X⸩, expand k m a = b ^ n := by
  by_cases ha : a = 0
  · refine ⟨0, ?_⟩
    have hn0 : n ≠ 0 := fun h ↦ hn (by simp [h])
    rw [ha, map_zero, zero_pow hn0]
  obtain ⟨d, rfl⟩ := hnm
  obtain ⟨v, hv⟩ := PowerSeries.exists_pow_eq_of_constantCoeff_ne_zero hn
    (u := a.powerSeriesPart) (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, powerSeriesPart_coeff, Nat.cast_zero,
        add_zero]
      exact HahnSeries.coeff_order_eq_zero.not.mpr ha)
  refine ⟨HahnSeries.single ((d : ℤ) * a.order) 1 *
    expand k (n * d) (HahnSeries.ofPowerSeries ℤ k v), ?_⟩
  conv_lhs => rw [← single_order_mul_powerSeriesPart a, ← hv]
  rw [map_mul, map_pow, mul_pow, expand_single, HahnSeries.single_pow, one_pow, map_pow,
    show ((n * d : ℕ) : ℤ) * a.order = n • ((d : ℤ) * a.order) by
      rw [nsmul_eq_mul]; push_cast; ring]

end LaurentSeries

namespace PatchingProjectiveLine

open HahnSeries

variable {k K : Type u} [Field k] [Field K]

/-- The local coordinate `x ↦ y⁻¹` at `∞` commutes with extension of scalars along `f : k → K`:
`k[x] → k((y)) → K((y))` equals `k[x] → K[x] → K((y))`. -/
lemma mapRingHom_comp_invX (f : k →+* K) :
    (mapRingHom ℤ f).comp (invX k) = (invX K).comp (Polynomial.mapRingHom f) := by
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · simp only [invX, RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C]
    exact mapRingHom_C ℤ f a
  · simp only [invX, RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, Polynomial.coe_mapRingHom, Polynomial.map_X]
    rw [mapRingHom_single, map_one]

variable (k) in
/-- `y ↦ yᵐ` and `x ↦ y⁻¹` commute with `x ↦ xᵐ`: `k[x] → k[x] → k((y))` equals
`k[x] → k((y)) → k((y))`. -/
lemma expand_comp_invX (m : ℕ) [NeZero m] :
    (LaurentSeries.expand k m).comp (invX k) = (invX k).comp (Polynomial.expand k m).toRingHom := by
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · simp [invX]
  · simp only [invX, RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.expand_X,
      Polynomial.eval₂_X_pow, LaurentSeries.expand_single, HahnSeries.single_pow, one_pow]
    rw [nsmul_eq_mul]

end PatchingProjectiveLine
