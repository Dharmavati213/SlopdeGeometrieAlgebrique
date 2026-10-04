/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.LaurentSeries
import SGA.Foundations.Patching.Fields

/-!
# Patching on the projective line over `k⟦t⟧` at one point

Let `k` be a field, `x` a coordinate on `ℙ¹_{k⟦t⟧}` and `y = 1/x`. On the closed fibre `ℙ¹_k`
take the point `P : y = 0` (the point at infinity) and its complement `U = 𝔸¹_k`. The rings of
formal patching (Harbater; Harbater–Hartmann, *Patching over fields*, Israel J. Math. 176
(2010)) are
* `R̂_U = k[x]⟦t⟧`, the `t`-adic completion of `k⟦t⟧[x]`;
* `R̂_P = k⟦y⟧⟦t⟧ = k⟦y, t⟧`, the complete local ring at `P`;
* `R̂_℘ = k((y))⟦t⟧`, the complete local ring of the branch `℘` of the closed fibre at `P`;
with `R̂_U → R̂_℘` given by `x ↦ y⁻¹`. Their fraction fields `F_U`, `F_P` are subfields of
`F_℘ = k((y))((t))` (`PatchingProjectiveLine.fieldU`, `PatchingProjectiveLine.fieldP`).

Main result: `PatchingProjectiveLine.hasGLFactorization`, `GLₙ(F_℘) = GLₙ(F_U) · GLₙ(F_P)` for all
`n`. Together with Galois patching (`SGA.Foundations.Patching.Fields`), this realizes a finite
group `G = ⟨H₁, H₂⟩` as a Galois group over `F_U ∩ F_P` from Galois extensions of `F_U` and
`F_P` with groups `H₁`, `H₂` that split over `F_℘` (`PatchingProjectiveLine.exists_isGaloisGroup`,
split case). The ingredients are
* `k((y)) = k[y⁻¹] + k⟦y⟧` (`PatchingProjectiveLine.exists_eq_invX_add_ofPowerSeries`), hence the
  simultaneous factorization over `R̂_℘` (`Matrix.exists_eq_map_mul_map`);
* `F_P` is `t`-adically dense in `F_℘` (`PatchingProjectiveLine.exists_mem_fieldP_sub_eq`).

That `F_U ∩ F_P` is the rational function field `k((t))(x)` is proved in
`SGA.Foundations.Patching.ProjectiveLineIntersection` (`PatchingProjectiveLine.fieldU_inf_fieldP`).
-/

universe u v

open PowerSeries HahnSeries

/-- `C a * single m 1 = single m a` in a ring of Hahn series. -/
lemma HahnSeries.C_mul_single_one {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ] [Semiring R] (m : Γ) (a : R) :
    (HahnSeries.C a : HahnSeries Γ R) * single m 1 = single m a := by
  rw [HahnSeries.C_apply, single_mul_single, zero_add, mul_one]

/-- A Laurent series is `y^{-m}` times a power series, for some `m : ℕ`. -/
lemma LaurentSeries.exists_eq_single_neg_mul {R : Type*} [Semiring R] (z : LaurentSeries R) :
    ∃ (m : ℕ) (q : PowerSeries R), z = single (-(m : ℤ)) 1 * ofPowerSeries ℤ R q := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, -(m : ℤ) ≤ z.order := ⟨(-z.order).toNat, by omega⟩
  refine ⟨m, X ^ (z.order + m).toNat * z.powerSeriesPart, ?_⟩
  rw [map_mul, ofPowerSeries_X_pow, ← mul_assoc, single_mul_single, one_mul,
    show -(m : ℤ) + ((z.order + m).toNat : ℤ) = z.order by omega]
  exact (LaurentSeries.single_order_mul_powerSeriesPart z).symm

namespace PatchingProjectiveLine

variable (k : Type u) [Field k]

/-- `x ↦ y⁻¹`, from `k[x]` to `k((y))`. -/
noncomputable def invX : Polynomial k →+* LaurentSeries k :=
  Polynomial.eval₂RingHom (HahnSeries.C) (single (-1 : ℤ) 1)

/-- The map `R̂_U = k[x]⟦t⟧ → R̂_℘ = k((y))⟦t⟧`. -/
noncomputable def mapU : PowerSeries (Polynomial k) →+* PowerSeries (LaurentSeries k) :=
  PowerSeries.map (invX k)

/-- The map `R̂_P = k⟦y⟧⟦t⟧ → R̂_℘ = k((y))⟦t⟧`. -/
noncomputable def mapP : PowerSeries (PowerSeries k) →+* PowerSeries (LaurentSeries k) :=
  PowerSeries.map (HahnSeries.ofPowerSeries ℤ k)

/-- The embedding `R̂_℘ = k((y))⟦t⟧ → F_℘ = k((y))((t))`. -/
noncomputable abbrev toField : PowerSeries (LaurentSeries k) →+* LaurentSeries (LaurentSeries k) :=
  HahnSeries.ofPowerSeries ℤ (LaurentSeries k)

/-- `F_U`, the fraction field of `k[x]⟦t⟧` inside `k((y))((t))`. -/
noncomputable def fieldU : Subfield (LaurentSeries (LaurentSeries k)) :=
  Subfield.closure (Set.range fun r ↦ toField k (mapU k r))

/-- `F_P`, the fraction field of `k⟦y⟧⟦t⟧ = k⟦y, t⟧` inside `k((y))((t))`. -/
noncomputable def fieldP : Subfield (LaurentSeries (LaurentSeries k)) :=
  Subfield.closure (Set.range fun r ↦ toField k (mapP k r))

lemma invX_monomial (j : ℕ) (a : k) :
    invX k (Polynomial.monomial j a) = single (-(j : ℤ)) a := by
  rw [invX, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, single_pow, one_pow,
    HahnSeries.C_mul_single_one]
  congr 1
  simp

/-- `k((y)) = k[y⁻¹] + k⟦y⟧`: every Laurent series is the sum of its principal part, a polynomial
in `y⁻¹`, and a power series. -/
theorem exists_eq_invX_add_ofPowerSeries (z : LaurentSeries k) :
    ∃ (p : Polynomial k) (s : PowerSeries k), z = invX k p + ofPowerSeries ℤ k s := by
  obtain ⟨m, q, hz⟩ := LaurentSeries.exists_eq_single_neg_mul z
  have hq : ofPowerSeries ℤ k q = ofPowerSeries ℤ k (X ^ m * PowerSeries.mk fun i ↦
      coeff (i + m) q) + ofPowerSeries ℤ k (q.trunc m : PowerSeries k) := by
    conv_lhs => rw [eq_X_pow_mul_shift_add_trunc m q]
    rw [map_add]
  refine ⟨∑ i ∈ Finset.range m, Polynomial.monomial (m - i) (coeff i q),
    PowerSeries.mk fun i ↦ coeff (i + m) q, ?_⟩
  rw [hz, hq, mul_add, map_mul, ofPowerSeries_X_pow, ← mul_assoc, single_mul_single,
    neg_add_cancel, one_mul, single_zero_one, one_mul, add_comm]
  congr 1
  rw [trunc_apply, Finset.range_eq_Ico, Polynomial.coeToPowerSeries.ringHom_apply.symm, map_sum,
    map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial, monomial_eq_C_mul_X_pow,
    map_mul, ofPowerSeries_C, ofPowerSeries_X_pow, HahnSeries.C_mul_single_one, single_mul_single,
    one_mul, invX_monomial]
  have := (Finset.mem_Ico.mp hi).2
  rw [Nat.cast_sub this.le, show -(m : ℤ) + i = -((m : ℤ) - i) by ring]

/-- `R̂_℘ = R̂_U + R̂_P + t R̂_℘`, the decomposition behind the simultaneous factorization. -/
lemma exists_eq_mapU_add_mapP_add_X_mul (r : PowerSeries (LaurentSeries k)) :
    ∃ a b c, r = mapU k a + mapP k b + X * c := by
  obtain ⟨p, s, hps⟩ := exists_eq_invX_add_ofPowerSeries k (constantCoeff r)
  refine ⟨PowerSeries.C p, PowerSeries.C s, mk fun n ↦ coeff (n + 1) r, ?_⟩
  conv_lhs => rw [eq_X_mul_shift_add_const r]
  rw [mapU, mapP, PowerSeries.map_C, PowerSeries.map_C, hps, map_add]
  ring

lemma toField_X : toField k X = single 1 1 := ofPowerSeries_X

lemma mapP_X : mapP k X = X := map_X _

lemma single_one_mem_fieldP : (single 1 1 : LaurentSeries (LaurentSeries k)) ∈ fieldP k := by
  rw [← toField_X, ← mapP_X]
  exact Subfield.subset_closure ⟨X, rfl⟩

/-- The constants `k((y)) ⊆ k((y))((t))` lie in `F_P`. -/
lemma toField_C_mem_fieldP (c : LaurentSeries k) : toField k (PowerSeries.C c) ∈ fieldP k := by
  obtain ⟨m, q, rfl⟩ := LaurentSeries.exists_eq_single_neg_mul c
  have h1 : toField k (PowerSeries.C (single (1 : ℤ) (1 : k))) ∈ fieldP k := by
    have : PowerSeries.C (single (1 : ℤ) (1 : k)) = mapP k (PowerSeries.C X) := by
      rw [mapP, PowerSeries.map_C, ofPowerSeries_X]
    rw [this]
    exact Subfield.subset_closure ⟨_, rfl⟩
  have h2 : toField k (PowerSeries.C (ofPowerSeries ℤ k q)) ∈ fieldP k := by
    have : PowerSeries.C (ofPowerSeries ℤ k q) = mapP k (PowerSeries.C q) := by
      rw [mapP, PowerSeries.map_C]
    rw [this]
    exact Subfield.subset_closure ⟨_, rfl⟩
  have hz : ∀ (u : LaurentSeries k) (n : ℤ),
      toField k (PowerSeries.C (u ^ n)) = toField k (PowerSeries.C u) ^ n :=
    fun u n ↦ map_zpow₀ ((toField k).comp PowerSeries.C) u n
  rw [map_mul, map_mul, RatFunc.single_zpow, hz]
  exact (fieldP k).mul_mem ((fieldP k).zpow_mem h1 _) h2

/-- Polynomials in `t` over `k((y))` lie in `F_P`. -/
lemma toField_coe_polynomial_mem_fieldP (p : Polynomial (LaurentSeries k)) :
    toField k (p : PowerSeries (LaurentSeries k)) ∈ fieldP k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.coe_add, map_add]; exact (fieldP k).add_mem hp hq
  | monomial n c =>
    rw [Polynomial.coe_monomial, monomial_eq_C_mul_X_pow, map_mul, map_pow]
    refine (fieldP k).mul_mem (toField_C_mem_fieldP k c) ((fieldP k).pow_mem ?_ _)
    rw [toField_X]
    exact single_one_mem_fieldP k

/-- Every element of `k((y))((t))` becomes integral after multiplication by a power of `t`. -/
lemma exists_mul_pow_eq (z : LaurentSeries (LaurentSeries k)) :
    ∃ (a : ℕ) (r : PowerSeries (LaurentSeries k)), z * toField k X ^ a = toField k r := by
  obtain ⟨m, q, rfl⟩ := LaurentSeries.exists_eq_single_neg_mul z
  refine ⟨m, q, ?_⟩
  rw [toField_X, single_pow, one_pow, mul_comm, ← mul_assoc, single_mul_single, one_mul,
    nsmul_one, add_neg_cancel, single_zero_one, one_mul]

/-- `F_P` is `t`-adically dense in `k((y))((t))`. -/
lemma exists_mem_fieldP_sub_eq (z : LaurentSeries (LaurentSeries k)) (N : ℕ) :
    ∃ z' ∈ fieldP k, ∃ r : PowerSeries (LaurentSeries k),
      z - z' = toField k X ^ N * toField k r := by
  obtain ⟨m, q, rfl⟩ := LaurentSeries.exists_eq_single_neg_mul z
  have hq := eq_X_pow_mul_shift_add_trunc (N + m) q
  refine ⟨single (-(m : ℤ)) 1 * toField k (q.trunc (N + m) : PowerSeries (LaurentSeries k)),
    (fieldP k).mul_mem ?_ (toField_coe_polynomial_mem_fieldP k _),
    PowerSeries.mk fun i ↦ coeff (i + (N + m)) q, ?_⟩
  · rw [RatFunc.single_zpow]
    exact (fieldP k).zpow_mem (single_one_mem_fieldP k) _
  · have hq' : toField k q =
        toField k (X ^ (N + m) * PowerSeries.mk fun i ↦ coeff (i + (N + m)) q) +
        toField k (q.trunc (N + m) : PowerSeries (LaurentSeries k)) := by
      conv_lhs => rw [hq]
      rw [map_add]
    rw [hq', mul_add, add_sub_cancel_right, map_mul, map_pow, toField_X, ← mul_assoc,
      single_pow, one_pow, single_pow, one_pow, single_mul_single, one_mul]
    rw [show -(m : ℤ) + (N + m) • (1 : ℤ) = N • (1 : ℤ) by simp]

/-- **Factorization on `ℙ¹` over `k⟦t⟧` at one point** (Harbater–Hartmann): every invertible
matrix over `F_℘ = k((y))((t))` is a product of an invertible matrix over `F_U = Frac k[x]⟦t⟧`
and one over `F_P = Frac k⟦y, t⟧` (`x = y⁻¹`). -/
theorem hasGLFactorization (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (fieldU k).toSubring.HasGLFactorization (fieldP k).toSubring ι :=
  Subring.hasGLFactorization_of_isAdicComplete (toField k) (f₁ := mapU k) (f₂ := mapP k)
    (t₁ := X) (t₂ := X) (t := X) (map_X _) (map_X _) (exists_eq_mapU_add_mapP_add_X_mul k)
    (fun r ↦ Subfield.subset_closure ⟨r, rfl⟩) (fun r ↦ Subfield.subset_closure ⟨r, rfl⟩)
    (Subfield.isUnit_of_isUnit_coe _) (Subfield.isUnit_of_isUnit_coe _)
    (exists_mul_pow_eq k) (exists_mem_fieldP_sub_eq k)

/-- **Galois patching on `ℙ¹` over `k⟦t⟧`**, split case: a finite group `G` generated by
subgroups `H₁, H₂` is a Galois group over `F_U ∩ F_P` as soon as `H₁` is the Galois group of an
extension of `F_U = Frac k[x]⟦t⟧` and `H₂` that of an extension of `F_P = Frac k⟦y, t⟧`, both
contained in `F_℘ = k((y))((t))` (i.e. split over the branch `℘`). The extension is
`GaloisPatching.patched`, compatible with the local data by `GaloisPatching.exists_basis_patched`
and `hasGLFactorization`. -/
theorem exists_isGaloisGroup (G : Type v) [Group G] [Finite G]
    {H₁ H₂ : Subgroup G} (hH : H₁ ⊔ H₂ = ⊤)
    (E₁ : IntermediateField (fieldU k) (LaurentSeries (LaurentSeries k)))
    (E₂ : IntermediateField (fieldP k) (LaurentSeries (LaurentSeries k)))
    [IsGalois (fieldU k) E₁] [FiniteDimensional (fieldU k) E₁]
    [IsGalois (fieldP k) E₂] [FiniteDimensional (fieldP k) E₂]
    (ρ₁ : H₁ ≃* (E₁ ≃ₐ[fieldU k] E₁)) (ρ₂ : H₂ ≃* (E₂ ≃ₐ[fieldP k] E₂)) :
    ∃ (E : Type (max u v)) (_ : Field E) (_ : Algebra ↥(fieldU k ⊓ fieldP k) E)
      (_ : MulSemiringAction G E), IsGaloisGroup G ↥(fieldU k ⊓ fieldP k) E := by
  classical
  have := Fintype.ofFinite G
  exact Subfield.exists_isGaloisGroup_of_hasGLFactorization (hasGLFactorization k G) hH E₁ E₂ ρ₁
    ρ₂

end PatchingProjectiveLine
