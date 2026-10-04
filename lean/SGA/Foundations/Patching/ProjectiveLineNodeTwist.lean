/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.Away.Basic
import SGA.Foundations.Patching.ProjectiveLineNode

/-!
# Artin–Schreier classes on the punctured node

With the notation of `SGA.Foundations.Patching.ProjectiveLineNode`, the node ring
`R̂_O = k⟦y, t⟧[T]/(T² - y T + t²)` (geometrically `k⟦t, u, v⟧/(uv - t²)`, `u = T`, `v = y - T`)
has two reductions to the branches of the closed fibre, `t ↦ 0` with `u ↦ y, v ↦ 0`
(`PatchingProjectiveLine.nodeReduceOne`), resp. `u ↦ 0, v ↦ y`
(`PatchingProjectiveLine.nodeReduceTwo`). They extend to the punctured node
`R' = R̂_O[1/(u + v - 2t)]` (`PatchingProjectiveLine.nodePunctured`), with values in `k((y))`.

Main result (`PatchingProjectiveLine.exists_nodePunctured_reduce_eq`, the Artin–Schreier step of
the lemma on p. 23 of Harbater–Stevenson, *Patching and thickening problems*, J. Algebra 212
(1999)): in characteristic `p`, if every element of `k` is of the form `d^p - d` (e.g. `k`
algebraically closed), then for any `r, s ∈ k((y))` there is `e ∈ R'` whose two reductions are
`r` and `s` modulo `℘(k⟦y⟧) = {a^p - a}`. The element is
`e = (f(u) + g(v)) / (u + v - 2t)ⁿ`, where `f(y)/yⁿ` and `g(y)/yⁿ` are the principal parts of `r`
and `s`, and the remaining power series parts are Artin–Schreier coboundaries by Hensel's lemma
(`PatchingProjectiveLine.exists_pow_sub_eq`). In particular `R'/℘(R') → k((y))/℘ × k((y))/℘` is
onto: Artin–Schreier covers of the two branches of the closed fibre extend to the punctured node,
the step that Harbater–Stevenson iterate along a central series of a `p`-group.
-/

universe u

open PowerSeries HahnSeries

namespace PatchingProjectiveLine

variable (k : Type u) [Field k]

lemma eval₂_nodePoly_hom {S : Type*} [CommRing S] (f : PowerSeries (PowerSeries k) →+* S)
    (T : S) : (nodePoly k).eval₂ f T =
      T ^ 2 - f (PowerSeries.C PowerSeries.X) * T + f PowerSeries.X ^ 2 := by
  rw [nodePoly, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_C, map_neg,
    map_pow]
  ring

/-- The reduction of the node ring to the branch `v = 0` of the closed fibre:
`t ↦ 0`, `u ↦ y`. -/
noncomputable def nodeReduceOne : nodeRing k →+* PowerSeries k :=
  AdjoinRoot.lift PowerSeries.constantCoeff PowerSeries.X (by
    rw [eval₂_nodePoly_hom, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X]
    ring)

/-- The reduction of the node ring to the branch `u = 0` of the closed fibre:
`t ↦ 0`, `u ↦ 0` (so `v = y - u ↦ y`). -/
noncomputable def nodeReduceTwo : nodeRing k →+* PowerSeries k :=
  AdjoinRoot.lift PowerSeries.constantCoeff 0 (by
    rw [eval₂_nodePoly_hom, PowerSeries.constantCoeff_X]
    ring)

/-- `u + v - 2t = y - 2t` in the node ring. -/
noncomputable def nodeDelta : nodeRing k :=
  AdjoinRoot.of _ (PowerSeries.C PowerSeries.X - 2 * PowerSeries.X)

/-- The punctured node `R' = R̂_O[1/(u + v - 2t)]`. -/
abbrev nodePunctured : Type u :=
  Localization.Away (nodeDelta k)

lemma nodeReduceOne_delta : nodeReduceOne k (nodeDelta k) = PowerSeries.X := by
  simp [nodeReduceOne, nodeDelta]

lemma nodeReduceTwo_delta : nodeReduceTwo k (nodeDelta k) = PowerSeries.X := by
  simp [nodeReduceTwo, nodeDelta]

lemma isUnit_ofPowerSeries_X : IsUnit (ofPowerSeries ℤ k (PowerSeries.X : PowerSeries k)) := by
  rw [ofPowerSeries_X]
  exact isUnit_iff_ne_zero.mpr (single_ne_zero one_ne_zero)

/-- The reduction of the punctured node to `k((y))` along the branch `v = 0`. -/
noncomputable def nodePuncturedReduceOne : nodePunctured k →+* LaurentSeries k :=
  IsLocalization.Away.lift (nodeDelta k) (g := (ofPowerSeries ℤ k).comp (nodeReduceOne k))
    (by rw [RingHom.comp_apply, nodeReduceOne_delta]; exact isUnit_ofPowerSeries_X k)

/-- The reduction of the punctured node to `k((y))` along the branch `u = 0`. -/
noncomputable def nodePuncturedReduceTwo : nodePunctured k →+* LaurentSeries k :=
  IsLocalization.Away.lift (nodeDelta k) (g := (ofPowerSeries ℤ k).comp (nodeReduceTwo k))
    (by rw [RingHom.comp_apply, nodeReduceTwo_delta]; exact isUnit_ofPowerSeries_X k)

variable {k} (p : ℕ) [hp : Fact p.Prime] [CharP k p]

/-- Every power series over `k` is an Artin–Schreier coboundary `a^p - a`, if every element of
`k` is (Hensel's lemma for `T^p - T - z`, whose derivative is `-1`). -/
theorem exists_pow_sub_eq (hk : ∀ c : k, ∃ d : k, d ^ p - d = c) (z : PowerSeries k) :
    ∃ a : PowerSeries k, a ^ p - a = z := by
  obtain ⟨d, hd⟩ := hk (PowerSeries.constantCoeff z)
  have hz' : z - PowerSeries.C (PowerSeries.constantCoeff z) ∈
      Ideal.span {(PowerSeries.X : PowerSeries k)} := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simp
  have : CharP (PowerSeries k) p :=
    charP_of_injective_algebraMap (algebraMap k (PowerSeries k)).injective p
  set f : Polynomial (PowerSeries k) := Polynomial.X ^ p -
    (Polynomial.X + Polynomial.C (z - PowerSeries.C (PowerSeries.constantCoeff z)))
  have hf : f.Monic := by
    refine (Polynomial.monic_X_pow p).sub_of_left ?_
    refine (Polynomial.degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · rw [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast hp.out.one_lt
    · refine Polynomial.degree_C_le.trans_lt ?_
      rw [Polynomial.degree_X_pow]
      exact_mod_cast hp.out.pos
  have h₁ : f.eval 0 ∈ Ideal.span {(PowerSeries.X : PowerSeries k)} := by
    simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_C, zero_pow hp.out.ne_zero, zero_add, zero_sub]
    exact neg_mem hz'
  have h₂ : IsUnit (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries k)})
      (f.derivative.eval 0)) := by
    have : f.derivative.eval 0 = -1 := by
      simp [f, Polynomial.derivative_X_pow, CharP.cast_eq_zero]
    rw [this, map_neg, map_one]
    exact isUnit_one.neg
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian f hf 0 h₁ h₂
  have ha' : a ^ p - (a + (z - PowerSeries.C (PowerSeries.constantCoeff z))) = 0 := by
    simpa [f] using ha
  have hC : PowerSeries.C (d ^ p) - PowerSeries.C d =
      PowerSeries.C (PowerSeries.constantCoeff z) := by
    rw [← map_sub, hd]
  refine ⟨a + PowerSeries.C d, ?_⟩
  rw [add_pow_char, ← map_pow]
  linear_combination ha' + hC

omit hp [CharP k p] in
lemma invX_eq_sum (P : Polynomial k) {n : ℕ} (hn : P.natDegree < n) :
    invX k P = ∑ j ∈ Finset.range n, single (-(j : ℤ)) (P.coeff j) := by
  conv_lhs => rw [P.as_sum_range' n hn]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ invX_monomial k j _

omit hp [CharP k p] in
lemma ofPowerSeries_sum_C_mul_X_pow (c : ℕ → k) (n : ℕ) :
    ofPowerSeries ℤ k (∑ j ∈ Finset.range n, PowerSeries.C (c j) * PowerSeries.X ^ (n - j)) =
      ∑ j ∈ Finset.range n, single ((n - j : ℕ) : ℤ) (c j) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, map_pow, ofPowerSeries_C, ofPowerSeries_X, single_pow, one_pow,
    HahnSeries.C_mul_single_one, nsmul_one]

omit hp [CharP k p] in
/-- `(f(u) + g(v)) / (u + v - 2t)ⁿ` reduces to `f(y)/yⁿ` on the branch `v = 0` and to `g(y)/yⁿ`
on the branch `u = 0`: the principal parts of any two Laurent series are matched exactly. -/
theorem exists_nodePunctured_reduce_principal (P Q : Polynomial k) :
    ∃ e : nodePunctured k, nodePuncturedReduceOne k e = invX k P ∧
      nodePuncturedReduceTwo k e = invX k Q := by
  set n := P.natDegree + Q.natDegree + 1
  let cst : k → nodeRing k := fun c ↦ AdjoinRoot.of _ (PowerSeries.C (PowerSeries.C c))
  let vN : nodeRing k := AdjoinRoot.of _ (PowerSeries.C PowerSeries.X) - AdjoinRoot.root _
  let fU : nodeRing k := ∑ j ∈ Finset.range n, cst (P.coeff j) * AdjoinRoot.root _ ^ (n - j)
  let gV : nodeRing k := ∑ j ∈ Finset.range n, cst (Q.coeff j) * vN ^ (n - j)
  have h1f : nodeReduceOne k fU =
      ∑ j ∈ Finset.range n, PowerSeries.C (P.coeff j) * PowerSeries.X ^ (n - j) := by
    simp [fU, cst, nodeReduceOne]
  have h1g : nodeReduceOne k gV = 0 := by
    simp only [gV, cst, vN, nodeReduceOne, map_sum, map_mul, map_pow, map_sub,
      AdjoinRoot.lift_of, AdjoinRoot.lift_root, PowerSeries.constantCoeff_C, sub_self]
    exact Finset.sum_eq_zero fun j hj ↦ by
      rw [zero_pow (by have := Finset.mem_range.mp hj; omega), mul_zero]
  have h2f : nodeReduceTwo k fU = 0 := by
    simp only [fU, cst, nodeReduceTwo, map_sum, map_mul, map_pow, AdjoinRoot.lift_of,
      AdjoinRoot.lift_root]
    exact Finset.sum_eq_zero fun j hj ↦ by
      rw [zero_pow (by have := Finset.mem_range.mp hj; omega), mul_zero]
  have h2g : nodeReduceTwo k gV =
      ∑ j ∈ Finset.range n, PowerSeries.C (Q.coeff j) * PowerSeries.X ^ (n - j) := by
    simp [gV, cst, vN, nodeReduceTwo]
  set m : Submonoid.powers (nodeDelta k) := ⟨nodeDelta k ^ n, n, rfl⟩
  refine ⟨IsLocalization.mk' (nodePunctured k) (fU + gV) m, ?_, ?_⟩
  · have hspec := congrArg (nodePuncturedReduceOne k)
      (IsLocalization.mk'_spec (nodePunctured k) (fU + gV) m)
    rw [map_mul] at hspec
    simp only [nodePuncturedReduceOne, IsLocalization.Away.lift, IsLocalization.lift_eq,
      RingHom.comp_apply, map_add, map_pow, nodeReduceOne_delta, h1f, h1g, m] at hspec
    have hy : ofPowerSeries ℤ k (PowerSeries.X : PowerSeries k) ^ n ≠ 0 :=
      pow_ne_zero _ (isUnit_ofPowerSeries_X k).ne_zero
    refine mul_right_cancel₀ hy ?_
    rw [nodePuncturedReduceOne, IsLocalization.Away.lift] at *
    rw [hspec, map_zero, add_zero, ofPowerSeries_sum_C_mul_X_pow, invX_eq_sum P (n := n) (by omega),
      Finset.sum_mul,
      ofPowerSeries_X, single_pow, one_pow]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [single_mul_single, mul_one]
    congr 1
    have := Finset.mem_range.mp hj
    simp only [nsmul_eq_mul, mul_one]
    push_cast [Nat.cast_sub this.le]
    ring_nf
  · have hspec := congrArg (nodePuncturedReduceTwo k)
      (IsLocalization.mk'_spec (nodePunctured k) (fU + gV) m)
    rw [map_mul] at hspec
    simp only [nodePuncturedReduceTwo, IsLocalization.Away.lift, IsLocalization.lift_eq,
      RingHom.comp_apply, map_add, map_pow, nodeReduceTwo_delta, h2f, h2g, m] at hspec
    have hy : ofPowerSeries ℤ k (PowerSeries.X : PowerSeries k) ^ n ≠ 0 :=
      pow_ne_zero _ (isUnit_ofPowerSeries_X k).ne_zero
    refine mul_right_cancel₀ hy ?_
    rw [nodePuncturedReduceTwo, IsLocalization.Away.lift] at *
    rw [hspec, map_zero, zero_add, ofPowerSeries_sum_C_mul_X_pow, invX_eq_sum Q (n := n) (by omega),
      Finset.sum_mul,
      ofPowerSeries_X, single_pow, one_pow]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [single_mul_single, mul_one]
    congr 1
    have := Finset.mem_range.mp hj
    simp only [nsmul_eq_mul, mul_one]
    push_cast [Nat.cast_sub this.le]
    ring_nf

/-- **Artin–Schreier classes on the punctured node** (the Artin–Schreier step of
Harbater–Stevenson's node lemma): in characteristic `p`, if every element of `k` is of the form
`d^p - d`, then for all `r, s ∈ k((y))` there is `e ∈ R' = R̂_O[1/(u + v - 2t)]` whose reductions to
the two branches of the closed fibre are `r` and `s` modulo Artin–Schreier coboundaries
`a^p - a`, `a ∈ k⟦y⟧`. -/
theorem exists_nodePunctured_reduce_eq (hk : ∀ c : k, ∃ d : k, d ^ p - d = c)
    (r s : LaurentSeries k) :
    ∃ (e : nodePunctured k) (a b : PowerSeries k),
      nodePuncturedReduceOne k e + (ofPowerSeries ℤ k a ^ p - ofPowerSeries ℤ k a) = r ∧
        nodePuncturedReduceTwo k e + (ofPowerSeries ℤ k b ^ p - ofPowerSeries ℤ k b) = s := by
  obtain ⟨P, S, hr⟩ := exists_eq_invX_add_ofPowerSeries k r
  obtain ⟨Q, S', hs⟩ := exists_eq_invX_add_ofPowerSeries k s
  obtain ⟨e, he₁, he₂⟩ := exists_nodePunctured_reduce_principal P Q
  obtain ⟨a, ha⟩ := exists_pow_sub_eq p hk S
  obtain ⟨b, hb⟩ := exists_pow_sub_eq p hk S'
  refine ⟨e, a, b, ?_, ?_⟩
  · rw [he₁, ← map_pow, ← map_sub, ha, hr]
  · rw [he₂, ← map_pow, ← map_sub, hb, hs]

end PatchingProjectiveLine
