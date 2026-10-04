/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Polynomial.RationalRoot
import SGA.Foundations.Patching.ProjectiveLineNode

/-!
# The function field of the nodal model

With the notation of `SGA.Foundations.Patching.ProjectiveLineNode`, the polynomial
`T² - y T + t²` is irreducible over `k((t))(x)` (`y = 1/x`): its root `T₂` does not even lie in
`F_P = Frac k⟦y, t⟧` (`PatchingProjectiveLine.nodeRootTwo_not_mem_fieldP`), because `T₂` is
integral over `k⟦y⟧⟦t⟧`, which is integrally closed (a unique factorization domain, as a power
series ring over the principal ideal domain `k⟦y⟧`), while its coefficient of `t²` is `y⁻¹`. Hence
the intersection `k((t))(x)[u]` of the nodal model (`PatchingProjectiveLine.nodeBase`) is a field
(`PatchingProjectiveLine.isField_nodeBase`): the function field `k((t))(u)` of the generic fibre.
Likewise the node field `F_O = F_P[u]/(u² - y u + t²)` is a field
(`PatchingProjectiveLine.isField_nodeSubring`), and the node ring
`R̂_O = k⟦y⟧⟦t⟧[T]/(T² - y T + t²)` embeds into `F_℘ = k((y))((t))` through the first branch
(`PatchingProjectiveLine.injective_toField_comp_nodeMapOne`, because `T₁ ∉ F_P`), so it is a domain
(`PatchingProjectiveLine.isDomain_nodeRing`).
-/

universe u

open PowerSeries HahnSeries

namespace PatchingProjectiveLine

variable (k : Type u) [Field k]

/-- `k⟦y⟧⟦t⟧ → F_P`. -/
noncomputable def toFieldP : PowerSeries (PowerSeries k) →+* fieldP k :=
  ((toField k).comp (mapP k)).codRestrict (fieldP k) fun r ↦ Subfield.subset_closure ⟨r, rfl⟩

lemma nodeRootCoeff_one : nodeRootCoeff k 1 = 0 := by
  rw [nodeRootCoeff.eq_2]
  simp

lemma nodeRootCoeff_two : nodeRootCoeff k 2 = Polynomial.X := by
  rw [nodeRootCoeff.eq_2]
  simp [nodeRootCoeff_one]

/-- If `T₂ ∈ F_P`, then `T₂` comes from `k⟦y⟧⟦t⟧`: it is integral over this integrally closed
ring. -/
lemma exists_mapP_eq_nodeRootTwo' (h : nodeRootTwo k ∈ fieldP k) :
    ∃ r, mapP k r = nodeRootTwo' k := by
  let : Algebra (PowerSeries (PowerSeries k)) (fieldP k) := (toFieldP k).toAlgebra
  have hcoe : ∀ a, ((algebraMap (PowerSeries (PowerSeries k)) (fieldP k) a : fieldP k) :
      LaurentSeries (LaurentSeries k)) = toField k (mapP k a) := fun a ↦ rfl
  have hinj : Function.Injective (algebraMap (PowerSeries (PowerSeries k)) (fieldP k)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    rw [hcoe, hcoe] at this
    exact PowerSeries.map_injective _ ofPowerSeries_injective (ofPowerSeries_injective this)
  have : FaithfulSMul (PowerSeries (PowerSeries k)) (fieldP k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : IsFractionRing (PowerSeries (PowerSeries k)) (fieldP k) :=
    IsFractionRing.of_field _ _ fun z ↦ by
      obtain ⟨a, d, hz⟩ := (Subfield.mem_closure_range_iff ((toField k).comp (mapP k))).mp z.2
      refine ⟨a, d, Subtype.ext ?_⟩
      rw [Subfield.coe_div, hcoe, hcoe]
      exact hz.symm
  have hint : IsIntegral (PowerSeries (PowerSeries k)) (⟨nodeRootTwo k, h⟩ : fieldP k) := by
    refine ⟨nodePoly k, nodePoly_monic k, Subtype.val_injective ?_⟩
    have hcomp : (fieldP k).subtype.comp (algebraMap (PowerSeries (PowerSeries k)) (fieldP k)) =
        (toField k).comp (mapP k) := RingHom.ext hcoe
    have key := Polynomial.hom_eval₂ (nodePoly k) (algebraMap (PowerSeries (PowerSeries k))
      (fieldP k)) (fieldP k).subtype ⟨nodeRootTwo k, h⟩
    rw [hcomp] at key
    change (fieldP k).subtype _ = (0 : LaurentSeries (LaurentSeries k))
    rw [key]
    change Polynomial.eval₂ ((toField k).comp (mapP k)) (toField k (nodeRootTwo' k))
      (nodePoly k) = 0
    rw [← Polynomial.hom_eval₂, eval₂_nodePoly, nodeRootTwo'_sq, map_zero]
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have := congrArg Subtype.val hr
  rw [hcoe] at this
  exact ⟨r, ofPowerSeries_injective this⟩

/-- `T₂ ∉ F_P`: the root `T₂` is integral over the integrally closed ring `k⟦y⟧⟦t⟧` but does not
lie in it, since its coefficient of `t²` is `y⁻¹`. -/
theorem nodeRootTwo_not_mem_fieldP : nodeRootTwo k ∉ fieldP k := by
  intro h
  obtain ⟨r, hr'⟩ := exists_mapP_eq_nodeRootTwo' k h
  have h2 := congrArg (fun z ↦ HahnSeries.coeff (PowerSeries.coeff 2 z) (-1)) hr'
  simp only [mapP, nodeRootTwo', mapU, PowerSeries.coeff_map, nodeRoot, PowerSeries.coeff_mk,
    nodeRootCoeff_two, PowerSeries.coeff_coe] at h2
  simp [invX] at h2

lemma nodeRootTwo_not_mem_fieldBase : nodeRootTwo k ∉ fieldBase k := fun h ↦
  nodeRootTwo_not_mem_fieldP k (fieldBase_le k h).2

lemma nodeRootOne_not_mem_fieldBase : nodeRootOne k ∉ fieldBase k := fun h ↦
  nodeRootTwo_not_mem_fieldBase k (by
    rw [show nodeRootTwo k = yF k - nodeRootOne k by
      rw [← nodeRootOne_add_nodeRootTwo k]; ring]
    exact (fieldBase k).sub_mem (yF_mem_fieldBase k) h)

lemma nodeRootOne_not_mem_fieldP : nodeRootOne k ∉ fieldP k := fun h ↦
  nodeRootTwo_not_mem_fieldP k (by
    rw [show nodeRootTwo k = yF k - nodeRootOne k by
      rw [← nodeRootOne_add_nodeRootTwo k]; ring]
    exact (fieldP k).sub_mem (yF_mem_fieldP k) h)

/-- `F[T]/(T² - y T + t²)`, embedded in `F_℘ × F_℘` through the two roots, is a field as soon as
neither root lies in `F`. -/
theorem isField_nodePairs {F : Subfield (LaurentSeries (LaurentSeries k))} (hy : yF k ∈ F)
    (ht : tF k ∈ F) (h₁ : nodeRootOne k ∉ F) (h₂ : nodeRootTwo k ∉ F) :
    IsField (nodePairs k F hy ht) := by
  have hne : ∀ {α β : LaurentSeries (LaurentSeries k)}, α ∈ F → β ∈ F →
      ∀ {T : LaurentSeries (LaurentSeries k)}, T ∉ F → α + β * T = 0 →
        α = 0 ∧ β = 0 := fun {α β} hα hβ {T} hT h ↦ by
    by_cases hβ0 : β = 0
    · subst hβ0
      simpa using h
    · refine absurd ?_ hT
      rw [show T = -α / β by field_simp; linear_combination h]
      exact F.div_mem (F.neg_mem hα) hβ
  refine ⟨⟨0, 1, fun h ↦ ?_⟩, mul_comm, fun {z} hz ↦ ?_⟩
  · have := congrArg (fun z : nodePairs k F hy ht ↦ (z : LaurentSeries (LaurentSeries k) ×
      LaurentSeries (LaurentSeries k)).1) h
    simp at this
  obtain ⟨α, hα, β, hβ, hzαβ⟩ := z.2
  have hz0 : ∀ {T : LaurentSeries (LaurentSeries k)}, T ∉ F → α + β * T = 0 →
      False := fun hT h ↦ hz (by
    obtain ⟨rfl, rfl⟩ := hne hα hβ hT h
    exact Subtype.ext (by rw [hzαβ]; simp))
  have hz₁ : (z : LaurentSeries (LaurentSeries k) × LaurentSeries (LaurentSeries k)).1 ≠ 0 :=
    fun h ↦ hz0 h₁ (by rw [← h, hzαβ])
  have hz₂ : (z : LaurentSeries (LaurentSeries k) × LaurentSeries (LaurentSeries k)).2 ≠ 0 :=
    fun h ↦ hz0 h₂ (by rw [← h, hzαβ])
  obtain ⟨w, hw, hzw⟩ := nodePairs_exists_mul_eq_one k _ _ z.2 hz₁ hz₂
  exact ⟨⟨w, hw⟩, Subtype.ext hzw⟩

/-- **`k((t))(x)[u]` is a field**: `T² - y T + t²` is irreducible over `k((t))(x)`, so
`nodeBase` is the function field `k((t))(u)` of the generic fibre of the nodal model. -/
theorem isField_nodeBase : IsField (nodeBase k) :=
  isField_nodePairs k _ _ (nodeRootOne_not_mem_fieldBase k) (nodeRootTwo_not_mem_fieldBase k)

/-- The node field `F_O = F_P[u]/(u² - y u + t²)` (`nodeSubring`) is a field: `T² - y T + t²` is
irreducible over `F_P`. -/
theorem isField_nodeSubring : IsField (nodeSubring k) :=
  isField_nodePairs k _ _ (nodeRootOne_not_mem_fieldP k) (nodeRootTwo_not_mem_fieldP k)

lemma natDegree_nodePoly : (nodePoly k).natDegree = 2 := by
  have h : (Polynomial.C (-PowerSeries.C PowerSeries.X) * Polynomial.X +
      Polynomial.C (PowerSeries.X ^ 2) : Polynomial (PowerSeries (PowerSeries k))).degree <
      ((2 : ℕ) : WithBot ℕ) := by
    refine (Polynomial.degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · exact (Polynomial.degree_C_mul_X_le _).trans_lt (by decide)
    · exact Polynomial.degree_C_le.trans_lt (by decide)
  unfold nodePoly
  rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
    Polynomial.natDegree_X_pow]

lemma injective_toField_comp_mapP : Function.Injective ((toField k).comp (mapP k)) := by
  rw [RingHom.coe_comp]
  exact HahnSeries.ofPowerSeries_injective.comp
    (PowerSeries.map_injective _ HahnSeries.ofPowerSeries_injective)

/-- The node ring `R̂_O = k⟦y⟧⟦t⟧[T]/(T² - yT + t²)` embeds into `F_℘ = k((y))((t))` through the
first branch `T ↦ T₁`, because `T₁ ∉ F_P`. -/
theorem injective_toField_comp_nodeMapOne :
    Function.Injective ((toField k).comp (nodeMapOne k)) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective r
  have hne : nodePoly k ≠ 1 := fun h ↦ by
    have := natDegree_nodePoly k
    rw [h, Polynomial.natDegree_one] at this
    exact absurd this (by decide)
  obtain ⟨q', hq'def⟩ : ∃ q', q' = q %ₘ nodePoly k := ⟨_, rfl⟩
  have hq : AdjoinRoot.mk (nodePoly k) q = AdjoinRoot.mk (nodePoly k) q' := by
    rw [AdjoinRoot.mk_eq_mk]
    refine ⟨q /ₘ nodePoly k, ?_⟩
    have := Polynomial.modByMonic_add_div q (nodePoly k)
    rw [hq'def]
    linear_combination this.symm
  have hdeg : q'.natDegree ≤ 1 := by
    have := Polynomial.natDegree_modByMonic_lt q (nodePoly_monic k) hne
    rw [natDegree_nodePoly, ← hq'def] at this
    omega
  rw [hq, Polynomial.eq_X_add_C_of_natDegree_le_one hdeg] at hr ⊢
  set a := q'.coeff 0
  set b := q'.coeff 1
  have himage : (toField k).comp (nodeMapOne k)
      (AdjoinRoot.mk (nodePoly k) (Polynomial.C b * Polynomial.X + Polynomial.C a)) =
      toField k (mapP k a) + toField k (mapP k b) * nodeRootOne k := by
    simp only [RingHom.comp_apply, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
      nodeMapOne, AdjoinRoot.lift_of, AdjoinRoot.lift_root, nodeRootOne]
    ring
  rw [himage] at hr
  have hb : b = 0 := by
    by_contra hb
    have hb' : toField k (mapP k b) ≠ 0 := fun h ↦ hb (injective_toField_comp_mapP k
      (by rw [RingHom.comp_apply, h, map_zero]))
    refine nodeRootOne_not_mem_fieldP k ?_
    rw [show nodeRootOne k = -toField k (mapP k a) / toField k (mapP k b) by
      field_simp; linear_combination hr]
    exact (fieldP k).div_mem ((fieldP k).neg_mem (Subfield.subset_closure ⟨a, rfl⟩))
      (Subfield.subset_closure ⟨b, rfl⟩)
  rw [hb, map_zero, map_zero, zero_mul, add_zero] at hr
  have ha : a = 0 := injective_toField_comp_mapP k (by rw [RingHom.comp_apply, hr, map_zero])
  rw [hb, ha]
  simp

instance isDomain_nodeRing : IsDomain (nodeRing k) :=
  (injective_toField_comp_nodeMapOne k).isDomain _

end PatchingProjectiveLine
