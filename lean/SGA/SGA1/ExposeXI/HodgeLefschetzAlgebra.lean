/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.UnirationalCoversParametrization
import SGA.SGA1.ExposeXI.UnirationalCurves
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Unirationality under extension of the base field (XI.1.4, Lefschetz principle)

The algebra behind the Lefschetz principle for XI.1.4: unirationality is preserved by extension
of the base field. Let `k → K` be a field extension, `A` a `k`-domain with fraction field `F`
essentially of finite type over `k`, and `B = K ⊗_k A` (an `Algebra.IsPushout`), assumed to be a
domain, with fraction field `F'`. If `F` is unirational over `k`, then `F'` is unirational over
`K`.

The proof: `F` embeds over `k` into a rational function field `k(σ)` finite over `F`
(`exists_algHom_fractionRing_of_isUnirational`). Then `B = K ⊗_k A ↪ K ⊗_k k(σ) ↪ K(σ)`
(`HodgeLefschetz.tensorRatFunc_injective`: `k(σ)` and `K` are linearly disjoint over `k` inside
`K(σ)`), so `F' ↪ K(σ)`; the variables of `K(σ)` are integral over `F'` because they are
integral over `F`, so `K(σ)` is finite over `F'`, and it is purely transcendental over `K`.

* `HodgeLefschetz.ratFuncMap`: the map `k(σ) → K(σ)` of rational function fields;
* `HodgeLefschetz.tensorRatFunc`, `HodgeLefschetz.tensorRatFunc_injective`: the injective map
  `K ⊗_k k(σ) → K(σ)`;
* `HodgeLefschetz.eq_top_of_algebraMap_mem`: a subfield of `K(σ)` containing `K` and the
  variables is `K(σ)`; `HodgeLefschetz.isPurelyTranscendental_fractionRing`: `K(σ)` is purely
  transcendental over `K`;
* `isUnirational_of_isPushout`: the main result.

## References

* [S. Lang, *Algebra*, VIII §3] (linearly disjoint extensions; a purely transcendental extension
  `k(σ)` is linearly disjoint from every extension `K` of `k`).
-/

universe u

open TensorProduct

namespace SGA.SGA1.ExposeXI

namespace HodgeLefschetz

section RatFunc

variable (k K : Type u) [Field k] [Field K] [Algebra k K] (σ : Type u)

/-- The inclusion `k[σ] → K(σ)`, the polynomial map induced by `k → K` followed by
`K[σ] → K(σ)`. -/
noncomputable def polyToRatFunc :
    MvPolynomial σ k →ₐ[k] FractionRing (MvPolynomial σ K) :=
  (IsScalarTower.toAlgHom k (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))).comp
    (MvPolynomial.mapAlgHom (Algebra.ofId k K))

theorem polyToRatFunc_injective : Function.Injective (polyToRatFunc k K σ) :=
  (IsFractionRing.injective (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))).comp
    (MvPolynomial.map_injective _ (algebraMap k K).injective)

theorem polyToRatFunc_X (i : σ) :
    polyToRatFunc k K σ (MvPolynomial.X i) =
      algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (MvPolynomial.X i) := by
  simp [polyToRatFunc]

/-- The map `k(σ) → K(σ)` of rational function fields induced by `k → K`. -/
noncomputable def ratFuncMap :
    FractionRing (MvPolynomial σ k) →ₐ[k] FractionRing (MvPolynomial σ K) :=
  IsFractionRing.liftAlgHom (polyToRatFunc_injective k K σ)

theorem ratFuncMap_algebraMap (p : MvPolynomial σ k) :
    ratFuncMap k K σ (algebraMap _ _ p) = polyToRatFunc k K σ p :=
  IsFractionRing.lift_algebraMap (polyToRatFunc_injective k K σ) p

/-- The map `K ⊗_k k(σ) → K(σ)`, `c ⊗ x ↦ c x`. -/
noncomputable def tensorRatFunc :
    K ⊗[k] FractionRing (MvPolynomial σ k) →ₐ[K] FractionRing (MvPolynomial σ K) :=
  AlgHom.liftEquiv k K _ _ (ratFuncMap k K σ)

/-- Every element of `K ⊗_k k(σ)` becomes an element of `K ⊗_k k[σ]` after multiplication by
`1 ⊗ d` for some nonzero `d ∈ k[σ]` (common denominators). -/
theorem exists_mul_eq (z : K ⊗[k] FractionRing (MvPolynomial σ k)) :
    ∃ d : MvPolynomial σ k, d ≠ 0 ∧ ∃ w : K ⊗[k] MvPolynomial σ k,
      ((1 : K) ⊗ₜ[k] algebraMap _ (FractionRing (MvPolynomial σ k)) d) * z =
        Algebra.TensorProduct.map (AlgHom.id K K)
          (IsScalarTower.toAlgHom k (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))) w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul c x =>
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ k) x
    refine ⟨q, nonZeroDivisors.ne_zero hq, c ⊗ₜ p, ?_⟩
    have hq' : algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_div_cancel₀ _ hq']
    simp
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨d₁, hd₁, w₁, e₁⟩ := h₁
    obtain ⟨d₂, hd₂, w₂, e₂⟩ := h₂
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ((1 : K) ⊗ₜ d₂) * w₁ + ((1 : K) ⊗ₜ d₁) * w₂, ?_⟩
    have hD : ((1 : K) ⊗ₜ[k] algebraMap _ (FractionRing (MvPolynomial σ k)) (d₁ * d₂)) =
          ((1 : K) ⊗ₜ[k] algebraMap _ (FractionRing (MvPolynomial σ k)) d₁) *
            ((1 : K) ⊗ₜ[k] algebraMap _ (FractionRing (MvPolynomial σ k)) d₂) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
    rw [hD]
    simp only [map_add, map_mul, ← e₁, ← e₂, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
      id_eq, IsScalarTower.coe_toAlgHom']
    ring

/-- `K ⊗_k k(σ) → K(σ)` is injective: `k(σ)` and `K` are linearly disjoint over `k`. -/
theorem tensorRatFunc_injective : Function.Injective (tensorRatFunc k K σ) := by
  -- on `K ⊗_k k[σ] ≅ K[σ]` the map is the inclusion `K[σ] → K(σ)`
  have h₁ : (tensorRatFunc k K σ).comp (Algebra.TensorProduct.map (AlgHom.id K K)
      (IsScalarTower.toAlgHom k (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)))) =
      (IsScalarTower.toAlgHom K (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))).comp
        (MvPolynomial.algebraTensorAlgEquiv k K).toAlgHom := by
    refine Algebra.TensorProduct.ext' fun c p ↦ ?_
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, IsScalarTower.coe_toAlgHom', tensorRatFunc,
      AlgHom.liftEquiv_tmul, ratFuncMap_algebraMap]
    simp only [polyToRatFunc, AlgHom.coe_comp, Function.comp_apply, IsScalarTower.coe_toAlgHom',
      AlgEquiv.coe_toAlgHom, MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.mapAlgHom_apply,
      Algebra.smul_def, map_mul]
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))]
    rfl
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨d, hd, w, e⟩ := exists_mul_eq k K σ z
  have hw : w = 0 := by
    have h₂ := congrArg (fun φ ↦ φ w) h₁
    simp only [AlgHom.coe_comp, Function.comp_apply] at h₂
    rw [← e, map_mul, hz, mul_zero] at h₂
    have h₃ := (IsFractionRing.injective (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)))
      ((h₂.symm.trans (map_zero _).symm))
    exact (MvPolynomial.algebraTensorAlgEquiv k K).injective (h₃.trans (map_zero _).symm)
  rw [hw, map_zero] at e
  have hu : IsUnit ((1 : K) ⊗ₜ[k] algebraMap _ (FractionRing (MvPolynomial σ k)) d) := by
    have : IsUnit (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) d) :=
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hd)).isUnit
    exact this.map (Algebra.TensorProduct.includeRight (R := k) (A := K))
  exact (hu.mul_right_eq_zero).mp e

/-- A subfield of `K(σ)` containing `K` and the variables is all of `K(σ)`. -/
theorem eq_top_of_algebraMap_mem (E : Subfield (FractionRing (MvPolynomial σ K)))
    (hC : ∀ c : K, algebraMap K (FractionRing (MvPolynomial σ K)) c ∈ E)
    (hX : ∀ i, algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
      (MvPolynomial.X i) ∈ E) : E = ⊤ := by
  have hP (p : MvPolynomial σ K) :
      algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p ∈ E := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact hC c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp => rw [map_mul]; exact mul_mem hp (hX i)
  refine eq_top_iff.mpr fun z _ ↦ ?_
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ K) z
  exact div_mem (hP p) (hP q)

/-- The rational function field `K(σ)` is purely transcendental over `K`. -/
theorem isPurelyTranscendental_fractionRing :
    IsPurelyTranscendental K (FractionRing (MvPolynomial σ K)) := by
  let x : σ → FractionRing (MvPolynomial σ K) :=
    fun i ↦ algebraMap (MvPolynomial σ K) _ (MvPolynomial.X i)
  have hx : AlgebraicIndependent K x :=
    (MvPolynomial.algebraicIndependent_X σ K :
        AlgebraicIndependent K (MvPolynomial.X : σ → MvPolynomial σ K)).map'
      (f := IsScalarTower.toAlgHom K (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)))
      (IsFractionRing.injective _ _)
  refine ⟨Set.range x, hx.to_subtype_range, ?_⟩
  have h := eq_top_of_algebraMap_mem K σ (IntermediateField.adjoin K (Set.range x)).toSubfield
    (fun c ↦ IntermediateField.algebraMap_mem _ c)
    (fun i ↦ IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
  refine eq_top_iff.mpr fun z _ ↦ ?_
  have hz : z ∈ (IntermediateField.adjoin K (Set.range x)).toSubfield := h ▸ Subfield.mem_top z
  exact hz

end RatFunc

end HodgeLefschetz

open HodgeLefschetz

section Pushout

variable {k K A B F F' : Type u} [Field k] [Field K] [Algebra k K]
  [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Algebra A B]
  [Algebra K B] [IsScalarTower k A B] [IsScalarTower k K B] [Algebra.IsPushout k K A B]
  [Field F] [Algebra A F] [IsFractionRing A F] [Algebra k F] [IsScalarTower k A F]
  [Field F'] [Algebra B F'] [IsFractionRing B F'] [Algebra K F'] [IsScalarTower K B F']

variable (A B) in
include A B in
/-- **Unirationality under base field extension**: let `k → K` be a field extension, `A` a
`k`-algebra with fraction field `F` (so `A` is a domain), `F` essentially of finite type over `k`,
and `B = K ⊗_k A` (an `Algebra.IsPushout`) with fraction field `F'` (so `B` is a domain too, which
holds for instance when `k` is algebraically closed,
`Algebra.TensorProduct.isDomain_of_isAlgClosed`). If `F` is unirational over `k`, then `F'` is
unirational over `K`. -/
theorem isUnirational_of_isPushout [Algebra.EssFiniteType k F] (h : IsUnirational k F) :
    IsUnirational K F' := by
  obtain ⟨σ, _, ι, hfin⟩ := exists_algHom_fractionRing_of_isUnirational h
  let L := FractionRing (MvPolynomial σ K)
  -- `ι' : A ↪ k(σ)`
  let ι' : A →ₐ[k] FractionRing (MvPolynomial σ k) := ι.comp (IsScalarTower.toAlgHom k A F)
  have hι' : Function.Injective ι' := ι.injective.comp (IsFractionRing.injective A F)
  -- `θ : B = K ⊗_k A ↪ K ⊗_k k(σ) ↪ K(σ)`
  let θ : B →ₐ[K] L := (tensorRatFunc k K σ).comp ((Algebra.TensorProduct.map (AlgHom.id K K)
    ι').comp (Algebra.IsPushout.equiv k K A B).symm.toAlgHom)
  have hmap : Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) ι') := by
    have : ⇑(Algebra.TensorProduct.map (AlgHom.id K K) ι') = ⇑(ι'.toLinearMap.lTensor K) := by
      funext z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c a => simp
      | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    rw [this]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hι'
  have hθ : Function.Injective θ :=
    (tensorRatFunc_injective k K σ).comp (hmap.comp (AlgEquiv.injective _))
  have hθA (a : A) : θ (algebraMap A B a) = ratFuncMap k K σ (ι' a) := by
    simp only [θ, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
      Algebra.IsPushout.equiv_symm_algebraMap_right, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, tensorRatFunc, AlgHom.liftEquiv_tmul, one_smul]
  -- `ψ : F' ↪ K(σ)`
  let ψ : F' →ₐ[K] L := IsFractionRing.liftAlgHom hθ
  have hψB (b : B) : ψ (algebraMap B F' b) = θ b := IsFractionRing.lift_algebraMap hθ b
  -- `φ : F → F'`
  have hAB : Function.Injective (algebraMap A B) := by
    refine Function.Injective.of_comp (f := θ) ?_
    have : ⇑θ ∘ ⇑(algebraMap A B) = ⇑(ratFuncMap k K σ) ∘ ⇑ι' := funext hθA
    rw [this]
    exact (ratFuncMap k K σ).injective.comp hι'
  let φ : F →+* F' := IsFractionRing.lift (A := A) (g := (algebraMap B F').comp (algebraMap A B))
    ((IsFractionRing.injective B F').comp hAB)
  have hφ : (ψ : F' →+* L).comp φ =
      (ratFuncMap k K σ : FractionRing (MvPolynomial σ k) →+* L).comp
        (ι : F →+* FractionRing (MvPolynomial σ k)) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext fun a ↦ ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, φ, IsFractionRing.lift_algebraMap,
      AlgHom.coe_toRingHom, hψB, hθA, ι']
    rfl
  -- the variables of `K(σ)` are integral over `F'`
  let _ : Algebra F' L := ψ.toRingHom.toAlgebra
  have hint (i : σ) : IsIntegral F' (algebraMap (MvPolynomial σ K) L (MvPolynomial.X i)) := by
    let _ := ι.toRingHom.toAlgebra
    have : Module.Finite F (FractionRing (MvPolynomial σ k)) := hfin
    have : Algebra.IsIntegral F (FractionRing (MvPolynomial σ k)) :=
      Algebra.IsIntegral.of_finite F _
    obtain ⟨p, hp, hpx⟩ := Algebra.IsIntegral.isIntegral (R := F)
      (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) (MvPolynomial.X i))
    refine ⟨p.map φ, hp.map φ, ?_⟩
    have hX : algebraMap (MvPolynomial σ K) L (MvPolynomial.X i) =
        (ratFuncMap k K σ : FractionRing (MvPolynomial σ k) →+* L)
          (algebraMap (MvPolynomial σ k) _ (MvPolynomial.X i)) := by
      rw [AlgHom.coe_toRingHom, ratFuncMap_algebraMap, polyToRatFunc_X]
    have h' : (algebraMap F' L).comp φ =
        (ratFuncMap k K σ : FractionRing (MvPolynomial σ k) →+* L).comp
          (ι : F →+* FractionRing (MvPolynomial σ k)) := hφ
    rw [hX, Polynomial.eval₂_map, h', ← Polynomial.hom_eval₂]
    have h'' : (ι : F →+* FractionRing (MvPolynomial σ k)) =
        algebraMap F (FractionRing (MvPolynomial σ k)) := rfl
    rw [h'', hpx, map_zero]
  -- `K(σ)` is generated over `F'` by the variables, hence finite over `F'`
  let S : Set L := Set.range fun i ↦ algebraMap (MvPolynomial σ K) L (MvPolynomial.X i)
  have hE : IntermediateField.adjoin F' S = ⊤ := by
    have h := eq_top_of_algebraMap_mem K σ (IntermediateField.adjoin F' S).toSubfield
      (fun c ↦ by
        have : algebraMap K L c = algebraMap F' L (algebraMap K F' c) := (ψ.commutes c).symm
        rw [this]
        exact IntermediateField.algebraMap_mem _ _)
      (fun i ↦ IntermediateField.subset_adjoin F' _ ⟨i, rfl⟩)
    refine eq_top_iff.mpr fun z _ ↦ ?_
    have hz : z ∈ (IntermediateField.adjoin F' S).toSubfield := h ▸ Subfield.mem_top z
    exact hz
  have hS : FiniteDimensional F' (IntermediateField.adjoin F' S) :=
    IntermediateField.finiteDimensional_adjoin fun _ ⟨i, hi⟩ ↦ hi ▸ hint i
  rw [hE] at hS
  have hfin' : FiniteDimensional F' L :=
    (IntermediateField.topEquiv (F := F') (E := L)).toLinearEquiv.finiteDimensional
  -- conclusion
  refine ⟨L, inferInstance, ψ.toRingHom.toAlgebra, hfin', ?_⟩
  have e : ((ψ : F' →+* L).comp (algebraMap K F')).toAlgebra = (inferInstance : Algebra K L) :=
    Algebra.algebra_ext _ _ fun c ↦ ψ.commutes c
  change @IsPurelyTranscendental K L _ _ ((ψ : F' →+* L).comp (algebraMap K F')).toAlgebra
  rw [e]
  exact isPurelyTranscendental_fractionRing K σ

end Pushout

end SGA.SGA1.ExposeXI
