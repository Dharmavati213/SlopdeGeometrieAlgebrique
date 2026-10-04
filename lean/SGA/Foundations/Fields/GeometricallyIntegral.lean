/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Nontrivial
import SGA.Foundations.Fields.GeometricallyConnected

/-!
# Tensor products of domains over an algebraically closed field

If `k` is algebraically closed and `R`, `S` are `k`-algebras which are domains, then `R ⊗ₖ S` is a
domain (`Algebra.TensorProduct.isDomain_of_isAlgClosed`): an integral scheme over an
algebraically closed field is geometrically integral, and a product of integral schemes over it
is integral.

The proof reduces to `R` of finite type (`Algebra.TensorProduct.exists_fg_mem_range_map`) and
uses the Nullstellensatz: write `z ∈ R ⊗ₖ S` as `∑ᵢ zᵢ ⊗ eᵢ` for a basis `(eᵢ)` of `S`; at a
`k`-point `x` of `R`, `z` restricts to `∑ᵢ x(zᵢ) eᵢ ∈ S`. If `z w = 0`, then at every `x` one of the
restrictions vanishes (`S` is a domain), so every product `zᵢ wⱼ` vanishes at every `k`-point of
`R`, hence is nilpotent, hence `0`.

We also record a piece of linear algebra used for normality of tensor products: for subspaces
`A ⊆ K`, `B ⊆ L` over a field, `(K ⊗ B) ∩ (A ⊗ L) = A ⊗ B` inside `K ⊗ L`
(`TensorProduct.mem_range_map_of_mem_range_lTensor_of_mem_range_rTensor`).

## References

* [Hartshorne, *Algebraic Geometry*, Exercise II.3.15]
* [EGA IV₂, 4.5.8, 4.6.1]
-/

open TensorProduct

namespace Algebra.TensorProduct

variable {k R S : Type*} [Field k] [IsAlgClosed k] [CommRing R] [CommRing S] [Algebra k R]
  [Algebra k S]

omit [IsAlgClosed k] in
/-- Restricting `z = ∑ᵢ zᵢ ⊗ eᵢ ∈ R ⊗ₖ S` to the fibre over a `k`-point `x` of `R` gives
`∑ᵢ x(zᵢ) eᵢ`: the `i`-th coordinate of the restriction is `x(zᵢ)`. -/
lemma coord_productMap_eq {κ : Type*} [DecidableEq κ] (𝒞 : Module.Basis κ k S)
    (x : R →ₐ[k] k) (z : R ⊗[k] S) (i : κ) :
    𝒞.coord i (productMap ((Algebra.ofId k S).comp x) (AlgHom.id k S) z) =
      x (equivFinsuppOfBasisRight 𝒞 z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [productMap_apply_tmul, equivFinsuppOfBasisRight_apply_tmul_apply, AlgHom.comp_apply,
      AlgHom.id_apply, Algebra.ofId_apply, ← Algebra.smul_def, map_smul, map_smul,
      Module.Basis.coord_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw]

/-- The finitely generated case of `isDomain_of_isAlgClosed`: if `R` is a domain of finite type
over the algebraically closed field `k` and `S` a domain over `k`, then `R ⊗ₖ S` has no zero
divisors. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero_of_finiteType [Algebra.FiniteType k R] [IsDomain R]
    [IsDomain S] {z w : R ⊗[k] S} (h : z * w = 0) : z = 0 ∨ w = 0 := by
  classical
  let 𝒞 := Module.Free.chooseBasis k S
  let c := equivFinsuppOfBasisRight (M := R) 𝒞
  let ρ : (R →ₐ[k] k) → R ⊗[k] S →ₐ[k] S := fun x ↦
    productMap ((Algebra.ofId k S).comp x) (AlgHom.id k S)
  -- at every `k`-point, the restriction of `z` or that of `w` vanishes
  have hx : ∀ x : R →ₐ[k] k, ρ x z = 0 ∨ ρ x w = 0 := fun x ↦
    mul_eq_zero.mp (by rw [← map_mul, h, map_zero])
  have hcoord : ∀ (x : R →ₐ[k] k) (y : R ⊗[k] S), ρ x y = 0 → ∀ i, x (c y i) = 0 :=
    fun x y hy i ↦ by rw [← coord_productMap_eq 𝒞 x y i]; simp [ρ, hy]
  by_cases hz : z = 0
  · exact Or.inl hz
  refine Or.inr (c.injective ?_)
  rw [map_zero]
  obtain ⟨i, hi⟩ : ∃ i, c z i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hz (c.injective (by rw [map_zero]; exact Finsupp.ext hall))
  ext j
  -- `c z i * c w j` vanishes at every `k`-point of `R`
  have hnil : IsNilpotent (c z i * c w j) :=
    IsAlgClosed.isNilpotent_of_forall_algHom_eq_zero (k := k) fun x ↦ by
      rw [map_mul]
      rcases hx x with h₁ | h₂
      · rw [hcoord x z h₁ i, zero_mul]
      · rw [hcoord x w h₂ j, mul_zero]
  rcases mul_eq_zero.mp hnil.eq_zero with h0 | h0
  · exact absurd h0 hi
  · exact h0

/-- **Products of integral schemes over an algebraically closed field are integral**: if `k` is
algebraically closed and `R`, `S` are `k`-algebras which are domains, then `R ⊗ₖ S` is a domain. -/
theorem isDomain_of_isAlgClosed [IsDomain R] [IsDomain S] : IsDomain (R ⊗[k] S) := by
  have : Nontrivial (R ⊗[k] S) := nontrivial_of_algebraMap_injective_of_isDomain k R S
    (algebraMap k R).injective (algebraMap k S).injective
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {z w} h ↦ ?_⟩
  obtain ⟨R₀, S₀, hR₀, -, z₀, rfl⟩ := exists_fg_mem_range_map z
  obtain ⟨R₁, S₁, hR₁, -, w₁, rfl⟩ := exists_fg_mem_range_map w
  change map R₀.val S₀.val z₀ * map R₁.val S₁.val w₁ = 0 at h
  change map R₀.val S₀.val z₀ = 0 ∨ map R₁.val S₁.val w₁ = 0
  -- move both factors to `(R₀ ⊔ R₁) ⊗ₖ (S₀ ⊔ S₁)`
  let R' := R₀ ⊔ R₁
  let S' := S₀ ⊔ S₁
  have : Algebra.FiniteType k R' := (Subalgebra.fg_iff_finiteType R').mp (hR₀.sup hR₁)
  have hmap : ∀ (R'' : Subalgebra k R) (S'' : Subalgebra k S) (hR : R'' ≤ R') (hS : S'' ≤ S')
      (y : R'' ⊗[k] S''), map R''.val S''.val y =
        map R'.val S'.val (map (Subalgebra.inclusion hR) (Subalgebra.inclusion hS) y) := by
    intro R'' S'' hR hS y
    rw [← AlgHom.comp_apply, ← map_comp]
    rfl
  have : Module.Flat k R' := Module.Flat.of_free
  have : Module.Flat k S' := Module.Flat.of_free
  have hinj : Function.Injective (map R'.val S'.val) :=
    TensorProduct.map_injective_of_flat_flat R'.val.toLinearMap S'.val.toLinearMap
      Subtype.val_injective Subtype.val_injective
  rw [hmap R₀ S₀ le_sup_left le_sup_left, hmap R₁ S₁ le_sup_right le_sup_right] at h ⊢
  rw [← map_mul, ← map_zero (map R'.val S'.val)] at h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero_of_finiteType (hinj h) with h' | h'
  · exact Or.inl (by rw [h', map_zero])
  · exact Or.inr (by rw [h', map_zero])

end Algebra.TensorProduct

namespace TensorProduct

variable {k A K B L : Type*} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup K] [Module k K]
  [AddCommGroup B] [Module k B] [AddCommGroup L] [Module k L]

/-- Over a field `k`, let `A ⊆ K` and `B ⊆ L` be subspaces (given by injective linear maps `i`,
`j`). Inside `K ⊗ₖ L`, the intersection of `K ⊗ₖ B` and `A ⊗ₖ L` is `A ⊗ₖ B`. -/
theorem mem_range_map_of_mem_range_lTensor_of_mem_range_rTensor (i : A →ₗ[k] K)
    (j : B →ₗ[k] L) (hj : Function.Injective j) {y : K ⊗[k] L}
    (h₁ : y ∈ LinearMap.range (j.lTensor K)) (h₂ : y ∈ LinearMap.range (i.rTensor L)) :
    y ∈ LinearMap.range (map i j) := by
  let π := (LinearMap.range i).mkQ
  have hex : Function.Exact i π := LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)
  have hπ : Function.Surjective π := Submodule.mkQ_surjective _
  have : Module.Flat k (K ⧸ LinearMap.range i) := Module.Flat.of_free
  have : Module.Flat k B := Module.Flat.of_free
  obtain ⟨u, rfl⟩ := h₁
  -- `u ∈ K ⊗ B` maps to `0` in `(K / A) ⊗ B`
  have hu : π.rTensor B u = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := K ⧸ LinearMap.range i) j hj
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply]
    exact (rTensor_exact L hex hπ _).mpr h₂
  obtain ⟨v, rfl⟩ := (rTensor_exact B hex hπ u).mp hu
  refine ⟨v, ?_⟩
  rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]

end TensorProduct
