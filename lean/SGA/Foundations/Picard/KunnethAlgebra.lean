/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!
# Degree-one cohomology of a complex tensored with a vector space

Let `k` be a field, `d₀ : K₀ → K₁`, `d₁ : K₁ → K₂` linear maps of `k`-vector spaces (in the
application `d₁ ∘ d₀ = 0`, but this is not used) and `C` a `k`-vector space. If cocycles
`e₁, …, e_r ∈ K₁` represent a basis of `H¹ = ker d₁ / im d₀`, then every cocycle of `K• ⊗ₖ C`
is `∑ eₜ ⊗ φₜ + (d₀ ⊗ 1) w`
(`exists_eq_sum_tmul_add_of_rTensor_eq_zero`), and the `φₜ ∈ C` are unique
(`eq_zero_of_sum_tmul_mem_range_rTensor`): `H¹(K• ⊗ C) = H¹ ⊗ C`. This is the linear algebra of the
Künneth formula for `H¹(X ×ₖ Y, 𝒪)` with product covers, `Γ(U × V) = Γ(U) ⊗ₖ Γ(V)`, used in the
proof of the theorem of the cube.

The same holds for an arbitrary family of cocycles representing a basis of `H¹`, with
coefficients `φ : ι →₀ C` (`exists_eq_finsupp_sum_tmul_add_of_rTensor_eq_zero`,
`eq_zero_of_finsupp_sum_tmul_mem_range_rTensor`); such a family exists
(`cocycleBasis`, `cocycleBasis_spec`), with no finiteness assumption on `H¹`.

## References

* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
-/

open TensorProduct

namespace LinearMap

variable {k : Type*} [Field k] {K₀ K₁ K₂ C : Type*} [AddCommGroup K₀] [Module k K₀]
  [AddCommGroup K₁] [Module k K₁] [AddCommGroup K₂] [Module k K₂] [AddCommGroup C] [Module k C]
  (d₀ : K₀ →ₗ[k] K₁) (d₁ : K₁ →ₗ[k] K₂) {ι : Type*} [Fintype ι] (e : ι → K₁)

/-- If the cocycles `eₜ` and the coboundaries span the cocycles, every cocycle of `K• ⊗ C` is
`∑ eₜ ⊗ φₜ` plus a coboundary. -/
theorem exists_eq_sum_tmul_add_of_rTensor_eq_zero
    (hspan : ∀ x, d₁ x = 0 → ∃ c : ι → k, x - ∑ t, c t • e t ∈ LinearMap.range d₀)
    (z : K₁ ⊗[k] C) (hz : d₁.rTensor C z = 0) :
    ∃ (φ : ι → C) (w : K₀ ⊗[k] C), z = ∑ t, e t ⊗ₜ φ t + d₀.rTensor C w := by
  have hex := Module.Flat.rTensor_exact C (LinearMap.exact_subtype_ker_map d₁)
  suffices H : ∀ z' : (LinearMap.ker d₁) ⊗[k] C, ∃ (φ : ι → C) (w : K₀ ⊗[k] C),
      (LinearMap.ker d₁).subtype.rTensor C z' = ∑ t, e t ⊗ₜ φ t + d₀.rTensor C w by
    obtain ⟨z', rfl⟩ := (hex z).1 hz
    exact H z'
  intro z'
  induction z' using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul x c =>
    obtain ⟨a, y, hy⟩ := hspan x.1 x.2
    refine ⟨fun t ↦ a t • c, y ⊗ₜ c, ?_⟩
    simp only [rTensor_tmul, Submodule.coe_subtype, hy, sub_tmul, sum_tmul, smul_tmul]
    abel
  | add x y hx hy =>
    obtain ⟨φ, w, hw⟩ := hx
    obtain ⟨φ', w', hw'⟩ := hy
    refine ⟨φ + φ', w + w', ?_⟩
    simp only [map_add, hw, hw', Pi.add_apply, tmul_add, Finset.sum_add_distrib]
    abel

/-- If the cocycles `eₜ` are linearly independent modulo the coboundaries, the coefficients in
`∑ eₜ ⊗ φₜ` of a coboundary of `K• ⊗ C` vanish. -/
theorem eq_zero_of_sum_tmul_mem_range_rTensor
    (hind : ∀ c : ι → k, ∑ t, c t • e t ∈ LinearMap.range d₀ → c = 0) (φ : ι → C)
    (h : ∑ t, e t ⊗ₜ φ t ∈ LinearMap.range (d₀.rTensor C)) : φ = 0 := by
  classical
  let π := (LinearMap.range d₀).mkQ
  have hli : LinearIndependent k (fun t ↦ π (e t)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc t
    have : ∑ t, c t • e t ∈ LinearMap.range d₀ := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
      simpa only [map_smul] using hc
    rw [hind c this]
    rfl
  let b := Module.Basis.span hli
  obtain ⟨w, hw⟩ := h
  funext s
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (b.coord s)
  let μ : K₁ →ₗ[k] k := g ∘ₗ π
  have hμe (t : ι) : μ (e t) = if t = s then 1 else 0 := by
    have hmem : π (e t) ∈ Submodule.span k (Set.range fun t ↦ π (e t)) :=
      Submodule.subset_span ⟨t, rfl⟩
    have hb : (⟨π (e t), hmem⟩ : Submodule.span k (Set.range fun t ↦ π (e t))) = b t := by
      ext
      simp [b, Module.Basis.span_apply]
    have h1 : μ (e t) = b.coord s ⟨π (e t), hmem⟩ := by
      rw [← hg]
      rfl
    rw [h1, hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hμd : μ ∘ₗ d₀ = 0 := by
    ext x
    simp only [μ, π, LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self d₀ x), map_zero]
  have key := congrArg (fun z ↦ TensorProduct.lid k C (μ.rTensor C z)) hw
  simp only [← LinearMap.comp_apply, ← rTensor_comp, hμd, rTensor_zero, LinearMap.zero_apply,
    map_zero, map_sum, rTensor_tmul, TensorProduct.lid_tmul, hμe, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at key
  exact key.symm

section Finsupp

variable {ι' : Type*} (e' : ι' → K₁)

/-- If the cocycles `eₜ` and the coboundaries span the cocycles, every cocycle of `K• ⊗ C` is
`∑ eₜ ⊗ φₜ` (finitely many `φₜ ≠ 0`) plus a coboundary. -/
theorem exists_eq_finsupp_sum_tmul_add_of_rTensor_eq_zero
    (hspan : ∀ x, d₁ x = 0 → ∃ c : ι' →₀ k, x - c.sum (fun t a ↦ a • e' t) ∈ LinearMap.range d₀)
    (z : K₁ ⊗[k] C) (hz : d₁.rTensor C z = 0) :
    ∃ (φ : ι' →₀ C) (w : K₀ ⊗[k] C), z = φ.sum (fun t c ↦ e' t ⊗ₜ c) + d₀.rTensor C w := by
  classical
  have hex := Module.Flat.rTensor_exact C (LinearMap.exact_subtype_ker_map d₁)
  suffices H : ∀ z' : (LinearMap.ker d₁) ⊗[k] C, ∃ (φ : ι' →₀ C) (w : K₀ ⊗[k] C),
      (LinearMap.ker d₁).subtype.rTensor C z' = φ.sum (fun t c ↦ e' t ⊗ₜ c) + d₀.rTensor C w by
    obtain ⟨z', rfl⟩ := (hex z).1 hz
    exact H z'
  intro z'
  induction z' using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul x c =>
    obtain ⟨a, hy⟩ := hspan x.1 x.2
    obtain ⟨y, hy⟩ := hy
    refine ⟨a.mapRange (fun r ↦ r • c) (zero_smul k c), y ⊗ₜ c, ?_⟩
    rw [Finsupp.sum_mapRange_index (fun t ↦ tmul_zero C (e' t))]
    simp only [rTensor_tmul, Submodule.coe_subtype, hy, sub_tmul, Finsupp.sum, sum_tmul,
      smul_tmul]
    abel
  | add x y hx hy =>
    obtain ⟨φ, w, hw⟩ := hx
    obtain ⟨φ', w', hw'⟩ := hy
    refine ⟨φ + φ', w + w', ?_⟩
    rw [Finsupp.sum_add_index' (fun t ↦ tmul_zero C (e' t)) (fun t ↦ tmul_add (e' t))]
    simp only [map_add, hw, hw']
    abel

/-- If the cocycles `eₜ` are linearly independent modulo the coboundaries, the coefficients in
`∑ eₜ ⊗ φₜ` of a coboundary of `K• ⊗ C` vanish. -/
theorem eq_zero_of_finsupp_sum_tmul_mem_range_rTensor
    (hind : ∀ c : ι' →₀ k, c.sum (fun t a ↦ a • e' t) ∈ LinearMap.range d₀ → c = 0)
    (φ : ι' →₀ C) (h : φ.sum (fun t c ↦ e' t ⊗ₜ c) ∈ LinearMap.range (d₀.rTensor C)) :
    φ = 0 := by
  classical
  let π := (LinearMap.range d₀).mkQ
  have hli : LinearIndependent k (fun t ↦ π (e' t)) := by
    rw [linearIndependent_iff]
    intro c hc
    refine hind c ?_
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    rw [Finsupp.linearCombination_apply] at hc
    simpa only [Finsupp.sum, map_sum, map_smul] using hc
  let b := Module.Basis.span hli
  obtain ⟨w, hw⟩ := h
  ext s
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (b.coord s)
  let μ : K₁ →ₗ[k] k := g ∘ₗ π
  have hμe (t : ι') : μ (e' t) = if t = s then 1 else 0 := by
    have hmem : π (e' t) ∈ Submodule.span k (Set.range fun t ↦ π (e' t)) :=
      Submodule.subset_span ⟨t, rfl⟩
    have hb : (⟨π (e' t), hmem⟩ : Submodule.span k (Set.range fun t ↦ π (e' t))) = b t := by
      ext
      simp [b, Module.Basis.span_apply]
    have h1 : μ (e' t) = b.coord s ⟨π (e' t), hmem⟩ := by
      rw [← hg]
      rfl
    rw [h1, hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hμd : μ ∘ₗ d₀ = 0 := by
    ext x
    simp only [μ, π, LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self d₀ x), map_zero]
  have key := congrArg (fun z ↦ TensorProduct.lid k C (μ.rTensor C z)) hw
  simp only [← LinearMap.comp_apply, ← rTensor_comp, hμd, rTensor_zero, LinearMap.zero_apply,
    map_zero, Finsupp.sum, map_sum, rTensor_tmul, TensorProduct.lid_tmul, hμe, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finsupp.mem_support_iff] at key
  by_cases hs : φ s = 0
  · simp [hs]
  · simpa [hs] using key.symm

end Finsupp

/-- The index set of a basis of `H¹ = ker d₁ / (ker d₁ ∩ im d₀)`. -/
abbrev CocycleBasisIndex : Type _ :=
  Module.Basis.ofVectorSpaceIndex k
    (LinearMap.ker d₁ ⧸ (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype)

/-- Cocycles representing a basis of `H¹ = ker d₁ / (ker d₁ ∩ im d₀)`. -/
noncomputable def cocycleBasis (t : CocycleBasisIndex d₀ d₁) : K₁ :=
  (Quotient.out (Module.Basis.ofVectorSpace k
    (LinearMap.ker d₁ ⧸ (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype) t) :
      LinearMap.ker d₁).1

/-- The cocycles `cocycleBasis d₀ d₁` represent a basis of `H¹`: they are cocycles, they span the
cocycles modulo coboundaries, and they are independent modulo coboundaries. -/
theorem cocycleBasis_spec : (∀ t, d₁ (cocycleBasis d₀ d₁ t) = 0) ∧
    (∀ x, d₁ x = 0 → ∃ c : CocycleBasisIndex d₀ d₁ →₀ k,
      x - c.sum (fun t a ↦ a • cocycleBasis d₀ d₁ t) ∈ LinearMap.range d₀) ∧
    (∀ c : CocycleBasisIndex d₀ d₁ →₀ k,
      c.sum (fun t a ↦ a • cocycleBasis d₀ d₁ t) ∈ LinearMap.range d₀ → c = 0) := by
  classical
  let Z := LinearMap.ker d₁
  let B : Submodule k Z := (LinearMap.range d₀).comap Z.subtype
  let b := Module.Basis.ofVectorSpace k (Z ⧸ B)
  have he' (t) : B.mkQ (Quotient.out (b t) : Z) = b t := Quotient.out_eq _
  have hsum (c : CocycleBasisIndex d₀ d₁ →₀ k) :
      c.sum (fun t a ↦ a • cocycleBasis d₀ d₁ t) =
        (c.sum (fun t a ↦ a • (Quotient.out (b t) : Z)) : Z) := by
    simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul, cocycleBasis]
    rfl
  have hmk (c : CocycleBasisIndex d₀ d₁ →₀ k) :
      B.mkQ (c.sum (fun t a ↦ a • (Quotient.out (b t) : Z))) = Finsupp.linearCombination k b c := by
    simp only [Finsupp.sum, map_sum, map_smul, he', Finsupp.linearCombination_apply]
    rfl
  refine ⟨fun t ↦ (Quotient.out (b t)).2, fun x hx ↦ ?_, fun c hc ↦ ?_⟩
  · refine ⟨b.repr (B.mkQ ⟨x, hx⟩), ?_⟩
    have : B.mkQ (⟨x, hx⟩ - (b.repr (B.mkQ ⟨x, hx⟩)).sum
        (fun t a ↦ a • (Quotient.out (b t) : Z))) = 0 := by
      rw [map_sub, hmk, b.linearCombination_repr, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    rw [hsum]
    exact this
  · rw [hsum] at hc
    have : B.mkQ (c.sum (fun t a ↦ a • (Quotient.out (b t) : Z))) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hc
    rw [hmk] at this
    exact b.linearIndependent (this.trans (map_zero _).symm)

end LinearMap
