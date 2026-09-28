/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.TensorProduct.Maps
import SGA.SGA1.ExposeXII.Points

/-!
# SGA 1, Exposé XII, 1.1 b), c) and 1.2: affine spaces and fibre products on points

* XII.1.1 c) and the affine-space step of XII.1.1: `Points K K[σ]` is `K^σ`
  (`homeomorphMvPolynomial`).
* XII.1.1 b) and XII.1.2 ("`Φ` commutes with finite projective limits"), affine case: the points
  of `Y ×_X Z = Spec (B ⊗_A C)` are the pairs of points of `Y` and `Z` over the same point of
  `X`, with the subspace topology of `Y(K) × Z(K)` (`homeomorphTensorProduct`).
-/

noncomputable section

namespace SGA.SGA1.ExposeXII

open Topology Set TensorProduct

namespace Points

variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

/-- XII.1.1 c): the points of the affine space `Spec K[σ]` are `K^σ`, with its product
topology. -/
def homeomorphMvPolynomial (σ : Type*) : Points K (MvPolynomial σ K) ≃ₜ (σ → K) :=
  have hq : Function.Surjective (AlgHom.id K (MvPolynomial σ K)) := Function.surjective_id
  have hr : range (coords (AlgHom.id K (MvPolynomial σ K))) = univ := by
    rw [range_coords hq]
    refine eq_univ_of_forall fun x p hp ↦ ?_
    have : p = 0 := RingHom.mem_ker.mp hp
    rw [this, map_zero]
  ((isClosedEmbedding_coords hq).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hr)).trans (Homeomorph.Set.univ _)

lemma homeomorphMvPolynomial_apply {σ : Type*} (φ : Points K (MvPolynomial σ K))
    (i : σ) : homeomorphMvPolynomial σ φ i = φ (MvPolynomial.X i) := rfl

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B]
  [Algebra K C] [Algebra A B] [Algebra A C] [IsScalarTower K A B] [IsScalarTower K A C]

/-- The first projection `Y ×_X Z → Y`. -/
abbrev inl : B →ₐ[K] B ⊗[A] C := Algebra.TensorProduct.includeLeft

/-- The second projection `Y ×_X Z → Z`. -/
abbrev inr : C →ₐ[K] B ⊗[A] C := (Algebra.TensorProduct.includeRight (R := A)).restrictScalars K

omit [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] in
lemma proj_map_inl (χ : Points K (B ⊗[A] C)) :
    proj A B (map (inl (A := A) (C := C)) χ) = proj A C (map inr χ) :=
  ext fun a ↦ by
    change χ (algebraMap A B a ⊗ₜ 1) = χ (1 ⊗ₜ algebraMap A C a)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

variable (K A B C) in
/-- XII.1.2, affine case: the points of `Y ×_X Z` as a set of pairs. -/
abbrev FiberProduct : Set (Points K B × Points K C) := {p | proj A B p.1 = proj A C p.2}

omit [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] in
/-- The point of `Y ×_X Z` attached to points of `Y` and `Z` over the same point of `X`. -/
def pair (p : FiberProduct K A B C) : Points K (B ⊗[A] C) :=
  letI : Algebra A K := (proj A B p.1.1).toRingHom.toAlgebra
  let f : B →ₐ[A] K := { p.1.1.toRingHom with commutes' := fun _ ↦ rfl }
  let g : C →ₐ[A] K := { p.1.2.toRingHom with commutes' := fun a ↦ congr($(p.2.symm) a) }
  let L := Algebra.TensorProduct.lift f g fun _ _ ↦ Commute.all _ _
  ofAlgHom
    { L.toRingHom with
      commutes' := fun c ↦ by
        change L (algebraMap K B c ⊗ₜ 1) = c
        rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
        exact p.1.1.apply_algebraMap c }

omit [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] in
@[simp] lemma pair_tmul (p : FiberProduct K A B C) (b : B) (c : C) :
    pair p (b ⊗ₜ c) = p.1.1 b * p.1.2 c := rfl

/-- XII.1.1 b), XII.1.2, affine case: `(Y ×_X Z)(K) = Y(K) ×_{X(K)} Z(K)` as topological spaces. -/
def homeomorphTensorProduct : Points K (B ⊗[A] C) ≃ₜ FiberProduct K A B C where
  toFun χ := ⟨(map inl χ, map inr χ), proj_map_inl χ⟩
  invFun := pair
  left_inv χ := by
    ext t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      rw [pair_tmul]
      simp [← map_mul, Algebra.TensorProduct.tmul_mul_tmul]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  right_inv p := by
    refine Subtype.ext (Prod.ext (ext fun b ↦ ?_) (ext fun c ↦ ?_))
    · simp
    · simp
  continuous_toFun := ((continuous_map _).prodMk (continuous_map _)).subtype_mk _
  continuous_invFun := by
    refine continuous_iff.mpr fun t ↦ ?_
    induction t using TensorProduct.induction_on with
    | zero => simpa using continuous_const
    | tmul b c =>
      simp only [pair_tmul]
      exact ((continuous_apply b).comp (continuous_fst.comp continuous_subtype_val)).mul
        ((continuous_apply c).comp (continuous_snd.comp continuous_subtype_val))
    | add s t hs ht =>
      simp only [map_add]
      exact hs.add ht

end Points

end SGA.SGA1.ExposeXII
