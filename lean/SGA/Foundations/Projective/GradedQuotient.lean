/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The grading of the quotient by a homogeneous ideal

Let `A = ⨁ᵢ 𝒜 i` be a graded `R`-algebra and `I` a homogeneous ideal. Then `A ⧸ I` is graded by
the images `ℬ i` of the `𝒜 i` (`HomogeneousIdeal.quotientGrading`, instance
`HomogeneousIdeal.gradedAlgebra`): the homogeneous components of the class of `a` are the classes
of the homogeneous components of `a` (`HomogeneousIdeal.coe_decompose_mk`). The projection
`A → A ⧸ I` is a graded ring homomorphism (`HomogeneousIdeal.quotientGradedRingHom`).

## References

* [N. Bourbaki, *Algèbre commutative*, III §1 no. 2][Bourbaki]
* [Stacks Project, Tag 00JM](https://stacks.math.columbia.edu/tag/00JM)
-/

open DirectSum

namespace HomogeneousIdeal

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)

/-- The grading of `A ⧸ I` by the images of the homogeneous components of `A`. -/
def quotientGrading (i : ι) : Submodule R (A ⧸ I.toIdeal) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

variable {I} in
lemma mk_mem_quotientGrading {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    Ideal.Quotient.mk I.toIdeal a ∈ I.quotientGrading i :=
  ⟨a, ha, rfl⟩

instance : SetLike.GradedMonoid I.quotientGrading where
  one_mem := mk_mem_quotientGrading SetLike.GradedOne.one_mem
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, map_mul (Ideal.Quotient.mkₐ R I.toIdeal) a b⟩

/-- The projection `𝒜 i → ℬ i`. -/
def quotientGradingMap (i : ι) : 𝒜 i →ₗ[R] I.quotientGrading i :=
  (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap.restrict fun _ ha ↦ mk_mem_quotientGrading ha

@[simp]
lemma coe_quotientGradingMap_apply (i : ι) (a : 𝒜 i) :
    (I.quotientGradingMap i a : A ⧸ I.toIdeal) = Ideal.Quotient.mk I.toIdeal (a : A) :=
  rfl

/-- The components `𝒜 i → ⨁ ℬ`. -/
private def auxMap (i : ι) : 𝒜 i →ₗ[R] ⨁ i, I.quotientGrading i :=
  (lof R ι (fun i ↦ I.quotientGrading i) i).comp (I.quotientGradingMap i)

private lemma auxMap_one : auxMap I 0 (GradedMonoid.GOne.one (A := fun i ↦ ↥(𝒜 i))) = 1 := by
  rw [auxMap, LinearMap.comp_apply, lof_eq_of, one_def]
  congr 1

private lemma auxMap_mul {i j : ι} (ai : 𝒜 i) (aj : 𝒜 j) :
    auxMap I (i + j) (GradedMonoid.GMul.mul (A := fun i ↦ ↥(𝒜 i)) ai aj) =
      auxMap I i ai * auxMap I j aj := by
  simp only [auxMap, LinearMap.comp_apply, lof_eq_of, of_mul_of]
  congr 1

/-- The graded map `⨁ 𝒜 i → ⨁ ℬ i`. -/
noncomputable def quotientDecomposeAux : (⨁ i, 𝒜 i) →ₐ[R] ⨁ i, I.quotientGrading i :=
  toAlgebra R _ (auxMap I) (auxMap_one I) (auxMap_mul I)

lemma quotientDecomposeAux_of (i : ι) (a : 𝒜 i) :
    I.quotientDecomposeAux (of _ i a) = of _ i (I.quotientGradingMap i a) :=
  (toSemiring_of (A := fun i ↦ ↥(𝒜 i)) (fun i ↦ (auxMap I i).toAddMonoidHom) (auxMap_one I)
    (auxMap_mul I) i a).trans (by simp [auxMap, lof_eq_of])

lemma quotientDecomposeAux_apply (x : ⨁ i, 𝒜 i) (i : ι) :
    I.quotientDecomposeAux x i = I.quotientGradingMap i (x i) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j b =>
    rw [quotientDecomposeAux_of]
    by_cases h : j = i
    · subst h
      simp only [of_eq_same]
    · rw [of_eq_of_ne _ _ _ (Ne.symm h), of_eq_of_ne _ _ _ (Ne.symm h), map_zero]
  | add x y hx hy => simp only [map_add, add_apply, hx, hy]

open Classical in
lemma quotientDecomposeAux_decompose (a : A) :
    I.quotientDecomposeAux (decompose 𝒜 a) =
      ∑ i ∈ (decompose 𝒜 a).support, of _ i (I.quotientGradingMap i (decompose 𝒜 a i)) := by
  classical
  conv_lhs => rw [← sum_support_of (decompose 𝒜 a)]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ quotientDecomposeAux_of I i _

/-- The decomposition of `A ⧸ I`. -/
noncomputable def quotientDecompose : A ⧸ I.toIdeal →ₐ[R] ⨁ i, I.quotientGrading i :=
  Ideal.Quotient.liftₐ I.toIdeal (I.quotientDecomposeAux.comp (decomposeAlgEquiv 𝒜).toAlgHom)
    fun a ha ↦ by
      change I.quotientDecomposeAux (decompose 𝒜 a) = 0
      rw [quotientDecomposeAux_decompose]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have : I.quotientGradingMap i (decompose 𝒜 a i) = 0 :=
        Subtype.ext ((Ideal.Quotient.eq_zero_iff_mem).mpr (I.isHomogeneous i ha))
      rw [this, map_zero]

lemma quotientDecompose_mk (a : A) :
    I.quotientDecompose (Ideal.Quotient.mk I.toIdeal a) = I.quotientDecomposeAux (decompose 𝒜 a) :=
  rfl

/-- `A ⧸ I` is graded by the images of the homogeneous components of `A`. -/
noncomputable instance gradedAlgebra : GradedAlgebra I.quotientGrading :=
  GradedAlgebra.ofAlgHom _ I.quotientDecompose
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      ext a
      classical
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply]
      rw [quotientDecompose_mk, quotientDecomposeAux_decompose, map_sum]
      simp only [coeAlgHom_of, coe_quotientGradingMap_apply]
      rw [← map_sum, sum_support_decompose])
    (by
      rintro i ⟨_, a, ha, rfl⟩
      change I.quotientDecompose (Ideal.Quotient.mk I.toIdeal a) = _
      rw [quotientDecompose_mk, decompose_of_mem 𝒜 ha, quotientDecomposeAux_of]
      rfl)

/-- The homogeneous components of the class of `a` are the classes of the homogeneous
components of `a`. -/
@[simp]
lemma coe_decompose_mk (a : A) (i : ι) :
    (decompose I.quotientGrading (Ideal.Quotient.mk I.toIdeal a) i : A ⧸ I.toIdeal) =
      Ideal.Quotient.mk I.toIdeal (decompose 𝒜 a i : A) := by
  change (I.quotientDecompose (Ideal.Quotient.mk I.toIdeal a) i : A ⧸ I.toIdeal) = _
  rw [quotientDecompose_mk, quotientDecomposeAux_apply]
  rfl

/-- The projection `A → A ⧸ I`, as a graded ring homomorphism. -/
def quotientGradedRingHom : 𝒜 →+*ᵍ I.quotientGrading where
  toRingHom := Ideal.Quotient.mk I.toIdeal
  map_mem ha := mk_mem_quotientGrading ha

end HomogeneousIdeal
