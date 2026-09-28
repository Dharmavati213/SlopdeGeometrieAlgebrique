/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulAugmentation
import SGA.SGA2.ExposeII.KoszulCofiber
import SGA.SGA2.ExposeII.KoszulExtComparison
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# The actual Koszul resolution of a regular sequence

The scalar-cofiber homology exact sequence proves positive Koszul homology
vanishing when the reversed list is weakly regular. For regular sequences
over noetherian local rings, permutability supplies this condition. The
original augmentation is therefore a quasi-isomorphism and the original
Koszul complex, with its already proved projective terms, is a projective
resolution of the original quotient. No exactness or comparison is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex Opposite RingTheory.Sequence

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- A scalar cofiber is acyclic in positive degrees if its source is so and
the scalar is regular on its actual zeroth homology. -/
theorem scalarCofiber_isZero_homology_pos
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (a : R)
    (hK : ∀ i : ℕ, 0 < i → IsZero (K.homology i))
    (ha : IsSMulRegular (K.homology 0) a) (i : ℕ) :
    IsZero ((homotopyCofiber (a • 𝟙 K)).homology (i + 1)) := by
  have hAnn : IsZero (ModuleCat.of R (Submodule.torsionBy R (K.homology i) a)) := by
    cases i with
    | zero =>
      rw [(isSMulRegular_iff_torsionBy_eq_bot (K.homology 0) a).mp ha]
      exact ModuleCat.isZero_of_subsingleton _
    | succ i =>
      have := ModuleCat.subsingleton_of_isZero (hK (i + 1) (Nat.zero_lt_succ i))
      exact ModuleCat.isZero_of_subsingleton _
  exact (scalarCofiberHomology_exact K a i).isZero_X₂
    ((hK (i + 1) (Nat.zero_lt_succ i)).eq_of_src _ 0) (hAnn.eq_of_tgt _ 0)

/-- The elementary cofiber induction, in the order used by the actual
recursive Koszul complex, needs only weak regularity of the reversed list. -/
theorem koszulComplex_isZero_homology_pos_of_reverse_isWeaklyRegular (fs : List R)
    (hreg : IsWeaklyRegular R fs.reverse) (i : ℕ) (hi : 0 < i) :
    IsZero ((koszulComplex (ModuleCat.of R R) fs).homology i) := by
  induction fs generalizing i with
  | nil => exact koszulComplex_isZero_homology (ModuleCat.of R R) [] i hi
  | cons f fs ih =>
    have hparts := (isWeaklyRegular_append_iff R fs.reverse [f]).mp
      (show IsWeaklyRegular R (fs.reverse ++ [f]) by simpa only [List.reverse_cons] using hreg)
    have hf := (isWeaklyRegular_singleton_iff _ f).mp hparts.2
    have hI : Ideal.ofList fs.reverse • (⊤ : Ideal R) = koszulIdeal fs := by
      simp only [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.ofList, koszulIdeal]
      congr 1
      ext x
      exact List.mem_reverse
    let e := Submodule.quotEquivOfEq _ (koszulIdeal fs) hI
    have hq : IsSMulRegular (R ⧸ koszulIdeal fs) f := (e.isSMulRegular_congr f).mp hf
    have hH : IsSMulRegular ((koszulComplex (ModuleCat.of R R) fs).homology 0) f :=
      ((koszulHomologyZeroIsoQuotient fs).toLinearEquiv.isSMulRegular_congr f).mpr hq
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact scalarCofiber_isZero_homology_pos _ f (ih hparts.1) hH j

/-- The actual augmentation is a quasi-isomorphism whenever its reversed
list is weakly regular; the degree-zero map is the existing quotient map. -/
theorem koszulAugmentation_quasiIso_of_reverse_isWeaklyRegular (fs : List R)
    (hreg : IsWeaklyRegular R fs.reverse) : QuasiIso (koszulAugmentation fs) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  cases i with
  | zero => infer_instance
  | succ i =>
    exact (koszulComplex_isZero_homology_pos_of_reverse_isWeaklyRegular fs hreg
      (i + 1) (Nat.zero_lt_succ i)).isIso
      (isZero_single_obj_homology (ComplexShape.down ℕ) 0
        (ModuleCat.of R (R ⧸ koszulIdeal fs)) (i + 1) (by omega)) _

/-- An actual regular Koszul augmentation over a noetherian local ring is
a quasi-isomorphism; permutability is proved, not an additional hypothesis. -/
theorem koszulAugmentation_quasiIso_of_isRegular [IsNoetherianRing R] [IsLocalRing R]
    (fs : List R) (hreg : IsRegular R fs) : QuasiIso (koszulAugmentation fs) :=
  koszulAugmentation_quasiIso_of_reverse_isWeaklyRegular fs
    (IsLocalRing.isRegular_of_perm hreg fs.reverse_perm.symm).1

/-- The original complex and original augmentation, packaged as a genuine
projective resolution of the quotient. -/
def koszulProjectiveResolutionOfReverse (fs : List R)
    (hreg : IsWeaklyRegular R fs.reverse) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ koszulIdeal fs)) where
  complex := koszulComplex (ModuleCat.of R R) fs
  π := koszulAugmentation fs
  quasiIso := koszulAugmentation_quasiIso_of_reverse_isWeaklyRegular fs hreg

/-- A regular sequence over a noetherian local ring gives its actual finite
Koszul projective resolution, rather than an unspecified resolution. -/
def koszulProjectiveResolution [IsNoetherianRing R] [IsLocalRing R]
    (fs : List R) (hreg : IsRegular R fs) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ koszulIdeal fs)) :=
  koszulProjectiveResolutionOfReverse fs
    (IsLocalRing.isRegular_of_perm hreg fs.reverse_perm.symm).1

/-- If an augmented complex is itself a projective resolution, the existing
comparison is exactly its canonical resolution isomorphism on Ext. -/
theorem extToHomComplexCohomology_eq_isoExt {X : ModuleCat.{u} R}
    (P : ProjectiveResolution X) (E : ModuleCat.{u} R) (i : ℕ) :
    extToHomComplexCohomology P.complex P.π E i = (P.isoExt i E).hom := by
  have h := projectiveResolution_isoExt_hom_naturality (𝟙 X) P (projectiveResolution X)
    (liftToResolution P.complex P.π (projectiveResolution X))
    (by
      rw [liftToResolution_commutes]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]) E i
  rw [op_id] at h
  erw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  exact h.symm

/-- The original finite-stage Ext-to-Koszul map is an isomorphism whenever
the reversed sequence is weakly regular. -/
theorem koszulExtComparison_isIso_of_reverse_isWeaklyRegular (fs : List R)
    (hreg : IsWeaklyRegular R fs.reverse) (E : ModuleCat.{u} R) (i : ℕ) :
    IsIso (koszulExtComparison fs E i) := by
  change IsIso (extToHomComplexCohomology
    (koszulProjectiveResolutionOfReverse fs hreg).complex
    (koszulProjectiveResolutionOfReverse fs hreg).π E i)
  rw [extToHomComplexCohomology_eq_isoExt]
  infer_instance

/-- For a regular sequence over a noetherian local ring the original
finite-stage comparison, not just its power-colimit, is an isomorphism. -/
theorem koszulExtComparison_isIso_of_isRegular [IsNoetherianRing R] [IsLocalRing R]
    (fs : List R) (hreg : IsRegular R fs) (E : ModuleCat.{u} R) (i : ℕ) :
    IsIso (koszulExtComparison fs E i) :=
  koszulExtComparison_isIso_of_reverse_isWeaklyRegular fs
    (IsLocalRing.isRegular_of_perm hreg fs.reverse_perm.symm).1 E i

/-- The actual finite-stage quotient-Ext/Koszul comparison as a natural
isomorphism in the coefficient module. -/
def koszulExtComparisonIsoOfIsRegular [IsNoetherianRing R] [IsLocalRing R]
    (fs : List R) (hreg : IsRegular R fs) (i : ℕ) :
    (_root_.Ext R (ModuleCat.{u} R) i).obj (op (ModuleCat.of R (R ⧸ koszulIdeal fs))) ≅
      koszulCohomologyFunctor fs i := by
  have h : ∀ E : ModuleCat.{u} R, IsIso ((koszulExtComparisonNatTrans fs i).app E) :=
    fun E ↦ koszulExtComparison_isIso_of_isRegular fs hreg E i
  have := NatIso.isIso_of_isIso_app (koszulExtComparisonNatTrans fs i)
  exact asIso (koszulExtComparisonNatTrans fs i)

end SGA.SGA2.ExposeII
