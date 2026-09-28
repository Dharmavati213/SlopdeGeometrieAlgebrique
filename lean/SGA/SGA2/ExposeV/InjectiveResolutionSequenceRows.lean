/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.InjectiveResolutionSequenceNat
import SGA.SGA2.ExposeV.InjectiveHorseshoeFunctor

/-! # Arbitrary specified resolution sequences as resolutions of rows

Every supplied augmented short exact sequence of injective resolutions is an
injective resolution of the entire original short complex. Its rows and
differentials retain the original three resolutions, while the horizontal
maps are the unique nonnegative maps extending to the supplied maps.
-/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Exactness of short complexes of rows is detected by the three projections. -/
theorem shortComplex_exact_of_projections (A : ShortComplex (ShortComplex C))
    (h₁ : (A.map ShortComplex.π₁).Exact)
    (h₂ : (A.map ShortComplex.π₂).Exact)
    (h₃ : (A.map ShortComplex.π₃).Exact) : A.Exact := by
  have z₁ : IsZero A.homology.X₁ :=
    ((A.map ShortComplex.π₁).exact_iff_isZero_homology.1 h₁).of_iso
      (A.mapHomologyIso ShortComplex.π₁).symm
  have z₂ : IsZero A.homology.X₂ :=
    ((A.map ShortComplex.π₂).exact_iff_isZero_homology.1 h₂).of_iso
      (A.mapHomologyIso ShortComplex.π₂).symm
  have z₃ : IsZero A.homology.X₃ :=
    ((A.map ShortComplex.π₃).exact_iff_isZero_homology.1 h₃).of_iso
      (A.mapHomologyIso ShortComplex.π₃).symm
  rw [A.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply ShortComplex.Hom.ext
  · exact z₁.eq_of_src _ _
  · exact z₂.eq_of_src _ _
  · exact z₃.eq_of_src _ _

namespace InjectiveResolutionSequence

variable {S : ShortComplex C} (R : InjectiveResolutionSequence S)

/-- Transpose the recovered nonnegative sequence, keeping its actual columns. -/
def rowCocomplex : CochainComplex (ShortComplex C) ℕ where
  X n := R.natSequence.map (eval C (ComplexShape.up ℕ) n)
  d i j :=
    { τ₁ := R.I₁.cocomplex.d i j
      τ₂ := R.I₂.cocomplex.d i j
      τ₃ := R.I₃.cocomplex.d i j
      comm₁₂ := (R.firstNatHom.hom.comm i j).symm
      comm₂₃ := (R.lastNatHom.hom.comm i j).symm }
  shape i j hij := by
    apply ShortComplex.Hom.ext
    · exact R.I₁.cocomplex.shape i j hij
    · exact R.I₂.cocomplex.shape i j hij
    · exact R.I₃.cocomplex.shape i j hij
  d_comp_d' i j k _ _ := by
    apply ShortComplex.Hom.ext
    · exact R.I₁.cocomplex.d_comp_d i j k
    · exact R.I₂.cocomplex.d_comp_d i j k
    · exact R.I₃.cocomplex.d_comp_d i j k

instance injective_rowCocomplex_X (n : ℕ) : Injective (R.rowCocomplex.X n) := by
  have : Injective (R.natSequence.map (eval C (ComplexShape.up ℕ) n)).X₁ := R.I₁.injective n
  have : Injective (R.natSequence.map (eval C (ComplexShape.up ℕ) n)).X₃ := R.I₃.injective n
  apply injective_of_shortExact
    (R.natSequence_shortExact.map_of_exact (eval C (ComplexShape.up ℕ) n))

/-- The original degree-zero augmentations, as a map of rows. -/
def rowι : S ⟶ R.rowCocomplex.X 0 where
  τ₁ := R.I₁.ι.f 0
  τ₂ := R.I₂.ι.f 0
  τ₃ := R.I₃.ι.f 0
  comm₁₂ := by simpa only [single₀_map_f_zero] using! R.firstNatHom.ι_f_zero_comp_hom_f_zero
  comm₂₃ := by simpa only [single₀_map_f_zero] using! R.lastNatHom.ι_f_zero_comp_hom_f_zero

instance mono_rowι : Mono R.rowι where
  right_cancellation {Z} a b h := by
    apply ShortComplex.Hom.ext
    · exact (cancel_mono (R.I₁.ι.f 0)).1 (congrArg ShortComplex.Hom.τ₁ h)
    · exact (cancel_mono (R.I₂.ι.f 0)).1 (congrArg ShortComplex.Hom.τ₂ h)
    · exact (cancel_mono (R.I₃.ι.f 0)).1 (congrArg ShortComplex.Hom.τ₃ h)

@[reassoc (attr := simp)]
theorem rowι_d : R.rowι ≫ R.rowCocomplex.d 0 1 = 0 := by
  apply ShortComplex.Hom.ext
  · exact R.I₁.ι_f_zero_comp_complex_d
  · exact R.I₂.ι_f_zero_comp_complex_d
  · exact R.I₃.ι_f_zero_comp_complex_d

/-- Exactness at degree zero is inherited from the unchanged three augmentations. -/
theorem rowExact₀ : (ShortComplex.mk R.rowι (R.rowCocomplex.d 0 1) R.rowι_d).Exact := by
  apply shortComplex_exact_of_projections
  · exact R.I₁.exact₀
  · exact R.I₂.exact₀
  · exact R.I₃.exact₀

/-- The original three positive-degree exactness statements give row exactness. -/
theorem rowCocomplex_exactAt_succ (n : ℕ) : R.rowCocomplex.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  apply shortComplex_exact_of_projections
  · exact R.I₁.exact_succ n
  · exact R.I₂.exact_succ n
  · exact R.I₃.exact_succ n

/-- The original augmentations, viewed as an augmentation of the entire row. -/
def rowAugmentation : (single₀ (ShortComplex C)).obj S ⟶ R.rowCocomplex :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨R.rowι, R.rowι_d⟩

@[simp]
theorem rowAugmentation_f_zero : R.rowAugmentation.f 0 = R.rowι :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

instance quasiIso_rowAugmentation : QuasiIso R.rowAugmentation := ⟨fun n => by
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨R.rowExact₀, by
        change Mono R.rowι
        infer_instance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    · rfl
    · rfl
    · exact R.rowCocomplex.shape 0 0 (by simp)
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact R.rowCocomplex_exactAt_succ n
    · apply CochainComplex.exactAt_succ_single_obj⟩

/-- Every supplied resolution sequence is an actual injective resolution of
the original short complex, without an additional existence hypothesis. -/
def rowResolution : InjectiveResolution S where
  cocomplex := R.rowCocomplex
  ι := R.rowAugmentation

end InjectiveResolutionSequence
end SGA.SGA2.ExposeV
