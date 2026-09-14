/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.InjectiveHorseshoeStep
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Iterating the injective horseshoe

The short exact cokernel rows are iterated to construct a cochain complex of
split injective rows. Its augmentation is exact at degree zero and the complex
is exact in every positive degree, also after each component projection.
-/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV.InjectiveHorseshoe

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable (S : ShortComplex C) (hS : S.ShortExact)

/-- The successive short exact rows of syzygies, starting with the given row. -/
def stage : ℕ → { T : ShortComplex C // T.ShortExact }
  | 0 => ⟨S, hS⟩
  | n + 1 => ⟨next (stage n).1 (stage n).2, next_shortExact (stage n).1 (stage n).2⟩

/-- The split injective row in degree `n`. -/
abbrev term (n : ℕ) : ShortComplex C := row (stage S hS n).1

/-- The embedding of the `n`th syzygy row. -/
abbrev ι (n : ℕ) : (stage S hS n).1 ⟶ term S hS n :=
  inclusion (stage S hS n).1 (stage S hS n).2

/-- The quotient onto the next syzygy row, using the actual cokernel. -/
abbrev π (n : ℕ) : term S hS n ⟶ (stage S hS (n + 1)).1 :=
  cokernel.π (ι S hS n)

/-- The horseshoe differential is a quotient followed by the next embedding. -/
def d (n : ℕ) : term S hS n ⟶ term S hS (n + 1) := π S hS n ≫ ι S hS (n + 1)

@[reassoc (attr := simp)]
theorem ι_d (n : ℕ) : ι S hS n ≫ d S hS n = 0 := by
  simp [d]

@[reassoc (attr := simp)]
theorem d_d (n : ℕ) : d S hS n ≫ d S hS (n + 1) = 0 := by
  simp [d, Category.assoc]

/-- The actual complex of split injective rows. -/
def cocomplex : CochainComplex (ShortComplex C) ℕ :=
  CochainComplex.of (term S hS) (d S hS) (d_d S hS)

@[simp]
theorem cocomplex_d (n : ℕ) : (cocomplex S hS).d n (n + 1) = d S hS n :=
  CochainComplex.of_d _ _ n

/-- Each syzygy row is the kernel of the next differential. -/
theorem exact_ι_d (n : ℕ) :
    (ShortComplex.mk (ι S hS n) (d S hS n) (ι_d S hS n)).Exact := by
  let φ : ShortComplex.mk (ι S hS n) (π S hS n) (by simp) ⟶
      ShortComplex.mk (ι S hS n) (d S hS n) (ι_d S hS n) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := ι S hS (n + 1) }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
    (ShortComplex.exact_cokernel (ι S hS n))

/-- The constructed complex is exact in every positive degree. -/
theorem cocomplex_exactAt_succ (n : ℕ) : (cocomplex S hS).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', cocomplex_d]
  let φ : ShortComplex.mk (d S hS n) (d S hS (n + 1)) (d_d S hS n) ⟶
      ShortComplex.mk (ι S hS (n + 1)) (d S hS (n + 1)) (ι_d S hS (n + 1)) :=
    { τ₁ := π S hS n
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (exact_ι_d S hS (n + 1))

variable (F : ShortComplex C ⥤ C) [F.Additive]

/-- Apply a component projection to the constructed complex of rows. -/
abbrev projected : CochainComplex C ℕ :=
  (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (cocomplex S hS)

/-- The original row embedding supplies the augmentation after projection. -/
def augmentation : (CochainComplex.single₀ C).obj (F.obj S) ⟶ projected S hS F :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨F.map (ι S hS 0), by
    change F.map (ι S hS 0) ≫ F.map ((cocomplex S hS).d 0 1) = 0
    rw [cocomplex_d, ← F.map_comp, ι_d, F.map_zero]⟩

@[simp]
theorem augmentation_f_zero : (augmentation S hS F).f 0 = F.map (ι S hS 0) := by
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Each projected augmentation is a quasi-isomorphism, with no resolution
existence hypothesis beyond enough injectives in the original category. -/
instance quasiIso_augmentation : QuasiIso (augmentation S hS F) := ⟨fun n => by
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨(exact_ι_d S hS 0).map F, by
          change Mono (F.map (ι S hS 0))
          infer_instance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp [projected])
    · rfl
    · rfl
    · change F.map ((cocomplex S hS).d 0 0) = 0
      rw [(cocomplex S hS).shape 0 0 (by simp), F.map_zero]
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact (cocomplex_exactAt_succ S hS n).map F
    · apply CochainComplex.exactAt_succ_single_obj⟩

/-- A component with injective terms is an actual injective resolution. -/
def resolution [∀ n, Injective ((projected S hS F).X n)] : InjectiveResolution (F.obj S) where
  cocomplex := projected S hS F
  ι := augmentation S hS F

end SGA.SGA2.ExposeV.InjectiveHorseshoe
