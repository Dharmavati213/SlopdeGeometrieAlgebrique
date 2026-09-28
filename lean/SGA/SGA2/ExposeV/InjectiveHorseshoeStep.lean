/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # The injective horseshoe step

A short exact sequence embeds into a split short exact sequence of injectives.
The actual categorical cokernel is again short exact, so this construction can
be iterated without assuming compatible injective resolutions.
-/

noncomputable section
universe v u
open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cokernel of a monomorphism between short exact sequences is short exact. -/
theorem shortExact_cokernel_of_mono {S T : ShortComplex C} (φ : S ⟶ T)
    [Mono φ] (hS : S.ShortExact) (hT : T.ShortExact) :
    (cokernel φ).ShortExact := by
  let D : ShortComplex.SnakeInput C :=
    { L₀ := kernel φ
      L₁ := S
      L₂ := T
      L₃ := cokernel φ
      v₀₁ := kernel.ι φ
      v₁₂ := φ
      v₂₃ := cokernel.π φ
      h₀ := kernelIsKernel φ
      h₃ := cokernelIsCokernel φ
      L₁_exact := hS.exact
      epi_L₁_g := hS.epi_g
      L₂_exact := hT.exact
      mono_L₂_f := hT.mono_f }
  have h₀ : IsZero D.L₀.X₃ :=
    (ShortComplex.π₃ : ShortComplex C ⥤ C).map_isZero (isZero_kernel_of_mono φ)
  have : Epi D.L₂.g := hT.epi_g
  exact ShortComplex.ShortExact.mk' D.L₃_exact
    ((D.L₂'.exact_iff_mono (h₀.eq_of_src _ _)).1 D.L₂'_exact) D.epi_L₃_g

namespace InjectiveHorseshoe

variable [EnoughInjectives C] (S : ShortComplex C)

/-- The split injective row used at one stage of the horseshoe. -/
abbrev row : ShortComplex C :=
  ShortComplex.mk
    (biprod.inl : Injective.under S.X₁ ⟶ Injective.under S.X₁ ⊞ Injective.under S.X₃)
    biprod.snd (by simp)

/-- Every constructed injective row has its specified biproduct splitting. -/
def splitting : (row S).Splitting :=
  ShortComplex.Splitting.ofHasBinaryBiproduct _ _

theorem row_shortExact : (row S).ShortExact := (splitting S).shortExact

instance injective_row_X₁ : Injective (row S).X₁ := inferInstance
instance injective_row_X₂ : Injective (row S).X₂ := inferInstance
instance injective_row_X₃ : Injective (row S).X₃ := inferInstance

variable (hS : S.ShortExact)

/-- The actual embedding of the original short exact sequence into the split row. -/
def inclusion : S ⟶ row S := by
  have := hS.mono_f
  exact
    { τ₁ := Injective.ι S.X₁
      τ₂ := biprod.lift (Injective.factorThru (Injective.ι S.X₁) S.f)
        (S.g ≫ Injective.ι S.X₃)
      τ₃ := Injective.ι S.X₃
      comm₁₂ := by ext <;> simp [Category.assoc]
      comm₂₃ := by simp }

instance mono_inclusion_τ₁ : Mono (inclusion S hS).τ₁ := by
  dsimp [inclusion]
  infer_instance

instance mono_inclusion_τ₃ : Mono (inclusion S hS).τ₃ := by
  dsimp [inclusion]
  infer_instance

instance mono_inclusion_τ₂ : Mono (inclusion S hS).τ₂ := by
  have := hS.mono_f
  exact ShortComplex.mono_τ₂_of_exact_of_mono (inclusion S hS) hS.exact

instance mono_inclusion : Mono (inclusion S hS) where
  right_cancellation {Z} a b h := by
    ext
    · exact (cancel_mono (inclusion S hS).τ₁).1 (congrArg ShortComplex.Hom.τ₁ h)
    · exact (cancel_mono (inclusion S hS).τ₂).1 (congrArg ShortComplex.Hom.τ₂ h)
    · exact (cancel_mono (inclusion S hS).τ₃).1 (congrArg ShortComplex.Hom.τ₃ h)

/-- The next row of syzygies is the original categorical cokernel. -/
abbrev next : ShortComplex C := cokernel (inclusion S hS)

theorem next_shortExact : (next S hS).ShortExact :=
  shortExact_cokernel_of_mono (inclusion S hS) hS (row_shortExact S)

end InjectiveHorseshoe
end SGA.SGA2.ExposeV
