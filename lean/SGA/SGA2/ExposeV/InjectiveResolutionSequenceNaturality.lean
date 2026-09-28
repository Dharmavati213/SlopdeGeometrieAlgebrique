/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.InjectiveHomModuleExtModelChange
import SGA.SGA2.ExposeV.InjectiveHorseshoeBoundaryNaturality

/-! # Boundary naturality between arbitrary supplied resolution sequences

The independently constructed Hom boundaries commute with the actual
comparison maps between arbitrary specified resolution-sequence models.
This uses the unchanged original maps and both differential conventions;
compatibility of the fixed Hom/Ext comparisons with model change is imported
from `InjectiveHomExtNaturality` and `InjectiveHomModuleExtModelChange`.
-/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV.InjectiveResolutionSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S T : ShortComplex C} (R : InjectiveResolutionSequence S)
  (R' : InjectiveResolutionSequence T) (φ : S ⟶ T)

/-- Standard covariant boundary naturality for the actual arbitrary-model comparison. -/
theorem covariantδ_compare_naturality (F : CochainComplex C ℤ) (n : ℤ) :
    homComplexCovariantδ F R.cochainShortComplex R.shortExact n ≫
        homologyMap (homComplexPostcomp F (R.compare R' φ).τ₁) (n + 1) =
      homologyMap (homComplexPostcomp F (R.compare R' φ).τ₃) n ≫
        homComplexCovariantδ F R'.cochainShortComplex R'.shortExact n :=
  homComplexCovariantδ_naturality F (R.compare R' φ) R.shortExact R'.shortExact n

/-- Literal-source covariant boundary naturality for the same comparison. -/
theorem sourceCovariantδ_compare_naturality (F : CochainComplex C ℤ) (n : ℤ) :
    sourceHomCovariantδ F R.cochainShortComplex R.shortExact n ≫
        homologyMap (sourceHomPostcomp F (R.compare R' φ).τ₁) (n + 1) =
      homologyMap (sourceHomPostcomp F (R.compare R' φ).τ₃) n ≫
        sourceHomCovariantδ F R'.cochainShortComplex R'.shortExact n :=
  sourceHomCovariantδ_naturality F (R.compare R' φ) R.shortExact R'.shortExact n

/-- Standard contravariant boundary naturality for the actual arbitrary-model comparison. -/
theorem contravariantδ_compare_naturality (P : CochainComplex C ℤ)
    [∀ q, Injective (P.X q)] (n : ℤ) :
    homComplexContravariantδ R'.cochainShortComplex R'.shortExact P n ≫
        homologyMap (homComplexPrecomp (R.compare R' φ).τ₃ P) (n + 1) =
      homologyMap (homComplexPrecomp (R.compare R' φ).τ₁ P) n ≫
        homComplexContravariantδ R.cochainShortComplex R.shortExact P n :=
  homComplexContravariantδ_naturality (R.compare R' φ) R.shortExact R'.shortExact P n

/-- Literal-source contravariant boundary naturality for the same comparison. -/
theorem sourceContravariantδ_compare_naturality (P : CochainComplex C ℤ)
    [∀ q, Injective (P.X q)] (n : ℤ) :
    sourceHomContravariantδ R'.cochainShortComplex R'.shortExact P n ≫
        homologyMap (sourceHomPrecomp (R.compare R' φ).τ₃ P) (n + 1) =
      homologyMap (sourceHomPrecomp (R.compare R' φ).τ₁ P) n ≫
        sourceHomContravariantδ R.cochainShortComplex R.shortExact P n :=
  sourceHomContravariantδ_naturality (R.compare R' φ) R.shortExact R'.shortExact P n

end SGA.SGA2.ExposeV.InjectiveResolutionSequence
