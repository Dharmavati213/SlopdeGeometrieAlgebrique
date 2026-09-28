/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.InjectiveHorseshoeFunctor
import SGA.SGA2.ExposeV.HomComplexCovariantNaturality
import SGA.SGA2.ExposeV.HomComplexContravariantNaturality

/-! # Naturality of the original Hom boundaries on constructed resolutions

Every map of original short exact sequences now has a constructed augmented
resolution-sequence map. The existing Hom boundaries commute with this actual
comparison in both variables and both differential conventions. No compatible
resolution map is supplied as an extra hypothesis.
-/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
open SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV.InjectiveHorseshoe

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)

/-- The standard covariant boundary is natural for the constructed comparison
over every map of the original short exact sequences. -/
theorem covariantδ_compare_naturality (F : CochainComplex C ℤ) (n : ℤ) :
    homComplexCovariantδ F (sequence S hS) (sequence_shortExact S hS) n ≫
        homologyMap (homComplexPostcomp F (sequenceCompare hS hT φ).τ₁) (n + 1) =
      homologyMap (homComplexPostcomp F (sequenceCompare hS hT φ).τ₃) n ≫
        homComplexCovariantδ F (sequence T hT) (sequence_shortExact T hT) n :=
  homComplexCovariantδ_naturality F (sequenceCompare hS hT φ)
    (sequence_shortExact S hS) (sequence_shortExact T hT) n

/-- The literal-source covariant boundary is natural for the same original comparison. -/
theorem sourceCovariantδ_compare_naturality (F : CochainComplex C ℤ) (n : ℤ) :
    sourceHomCovariantδ F (sequence S hS) (sequence_shortExact S hS) n ≫
        homologyMap (sourceHomPostcomp F (sequenceCompare hS hT φ).τ₁) (n + 1) =
      homologyMap (sourceHomPostcomp F (sequenceCompare hS hT φ).τ₃) n ≫
        sourceHomCovariantδ F (sequence T hT) (sequence_shortExact T hT) n :=
  sourceHomCovariantδ_naturality F (sequenceCompare hS hT φ)
    (sequence_shortExact S hS) (sequence_shortExact T hT) n

/-- The standard contravariant boundary is natural for the constructed comparison
into every degreewise-injective target complex. -/
theorem contravariantδ_compare_naturality (P : CochainComplex C ℤ)
    [∀ q, Injective (P.X q)] (n : ℤ) :
    homComplexContravariantδ (sequence T hT) (sequence_shortExact T hT) P n ≫
        homologyMap (homComplexPrecomp (sequenceCompare hS hT φ).τ₃ P) (n + 1) =
      homologyMap (homComplexPrecomp (sequenceCompare hS hT φ).τ₁ P) n ≫
        homComplexContravariantδ (sequence S hS) (sequence_shortExact S hS) P n :=
  homComplexContravariantδ_naturality (sequenceCompare hS hT φ)
    (sequence_shortExact S hS) (sequence_shortExact T hT) P n

/-- The literal-source contravariant boundary is natural for the same comparison. -/
theorem sourceContravariantδ_compare_naturality (P : CochainComplex C ℤ)
    [∀ q, Injective (P.X q)] (n : ℤ) :
    sourceHomContravariantδ (sequence T hT) (sequence_shortExact T hT) P n ≫
        homologyMap (sourceHomPrecomp (sequenceCompare hS hT φ).τ₃ P) (n + 1) =
      homologyMap (sourceHomPrecomp (sequenceCompare hS hT φ).τ₁ P) n ≫
        sourceHomContravariantδ (sequence S hS) (sequence_shortExact S hS) P n :=
  sourceHomContravariantδ_naturality (sequenceCompare hS hT φ)
    (sequence_shortExact S hS) (sequence_shortExact T hT) P n

end SGA.SGA2.ExposeV.InjectiveHorseshoe
