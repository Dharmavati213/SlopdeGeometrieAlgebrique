/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.InjectiveResolutionNatMap

/-! # The nonnegative form of an arbitrary specified resolution sequence

The integer-indexed maps in a supplied `InjectiveResolutionSequence` determine
maps of its original nonnegative resolutions by full faithfulness. Exactness
and augmentation compatibility are recovered from the supplied data, rather
than added as assumptions or obtained by replacing the resolution models.
-/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV.InjectiveResolutionSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C} (R : InjectiveResolutionSequence S)

/-- The first original map, recovered on the nonnegative resolutions. -/
abbrev firstNatHom : InjectiveResolution.Hom R.I₁ R.I₂ S.f :=
  injectiveResolutionNatHom R.I₁ R.I₂ S.f R.f R.comm₁₂

/-- The second original map, recovered on the nonnegative resolutions. -/
abbrev lastNatHom : InjectiveResolution.Hom R.I₂ R.I₃ S.g :=
  injectiveResolutionNatHom R.I₂ R.I₃ S.g R.g R.comm₂₃

@[simp]
theorem firstNatHom_hom' : R.firstNatHom.hom' = R.f :=
  injectiveResolutionNatHom_hom' _ _ _ _ _

@[simp]
theorem lastNatHom_hom' : R.lastNatHom.hom' = R.g :=
  injectiveResolutionNatHom_hom' _ _ _ _ _

theorem natZero : R.firstNatHom.hom ≫ R.lastNatHom.hom = 0 := by
  apply (ComplexShape.embeddingUpNat.extendFunctor C).map_injective
  change extendMap (R.firstNatHom.hom ≫ R.lastNatHom.hom) ComplexShape.embeddingUpNat =
    extendMap 0 ComplexShape.embeddingUpNat
  rw [extendMap_comp, extendMap_zero]
  change R.firstNatHom.hom' ≫ R.lastNatHom.hom' = 0
  rw [firstNatHom_hom', lastNatHom_hom', R.zero]

/-- The recovered nonnegative sequence, on the unchanged specified resolutions. -/
abbrev natSequence : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk R.firstNatHom.hom R.lastNatHom.hom R.natZero

/-- Evaluation identifies the original extended row with the recovered nonnegative row. -/
def natEvalIso (n : ℕ) :
    R.cochainShortComplex.map (eval C (ComplexShape.up ℤ) n) ≅
      R.natSequence.map (eval C (ComplexShape.up ℕ) n) :=
  ShortComplex.isoMk
    (R.I₁.cochainComplexXIso n n rfl)
    (R.I₂.cochainComplexXIso n n rfl)
    (R.I₃.cochainComplexXIso n n rfl)
    (by
      change _ = R.f.f n ≫ _
      rw [← R.firstNatHom_hom', R.firstNatHom.hom'_f n n rfl]
      simp)
    (by
      change _ = R.g.f n ≫ _
      rw [← R.lastNatHom_hom', R.lastNatHom.hom'_f n n rfl]
      simp)

/-- Short exactness of the original sequence is retained after recovering the nonnegative maps. -/
theorem natSequence_shortExact : R.natSequence.ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro n
  exact ShortComplex.shortExact_of_iso (R.natEvalIso n)
    (R.shortExact.map_of_exact (eval C (ComplexShape.up ℤ) n))

/-- The unchanged nonnegative augmentations form an actual map of short complexes. -/
def natAugmentation : S.map (single₀ C) ⟶ R.natSequence where
  τ₁ := R.I₁.ι
  τ₂ := R.I₂.ι
  τ₃ := R.I₃.ι
  comm₁₂ := R.firstNatHom.ι_comp_hom
  comm₂₃ := R.lastNatHom.ι_comp_hom

end SGA.SGA2.ExposeV.InjectiveResolutionSequence
