/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.SourceHomCovariantSequence

/-! # Original source covariant representatives and the derived boundary -/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : CochainComplex C ℤ) (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
  [∀ q, Injective (S.X₁.X q)]

/-- The actual source covariant boundary is lift-and-differentiate with
the literal displayed differential and original representatives. -/
theorem sourceHomCovariantδ_mk (n : ℤ)
    (a : Cocycle F S.X₁ (n + 1)) (b : Cochain F S.X₂ n) (c : Cocycle F S.X₃ n)
    (hb : sourceHomδ n (n + 1) b = a.1.comp (Cochain.ofHom S.f) (add_zero (n + 1)))
    (hc : b.comp (Cochain.ofHom S.g) (add_zero n) = c.1) :
    sourceHomCovariantδ F S hS n (sourceHomologyMk c) = sourceHomologyMk a := by
  have hn : δ n (n + 1) (sourceHomSign n • b) =
      sourceHomSign (n + 1) • sourceHomδ n (n + 1) b :=
    ConcreteCategory.congr_hom ((sourceHomComplexIso F S.X₂).hom.comm n (n + 1)) b
  have hb' : δ n (n + 1) (sourceHomSign n • b) =
      (sourceHomSign (n + 1) • a).1.comp (Cochain.ofHom S.f) (add_zero (n + 1)) := by
    rw [hn, hb, Cocycle.coe_units_smul, Cochain.units_smul_comp]
  have hc' : (sourceHomSign n • b).comp (Cochain.ofHom S.g) (add_zero n) =
      (sourceHomSign n • c).1 := by
    rw [Cochain.units_smul_comp, hc, Cocycle.coe_units_smul]
  apply (AddCommGrpCat.mono_iff_injective
    (homologyMap (sourceHomComplexIso F S.X₁).hom (n + 1))).mp inferInstance
  have ht := ConcreteCategory.congr_hom (sourceHomCovariantδ_normalization F S hS n)
    (sourceHomologyMk c)
  simp only [ConcreteCategory.comp_apply] at ht
  rw [ht, sourceHomologyMk_normalization,
    homComplexCovariantδ_mk F S hS n _ _ _ hb' hc', sourceHomologyMk_normalization]

include hS in
/-- Every original source quotient cocycle has a lift and boundary representative. -/
theorem exists_sourceHomCovariantBoundary (n : ℤ) (c : Cocycle F S.X₃ n) :
    ∃ (b : Cochain F S.X₂ n) (a : Cocycle F S.X₁ (n + 1)),
      sourceHomδ n (n + 1) b = a.1.comp (Cochain.ofHom S.f) (add_zero (n + 1)) ∧
        b.comp (Cochain.ofHom S.g) (add_zero n) = c.1 := by
  obtain ⟨b, a, hb, hc⟩ := exists_homComplexCovariantBoundary F S hS n c
  refine ⟨b, (n + 1).negOnePow • a, ?_, hc⟩
  simp only [sourceHomδ, hb, Cocycle.coe_units_smul, Cochain.units_smul_comp]

variable [HasDerivedCategory.{w} C] [S.X₁.IsKInjective] [S.X₃.IsKInjective]

/-- Under the fixed original unscaled quotient equivalence, the literal
source covariant boundary agrees with postcomposition by the derived
connecting arrow with exactly the target-degree sign, in every integer degree. -/
theorem sourceHomCovariantδ_compare (n : ℤ) (x : (sourceHomComplex F S.X₃).homology n) :
    ShiftedHom.comp (sourceHomologyUnscaledDerivedHomEquiv S.X₃ F n x)
        (DerivedCategory.triangleOfSESδ hS) (by omega) =
      (n + 1).negOnePow • sourceHomologyUnscaledDerivedHomEquiv S.X₁ F (n + 1)
        (sourceHomCovariantδ F S hS n x) := by
  obtain ⟨c, rfl⟩ := sourceHomologyMk_surjective S.X₃ F n x
  obtain ⟨b, a, hb, hc⟩ := exists_sourceHomCovariantBoundary F S hS n c
  rw [sourceHomCovariantδ_mk F S hS n a b c hb hc,
    sourceHomologyUnscaledDerivedHomEquiv_mk, sourceHomologyUnscaledDerivedHomEquiv_mk]
  exact sourceHomCocycle_connecting_eq_derived S rfl a b c hS hb hc

end SGA.SGA2.ExposeV
