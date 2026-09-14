/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.SourceHomContravariantSequence

/-! # The source Hom boundary on original representatives and derived morphisms -/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
  (P : CochainComplex C ℤ) [∀ q, Injective (P.X q)]

/-- The connecting map of the literal source sequence is computed by
extending and applying the displayed source differential. -/
theorem sourceHomContravariantδ_mk (n : ℤ)
    (a : Cocycle S.X₃ P (n + 1)) (b : Cochain S.X₂ P n) (c : Cocycle S.X₁ P n)
    (hb : sourceHomδ n (n + 1) b = (Cochain.ofHom S.g).comp a.1 (zero_add (n + 1)))
    (hc : (Cochain.ofHom S.f).comp b (zero_add n) = c.1) :
    sourceHomContravariantδ S hS P n (sourceHomologyMk c) = sourceHomologyMk a := by
  have hn : δ n (n + 1) (sourceHomSign n • b) =
      sourceHomSign (n + 1) • sourceHomδ n (n + 1) b :=
    ConcreteCategory.congr_hom ((sourceHomComplexIso S.X₂ P).hom.comm n (n + 1)) b
  have hb' : δ n (n + 1) (sourceHomSign n • b) =
      (Cochain.ofHom S.g).comp (sourceHomSign (n + 1) • a).1 (zero_add (n + 1)) := by
    rw [hn, hb, Cocycle.coe_units_smul, Cochain.comp_units_smul]
  have hc' : (Cochain.ofHom S.f).comp (sourceHomSign n • b) (zero_add n) =
      (sourceHomSign n • c).1 := by
    rw [Cochain.comp_units_smul, hc, Cocycle.coe_units_smul]
  apply (AddCommGrpCat.mono_iff_injective
    (homologyMap (sourceHomComplexIso S.X₃ P).hom (n + 1))).mp inferInstance
  have ht := ConcreteCategory.congr_hom (sourceHomContravariantδ_normalization S hS P n)
    (sourceHomologyMk c)
  simp only [ConcreteCategory.comp_apply] at ht
  rw [ht, sourceHomologyMk_normalization,
    homComplexContravariantδ_mk S hS P n _ _ _ hb' hc', sourceHomologyMk_normalization]

include hS in
/-- Every original source cocycle has a lift and a boundary representative. -/
theorem exists_sourceHomContravariantBoundary (n : ℤ) (c : Cocycle S.X₁ P n) :
    ∃ (b : Cochain S.X₂ P n) (a : Cocycle S.X₃ P (n + 1)),
      sourceHomδ n (n + 1) b = (Cochain.ofHom S.g).comp a.1 (zero_add (n + 1)) ∧
        (Cochain.ofHom S.f).comp b (zero_add n) = c.1 := by
  obtain ⟨b, a, hb, hc⟩ := exists_homComplexContravariantBoundary S hS P n c
  refine ⟨b, (n + 1).negOnePow • a, ?_, hc⟩
  simp only [sourceHomδ, hb, Cocycle.coe_units_smul, Cochain.comp_units_smul]

omit [∀ q, Injective (P.X q)] in
/-- The original source cocycles represent every actual homology class. -/
theorem sourceHomologyMk_surjective (F : CochainComplex C ℤ) (n : ℤ) :
    Function.Surjective (sourceHomologyMk (F := F) (G := P) (n := n)) := by
  intro x
  obtain ⟨z, hz⟩ := (sourceHomologyUnscaledAddEquiv F P n x).mk_surjective
  exact ⟨z, (sourceHomologyUnscaledAddEquiv F P n).injective (by
    simpa [sourceHomologyMk] using hz)⟩

variable [HasDerivedCategory.{w} C] [P.IsKInjective]

omit [∀ q, Injective (P.X q)] in
/-- The derived-Hom equivalence from the original, unscaled source quotient.
No boundary-dependent adjustment or degreewise sign is inserted. -/
def sourceHomologyUnscaledDerivedHomEquiv (F : CochainComplex C ℤ) (n : ℤ) :
    (sourceHomComplex F P).homology n ≃+
      ShiftedHom (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj P) n :=
  (sourceHomologyUnscaledAddEquiv F P n).trans
    ((HomComplex.homologyAddEquiv F P n).symm.trans
      (ExposeI.homComplexHomologyDerivedHomEquiv F P n))

omit [∀ q, Injective (P.X q)] in
/-- This fixed equivalence sends an original representative to its original
shifted derived morphism. -/
theorem sourceHomologyUnscaledDerivedHomEquiv_mk {F : CochainComplex C ℤ} {n : ℤ}
    (z : Cocycle F P n) :
    sourceHomologyUnscaledDerivedHomEquiv P F n (sourceHomologyMk z) =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q := by
  have hz : (HomComplex.homologyAddEquiv F P n).symm (CohomologyClass.mk z) =
      homComplexHomologyMk z := by
    apply (HomComplex.homologyAddEquiv F P n).injective
    rw [AddEquiv.apply_symm_apply, homComplexHomologyMk_compare]
  simp only [sourceHomologyUnscaledDerivedHomEquiv, AddEquiv.trans_apply,
    sourceHomologyMk, AddEquiv.apply_symm_apply, hz]
  exact homComplexHomologyDerivedHomEquiv_mk z

/-- In every integer degree, the actual literal-source Hom connecting map
is precomposition by the original derived connecting arrow under the fixed
unscaled equivalence. The displayed source convention requires no extra sign. -/
theorem sourceHomContravariantδ_compare (n : ℤ)
    (x : (sourceHomComplex S.X₁ P).homology n) :
    ShiftedHom.comp (DerivedCategory.triangleOfSESδ hS)
        (sourceHomologyUnscaledDerivedHomEquiv P S.X₁ n x) (by omega) =
      sourceHomologyUnscaledDerivedHomEquiv P S.X₃ (n + 1)
        (sourceHomContravariantδ S hS P n x) := by
  obtain ⟨c, rfl⟩ := sourceHomologyMk_surjective P S.X₁ n x
  obtain ⟨b, a, hb, hc⟩ := exists_sourceHomContravariantBoundary S hS P n c
  rw [sourceHomContravariantδ_mk S hS P n a b c hb hc,
    sourceHomologyUnscaledDerivedHomEquiv_mk, sourceHomologyUnscaledDerivedHomEquiv_mk]
  exact sourceHomCocycle_contravariantConnecting_eq_derived S rfl a b c hS hb hc

end SGA.SGA2.ExposeV
