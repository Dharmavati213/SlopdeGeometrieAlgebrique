/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.InjectiveResolutionSequence

/-! # The chosen double-resolution comparison and the contravariant Ext boundary -/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C} (R : InjectiveResolutionSequence S) {Y : C}
  (J : InjectiveResolution Y)

/-- Original lifted cocycles compute the actual Ext connecting class under
the fixed augmentation comparison, including the contravariant sign. -/
theorem injectiveHomClassExt_contravariantConnecting (hS : S.ShortExact) (n : ℕ)
    (a : Cocycle R.I₃.cochainComplex J.cochainComplex (n + 1 : ℕ))
    (b : Cochain R.I₂.cochainComplex J.cochainComplex (n : ℤ))
    (c : Cocycle R.I₁.cochainComplex J.cochainComplex (n : ℤ))
    (hb : δ (n : ℤ) (n + 1 : ℕ) b = (Cochain.ofHom R.g).comp a.1 (zero_add _))
    (hc : (Cochain.ofHom R.f).comp b (zero_add _) = c.1) :
    hS.extClass.comp (injectiveHomClassExt R.I₁ J n (CohomologyClass.mk c)) (Nat.add_comm 1 n) =
      (n + 1 : ℤ).negOnePow • injectiveHomClassExt R.I₃ J (n + 1) (CohomologyClass.mk a) := by
  let := HasDerivedCategory.standard C
  have ht := homCocycle_contravariantConnecting_eq_derived R.cochainShortComplex
    (n := (n : ℤ)) (m := ((n + 1 : ℕ) : ℤ)) (by omega) a b c hb hc R.shortExact
  apply Abelian.Ext.ext
  rw [Abelian.Ext.comp_hom]
  rw [injectiveHomClassExt_mk_hom R.I₁ J c]
  simp only [Units.smul_def]
  have hs (z : Abelian.Ext S.X₃ Y (n + 1)) (r : ℤ) : (r • z).hom = r • z.hom :=
    (Abelian.Ext.homAddEquiv (C := C) (X := S.X₃) (Y := Y)
      (n := n + 1)).toAddMonoidHom.map_zsmul r z
  rw [hs]
  rw [injectiveHomClassExt_mk_hom R.I₃ J a]
  simp only [ShiftedHom.comp, CategoryTheory.Functor.map_comp, Category.assoc]
  erw [R.extClass_augmentation_assoc hS]
  simp only [← CategoryTheory.Functor.comp_map]
  rw [NatTrans.naturality]
  have ht' := congrArg (fun z => (injectiveResolutionDerivedIso R.I₃).hom ≫ z ≫
    (injectiveResolutionDerivedIso J).inv⟦(n + 1 : ℤ)⟧') ht
  simpa [ShiftedHom.comp, Units.smul_def, Category.assoc] using ht'

/-- The unchanged standard double-resolution Ext equivalence intertwines
the actual Hom boundary with the original Ext boundary, in every natural degree. -/
theorem injectiveHomologyExtAddEquiv_contravariantδ (hS : S.ShortExact) (n : ℕ)
    (x : (HomComplex R.I₁.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    hS.extClass.comp (injectiveHomologyExtAddEquiv R.I₁ J n x) (Nat.add_comm 1 n) =
      (n + 1 : ℤ).negOnePow • injectiveHomologyExtAddEquiv R.I₃ J (n + 1)
        (homComplexContravariantδ R.cochainShortComplex R.shortExact
          J.cochainComplex (n : ℤ) x) := by
  obtain ⟨c, rfl⟩ := homComplexHomologyMk_surjective R.I₁.cochainComplex J.cochainComplex n x
  obtain ⟨b, a, hb, hc⟩ := exists_homComplexContravariantBoundary R.cochainShortComplex
    R.shortExact J.cochainComplex (n : ℤ) c
  rw [homComplexContravariantδ_mk _ _ _ _ a b c hb hc,
    injectiveHomologyExtAddEquiv_eq_class, injectiveHomologyExtAddEquiv_eq_class,
    homComplexHomologyMk_compare, homComplexHomologyMk_compare]
  exact injectiveHomClassExt_contravariantConnecting R J hS n a b c hb hc

/-- The same signed identity holds for the previously specified normalized
source Ext comparison and the actual literal-source Hom connecting map. -/
theorem sourceInjectiveHomologyExtAddEquiv_contravariantδ (hS : S.ShortExact) (n : ℕ)
    (x : (sourceHomComplex R.I₁.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    hS.extClass.comp (sourceInjectiveHomologyExtAddEquiv R.I₁ J n x) (Nat.add_comm 1 n) =
      (n + 1 : ℤ).negOnePow • sourceInjectiveHomologyExtAddEquiv R.I₃ J (n + 1)
        (sourceHomContravariantδ R.cochainShortComplex R.shortExact
          J.cochainComplex (n : ℤ) x) := by
  rw [sourceInjectiveHomologyExtAddEquiv_eq_normalized,
    sourceInjectiveHomologyExtAddEquiv_eq_normalized]
  have hn := ConcreteCategory.congr_hom (sourceHomContravariantδ_normalization
    R.cochainShortComplex R.shortExact J.cochainComplex (n : ℤ)) x
  simp only [ConcreteCategory.comp_apply] at hn
  erw [hn]
  exact injectiveHomologyExtAddEquiv_contravariantδ R J hS n _

end SGA.SGA2.ExposeV
