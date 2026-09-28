/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.InjectiveHomContravariantBoundary

/-! # The chosen double-resolution comparison and the covariant Ext boundary -/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C} (R : InjectiveResolutionSequence S) {X : C}
  (I : InjectiveResolution X)

/-- The original lifted covariant cocycle computes the actual Ext boundary
under the existing augmentation comparison, with no additional standard sign. -/
theorem injectiveHomClassExt_covariantConnecting (hS : S.ShortExact) (n : ℕ)
    (a : Cocycle I.cochainComplex R.I₁.cochainComplex (n + 1 : ℕ))
    (b : Cochain I.cochainComplex R.I₂.cochainComplex (n : ℤ))
    (c : Cocycle I.cochainComplex R.I₃.cochainComplex (n : ℤ))
    (hb : δ (n : ℤ) (n + 1 : ℕ) b = a.1.comp (Cochain.ofHom R.f) (add_zero _))
    (hc : b.comp (Cochain.ofHom R.g) (add_zero _) = c.1) :
    (injectiveHomClassExt I R.I₃ n (CohomologyClass.mk c)).comp hS.extClass rfl =
      injectiveHomClassExt I R.I₁ (n + 1) (CohomologyClass.mk a) := by
  let := HasDerivedCategory.standard C
  have ht := homCocycle_connecting_eq_derived R.cochainShortComplex
    (n := (n : ℤ)) (m := ((n + 1 : ℕ) : ℤ)) (by omega) a b c hb hc R.shortExact
  apply Abelian.Ext.ext
  rw [Abelian.Ext.comp_hom, injectiveHomClassExt_mk_hom I R.I₃ c,
    injectiveHomClassExt_mk_hom I R.I₁ a]
  simp only [ShiftedHom.comp, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, R.extClass_inv_augmentation hS]
  simp only [CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.comp_map, Category.assoc]
  erw [NatTrans.naturality]
  have ht' := congrArg (fun z => (injectiveResolutionDerivedIso I).hom ≫ z ≫
    (injectiveResolutionDerivedIso R.I₁).inv⟦(n + 1 : ℤ)⟧') ht
  simpa [ShiftedHom.comp, Category.assoc] using ht'

/-- The unchanged standard double-resolution equivalence carries the actual
covariant Hom boundary to the original Ext boundary in every natural degree. -/
theorem injectiveHomologyExtAddEquiv_covariantδ (hS : S.ShortExact) (n : ℕ)
    (x : (HomComplex I.cochainComplex R.I₃.cochainComplex).homology (n : ℤ)) :
    (injectiveHomologyExtAddEquiv I R.I₃ n x).comp hS.extClass rfl =
      injectiveHomologyExtAddEquiv I R.I₁ (n + 1)
        (homComplexCovariantδ I.cochainComplex R.cochainShortComplex R.shortExact (n : ℤ) x) := by
  obtain ⟨c, rfl⟩ := homComplexHomologyMk_surjective I.cochainComplex R.I₃.cochainComplex n x
  obtain ⟨b, a, hb, hc⟩ := exists_homComplexCovariantBoundary I.cochainComplex
    R.cochainShortComplex R.shortExact (n : ℤ) c
  rw [homComplexCovariantδ_mk _ _ _ _ a b c hb hc,
    injectiveHomologyExtAddEquiv_eq_class, injectiveHomologyExtAddEquiv_eq_class,
    homComplexHomologyMk_compare, homComplexHomologyMk_compare]
  exact injectiveHomClassExt_covariantConnecting R I hS n a b c hb hc

/-- The same unsigned covariant comparison holds for the already specified
normalized source Ext equivalence and the actual displayed-source Hom boundary. -/
theorem sourceInjectiveHomologyExtAddEquiv_covariantδ (hS : S.ShortExact) (n : ℕ)
    (x : (sourceHomComplex I.cochainComplex R.I₃.cochainComplex).homology (n : ℤ)) :
    (sourceInjectiveHomologyExtAddEquiv I R.I₃ n x).comp hS.extClass rfl =
      sourceInjectiveHomologyExtAddEquiv I R.I₁ (n + 1)
        (sourceHomCovariantδ I.cochainComplex R.cochainShortComplex R.shortExact (n : ℤ) x) := by
  rw [sourceInjectiveHomologyExtAddEquiv_eq_normalized,
    sourceInjectiveHomologyExtAddEquiv_eq_normalized]
  have hn := ConcreteCategory.congr_hom (sourceHomCovariantδ_normalization
    I.cochainComplex R.cochainShortComplex R.shortExact (n : ℤ)) x
  simp only [ConcreteCategory.comp_apply] at hn
  erw [hn]
  exact injectiveHomologyExtAddEquiv_covariantδ R I hS n _

end SGA.SGA2.ExposeV
