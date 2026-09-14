/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.HomComplexContravariantSequence
import SGA.SGA2.ExposeV.HomComplexHomologyRepresentatives

/-! # The actual contravariant Hom boundary and the derived connecting map -/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
  (P : CochainComplex C ℤ) [∀ q, Injective (P.X q)]

include hS

/-- The original connecting morphism of the actual contravariant Hom
short exact sequence, without transport from a derived-category map. -/
def homComplexContravariantδ (n : ℤ) :
    (HomComplex S.X₁ P).homology n ⟶ (HomComplex S.X₃ P).homology (n + 1) :=
  (homComplexContravariantSequence_shortExact S hS P).δ n (n + 1) rfl

@[reassoc (attr := simp)]
theorem homComplexContravariantδ_comp (n : ℤ) :
    homComplexContravariantδ S hS P n ≫ homologyMap (homComplexPrecomp S.g P) (n + 1) = 0 :=
  (homComplexContravariantSequence_shortExact S hS P).δ_comp n (n + 1) rfl

@[reassoc (attr := simp)]
theorem comp_homComplexContravariantδ (n : ℤ) :
    homologyMap (homComplexPrecomp S.f P) n ≫ homComplexContravariantδ S hS P n = 0 :=
  (homComplexContravariantSequence_shortExact S hS P).comp_δ n (n + 1) rfl

/-- Exactness after the original contravariant connecting map. -/
theorem homComplexContravariant_exact₁ (n : ℤ) :
    (ShortComplex.mk _ _ (homComplexContravariantδ_comp S hS P n)).Exact :=
  (homComplexContravariantSequence_shortExact S hS P).homology_exact₁ n (n + 1) rfl

/-- Exactness at the middle term of the original Hom sequence. -/
theorem homComplexContravariant_exact₂ (n : ℤ) :
    ((homComplexContravariantSequence S P).map
      (homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) n)).Exact :=
  (homComplexContravariantSequence_shortExact S hS P).homology_exact₂ n

/-- Exactness before the original contravariant connecting map. -/
theorem homComplexContravariant_exact₃ (n : ℤ) :
    (ShortComplex.mk _ _ (comp_homComplexContravariantδ S hS P n)).Exact :=
  (homComplexContravariantSequence_shortExact S hS P).homology_exact₃ n (n + 1) rfl

/-- The actual contravariant Hom boundary is lift-and-differentiate on
the original cocycle representatives. -/
theorem homComplexContravariantδ_mk (n : ℤ)
    (a : Cocycle S.X₃ P (n + 1)) (b : Cochain S.X₂ P n) (c : Cocycle S.X₁ P n)
    (hb : δ n (n + 1) b = (Cochain.ofHom S.g).comp a.1 (zero_add (n + 1)))
    (hc : (Cochain.ofHom S.f).comp b (zero_add n) = c.1) :
    homComplexContravariantδ S hS P n (homComplexHomologyMk c) = homComplexHomologyMk a := by
  have ht := (homComplexContravariantSequence_shortExact S hS P).δ_eq n (n + 1) rfl
    (abElementMap c.1) (by rw [abElementMap_comp]; exact
      (congrArg abElementMap (c.δ_eq_zero (n + 1))).trans (abElementMap_zero _))
    (abElementMap b) (by rw [abElementMap_comp]; exact congrArg abElementMap hc)
    (abElementMap a.1) (by simp only [abElementMap_comp]; exact congrArg abElementMap hb.symm)
    (n + 1 + 1) (by simp)
  simpa only [homComplexHomologyMk, homComplexCocycleLift_eq_liftCycles,
    ConcreteCategory.comp_apply] using! ConcreteCategory.congr_hom ht (ULift.up 1)

/-- Every original cocycle has actual extension and boundary cocycles,
using only degreewise injectivity and the original short exact sequence. -/
theorem exists_homComplexContravariantBoundary (n : ℤ) (c : Cocycle S.X₁ P n) :
    ∃ (b : Cochain S.X₂ P n) (a : Cocycle S.X₃ P (n + 1)),
      δ n (n + 1) b = (Cochain.ofHom S.g).comp a.1 (zero_add (n + 1)) ∧
        (Cochain.ofHom S.f).comp b (zero_add n) = c.1 := by
  obtain ⟨b, hb⟩ := exists_homCochainExtension S hS P n c.1
  have hz : (Cochain.ofHom S.f).comp (δ n (n + 1) b) (zero_add (n + 1)) = 0 := by
    rw [← δ_ofHom_comp, hb, c.δ_eq_zero]
  obtain ⟨a, ha⟩ := exists_homCochainQuotient S hS P (n + 1) (δ n (n + 1) b) hz
  have hza : δ (n + 1) (n + 1 + 1) a = 0 := by
    apply homCochainPrecomp_injective S hS P (n + 1 + 1)
    dsimp only
    rw [← δ_ofHom_comp, ha, δ_δ, Cochain.comp_zero]
  exact ⟨b, Cocycle.mk a (n + 1 + 1) rfl hza, ha.symm, hb⟩

variable [HasDerivedCategory.{w} C] [P.IsKInjective]

/-- In every integer degree, the previously specified derived-Hom
equivalence identifies the actual contravariant Hom connecting map with
precomposition by the original derived connecting arrow, with its exact sign. -/
theorem homComplexContravariantδ_compare (n : ℤ)
    (x : (HomComplex S.X₁ P).homology n) :
    ShiftedHom.comp (DerivedCategory.triangleOfSESδ hS)
        (ExposeI.homComplexHomologyDerivedHomEquiv S.X₁ P n x) (by omega) =
      (n + 1).negOnePow • ExposeI.homComplexHomologyDerivedHomEquiv S.X₃ P (n + 1)
        (homComplexContravariantδ S hS P n x) := by
  obtain ⟨c, rfl⟩ := homComplexHomologyMk_surjective S.X₁ P n x
  obtain ⟨b, a, hb, hc⟩ := exists_homComplexContravariantBoundary S hS P n c
  rw [homComplexContravariantδ_mk S hS P n a b c hb hc,
    homComplexHomologyDerivedHomEquiv_mk, homComplexHomologyDerivedHomEquiv_mk]
  exact homCocycle_contravariantConnecting_eq_derived S rfl a b c hb hc hS

end SGA.SGA2.ExposeV
