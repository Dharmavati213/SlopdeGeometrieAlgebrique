/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.HomComplexCovariantSequence
import SGA.SGA2.ExposeV.HomComplexHomologyRepresentatives

/-! # The actual covariant Hom boundary and its derived comparison -/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
open SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : CochainComplex C ℤ) (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
  [∀ q, Injective (S.X₁.X q)]

include hS

/-- The actual covariant connecting map, constructed from the original
short exact sequence of Hom complexes. -/
def homComplexCovariantδ (n : ℤ) :
    (HomComplex F S.X₃).homology n ⟶ (HomComplex F S.X₁).homology (n + 1) :=
  (homComplexCovariantSequence_shortExact F S hS).δ n (n + 1) rfl

@[reassoc (attr := simp)]
theorem homComplexCovariantδ_comp (n : ℤ) :
    homComplexCovariantδ F S hS n ≫ homologyMap (homComplexPostcomp F S.f) (n + 1) = 0 :=
  (homComplexCovariantSequence_shortExact F S hS).δ_comp n (n + 1) rfl

@[reassoc (attr := simp)]
theorem comp_homComplexCovariantδ (n : ℤ) :
    homologyMap (homComplexPostcomp F S.g) n ≫ homComplexCovariantδ F S hS n = 0 :=
  (homComplexCovariantSequence_shortExact F S hS).comp_δ n (n + 1) rfl

/-- Exactness after the original covariant boundary. -/
theorem homComplexCovariant_exact₁ (n : ℤ) :
    (ShortComplex.mk _ _ (homComplexCovariantδ_comp F S hS n)).Exact :=
  (homComplexCovariantSequence_shortExact F S hS).homology_exact₁ n (n + 1) rfl

/-- Exactness at the middle coefficient complex. -/
theorem homComplexCovariant_exact₂ (n : ℤ) :
    ((homComplexCovariantSequence F S).map
      (homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) n)).Exact :=
  (homComplexCovariantSequence_shortExact F S hS).homology_exact₂ n

/-- Exactness before the original covariant boundary. -/
theorem homComplexCovariant_exact₃ (n : ℤ) :
    (ShortComplex.mk _ _ (comp_homComplexCovariantδ F S hS n)).Exact :=
  (homComplexCovariantSequence_shortExact F S hS).homology_exact₃ n (n + 1) rfl

/-- The original covariant boundary is lift-and-differentiate on actual
Hom-complex representatives, with the standard differential. -/
theorem homComplexCovariantδ_mk (n : ℤ)
    (a : Cocycle F S.X₁ (n + 1)) (b : Cochain F S.X₂ n) (c : Cocycle F S.X₃ n)
    (hb : δ n (n + 1) b = a.1.comp (Cochain.ofHom S.f) (add_zero (n + 1)))
    (hc : b.comp (Cochain.ofHom S.g) (add_zero n) = c.1) :
    homComplexCovariantδ F S hS n (homComplexHomologyMk c) = homComplexHomologyMk a := by
  have ht := (homComplexCovariantSequence_shortExact F S hS).δ_eq n (n + 1) rfl
    (abElementMap c.1) (by rw [abElementMap_comp]; exact
      (congrArg abElementMap (c.δ_eq_zero (n + 1))).trans (abElementMap_zero _))
    (abElementMap b) (by rw [abElementMap_comp]; exact congrArg abElementMap hc)
    (abElementMap a.1) (by simp only [abElementMap_comp]; exact congrArg abElementMap hb.symm)
    (n + 1 + 1) (by simp)
  simpa only [homComplexHomologyMk, homComplexCocycleLift_eq_liftCycles,
    ConcreteCategory.comp_apply] using! ConcreteCategory.congr_hom ht (ULift.up 1)

/-- Every original quotient cocycle has an actual lift and boundary cocycle. -/
theorem exists_homComplexCovariantBoundary (n : ℤ) (c : Cocycle F S.X₃ n) :
    ∃ (b : Cochain F S.X₂ n) (a : Cocycle F S.X₁ (n + 1)),
      δ n (n + 1) b = a.1.comp (Cochain.ofHom S.f) (add_zero (n + 1)) ∧
        b.comp (Cochain.ofHom S.g) (add_zero n) = c.1 := by
  obtain ⟨b, hb⟩ := exists_homCochainLift F S hS n c.1
  have hz : (δ n (n + 1) b).comp (Cochain.ofHom S.g) (add_zero (n + 1)) = 0 := by
    rw [← δ_comp_ofHom, hb, c.δ_eq_zero]
  obtain ⟨a, ha⟩ := exists_homCochainSubcomplex F S hS (n + 1) (δ n (n + 1) b) hz
  have hza : δ (n + 1) (n + 1 + 1) a = 0 := by
    apply homCochainPostcomp_injective F S hS (n + 1 + 1)
    dsimp only
    rw [← δ_comp_ofHom, ha, δ_δ, Cochain.zero_comp]
  exact ⟨b, Cocycle.mk a (n + 1 + 1) rfl hza, ha.symm, hb⟩

variable [HasDerivedCategory.{w} C] [S.X₁.IsKInjective] [S.X₃.IsKInjective]

/-- In all integer degrees, the unchanged covariant Hom boundary is
postcomposition with the original derived connecting arrow, under the
previously specified derived-Hom equivalences. -/
theorem homComplexCovariantδ_compare (n : ℤ) (x : (HomComplex F S.X₃).homology n) :
    ShiftedHom.comp (homComplexHomologyDerivedHomEquiv F S.X₃ n x)
        (DerivedCategory.triangleOfSESδ hS) (by omega) =
      homComplexHomologyDerivedHomEquiv F S.X₁ (n + 1) (homComplexCovariantδ F S hS n x) := by
  obtain ⟨c, rfl⟩ := homComplexHomologyMk_surjective F S.X₃ n x
  obtain ⟨b, a, hb, hc⟩ := exists_homComplexCovariantBoundary F S hS n c
  rw [homComplexCovariantδ_mk F S hS n a b c hb hc,
    homComplexHomologyDerivedHomEquiv_mk, homComplexHomologyDerivedHomEquiv_mk]
  exact homCocycle_connecting_eq_derived S rfl a b c hb hc hS

end SGA.SGA2.ExposeV
