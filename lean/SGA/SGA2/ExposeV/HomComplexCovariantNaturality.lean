/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.SourceHomCovariantBoundary

/-! # Naturality of the original covariant Hom connecting maps -/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
open SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]

@[simp]
theorem homComplexPostcomp_comp (F : CochainComplex C ℤ) {G H K : CochainComplex C ℤ}
    (f : G ⟶ H) (g : H ⟶ K) :
    homComplexPostcomp F (f ≫ g) = homComplexPostcomp F f ≫ homComplexPostcomp F g := by
  ext n z
  change z.comp (Cochain.ofHom (f ≫ g)) (add_zero n) =
    (z.comp (Cochain.ofHom f) (add_zero n)).comp (Cochain.ofHom g) (add_zero n)
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_third_is_zero_cochain]

@[simp]
theorem sourceHomPostcomp_comp (F : CochainComplex C ℤ) {G H K : CochainComplex C ℤ}
    (f : G ⟶ H) (g : H ⟶ K) :
    sourceHomPostcomp F (f ≫ g) = sourceHomPostcomp F f ≫ sourceHomPostcomp F g := by
  ext n z
  exact ConcreteCategory.congr_hom
    (congrArg (fun k => k.f n) (homComplexPostcomp_comp F f g)) z

/-- Original coefficient maps define a map of the covariant Hom short complexes. -/
def homComplexCovariantSequenceMap (F : CochainComplex C ℤ)
    {S T : ShortComplex (CochainComplex C ℤ)} (φ : S ⟶ T) :
    homComplexCovariantSequence F S ⟶ homComplexCovariantSequence F T where
  τ₁ := homComplexPostcomp F φ.τ₁
  τ₂ := homComplexPostcomp F φ.τ₂
  τ₃ := homComplexPostcomp F φ.τ₃
  comm₁₂ := by
    change homComplexPostcomp F φ.τ₁ ≫ homComplexPostcomp F T.f =
      homComplexPostcomp F S.f ≫ homComplexPostcomp F φ.τ₂
    simp only [← homComplexPostcomp_comp, φ.comm₁₂]
  comm₂₃ := by
    change homComplexPostcomp F φ.τ₂ ≫ homComplexPostcomp F T.g =
      homComplexPostcomp F S.g ≫ homComplexPostcomp F φ.τ₃
    simp only [← homComplexPostcomp_comp, φ.comm₂₃]

/-- The same actual maps give a map of literal source short complexes. -/
def sourceHomCovariantSequenceMap (F : CochainComplex C ℤ)
    {S T : ShortComplex (CochainComplex C ℤ)} (φ : S ⟶ T) :
    sourceHomCovariantSequence F S ⟶ sourceHomCovariantSequence F T where
  τ₁ := sourceHomPostcomp F φ.τ₁
  τ₂ := sourceHomPostcomp F φ.τ₂
  τ₃ := sourceHomPostcomp F φ.τ₃
  comm₁₂ := by
    change sourceHomPostcomp F φ.τ₁ ≫ sourceHomPostcomp F T.f =
      sourceHomPostcomp F S.f ≫ sourceHomPostcomp F φ.τ₂
    simp only [← sourceHomPostcomp_comp, φ.comm₁₂]
  comm₂₃ := by
    change sourceHomPostcomp F φ.τ₂ ≫ sourceHomPostcomp F T.g =
      sourceHomPostcomp F S.g ≫ sourceHomPostcomp F φ.τ₃
    simp only [← sourceHomPostcomp_comp, φ.comm₂₃]

/-- The covariant Hom connecting maps commute with every original morphism
of short exact coefficient sequences, in every integer degree. -/
theorem homComplexCovariantδ_naturality (F : CochainComplex C ℤ)
    {S T : ShortComplex (CochainComplex C ℤ)} (φ : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact)
    [∀ q, Injective (S.X₁.X q)] [∀ q, Injective (T.X₁.X q)] (n : ℤ) :
    homComplexCovariantδ F S hS n ≫ homologyMap (homComplexPostcomp F φ.τ₁) (n + 1) =
      homologyMap (homComplexPostcomp F φ.τ₃) n ≫ homComplexCovariantδ F T hT n :=
  HomologicalComplex.HomologySequence.δ_naturality (homComplexCovariantSequenceMap F φ)
    (homComplexCovariantSequence_shortExact F S hS)
    (homComplexCovariantSequence_shortExact F T hT) n (n + 1) rfl

/-- Naturality of the actual literal-source covariant connecting maps. -/
theorem sourceHomCovariantδ_naturality (F : CochainComplex C ℤ)
    {S T : ShortComplex (CochainComplex C ℤ)} (φ : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact)
    [∀ q, Injective (S.X₁.X q)] [∀ q, Injective (T.X₁.X q)] (n : ℤ) :
    sourceHomCovariantδ F S hS n ≫ homologyMap (sourceHomPostcomp F φ.τ₁) (n + 1) =
      homologyMap (sourceHomPostcomp F φ.τ₃) n ≫ sourceHomCovariantδ F T hT n :=
  HomologicalComplex.HomologySequence.δ_naturality (sourceHomCovariantSequenceMap F φ)
    (sourceHomCovariantSequence_shortExact F S hS)
    (sourceHomCovariantSequence_shortExact F T hT) n (n + 1) rfl

/-- Actual postcomposition respects the original unscaled source homology data. -/
def sourceHomPostcompHomologyMapData (F : CochainComplex C ℤ)
    {G H : CochainComplex C ℤ} (f : G ⟶ H) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map (sourceHomPostcomp F f))
      (sourceHomLeftHomologyData F G n) (sourceHomLeftHomologyData F H n) where
  φK := AddCommGrpCat.ofHom
    { toFun z := z.postcomp f
      map_zero' := by ext; simp [Cocycle.postcomp]
      map_add' z w := by ext; simp [Cocycle.postcomp] }
  φH := AddCommGrpCat.ofHom (homComplexClassPostcomp F f n)
  commi := rfl
  commf' := by
    ext z
    apply Subtype.ext
    exact (ConcreteCategory.congr_hom ((sourceHomPostcomp F f).comm
      ((ComplexShape.up ℤ).prev n) n) z).symm
  commπ := by ext z; exact homComplexClassPostcomp_mk F f n z

/-- The original unscaled quotient equivalence is natural in coefficients. -/
theorem sourceHomologyUnscaledAddEquiv_postcomp (F : CochainComplex C ℤ)
    {G H : CochainComplex C ℤ} (f : G ⟶ H) (n : ℤ) (x : (sourceHomComplex F G).homology n) :
    sourceHomologyUnscaledAddEquiv F H n (homologyMap (sourceHomPostcomp F f) n x) =
      homComplexClassPostcomp F f n (sourceHomologyUnscaledAddEquiv F G n x) :=
  ConcreteCategory.congr_hom (sourceHomPostcompHomologyMapData F f n).homologyMap_comm x

/-- Actual postcomposition sends an original representative to its postcomposition. -/
theorem sourceHomologyMk_postcomp (F : CochainComplex C ℤ)
    {G H : CochainComplex C ℤ} (f : G ⟶ H) {n : ℤ} (z : Cocycle F G n) :
    homologyMap (sourceHomPostcomp F f) n (sourceHomologyMk z) =
      sourceHomologyMk (z.postcomp f) := by
  apply (sourceHomologyUnscaledAddEquiv F H n).injective
  rw [sourceHomologyUnscaledAddEquiv_postcomp]
  simp only [sourceHomologyMk, AddEquiv.apply_symm_apply, homComplexClassPostcomp_mk]

/-- The fixed unscaled source derived-Hom comparison is natural in coefficients. -/
theorem sourceHomologyUnscaledDerivedHomEquiv_postcomp [HasDerivedCategory.{w} C]
    (F : CochainComplex C ℤ) {G H : CochainComplex C ℤ} [G.IsKInjective] [H.IsKInjective]
    (f : G ⟶ H) (n : ℤ) (x : (sourceHomComplex F G).homology n) :
    sourceHomologyUnscaledDerivedHomEquiv H F n (homologyMap (sourceHomPostcomp F f) n x) =
      sourceHomologyUnscaledDerivedHomEquiv G F n x ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  obtain ⟨z, rfl⟩ := sourceHomologyMk_surjective G F n x
  rw [sourceHomologyMk_postcomp, sourceHomologyUnscaledDerivedHomEquiv_mk,
    sourceHomologyUnscaledDerivedHomEquiv_mk, Cocycle.equivHomShift_symm_postcomp]
  simp [ShiftedHom.map, Category.assoc]

end SGA.SGA2.ExposeV
