/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.SourceHomContravariantBoundary

/-! # Naturality of the original contravariant Hom boundaries -/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]

@[simp]
theorem homComplexPrecomp_comp {F G H : CochainComplex C ℤ} (f : F ⟶ G) (g : G ⟶ H)
    (P : CochainComplex C ℤ) :
    homComplexPrecomp (f ≫ g) P = homComplexPrecomp g P ≫ homComplexPrecomp f P := by
  ext n z
  change (Cochain.ofHom (f ≫ g)).comp z (zero_add n) =
    (Cochain.ofHom f).comp ((Cochain.ofHom g).comp z (zero_add n)) (zero_add n)
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

@[simp]
theorem sourceHomPrecomp_comp {F G H : CochainComplex C ℤ} (f : F ⟶ G) (g : G ⟶ H)
    (P : CochainComplex C ℤ) :
    sourceHomPrecomp (f ≫ g) P = sourceHomPrecomp g P ≫ sourceHomPrecomp f P := by
  ext n z
  exact ConcreteCategory.congr_hom
    (congrArg (fun k => k.f n) (homComplexPrecomp_comp f g P)) z

/-- A morphism of the original short complexes induces the reversed
map of their actual standard Hom complexes. -/
def homComplexContravariantSequenceMap {S T : ShortComplex (CochainComplex C ℤ)}
    (φ : S ⟶ T) (P : CochainComplex C ℤ) :
    homComplexContravariantSequence T P ⟶ homComplexContravariantSequence S P where
  τ₁ := homComplexPrecomp φ.τ₃ P
  τ₂ := homComplexPrecomp φ.τ₂ P
  τ₃ := homComplexPrecomp φ.τ₁ P
  comm₁₂ := by
    change homComplexPrecomp φ.τ₃ P ≫ homComplexPrecomp S.g P =
      homComplexPrecomp T.g P ≫ homComplexPrecomp φ.τ₂ P
    simp only [← homComplexPrecomp_comp, φ.comm₂₃]
  comm₂₃ := by
    change homComplexPrecomp φ.τ₂ P ≫ homComplexPrecomp S.f P =
      homComplexPrecomp T.f P ≫ homComplexPrecomp φ.τ₁ P
    simp only [← homComplexPrecomp_comp, φ.comm₁₂]

/-- The same reversed map, on the literal source complexes and without
modification of its cochain components. -/
def sourceHomContravariantSequenceMap {S T : ShortComplex (CochainComplex C ℤ)}
    (φ : S ⟶ T) (P : CochainComplex C ℤ) :
    sourceHomContravariantSequence T P ⟶ sourceHomContravariantSequence S P where
  τ₁ := sourceHomPrecomp φ.τ₃ P
  τ₂ := sourceHomPrecomp φ.τ₂ P
  τ₃ := sourceHomPrecomp φ.τ₁ P
  comm₁₂ := by
    change sourceHomPrecomp φ.τ₃ P ≫ sourceHomPrecomp S.g P =
      sourceHomPrecomp T.g P ≫ sourceHomPrecomp φ.τ₂ P
    simp only [← sourceHomPrecomp_comp, φ.comm₂₃]
  comm₂₃ := by
    change sourceHomPrecomp φ.τ₂ P ≫ sourceHomPrecomp S.f P =
      sourceHomPrecomp T.f P ≫ sourceHomPrecomp φ.τ₁ P
    simp only [← sourceHomPrecomp_comp, φ.comm₁₂]

/-- Naturality of the actual standard Hom connecting map in every degree. -/
theorem homComplexContravariantδ_naturality {S T : ShortComplex (CochainComplex C ℤ)}
    (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)
    (P : CochainComplex C ℤ) [∀ q, Injective (P.X q)] (n : ℤ) :
    homComplexContravariantδ T hT P n ≫ homologyMap (homComplexPrecomp φ.τ₃ P) (n + 1) =
      homologyMap (homComplexPrecomp φ.τ₁ P) n ≫ homComplexContravariantδ S hS P n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (homComplexContravariantSequenceMap φ P)
    (homComplexContravariantSequence_shortExact T hT P)
    (homComplexContravariantSequence_shortExact S hS P) n (n + 1) rfl

/-- Naturality of the literal source Hom connecting map in every degree. -/
theorem sourceHomContravariantδ_naturality {S T : ShortComplex (CochainComplex C ℤ)}
    (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)
    (P : CochainComplex C ℤ) [∀ q, Injective (P.X q)] (n : ℤ) :
    sourceHomContravariantδ T hT P n ≫ homologyMap (sourceHomPrecomp φ.τ₃ P) (n + 1) =
      homologyMap (sourceHomPrecomp φ.τ₁ P) n ≫ sourceHomContravariantδ S hS P n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (sourceHomContravariantSequenceMap φ P)
    (sourceHomContravariantSequence_shortExact T hT P)
    (sourceHomContravariantSequence_shortExact S hS P) n (n + 1) rfl

/-- Precomposition respects the original unscaled source homology data. -/
def sourceHomPrecompHomologyMapData {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    (P : CochainComplex C ℤ) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map (sourceHomPrecomp f P))
      (sourceHomLeftHomologyData F P n) (sourceHomLeftHomologyData F' P n) where
  φK := AddCommGrpCat.ofHom
    { toFun z := z.precomp f
      map_zero' := by ext; simp [Cocycle.precomp]
      map_add' z w := by ext; simp [Cocycle.precomp] }
  φH := AddCommGrpCat.ofHom (homComplexClassPrecomp f P n)
  commi := rfl
  commf' := by
    ext z
    apply Subtype.ext
    exact (ConcreteCategory.congr_hom ((sourceHomPrecomp f P).comm
      ((ComplexShape.up ℤ).prev n) n) z).symm
  commπ := by ext z; exact homComplexClassPrecomp_mk f P n z

/-- The unscaled source quotient equivalence is natural for original maps. -/
theorem sourceHomologyUnscaledAddEquiv_precomp {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    (P : CochainComplex C ℤ) (n : ℤ) (x : (sourceHomComplex F P).homology n) :
    sourceHomologyUnscaledAddEquiv F' P n (homologyMap (sourceHomPrecomp f P) n x) =
      homComplexClassPrecomp f P n (sourceHomologyUnscaledAddEquiv F P n x) :=
  ConcreteCategory.congr_hom (sourceHomPrecompHomologyMapData f P n).homologyMap_comm x

/-- Sign normalization preserves naturality in the source complex. -/
theorem sourceHomologyAddEquiv_precomp {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    (P : CochainComplex C ℤ) (n : ℤ) (x : (sourceHomComplex F P).homology n) :
    sourceHomologyAddEquiv F' P n (homologyMap (sourceHomPrecomp f P) n x) =
      homComplexClassPrecomp f P n (sourceHomologyAddEquiv F P n x) := by
  simp only [sourceHomologyAddEquiv_eq_sign, sourceHomologyUnscaledAddEquiv_precomp,
    Units.smul_def, map_zsmul]

/-- Actual source precomposition carries an original representative to its
unchanged precomposed representative. -/
theorem sourceHomologyMk_precomp {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    (P : CochainComplex C ℤ) {n : ℤ} (z : Cocycle F P n) :
    homologyMap (sourceHomPrecomp f P) n (sourceHomologyMk z) =
      sourceHomologyMk (z.precomp f) := by
  apply (sourceHomologyUnscaledAddEquiv F' P n).injective
  rw [sourceHomologyUnscaledAddEquiv_precomp]
  simp only [sourceHomologyMk, AddEquiv.apply_symm_apply, homComplexClassPrecomp_mk]

/-- The fixed unscaled derived-Hom comparison respects original
precomposition as well as the original connecting arrows. -/
theorem sourceHomologyUnscaledDerivedHomEquiv_precomp [HasDerivedCategory.{w} C]
    {F' F : CochainComplex C ℤ} (f : F' ⟶ F) (P : CochainComplex C ℤ)
    [P.IsKInjective] (n : ℤ) (x : (sourceHomComplex F P).homology n) :
    sourceHomologyUnscaledDerivedHomEquiv P F' n (homologyMap (sourceHomPrecomp f P) n x) =
      DerivedCategory.Q.map f ≫ sourceHomologyUnscaledDerivedHomEquiv P F n x := by
  obtain ⟨z, rfl⟩ := sourceHomologyMk_surjective P F n x
  rw [sourceHomologyMk_precomp, sourceHomologyUnscaledDerivedHomEquiv_mk,
    sourceHomologyUnscaledDerivedHomEquiv_mk, Cocycle.equivHomShift_symm_precomp]
  simp only [ShiftedHom.map, CategoryTheory.Functor.map_comp, Category.assoc]

end SGA.SGA2.ExposeV
