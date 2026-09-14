/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.HomComplexContravariantBoundary
import SGA.SGA2.ExposeV.SourceHomComplexCohomology

/-! # The literal source Hom-complex contravariant boundary -/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The original reversed Hom sequence with the literal displayed differential. -/
def sourceHomContravariantSequence (S : ShortComplex (CochainComplex C ℤ))
    (P : CochainComplex C ℤ) : ShortComplex (CochainComplex AddCommGrpCat ℤ) :=
  ShortComplex.mk (sourceHomPrecomp S.g P) (sourceHomPrecomp S.f P) (by
    ext n z
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.f n) (homComplexContravariantSequence S P).zero) z)

/-- The explicit sign normalization is an isomorphism of the original
short complexes, with all three precomposition maps unchanged. -/
def sourceHomContravariantSequenceIso (S : ShortComplex (CochainComplex C ℤ))
    (P : CochainComplex C ℤ) :
    sourceHomContravariantSequence S P ≅ homComplexContravariantSequence S P :=
  ShortComplex.isoMk (sourceHomComplexIso S.X₃ P) (sourceHomComplexIso S.X₂ P)
    (sourceHomComplexIso S.X₁ P)
    (sourceHomComplexIso_precomp S.g P).symm (sourceHomComplexIso_precomp S.f P).symm

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
  (P : CochainComplex C ℤ) [∀ q, Injective (P.X q)]

include hS in
/-- The literal source Hom sequence is short exact into every degreewise
injective complex, without a degreewise splitting assumption on the sequence. -/
theorem sourceHomContravariantSequence_shortExact :
    (sourceHomContravariantSequence S P).ShortExact :=
  ShortComplex.shortExact_of_iso (sourceHomContravariantSequenceIso S P).symm
    (homComplexContravariantSequence_shortExact S hS P)

/-- The actual connecting map for the literal source Hom complexes. -/
def sourceHomContravariantδ (n : ℤ) :
    (sourceHomComplex S.X₁ P).homology n ⟶
      (sourceHomComplex S.X₃ P).homology (n + 1) :=
  (sourceHomContravariantSequence_shortExact S hS P).δ n (n + 1) rfl

@[reassoc (attr := simp)]
theorem sourceHomContravariantδ_comp (n : ℤ) :
    sourceHomContravariantδ S hS P n ≫ homologyMap (sourceHomPrecomp S.g P) (n + 1) = 0 :=
  (sourceHomContravariantSequence_shortExact S hS P).δ_comp n (n + 1) rfl

@[reassoc (attr := simp)]
theorem comp_sourceHomContravariantδ (n : ℤ) :
    homologyMap (sourceHomPrecomp S.f P) n ≫ sourceHomContravariantδ S hS P n = 0 :=
  (sourceHomContravariantSequence_shortExact S hS P).comp_δ n (n + 1) rfl

/-- Exactness after the literal source connecting map. -/
theorem sourceHomContravariant_exact₁ (n : ℤ) :
    (ShortComplex.mk _ _ (sourceHomContravariantδ_comp S hS P n)).Exact :=
  (sourceHomContravariantSequence_shortExact S hS P).homology_exact₁ n (n + 1) rfl

include hS in
/-- Exactness at the middle term, for the displayed differential. -/
theorem sourceHomContravariant_exact₂ (n : ℤ) :
    ((sourceHomContravariantSequence S P).map
      (homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) n)).Exact :=
  (sourceHomContravariantSequence_shortExact S hS P).homology_exact₂ n

/-- Exactness before the literal source connecting map. -/
theorem sourceHomContravariant_exact₃ (n : ℤ) :
    (ShortComplex.mk _ _ (comp_sourceHomContravariantδ S hS P n)).Exact :=
  (sourceHomContravariantSequence_shortExact S hS P).homology_exact₃ n (n + 1) rfl

/-- The original connecting maps commute with the specified sign-normalizing
chain maps on actual homology. -/
theorem sourceHomContravariantδ_normalization (n : ℤ) :
    sourceHomContravariantδ S hS P n ≫
        homologyMap (sourceHomComplexIso S.X₃ P).hom (n + 1) =
      homologyMap (sourceHomComplexIso S.X₁ P).hom n ≫ homComplexContravariantδ S hS P n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (sourceHomContravariantSequenceIso S P).hom
    (sourceHomContravariantSequence_shortExact S hS P)
    (homComplexContravariantSequence_shortExact S hS P) n (n + 1) rfl

omit [∀ q, Injective (P.X q)] in
/-- Actual normalization on original source cohomology representatives. -/
theorem sourceHomologyMk_normalization {F : CochainComplex C ℤ} {n : ℤ}
    (z : Cocycle F P n) :
    homologyMap (sourceHomComplexIso F P).hom n (sourceHomologyMk z) =
      homComplexHomologyMk (sourceHomSign n • z) := by
  apply (HomComplex.homologyAddEquiv F P n).injective
  rw [homComplexHomologyMk_compare]
  change sourceHomologyAddEquiv F P n (sourceHomologyMk z) = _
  rw [sourceHomologyAddEquiv_eq_sign]
  change sourceHomSign n • (sourceHomologyUnscaledAddEquiv F P n
    ((sourceHomologyUnscaledAddEquiv F P n).symm (CohomologyClass.mk z))) = _
  rw [AddEquiv.apply_symm_apply]
  exact ((CohomologyClass.mkAddMonoidHom F P n).map_zsmul (sourceHomSign n : ℤ) z).symm

end SGA.SGA2.ExposeV
