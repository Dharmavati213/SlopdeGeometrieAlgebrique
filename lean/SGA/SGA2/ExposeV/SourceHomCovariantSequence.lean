/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.HomComplexCovariantBoundary
import SGA.SGA2.ExposeV.SourceHomContravariantBoundary

/-! # The literal source covariant Hom long exact sequence -/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
open SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The literal source differential commutes with original postcomposition. -/
def sourceHomPostcomp (F : CochainComplex C ℤ) {G H : CochainComplex C ℤ} (f : G ⟶ H) :
    sourceHomComplex F G ⟶ sourceHomComplex F H where
  f n := AddCommGrpCat.ofHom
    { toFun z := z.comp (Cochain.ofHom f) (add_zero n)
      map_zero' := by simp
      map_add' z w := by simp }
  comm' i j hij := by
    ext z
    change sourceHomδ i j (z.comp (Cochain.ofHom f) (add_zero i)) =
      (sourceHomδ i j z).comp (Cochain.ofHom f) (add_zero j)
    simp [sourceHomδ, δ_comp_ofHom]

/-- The explicit degreewise sign normalization preserves postcomposition. -/
@[reassoc]
theorem sourceHomComplexIso_postcomp (F : CochainComplex C ℤ)
    {G H : CochainComplex C ℤ} (f : G ⟶ H) :
    sourceHomPostcomp F f ≫ (sourceHomComplexIso F H).hom =
      (sourceHomComplexIso F G).hom ≫ homComplexPostcomp F f := by
  ext n z
  change Cochain F G n at z
  change sourceHomSign n • z.comp (Cochain.ofHom f) (add_zero n) =
    (sourceHomSign n • z).comp (Cochain.ofHom f) (add_zero n)
  simp only [Cochain.units_smul_comp]

/-- The original covariant Hom sequence with the displayed source differential. -/
def sourceHomCovariantSequence (F : CochainComplex C ℤ)
    (S : ShortComplex (CochainComplex C ℤ)) : ShortComplex (CochainComplex AddCommGrpCat ℤ) :=
  ShortComplex.mk (sourceHomPostcomp F S.f) (sourceHomPostcomp F S.g) (by
    ext n z
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.f n) (homComplexCovariantSequence F S).zero) z)

/-- Explicit normalization of the three original Hom complexes respects the
original short complex, not just its individual objects. -/
def sourceHomCovariantSequenceIso (F : CochainComplex C ℤ)
    (S : ShortComplex (CochainComplex C ℤ)) :
    sourceHomCovariantSequence F S ≅ homComplexCovariantSequence F S :=
  ShortComplex.isoMk (sourceHomComplexIso F S.X₁) (sourceHomComplexIso F S.X₂)
    (sourceHomComplexIso F S.X₃)
    (sourceHomComplexIso_postcomp F S.f).symm (sourceHomComplexIso_postcomp F S.g).symm

variable (F : CochainComplex C ℤ) (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
  [∀ q, Injective (S.X₁.X q)]

include hS

/-- The actual source Hom sequence is short exact whenever the first
coefficient complex is degreewise injective. The source complex is arbitrary. -/
theorem sourceHomCovariantSequence_shortExact :
    (sourceHomCovariantSequence F S).ShortExact :=
  ShortComplex.shortExact_of_iso (sourceHomCovariantSequenceIso F S).symm
    (homComplexCovariantSequence_shortExact F S hS)

/-- The actual connecting map of the literal source covariant Hom sequence. -/
def sourceHomCovariantδ (n : ℤ) :
    (sourceHomComplex F S.X₃).homology n ⟶ (sourceHomComplex F S.X₁).homology (n + 1) :=
  (sourceHomCovariantSequence_shortExact F S hS).δ n (n + 1) rfl

@[reassoc (attr := simp)]
theorem sourceHomCovariantδ_comp (n : ℤ) :
    sourceHomCovariantδ F S hS n ≫ homologyMap (sourceHomPostcomp F S.f) (n + 1) = 0 :=
  (sourceHomCovariantSequence_shortExact F S hS).δ_comp n (n + 1) rfl

@[reassoc (attr := simp)]
theorem comp_sourceHomCovariantδ (n : ℤ) :
    homologyMap (sourceHomPostcomp F S.g) n ≫ sourceHomCovariantδ F S hS n = 0 :=
  (sourceHomCovariantSequence_shortExact F S hS).comp_δ n (n + 1) rfl

/-- Exactness after the original source boundary. -/
theorem sourceHomCovariant_exact₁ (n : ℤ) :
    (ShortComplex.mk _ _ (sourceHomCovariantδ_comp F S hS n)).Exact :=
  (sourceHomCovariantSequence_shortExact F S hS).homology_exact₁ n (n + 1) rfl

/-- Exactness at the original middle source Hom complex. -/
theorem sourceHomCovariant_exact₂ (n : ℤ) :
    ((sourceHomCovariantSequence F S).map
      (homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) n)).Exact :=
  (sourceHomCovariantSequence_shortExact F S hS).homology_exact₂ n

/-- Exactness before the original source boundary. -/
theorem sourceHomCovariant_exact₃ (n : ℤ) :
    (ShortComplex.mk _ _ (comp_sourceHomCovariantδ F S hS n)).Exact :=
  (sourceHomCovariantSequence_shortExact F S hS).homology_exact₃ n (n + 1) rfl

/-- Explicit normalization commutes with the original covariant connecting maps. -/
theorem sourceHomCovariantδ_normalization (n : ℤ) :
    sourceHomCovariantδ F S hS n ≫ homologyMap (sourceHomComplexIso F S.X₁).hom (n + 1) =
      homologyMap (sourceHomComplexIso F S.X₃).hom n ≫ homComplexCovariantδ F S hS n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (sourceHomCovariantSequenceIso F S).hom
    (sourceHomCovariantSequence_shortExact F S hS)
    (homComplexCovariantSequence_shortExact F S hS) n (n + 1) rfl

end SGA.SGA2.ExposeV
