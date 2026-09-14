/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.HomComplexNaturality
import SGA.SGA2.ExposeI.DerivedSupportedSections

/-!
# Integer-indexed resolution cohomology and the original right-derived functor

The original nonnegative resolution comparison extends to the corresponding
integer-indexed complex. The comparison retains actual coefficient maps and
the augmentation condition on their resolution representatives.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive]

/-- Integer-indexed cohomology of a mapped injective resolution computes the
original right-derived functor. -/
def injectiveResolutionIntHomologyIso {M : C} (I : InjectiveResolution M) (n : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) ≅
        (F.rightDerived n).obj M :=
  (homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).mapIso
      (mapExtendIso F ComplexShape.embeddingUpNat I.cocomplex) ≪≫
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl ≪≫
    (I.isoRightDerivedObj F n).symm

/-- The integer-indexed comparison is natural for every actual augmented
resolution map, not only for the chosen comparison map. -/
@[reassoc]
theorem injectiveResolutionIntHomologyIso_naturality
    {M N : C} (a : M ⟶ N) (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = a ≫ J.ι.f 0) (n : ℕ) :
    homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (extendMap φ ComplexShape.embeddingUpNat)) (n : ℤ) ≫
        (injectiveResolutionIntHomologyIso F J n).hom =
      (injectiveResolutionIntHomologyIso F I n).hom ≫ (F.rightDerived n).map a := by
  have h := congrArg (fun ψ ↦ homologyMap ψ (n : ℤ))
    (mapExtendIso_naturality F ComplexShape.embeddingUpNat φ)
  simp only [homologyMap_comp] at h
  dsimp only [injectiveResolutionIntHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  erw [← Category.assoc, h, Category.assoc]
  erw [extendHomologyIso_hom_naturality_assoc]
  erw [← InjectiveResolution.isoRightDerivedObj_inv_naturality a I J φ hφ F n]
  simp only [Category.assoc]
  rfl

end SGA.SGA2.ExposeI
