/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.InjectiveHorseshoeComparison
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Functorial horseshoes and coherent row-resolution change

The simultaneous horseshoe comparison is a functor on short exact sequences
after passing to homotopy. Its morphisms are independent of the chosen
augmentation-compatible simultaneous lift. More generally, arbitrary injective
resolutions of the whole short complex have natural comparison isomorphisms
satisfying the identity and cocycle laws in the same homotopy category.
-/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV
namespace InjectiveHorseshoe

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The full category of short exact sequences, with their original morphisms. -/
abbrev ShortExactRows :=
  ObjectProperty.FullSubcategory (fun S : ShortComplex C => S.ShortExact)

variable [EnoughInjectives C]

/-- The horseshoe construction is functorial up to simultaneous homotopy. -/
def homotopyFunctor : ShortExactRows C ⥤ HomotopyCategory (ShortComplex C) (ComplexShape.up ℕ) where
  obj S := (HomotopyCategory.quotient _ _).obj (cocomplex S.obj S.property)
  map {S T} φ := (HomotopyCategory.quotient _ _).map (compare S.property T.property φ.hom)
  map_id S := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    exact HomotopyCategory.eq_of_homotopy _ _ (compareIdHomotopy S.property)
  map_comp {S T U} φ ψ := by
    rw [← (HomotopyCategory.quotient _ _).map_comp]
    exact HomotopyCategory.eq_of_homotopy _ _
      (compareCompHomotopy S.property T.property U.property φ.hom ψ.hom)

variable {C}

/-- Any simultaneous augmentation-compatible lift represents the same functorial map. -/
theorem homotopyFunctor_map_eq {S T : ShortExactRows C} (φ : S ⟶ T)
    (a : cocomplex S.obj S.property ⟶ cocomplex T.obj T.property)
    (ha : rowAugmentation S.obj S.property ≫ a =
      (single₀ (ShortComplex C)).map φ.hom ≫ rowAugmentation T.obj T.property) :
    (homotopyFunctor C).map φ = (HomotopyCategory.quotient _ _).map a :=
  HomotopyCategory.eq_of_homotopy _ _
    (compareHomotopy S.property T.property φ.hom _ _
      (compare_augmentation S.property T.property φ.hom) ha)

end InjectiveHorseshoe

namespace InjectiveRowResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {S T : ShortComplex C}

/-- Canonical comparison between any two injective resolutions of the whole
short complex, without assuming enough injectives in `ShortComplex C`. -/
def change (I J : InjectiveResolution S) :
    (HomotopyCategory.quotient (ShortComplex C) (ComplexShape.up ℕ)).obj I.cocomplex ≅
      (HomotopyCategory.quotient (ShortComplex C) (ComplexShape.up ℕ)).obj J.cocomplex :=
  HomotopyCategory.isoOfHomotopyEquiv (InjectiveResolution.homotopyEquiv I J)

@[simp]
theorem change_refl (I : InjectiveResolution S) : change I I = Iso.refl _ := by
  apply Iso.ext
  change (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc (𝟙 S) I I) = 𝟙 _
  rw [← (HomotopyCategory.quotient _ _).map_id]
  exact HomotopyCategory.eq_of_homotopy _ _ (InjectiveResolution.descIdHomotopy S I)

/-- The comparison isomorphisms satisfy the actual cocycle identity. -/
@[simp]
theorem change_trans (I J K : InjectiveResolution S) :
    change I J ≪≫ change J K = change I K := by
  apply Iso.ext
  change (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc (𝟙 S) J I) ≫
    (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc (𝟙 S) K J) =
      (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc (𝟙 S) K I)
  rw [← (HomotopyCategory.quotient _ _).map_comp]
  apply HomotopyCategory.eq_of_homotopy
  simpa only [Category.id_comp]
    using (InjectiveResolution.descCompHomotopy (𝟙 S) (𝟙 S) I J K).symm

/-- Changing row resolutions is natural for maps of the original short complexes. -/
@[reassoc]
theorem change_naturality (φ : S ⟶ T)
    (I I' : InjectiveResolution S) (J J' : InjectiveResolution T) :
    (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc φ J I) ≫ (change J J').hom =
      (change I I').hom ≫
        (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc φ J' I') := by
  change (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc φ J I) ≫
    (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc (𝟙 T) J' J) =
      (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc (𝟙 S) I' I) ≫
        (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc φ J' I')
  rw [← (HomotopyCategory.quotient _ _).map_comp, ← (HomotopyCategory.quotient _ _).map_comp]
  apply HomotopyCategory.eq_of_homotopy
  apply InjectiveResolution.descHomotopy φ <;> simp

end InjectiveRowResolution
end SGA.SGA2.ExposeV
