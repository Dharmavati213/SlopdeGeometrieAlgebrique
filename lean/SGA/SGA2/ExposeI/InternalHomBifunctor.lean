/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.InternalHomPrecomposition
import SGA.SGA2.ExposeI.SheafExtLocalComparison

/-!
# First-variable maps of sheaf Ext

Internal Hom precomposition, already constructed, derives to sheaf Ext.
Identity and composition of first-variable maps are recorded, together with
commutation against coefficient postcomposition.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

theorem abelianSheafHomPrecomp_id {F : CategoryTheory.Sheaf J AddCommGrpCat.{u}} :
    abelianSheafHomPrecomp J (𝟙 F) = 𝟙 _ := by
  apply NatTrans.ext
  funext G
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  change Functor.whiskerLeft (Over.forget U.unop).op (𝟙 F.obj) ≫ φ = φ
  simp

section Derived

variable [HasSheafify J AddCommGrpCat.{u}]
  [HasInjectiveResolutions (CategoryTheory.Sheaf J AddCommGrpCat.{u})]

/-- First-variable precomposition of sheaf Ext, obtained by deriving the
internal-Hom precomposition. -/
def internalSheafExtPrecomp {F F' : CategoryTheory.Sheaf J AddCommGrpCat.{u}}
    (f : F ⟶ F') (n : ℕ) :
    internalSheafExtFunctor J F' n ⟶ internalSheafExtFunctor J F n :=
  (abelianSheafHomPrecomp J f).rightDerived n

theorem internalSheafExtPrecomp_id (F : CategoryTheory.Sheaf J AddCommGrpCat.{u})
    (n : ℕ) : internalSheafExtPrecomp J (𝟙 F) n = 𝟙 _ := by
  rw [internalSheafExtPrecomp, abelianSheafHomPrecomp_id, NatTrans.rightDerived_id]
  rfl

theorem internalSheafExtPrecomp_comp
    {E F G : CategoryTheory.Sheaf J AddCommGrpCat.{u}} (f : E ⟶ F) (g : F ⟶ G)
    (n : ℕ) :
    internalSheafExtPrecomp J (f ≫ g) n =
      internalSheafExtPrecomp J g n ≫ internalSheafExtPrecomp J f n := by
  rw [internalSheafExtPrecomp, abelianSheafHomPrecomp_comp, NatTrans.rightDerived_comp]
  rfl

/-- Precomposition and coefficient postcomposition commute after derivation. -/
theorem internalSheafExt_precomp_postcomp
    {F F' G G' : CategoryTheory.Sheaf J AddCommGrpCat.{u}}
    (f : F ⟶ F') (g : G ⟶ G') (n : ℕ) :
    (internalSheafExtFunctor J F' n).map g ≫ (internalSheafExtPrecomp J f n).app G' =
      (internalSheafExtPrecomp J f n).app G ≫ (internalSheafExtFunctor J F n).map g :=
  (internalSheafExtPrecomp J f n).naturality g

end Derived

end SGA.SGA2.ExposeI
