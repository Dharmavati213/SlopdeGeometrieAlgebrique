/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.AdditiveFunctorModules

/-!
# Naturality of the canonical scalar lift

Every natural transformation of additive abelian-group-valued functors is
linear for their induced scalar actions. A linear module-valued functor is
recovered from its forgotten functor by an actual identity-on-elements iso.
These comparisons transport original functor statements, not extra scalar
compatibility hypotheses.
-/

noncomputable section

universe u v w

open CategoryTheory Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
variable {T U : C ⥤ AddCommGrpCat.{u}} [T.Additive] [U.Additive]

/-- Naturality at scalar endomorphisms supplies scalar compatibility. -/
def additiveFunctorModuleLiftNatTrans (α : T ⟶ U) :
    additiveFunctorModuleLift (R := R) T ⟶ additiveFunctorModuleLift (R := R) U where
  app M := ModuleCat.ofHom
    (X := (additiveFunctorModuleLift (R := R) T).obj M)
    (Y := (additiveFunctorModuleLift (R := R) U).obj M)
    { (α.app M).hom with
      map_smul' := fun r x => ConcreteCategory.congr_hom (α.naturality (r • 𝟙 M)) x }
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    ext x
    exact ConcreteCategory.congr_hom (α.naturality f) x

/-- Natural isomorphisms lift without a supplied linearity assumption. -/
def additiveFunctorModuleLiftIso (e : T ≅ U) :
    additiveFunctorModuleLift (R := R) T ≅ additiveFunctorModuleLift (R := R) U where
  hom := additiveFunctorModuleLiftNatTrans e.hom
  inv := additiveFunctorModuleLiftNatTrans e.inv
  hom_inv_id := by
    ext M x
    exact ConcreteCategory.congr_hom (e.hom_inv_id_app M) x
  inv_hom_id := by
    ext M x
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app M) x

/-- A functor with its existing linear scalar action agrees with the
canonical lift of its forgotten additive functor, on the same elements. -/
def linearFunctorModuleLiftForgetIso (L : C ⥤ ModuleCat.{u} R)
    [L.Additive] [L.Linear R] :
    additiveFunctorModuleLift (R := R) (L ⋙ forget₂ (ModuleCat R) AddCommGrpCat) ≅ L :=
  NatIso.ofComponents (fun M =>
    LinearEquiv.toModuleIso
      (X₁ := (additiveFunctorModuleLift (R := R)
        (L ⋙ forget₂ (ModuleCat R) AddCommGrpCat)).obj M) (X₂ := L.obj M)
      { toFun := id
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => by
          change L.map (r • 𝟙 M) (show L.obj M from x) = r • (show L.obj M from x)
          rw [L.map_smul, L.map_id]
          rfl }) (fun _ => by ext x; rfl)

/-- An original abelian-group-valued representation has an actual
module-valued refinement for the canonical source action. -/
def additiveFunctorModuleRepresentationIso
    (L : C ⥤ ModuleCat.{u} R) [L.Additive] [L.Linear R]
    (e : T ≅ L ⋙ forget₂ (ModuleCat R) AddCommGrpCat) :
    additiveFunctorModuleLift (R := R) T ≅ L :=
  additiveFunctorModuleLiftIso e ≪≫ linearFunctorModuleLiftForgetIso L

end SGA.SGA2.ExposeIV
