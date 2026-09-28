/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedSupportedSheaves

/-!
# SGA 2, I.2.5: original derived sheaves with open support

The full closed support kernel is the identity. Consequently the actual
ambient open-support functor is restriction followed by direct image. Exact,
injective-preserving restriction can be taken outside right derivation;
no exactness of the open direct-image functor is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat
open CategoryTheory.Functor
open scoped ConcreteCategory

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Every section is supported in the full closed subset. -/
def gammaZTopSectionsEquiv (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    gammaZSections F (⊤ : Closeds X) U ≃+ F.presheaf.obj (op U) where
  toFun s := s.val
  invFun s := ⟨s, by rw [gammaZSections_top]; trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The original full-support kernel, as an object, is the coefficient sheaf.
The forward map is its original kernel inclusion. -/
def underlineGammaZTopObjIso (F : Sheaf AddCommGrpCat.{u} X) :
    underlineGammaZ F (⊤ : Closeds X) ≅ F := by
  let e : (underlineGammaZ F (⊤ : Closeds X)).presheaf ≅ F.presheaf :=
    NatIso.ofComponents
      (fun U => ((underlineGammaZSectionsEquiv F ⊤ U.unop).trans
        (gammaZTopSectionsEquiv F U.unop)).toAddCommGrpIso)
      (fun i => by
        ext s
        exact congrArg Subtype.val (underlineGammaZSectionsEquiv_restrict F ⊤ i.unop s))
  have he : e.hom = (underlineGammaZ_ι F (⊤ : Closeds X)).hom := by
    apply NatTrans.ext
    funext U
    ext s
    exact underlineGammaZSectionsEquiv_val F ⊤ U.unop s
  refine
    { hom := underlineGammaZ_ι F ⊤
      inv := ⟨e.inv⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply CategoryTheory.Sheaf.hom_ext
    change (underlineGammaZ_ι F (⊤ : Closeds X)).hom ≫ e.inv = 𝟙 _
    rw [← he, e.hom_inv_id]
  · apply CategoryTheory.Sheaf.hom_ext
    change e.inv ≫ (underlineGammaZ_ι F (⊤ : Closeds X)).hom = 𝟙 _
    rw [← he, e.inv_hom_id]

theorem underlineGammaZTopObjIso_hom (F : Sheaf AddCommGrpCat.{u} X) :
    (underlineGammaZTopObjIso F).hom = underlineGammaZ_ι F (⊤ : Closeds X) := rfl

/-- The original full-support kernel functor is naturally the identity. -/
def underlineGammaZTopIso :
    underlineGammaZFunctor (⊤ : Closeds X) ≅ 𝟭 (Sheaf AddCommGrpCat.{u} X) :=
  NatIso.ofComponents underlineGammaZTopObjIso
    (fun f => underlineGammaZMap_comp_ι f ⊤)

/-- The actual ambient support functor of an open subset is ordinary open
restriction followed by the actual direct-image functor. -/
def underlineGammaLocallyClosedOfOpenIso (U : Opens X) :
    underlineGammaLocallyClosedFunctor (LocallyClosedIn.ofOpen U) ≅
      iShriek_open U ⋙ Sheaf.pushforward AddCommGrpCat.{u} U.inclusion' :=
  isoWhiskerLeft (iShriek_open U)
    (isoWhiskerRight (underlineGammaZTopIso (X := (Opens.toTopCat X).obj U))
      (Sheaf.pushforward AddCommGrpCat.{u} U.inclusion') ≪≫ Functor.leftUnitor _)

/-- **I.2.5, equation (22):** the original derived sheaves with open support
are the higher direct images of the actual restricted coefficient sheaf,
naturally in the coefficient sheaf and in every degree. -/
def derivedUnderlineGammaOfOpenIso (U : Opens X) (n : ℕ) :
    derivedUnderlineGammaLocallyClosed (LocallyClosedIn.ofOpen U) n ≅
      iShriek_open U ⋙ (Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').rightDerived n := by
  let := (openExtensionByZeroAdjunction U).isRightAdjoint
  letI : (iShriek_open U).PreservesHomology := inferInstance
  exact rightDerivedFunctorIso (underlineGammaLocallyClosedOfOpenIso U) n ≪≫
    rightDerivedPrecomposeIso (iShriek_open U)
      (Sheaf.pushforward AddCommGrpCat.{u} U.inclusion') n

/-- Explicit coefficient naturality of the open-support higher-direct-image comparison. -/
theorem derivedUnderlineGammaOfOpenIso_hom_naturality (U : Opens X) (n : ℕ)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    (derivedUnderlineGammaLocallyClosed (LocallyClosedIn.ofOpen U) n).map f ≫
      (derivedUnderlineGammaOfOpenIso U n).hom.app G =
        (derivedUnderlineGammaOfOpenIso U n).hom.app F ≫
          ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').rightDerived n).map
            ((iShriek_open U).map f) :=
  (derivedUnderlineGammaOfOpenIso U n).hom.naturality f

end SGA.SGA2.ExposeI
