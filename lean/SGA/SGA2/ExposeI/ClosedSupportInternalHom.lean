/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.ClosedSupportInternalHomSections
import SGA.SGA2.ExposeI.SupportedSheafModel

/-! # Internal Hom from the actual closed integer support sheaf -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Evaluation of a local morphism at the canonical integer generator
commutes with genuine restriction to a smaller open. -/
theorem closedSupportLocalGenerator_restrict (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) {U V : Opens X} (i : V ⟶ U)
    (φ : (abelianSheafHom (Opens.grothendieckTopology X) (zZX_closed Z) F).obj.obj
      (op U)) :
    (((abelianSheafHom (Opens.grothendieckTopology X) (zZX_closed Z) F).obj.map i.op φ).app
      (op (Over.mk (𝟙 V)))) ((integerPresheafToClosed Z).app (op V) ⟨1⟩) =
      F.presheaf.map i.op
        (φ.app (op (Over.mk (𝟙 U))) ((integerPresheafToClosed Z).app (op U) ⟨1⟩)) := by
  let j : Over.mk i ⟶ Over.mk (𝟙 U) := Over.homMk i (by simp)
  have hφ := φ.naturality_apply j.op
    ((integerPresheafToClosed Z).app (op U) ⟨1⟩)
  change φ.app (op (Over.mk i))
    ((zZX_closed Z).presheaf.map i.op ((integerPresheafToClosed Z).app (op U) ⟨1⟩)) =
      F.presheaf.map i.op
        (φ.app (op (Over.mk (𝟙 U))) ((integerPresheafToClosed Z).app (op U) ⟨1⟩)) at hφ
  have hc := (integerPresheafToClosed Z).naturality_apply i.op (⟨1⟩ : ULift ℤ)
  change (integerPresheafToClosed Z).app (op V) ⟨1⟩ = _ at hc
  rw [← hc] at hφ
  exact hφ

/-- The supported local-Hom comparison respects restriction of actual sections. -/
theorem closedSupportInternalHomSectionsEquiv_restrict (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) {U V : Opens X} (i : V ⟶ U)
    (φ : (abelianSheafHom (Opens.grothendieckTopology X) (zZX_closed Z) F).obj.obj
      (op U)) :
    closedSupportInternalHomSectionsEquiv Z V F
        ((abelianSheafHom (Opens.grothendieckTopology X) (zZX_closed Z) F).obj.map i.op φ) =
      gammaZSectionsRestriction F Z i (closedSupportInternalHomSectionsEquiv Z U F φ) := by
  apply Subtype.ext
  rw [closedSupportInternalHomSectionsEquiv_val]
  change _ = F.presheaf.map i.op (closedSupportInternalHomSectionsEquiv Z U F φ).val
  rw [closedSupportInternalHomSectionsEquiv_val]
  exact closedSupportLocalGenerator_restrict Z F i φ

/-- The supported local-Hom comparison respects actual coefficient maps. -/
theorem closedSupportInternalHomSectionsEquiv_naturality (Z : Closeds X) (U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (φ : (abelianSheafHom (Opens.grothendieckTopology X) (zZX_closed Z) F).obj.obj
      (op U)) :
    closedSupportInternalHomSectionsEquiv Z U G
        ((abelianSheafHomMap (Opens.grothendieckTopology X) (zZX_closed Z) f).hom.app
          (op U) φ) =
      gammaZSectionsMap f Z U (closedSupportInternalHomSectionsEquiv Z U F φ) := by
  apply Subtype.ext
  rw [closedSupportInternalHomSectionsEquiv_val]
  change _ = f.hom.app (op U) (closedSupportInternalHomSectionsEquiv Z U F φ).val
  rw [closedSupportInternalHomSectionsEquiv_val]
  rfl

/-- The underlying presheaf of actual internal Hom from the closed integer
support sheaf is the supported-section presheaf, naturally in both variables
that occur here: the coefficient sheaf and the open of sections. -/
def closedSupportInternalHomPresheafFunctorIso (Z : Closeds X) :
    abelianSheafHomFunctor (Opens.grothendieckTopology X) (zZX_closed Z) ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
        gammaZSectionsPresheafFunctor Z :=
  NatIso.ofComponents
    (fun F ↦ NatIso.ofComponents
      (fun U ↦ (closedSupportInternalHomSectionsEquiv Z U.unop F).toAddCommGrpIso)
      (fun i ↦ by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro φ
        exact closedSupportInternalHomSectionsEquiv_restrict Z F i.unop φ))
    (fun f ↦ by
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro φ
      exact closedSupportInternalHomSectionsEquiv_naturality Z U.unop f φ)

/-- **I.1.6, closed support, sheaf-valued:** actual internal Hom from
`ℤ_{Z,X}` is naturally the original kernel sheaf of supported sections. -/
def closedSupportInternalHomFunctorIso (Z : Closeds X) :
    abelianSheafHomFunctor (Opens.grothendieckTopology X) (zZX_closed Z) ≅
      underlineGammaZFunctor Z :=
  ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).whiskeringRight
    (Sheaf AddCommGrpCat.{u} X)).preimageIso
    (closedSupportInternalHomPresheafFunctorIso Z ≪≫
      (underlineGammaZPresheafFunctorIso Z).symm)

/-- **I.2.3 bis, closed support, sheaf-valued:** the actual derived internal
Hom sheaf agrees with the original derived supported-sheaf functor in every degree. -/
def closedSupportInternalSheafExtIso (Z : Closeds X) (n : ℕ) :
    internalSheafExtFunctor (Opens.grothendieckTopology X) (zZX_closed Z) n ≅
      derivedUnderlineGammaZ Z n := by
  letI : (underlineGammaZFunctor Z).Additive := inferInstance
  exact rightDerivedFunctorIso (closedSupportInternalHomFunctorIso Z) n

/-- The unchanged kernel/cokernel/derived-pushforward model also computes
the actual sheaf Ext from the closed integer support object. -/
def closedSupportInternalSheafExtIsoModel (Z : Closeds X) (n : ℕ) :
    internalSheafExtFunctor (Opens.grothendieckTopology X) (zZX_closed Z) n ≅
      sheafH_ZFunctor Z n :=
  closedSupportInternalSheafExtIso Z n ≪≫ derivedUnderlineGammaZIsoModel Z n

end SGA.SGA2.ExposeI
