/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.ClosedSupportRestriction
import SGA.SGA2.ExposeI.TopologicalInternalHom

/-! # Internal Hom from the closed integer support object: actual local sections -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat
open scoped ConcreteCategory

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Local internal Hom from the actual closed integer support object is
the original group of sections supported in that closed subset. -/
def closedSupportInternalHomSectionsEquiv (Z : Closeds X) (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (abelianSheafHom (Opens.grothendieckTopology X) (zZX_closed Z) F).obj.obj (op U) ≃+
      gammaZSections F Z U :=
  (internalHomSectionsRestrictEquiv U (zZX_closed Z) F).trans
    ((sheafHomAddCongr (closedSupportRestrictionIso Z U) (Iso.refl _)).trans
      ((closedSupportHomEquiv (closedSupportOnOpen Z U) (restrictToOpen F U)).trans
        (restrictToOpenGammaZEquiv Z U F)))

/-- The local section comparison is evaluation on the canonical integer
generator. This formula makes its restriction compatibility explicit. -/
theorem closedSupportInternalHomSectionsEquiv_val (Z : Closeds X) (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X)
    (φ : (abelianSheafHom (Opens.grothendieckTopology X) (zZX_closed Z) F).obj.obj (op U)) :
    (closedSupportInternalHomSectionsEquiv Z U F φ).val =
      φ.app (op (Over.mk (𝟙 U))) ((integerPresheafToClosed Z).app (op U) ⟨1⟩) := by
  change (restrictToOpenGammaZEquiv Z U F
    (closedSupportHomEquiv (closedSupportOnOpen Z U) (restrictToOpen F U)
      ((closedSupportRestrictionIso Z U).inv ≫
        internalHomSectionsRestrictEquiv U (zZX_closed Z) F φ ≫ 𝟙 _))).val = _
  rw [Category.comp_id, restrictToOpenGammaZEquiv_apply_val]
  change (restrictToOpenSectionsIso U F).hom
    (((closedSupportRestrictionIso Z U).inv ≫
      internalHomSectionsRestrictEquiv U (zZX_closed Z) F φ).hom.app (op ⊤)
        ((integerPresheafToClosed (closedSupportOnOpen Z U)).app (op ⊤) ⟨1⟩)) = _
  rw [internalHomSectionsRestrictEquiv_apply]
  let a := (((sheafToPresheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
    AddCommGrpCat.{u}).mapIso ((openPullbackSheafRestrictIso U).app F)).app (op ⊤))
  let hU : U.isOpenEmbedding.functor.obj ⊤ = U := by simp
  change F.presheaf.map (eqToHom (congrArg op hU))
    (a.hom (a.inv ((internalHomSectionsNaiveEquiv U (zZX_closed Z) F φ).hom.app (op ⊤)
      (((closedSupportRestrictionIso Z U).inv ≫
        (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).hom.app (zZX_closed Z)).hom.app
          (op ⊤) ((integerPresheafToClosed (closedSupportOnOpen Z U)).app (op ⊤) ⟨1⟩))))) = _
  rw [Iso.inv_hom_id_apply, closedSupportRestrictionIso_generator]
  let K : Over U := U.overEquivalence.inverse.obj ⊤
  let i : Over.mk (𝟙 U) ⟶ K := Over.homMk (eqToHom hU.symm)
  have hφ := φ.naturality_apply i.op
    ((integerPresheafToClosed Z).app (op (U.isOpenEmbedding.functor.obj ⊤)) (⟨1⟩ : ULift ℤ))
  have hc := (integerPresheafToClosed Z).naturality_apply i.left.op (⟨1⟩ : ULift ℤ)
  change (integerPresheafToClosed Z).app (op U) ⟨1⟩ =
    (zZX_closed Z).presheaf.map i.left.op
      ((integerPresheafToClosed Z).app (op (U.isOpenEmbedding.functor.obj ⊤)) ⟨1⟩) at hc
  change φ.app (op (Over.mk (𝟙 U)))
      ((zZX_closed Z).presheaf.map i.left.op
        ((integerPresheafToClosed Z).app (op (U.isOpenEmbedding.functor.obj ⊤)) ⟨1⟩)) =
    F.presheaf.map i.left.op
      (φ.app (op K) ((integerPresheafToClosed Z).app
        (op (U.isOpenEmbedding.functor.obj ⊤)) ⟨1⟩)) at hφ
  rw [← hc] at hφ
  have hi : i.left.op = eqToHom (congrArg op hU) := Subsingleton.elim _ _
  change φ.app (op (Over.mk (𝟙 U))) ((integerPresheafToClosed Z).app (op U) ⟨1⟩) =
    F.presheaf.map i.left.op
      (φ.app (op K) ((integerPresheafToClosed Z).app
        (op (U.isOpenEmbedding.functor.obj ⊤)) ⟨1⟩)) at hφ
  rw [hi] at hφ
  exact hφ.symm

end SGA.SGA2.ExposeI
