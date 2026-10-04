/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ModulesHomLocal
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# Inverse image and open restriction for module sheaves

Restriction to an open subspace is naturally isomorphic to inverse image along the
open immersion. Consequently inverse image commutes with restriction to the inverse
image of an open set.

Adopted from the unmerged branch `codex/foundations-missing-inputs` (commit `c65c9a0`, file
`ModuleHomPullback.lean`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X Y Z : LocallyRingedSpace.{u}}

/-- Strict restriction to an open subspace is left adjoint to direct image. -/
def restrictOpenAdjunction (U : Opens X) :
    restrictOpenFunctor U ⊣ pushforward (X.ofRestrict U.isOpenEmbedding) := by
  haveI : U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).toSheafedSpace)
      (Opens.grothendieckTopology X.toSheafedSpace) :=
    U.isOpenEmbedding.functor_isContinuous
  haveI : (Opens.map U.inclusion').IsContinuous
      (Opens.grothendieckTopology X.toSheafedSpace)
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).toSheafedSpace) :=
    inferInstanceAs ((Opens.map U.inclusion').IsContinuous
      (Opens.grothendieckTopology X.toTopCat)
      (Opens.grothendieckTopology ((Opens.toTopCat X.toTopCat).obj U)))
  refine SheafOfModules.pushforwardPushforwardAdj
    (F := U.isOpenEmbedding.functor) (G := Opens.map U.inclusion')
    (S := (X.restrict U.isOpenEmbedding).ringCatSheaf) (R := X.ringCatSheaf)
    U.isOpenEmbedding.isOpenMap.adjunction
    (show (X.restrict U.isOpenEmbedding).ringCatSheaf ⟶ _ from ⟨𝟙 _⟩)
    (X.ofRestrict U.isOpenEmbedding).toRingCatSheafHom ?_ ?_
  · ext V r
    rfl
  · ext V r
    change X.presheaf.map
      (U.isOpenEmbedding.functor.map (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V.unop)).op
        (X.presheaf.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app
          (U.isOpenEmbedding.functor.obj V.unop)).op r) = r
    erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      U.isOpenEmbedding.isOpenMap.adjunction.left_triangle_components, op_id,
      CategoryTheory.Functor.map_id]
    rfl

/-- Strict open restriction agrees naturally with inverse image along the open immersion. -/
def restrictOpenIsoPullback (U : Opens X) :
    restrictOpenFunctor U ≅ pullback (X.ofRestrict U.isOpenEmbedding) :=
  (restrictOpenAdjunction U).leftAdjointUniq
    (pullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding))

/-- Composition of inverse-image functors for module sheaves. -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  SheafOfModules.pullbackComp _ _

/-- A morphism restricted to an open set in its target. -/
def mapRestrictOpen (f : X ⟶ Y) (U : Opens Y) :
    X.restrict ((Opens.map f.base).obj U).isOpenEmbedding ⟶ Y.restrict U.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift (Y.ofRestrict U.isOpenEmbedding)
    (X.ofRestrict ((Opens.map f.base).obj U).isOpenEmbedding ≫ f) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨f.base x.1, x.2⟩, rfl⟩)

@[reassoc] lemma mapRestrictOpen_comp (f : X ⟶ Y) (U : Opens Y) :
    mapRestrictOpen f U ≫ Y.ofRestrict U.isOpenEmbedding =
      X.ofRestrict ((Opens.map f.base).obj U).isOpenEmbedding ≫ f :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- Inverse image commutes with restriction to the inverse image of an open set. -/
def pullbackRestrictOpenIso (f : X ⟶ Y) (U : Opens Y) :
    pullback f ⋙ restrictOpenFunctor ((Opens.map f.base).obj U) ≅
      restrictOpenFunctor U ⋙ pullback (mapRestrictOpen f U) :=
  Functor.isoWhiskerLeft (pullback f) (restrictOpenIsoPullback ((Opens.map f.base).obj U)) ≪≫
    pullbackComp _ f ≪≫
      eqToIso (congrArg pullback (mapRestrictOpen_comp f U).symm) ≪≫
        (pullbackComp _ _).symm ≪≫
          Functor.isoWhiskerRight (restrictOpenIsoPullback U).symm (pullback (mapRestrictOpen f U))

end AlgebraicGeometry.LocallyRingedSpace.Modules
