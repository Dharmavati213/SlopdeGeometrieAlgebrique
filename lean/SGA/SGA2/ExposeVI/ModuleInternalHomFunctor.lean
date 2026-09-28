/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleInternalHom
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Coefficient functor and left exactness of local linear Hom

Sections are actual morphisms of module presheaves on the slice category.
The coefficient functor is therefore left exact, by the left exactness of
restriction and ordinary Hom. Its maps are the original postcomposition maps.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- Local linearity is precisely the morphism condition for the restricted module presheaves. -/
def moduleLocalHomOverEquiv (F G : PresheafOfModules.{u} R) (U : C) :
    moduleLocalHom F G U ≃+
      ((PresheafOfModules.pushforward₀ (Over.forget U) R).obj F ⟶
        (PresheafOfModules.pushforward₀ (Over.forget U) R).obj G) where
  toFun φ := PresheafOfModules.homMk φ.val (fun V r x ↦ φ.property V.unop r x)
  invFun φ := ⟨(PresheafOfModules.toPresheaf _).map φ,
    fun V r x ↦ (φ.app (op V)).hom.map_smul r x⟩
  left_inv φ := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext x
    rfl
  right_inv φ := by
    ext V x
    rfl
  map_add' _ _ := rfl

/-- Postcomposition of local module-linear maps is additive. -/
def moduleLocalHomPostcomp (F : PresheafOfModules.{u} R)
    {G H : PresheafOfModules.{u} R} (a : G ⟶ H) (U : C) :
    moduleLocalHom F G U →+ moduleLocalHom F H U where
  toFun φ := ⟨φ.val ≫ Functor.whiskerLeft (Over.forget U).op
    ((PresheafOfModules.toPresheaf R).map a), by
      intro V r x
      change a.app (op V.left) (φ.val.app (op V) (r • x)) =
        r • a.app (op V.left) (φ.val.app (op V) x)
      rw [φ.property, (a.app (op V.left)).hom.map_smul]⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' φ ψ := by
    apply Subtype.ext
    change (φ.val + ψ.val) ≫ _ = φ.val ≫ _ + ψ.val ≫ _
    exact Preadditive.add_comp _ _ _ φ.val ψ.val
      (Functor.whiskerLeft (Over.forget U).op ((PresheafOfModules.toPresheaf R).map a))

/-- The actual coefficient map on the presheaf of local linear morphisms. -/
def moduleHomPresheafAbMap (F : PresheafOfModules.{u} R)
    {G H : PresheafOfModules.{u} R} (a : G ⟶ H) :
    moduleHomPresheafAb F G ⟶ moduleHomPresheafAb F H where
  app U := AddCommGrpCat.ofHom (moduleLocalHomPostcomp F a U.unop)
  naturality {U V} i := by ext φ; rfl

/-- Original precomposition of local module-linear maps. -/
def moduleLocalHomPrecomp {E F : PresheafOfModules.{u} R} (a : E ⟶ F)
    (G : PresheafOfModules.{u} R) (U : C) :
    moduleLocalHom F G U →+ moduleLocalHom E G U where
  toFun φ := ⟨Functor.whiskerLeft (Over.forget U).op
    ((PresheafOfModules.toPresheaf R).map a) ≫ φ.val, by
      intro V r x
      change φ.val.app (op V) (a.app (op V.left) (r • x)) = _
      rw [(a.app (op V.left)).hom.map_smul]
      exact φ.property V r (a.app (op V.left) x)⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' φ ψ := by
    apply Subtype.ext
    exact Preadditive.comp_add _ _ _
      (Functor.whiskerLeft (Over.forget U).op ((PresheafOfModules.toPresheaf R).map a))
      φ.val ψ.val

/-- Precomposition respects all restrictions of local linear morphisms. -/
def moduleHomPresheafAbPrecomp {E F : PresheafOfModules.{u} R} (a : E ⟶ F)
    (G : PresheafOfModules.{u} R) : moduleHomPresheafAb F G ⟶ moduleHomPresheafAb E G where
  app U := AddCommGrpCat.ofHom (moduleLocalHomPrecomp a G U.unop)
  naturality {U V} i := by ext φ; rfl

variable (J : GrothendieckTopology C)
variable {S : Sheaf J RingCat.{u}}

/-- The actual first-variable morphism of the local linear Hom sheaf. -/
def moduleSheafHomAbPrecomp {E F : SheafOfModules.{u} S} (a : E ⟶ F)
    (G : SheafOfModules.{u} S) : moduleSheafHomAb J F G ⟶ moduleSheafHomAb J E G :=
  ⟨moduleHomPresheafAbPrecomp a.val G.val⟩

/-- The local linear Hom sheaf, functorial in the actual coefficient module sheaf. -/
def moduleSheafHomAbFunctor (F : SheafOfModules.{u} S) :
    SheafOfModules.{u} S ⥤ Sheaf J AddCommGrpCat.{u} where
  obj G := moduleSheafHomAb J F G
  map a := ⟨moduleHomPresheafAbMap F.val a.val⟩
  map_id G := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    apply Subtype.ext
    change φ.val ≫ Functor.whiskerLeft (Over.forget U.unop).op
      ((PresheafOfModules.toPresheaf S.obj).map (𝟙 G.val)) = φ.val
    change φ.val ≫ 𝟙 _ = φ.val
    exact Category.comp_id _
  map_comp a b := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    apply Subtype.ext
    change φ.val ≫ Functor.whiskerLeft (Over.forget U.unop).op
        ((PresheafOfModules.toPresheaf S.obj).map (a.val ≫ b.val)) =
      (φ.val ≫ Functor.whiskerLeft (Over.forget U.unop).op
        ((PresheafOfModules.toPresheaf S.obj).map a.val)) ≫
          Functor.whiskerLeft (Over.forget U.unop).op
            ((PresheafOfModules.toPresheaf S.obj).map b.val)
    simp [Category.assoc]

instance (F : SheafOfModules.{u} S) : (moduleSheafHomAbFunctor J F).Additive where
  map_add := by
    intro G H a b
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext x
    rfl

/-- Sections are Hom from the actual restriction of the source module presheaf. -/
def moduleLocalMorphismFunctor (F : SheafOfModules.{u} S) (U : C) :
    SheafOfModules.{u} S ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.forget S ⋙ PresheafOfModules.pushforward₀ (Over.forget U) S.obj ⋙
    preadditiveCoyoneda.obj
      (op ((PresheafOfModules.pushforward₀ (Over.forget U) S.obj).obj F.val))

/-- The local-linear Hom identification retains coefficient postcomposition. -/
def moduleSheafHomAbSectionsFunctorIso (F : SheafOfModules.{u} S) (U : C) :
    moduleSheafHomAbFunctor J F ⋙ sheafToPresheaf J AddCommGrpCat ⋙
        (evaluation Cᵒᵖ AddCommGrpCat).obj (op U) ≅ moduleLocalMorphismFunctor J F U :=
  NatIso.ofComponents (fun G ↦ (moduleLocalHomOverEquiv F.val G.val U).toAddCommGrpIso)
    (fun a ↦ by ext φ; rfl)

section Reindex

variable {D : Type u} [SmallCategory D] (K : C ⥤ D) (T : Dᵒᵖ ⥤ RingCat.{u})

/-- Reindexing module presheaves preserves finite limits, pointwise. -/
instance presheafModuleReindex_preservesFiniteLimits :
    PreservesFiniteLimits (PresheafOfModules.pushforward₀.{u} K T) where
  preservesFiniteLimits A :=
    { preservesLimit := fun {L} ↦ by
        apply preservesLimit_of_preserves_limit_cone (limit.isLimit L)
        apply PresheafOfModules.evaluationJointlyReflectsLimits
        intro U
        exact isLimitOfPreserves (PresheafOfModules.evaluation T (K.op.obj U))
          (limit.isLimit L) }

end Reindex

/-- The sheaf of local module-linear maps is left exact in its coefficient module sheaf. -/
instance moduleSheafHomAbFunctor_preservesFiniteLimits (F : SheafOfModules.{u} S) :
    PreservesFiniteLimits (moduleSheafHomAbFunctor J F) := by
  let P := sheafToPresheaf J AddCommGrpCat.{u}
  have : PreservesFiniteLimits (moduleSheafHomAbFunctor J F ⋙ P) :=
    preservesFiniteLimits_of_evaluation _ (fun U ↦ by
      have : PreservesFiniteLimits (moduleLocalMorphismFunctor J F U.unop) := by
        dsimp [moduleLocalMorphismFunctor]
        infer_instance
      exact preservesFiniteLimits_of_natIso (moduleSheafHomAbSectionsFunctorIso J F U.unop).symm)
  exact preservesFiniteLimits_of_reflects_of_preserves (moduleSheafHomAbFunctor J F) P

end SGA.SGA2.ExposeVI
