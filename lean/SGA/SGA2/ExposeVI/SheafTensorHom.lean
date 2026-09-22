/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleInternalHomLinear
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Tensor products and the actual internal Hom of module sheaves

The tensor product is the sheafification of the sectionwise module tensor
product. Its tensor-Hom comparison is proved by local currying and the
universal property of sheafification.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Evaluation at the identity after restricting a local map. -/
theorem moduleLocalHomRestrict_eval
    {F G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat)}
    {U V : C} (i : V ⟶ U) (φ : moduleLocalHom F G U) (x : F.obj (op V)) :
    (moduleLocalHomRestrict F G i φ).val.app (op (Over.mk (𝟙 V))) x =
      φ.val.app (op (Over.mk i)) x := by
  change ((presheafHom F.presheaf G.presheaf).map i.op φ.val).app
    (op (Over.mk (𝟙 V))) x = _
  erw [presheafHom_map_app_op_mk_id]
  rfl

/-- Currying a sectionwise tensor morphism gives an actual local linear map. -/
def presheafTensorCurryLocal
    {M F G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat)}
    (φ : M ⊗ F ⟶ G) (U : C) (m : M.obj (op U)) : moduleLocalHom F G U :=
  ⟨
    { app V := AddCommGrpCat.ofHom
        { toFun x := φ.app (op V.unop.left)
            (M.map V.unop.hom.op m ⊗ₜ[R.obj (op V.unop.left)] x)
          map_zero' := by simp
          map_add' x y := by simp [TensorProduct.tmul_add] }
      naturality {V W} i := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        change φ.app (op W.unop.left)
            (M.map W.unop.hom.op m ⊗ₜ[R.obj (op W.unop.left)] F.map i.unop.left.op x) =
          G.map i.unop.left.op
            (φ.app (op V.unop.left)
              (M.map V.unop.hom.op m ⊗ₜ[R.obj (op V.unop.left)] x))
        rw [← PresheafOfModules.naturality_apply]
        erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
        congr 2
        rw [← M.map_comp_apply, ← op_comp, Over.w i.unop] },
    by
      intro V r x
      change R.obj (op V.left) at r
      change φ.app (op V.left) (M.map V.hom.op m ⊗ₜ[R.obj (op V.left)] (r • x)) =
        r • φ.app (op V.left) (M.map V.hom.op m ⊗ₜ[R.obj (op V.left)] x)
      rw [TensorProduct.tmul_smul, (φ.app (op V.left)).hom.map_smul]⟩

/-- Currying is linear and compatible with restriction of the source section. -/
def presheafTensorCurry
    {M F G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat)}
    (φ : M ⊗ F ⟶ G) : M ⟶ moduleHomPresheaf F G where
  app U := ModuleCat.ofHom (X := M.obj U) (Y := (moduleHomPresheaf F G).obj U)
    { toFun := presheafTensorCurryLocal φ U.unop
      map_add' m n := by
        apply moduleLocalHom_ext
        intro V x
        change φ.app (op V.left) (M.map V.hom.op (m + n) ⊗ₜ[R.obj (op V.left)] x) = _
        rw [map_add, TensorProduct.add_tmul, map_add]
        rfl
      map_smul' r m := by
        change R.obj U at r
        apply moduleLocalHom_ext
        intro V x
        change φ.app (op V.left) (M.map V.hom.op (r • m) ⊗ₜ[R.obj (op V.left)] x) =
          R.map V.hom.op r • φ.app (op V.left) (M.map V.hom.op m ⊗ₜ[R.obj (op V.left)] x)
        erw [M.map_smul]
        exact (congrArg (φ.app (op V.left))
          (TensorProduct.smul_tmul' (R := R.obj (op V.left))
            (R.map V.hom.op r) (show M.obj (op V.left) from M.map V.hom.op m) x).symm).trans
          ((φ.app (op V.left)).hom.map_smul (R.map V.hom.op r) _) }
  naturality {U V} i := by
    ext m
    apply moduleLocalHom_ext
    intro W x
    change φ.app (op W.left)
        (M.map W.hom.op (M.map i m) ⊗ₜ[R.obj (op W.left)] x) =
      φ.app (op W.left) (M.map (W.hom ≫ i.unop).op m ⊗ₜ[R.obj (op W.left)] x)
    rw [op_comp, M.map_comp_apply]
    rfl

/-- Pointwise bilinear evaluation of local Hom. -/
def presheafTensorUncurryApp
    {M F G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat)}
    (φ : M ⟶ moduleHomPresheaf F G) (U : Cᵒᵖ) : (M ⊗ F).obj U ⟶ G.obj U :=
  ModuleCat.MonoidalCategory.tensorLift (R := R.obj U)
    (fun m x ↦ (φ.app U m).val.app (op (Over.mk (𝟙 U.unop))) x)
    (by intros; rw [map_add]; rfl)
    (by
      intro r m x
      rw [(φ.app U).hom.map_smul]
      let y : G.obj U := (φ.app U m).val.app (op (Over.mk (𝟙 U.unop))) x
      change R.map (𝟙 U.unop).op r • y = r • y
      simp)
    (by intro m x y; exact map_add _ x y)
    (by intro r m x; exact (φ.app U m).property (Over.mk (𝟙 U.unop)) r x)

@[simp]
theorem presheafTensorUncurryApp_tmul
    {M F G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat)}
    (φ : M ⟶ moduleHomPresheaf F G) (U : Cᵒᵖ) (m : M.obj U) (x : F.obj U) :
    presheafTensorUncurryApp φ U (m ⊗ₜ[R.obj U] x) =
      (φ.app U m).val.app (op (Over.mk (𝟙 U.unop))) x := rfl

/-- Evaluation of local Hom yields the inverse tensor morphism. -/
def presheafTensorUncurry
    {M F G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat)}
    (φ : M ⟶ moduleHomPresheaf F G) : M ⊗ F ⟶ G where
  app := presheafTensorUncurryApp φ
  naturality {U V} i := ModuleCat.MonoidalCategory.tensor_ext (R := R.obj U) (fun m x ↦ by
    change presheafTensorUncurryApp φ V ((M ⊗ F).map i (m ⊗ₜ[R.obj U] x)) =
      G.map i (presheafTensorUncurryApp φ U (m ⊗ₜ[R.obj U] x))
    change presheafTensorUncurryApp φ V (M.map i m ⊗ₜ[R.obj V] F.map i x) =
      G.map i (presheafTensorUncurryApp φ U (m ⊗ₜ[R.obj U] x))
    rw [presheafTensorUncurryApp_tmul, presheafTensorUncurryApp_tmul]
    have h := PresheafOfModules.naturality_apply φ i m
    have he := congrArg (fun ψ : moduleLocalHom F G V.unop ↦
      ψ.val.app (op (Over.mk (𝟙 V.unop))) (F.map i x)) h
    change (φ.app V (M.map i m)).val.app (op (Over.mk (𝟙 V.unop))) (F.map i x) =
      (moduleLocalHomRestrict F G i.unop (φ.app U m)).val.app
        (op (Over.mk (𝟙 V.unop))) (F.map i x) at he
    rw [moduleLocalHomRestrict_eval] at he
    have hn := NatTrans.naturality_apply (φ.app U m).val
      (Over.homMk i.unop : Over.mk i.unop ⟶ Over.mk (𝟙 U.unop)).op x
    exact he.trans hn)

/-- The presheaf tensor-Hom adjunction, with its additive structure. -/
def presheafTensorHomEquiv (M F G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat)) :
    (M ⊗ F ⟶ G) ≃+ (M ⟶ moduleHomPresheaf F G) where
  toFun := presheafTensorCurry
  invFun := presheafTensorUncurry
  left_inv φ := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m x
    change φ.app U (M.map (𝟙 U.unop).op m ⊗ₜ[R.obj U] x) =
      φ.app U (m ⊗ₜ[R.obj U] x)
    rw [show M.map (𝟙 U.unop).op m = m from
      ConcreteCategory.congr_hom (M.presheaf.map_id U) m]
  right_inv φ := by
    ext U m
    apply moduleLocalHom_ext
    intro V x
    have h := congrArg (fun ψ : moduleLocalHom F G V.left ↦
      ψ.val.app (op (Over.mk (𝟙 V.left))) x)
      (PresheafOfModules.naturality_apply φ V.hom.op m)
    change (φ.app (op V.left) (M.map V.hom.op m)).val.app (op (Over.mk (𝟙 V.left))) x =
      (moduleLocalHomRestrict F G V.hom (φ.app U m)).val.app
        (op (Over.mk (𝟙 V.left))) x at h
    rw [moduleLocalHomRestrict_eval] at h
    exact h
  map_add' φ ψ := by ext U m; rfl

variable (J : GrothendieckTopology C) (S : Sheaf J CommRingCat.{u})

/-- The actual sheaf tensor product: sheafification of the pointwise module tensor product. -/
def moduleSheafTensor (M F : SheafOfModules.{u} (commRingSheafToRing J S)) :
    SheafOfModules.{u} (commRingSheafToRing J S) :=
  (PresheafOfModules.sheafification (𝟙 (commRingSheafToRing J S).obj)).obj
    (PresheafOfModules.Monoidal.tensorObj (R := S.obj) M.val F.val)

/-- The actual tensor of two morphisms, followed by module sheafification. -/
def moduleSheafTensorMap
    {M N E F : SheafOfModules.{u} (commRingSheafToRing J S)} (a : M ⟶ N) (b : E ⟶ F) :
    moduleSheafTensor J S M E ⟶ moduleSheafTensor J S N F :=
  (PresheafOfModules.sheafification (𝟙 (commRingSheafToRing J S).obj)).map
    (PresheafOfModules.Monoidal.tensorHom (R := S.obj) a.val b.val)

instance moduleSheafification_additive :
    (PresheafOfModules.sheafification (𝟙 (commRingSheafToRing J S).obj)).Additive :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (commRingSheafToRing J S).obj)).left_adjoint_additive

/-- The tensor-Hom equivalence for the actual sheaf tensor and actual internal Hom. -/
def moduleSheafTensorHomEquiv
    (M F G : SheafOfModules.{u} (commRingSheafToRing J S)) :
    (moduleSheafTensor J S M F ⟶ G) ≃+ (M ⟶ moduleSheafHom J F G) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (commRingSheafToRing J S).obj)).homAddEquiv
    (PresheafOfModules.Monoidal.tensorObj (R := S.obj) M.val F.val) G).trans
      ((presheafTensorHomEquiv M.val F.val G.val).trans
        { toFun f := ⟨f⟩
          invFun f := f.val
          left_inv _ := rfl
          right_inv _ := rfl
          map_add' _ _ := rfl })

/-- Tensor-Hom currying commutes with actual coefficient postcomposition. -/
theorem moduleSheafTensorHomEquiv_naturality
    (M F : SheafOfModules.{u} (commRingSheafToRing J S))
    {G H : SheafOfModules.{u} (commRingSheafToRing J S)} (a : G ⟶ H)
    (φ : moduleSheafTensor J S M F ⟶ G) :
    moduleSheafTensorHomEquiv J S M F H (φ ≫ a) =
      moduleSheafTensorHomEquiv J S M F G φ ≫ moduleSheafHomMap J F a := by
  ext U m
  apply moduleLocalHom_ext
  intro V x
  rfl

/-- Tensor-Hom currying also respects actual precomposition in its second tensor factor. -/
theorem moduleSheafTensorHomEquiv_precomp
    (M : SheafOfModules.{u} (commRingSheafToRing J S))
    {E F : SheafOfModules.{u} (commRingSheafToRing J S)} (a : E ⟶ F)
    (G : SheafOfModules.{u} (commRingSheafToRing J S))
    (φ : moduleSheafTensor J S M F ⟶ G) :
    moduleSheafTensorHomEquiv J S M E G (moduleSheafTensorMap J S (𝟙 M) a ≫ φ) =
      moduleSheafTensorHomEquiv J S M F G φ ≫ moduleSheafHomPrecomp J a G := by
  apply SheafOfModules.hom_ext
  change presheafTensorCurry (R := S.obj) (M := M.val) (F := E.val) (G := G.val)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (commRingSheafToRing J S).obj)).homEquiv
        _ G ((PresheafOfModules.sheafification (𝟙 (commRingSheafToRing J S).obj)).map
          (PresheafOfModules.Monoidal.tensorHom (R := S.obj) (𝟙 M.val) a.val) ≫ φ)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext U m
  apply moduleLocalHom_ext
  intro V x
  rfl

end SGA.SGA2.ExposeVI
