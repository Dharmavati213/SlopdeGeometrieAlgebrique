/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleInternalHomFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# The module-valued internal Hom over a commutative ring sheaf

The scalar action on a local linear map is multiplication by the restriction
of the scalar on each smaller open. This equips the actual local-linear Hom
sheaf with its structure of a module sheaf.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

local instance (G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat)) (U : C)
    (V : (Over U)ᵒᵖ) :
    Module (R.obj (op V.unop.left)) (((Over.forget U).op ⋙ G.presheaf).obj V) :=
  inferInstanceAs (Module (R.obj (op V.unop.left)) (G.obj (op V.unop.left)))

local instance (G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat)) (U : C)
    (V : Over U) :
    Module (R.obj (op V.left)) (((Over.forget U).op ⋙ G.presheaf).obj (op V)) :=
  inferInstanceAs (Module (R.obj (op V.left)) (G.obj (op V.left)))

/-- Multiplication of a local linear map by a local scalar. -/
def moduleLocalHomSMul (F G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat))
    (U : C) (r : R.obj (op U)) (φ : moduleLocalHom F G U) : moduleLocalHom F G U :=
  ⟨
    { app V := AddCommGrpCat.ofHom
        { toFun x := R.map V.unop.hom.op r • (φ.val.app V x : G.obj (op V.unop.left))
          map_zero' := by rw [map_zero, smul_zero]
          map_add' x y := by rw [map_add, smul_add] }
      naturality {V W} i := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        change R.map W.unop.hom.op r • φ.val.app W (F.map i.unop.left.op x) =
          G.map i.unop.left.op (R.map V.unop.hom.op r • φ.val.app V x)
        rw [G.map_smul]
        have h := NatTrans.naturality_apply φ.val i x
        change φ.val.app W (F.map i.unop.left.op x) = G.map i.unop.left.op (φ.val.app V x) at h
        rw [h]
        congr 1
        change R.map W.unop.hom.op r = R.map i.unop.left.op (R.map V.unop.hom.op r)
        rw [← ConcreteCategory.comp_apply, ← R.map_comp, ← op_comp, Over.w i.unop] },
    by
      intro V s x
      let : Module ((R ⋙ forget₂ _ RingCat).obj (op V.left))
          (((Over.forget U).op ⋙ G.presheaf).obj (op V)) :=
        inferInstanceAs (Module ((R ⋙ forget₂ _ RingCat).obj (op V.left)) (G.obj (op V.left)))
      change R.map V.hom.op r • (φ.val.app (op V) (s • x) : G.obj (op V.left)) =
        s • (R.map V.hom.op r • (φ.val.app (op V) x : G.obj (op V.left)))
      rw [φ.property]
      exact smul_comm (R.map V.hom.op r) (show R.obj (op V.left) from s)
        (show G.obj (op V.left) from φ.val.app (op V) x)⟩

instance moduleLocalHomModule (F G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat))
    (U : C) : Module (R.obj (op U)) (moduleLocalHom F G U) where
  smul := moduleLocalHomSMul F G U
  one_smul φ := by
    apply moduleLocalHom_ext
    intro V x
    change R.map V.hom.op 1 • φ.val.app (op V) x = φ.val.app (op V) x
    simp
  mul_smul r s φ := by
    apply moduleLocalHom_ext
    intro V x
    change R.map V.hom.op (r * s) • φ.val.app (op V) x =
      R.map V.hom.op r • (R.map V.hom.op s • φ.val.app (op V) x)
    simp [mul_smul]
  smul_zero r := by
    apply moduleLocalHom_ext
    intro V x
    exact smul_zero _
  smul_add r φ ψ := by
    apply moduleLocalHom_ext
    intro V x
    exact smul_add _ _ _
  add_smul r s φ := by
    apply moduleLocalHom_ext
    intro V x
    change R.map V.hom.op (r + s) • φ.val.app (op V) x = _
    rw [map_add, add_smul]
    rfl
  zero_smul φ := by
    apply moduleLocalHom_ext
    intro V x
    change R.map V.hom.op 0 • φ.val.app (op V) x = 0
    simp

@[simp]
theorem moduleLocalHom_smul_app (F G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat))
    (U : C) (r : R.obj (op U)) (φ : moduleLocalHom F G U) (V : Over U)
    (x : F.obj (op V.left)) :
    (r • φ).val.app (op V) x = R.map V.hom.op r • φ.val.app (op V) x := rfl

/-- Restrictions of local Hom are semilinear in the local structure rings. -/
theorem moduleLocalHomRestrict_smul
    (F G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat)) {U V : C} (i : V ⟶ U)
    (r : R.obj (op U)) (φ : moduleLocalHom F G U) :
    moduleLocalHomRestrict F G i (r • φ) =
      R.map i.op r • moduleLocalHomRestrict F G i φ := by
  apply moduleLocalHom_ext
  intro W x
  let : Module (R.obj (op W.left))
      (((Over.forget U).op ⋙ G.presheaf).obj (op ((Over.map i).obj W))) :=
    inferInstanceAs (Module (R.obj (op W.left)) (G.obj (op W.left)))
  change R.map (W.hom ≫ i).op r •
      (φ.val.app (op ((Over.map i).obj W)) x : G.obj (op W.left)) =
    R.map W.hom.op (R.map i.op r) •
      (φ.val.app (op ((Over.map i).obj W)) x : G.obj (op W.left))
  rw [op_comp, R.map_comp]
  rfl

/-- The presheaf of local linear morphisms, with its actual local module structures. -/
def moduleHomPresheaf (F G : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat)) :
    PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat) := by
  let (U : Cᵒᵖ) : Module ((R ⋙ forget₂ _ RingCat).obj U)
      ((moduleHomPresheafAb F G).obj U) :=
    moduleLocalHomModule (R := R) F G U.unop
  exact PresheafOfModules.ofPresheaf (moduleHomPresheafAb F G)
    (fun {U V} i r φ ↦ moduleLocalHomRestrict_smul F G i.unop r φ)

variable (J : GrothendieckTopology C)

/-- The structure ring sheaf with its commutativity forgotten. -/
abbrev commRingSheafToRing (S : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj S

variable {S : Sheaf J CommRingCat.{u}}

/-- The genuine internal Hom module sheaf. -/
def moduleSheafHom (F G : SheafOfModules.{u} (commRingSheafToRing J S)) :
    SheafOfModules.{u} (commRingSheafToRing J S) where
  val := moduleHomPresheaf F.val G.val
  isSheaf := (moduleSheafHomAb J F G).property

/-- Forgetting scalars recovers exactly the existing sheaf of local linear maps. -/
def moduleSheafHomForgetIso (F G : SheafOfModules.{u} (commRingSheafToRing J S)) :
    (SheafOfModules.toSheaf _).obj (moduleSheafHom J F G) ≅ moduleSheafHomAb J F G :=
  Iso.refl _

/-- The coefficient map of internal Hom is ordinary local postcomposition. -/
def moduleSheafHomMap (F : SheafOfModules.{u} (commRingSheafToRing J S))
    {G H : SheafOfModules.{u} (commRingSheafToRing J S)} (a : G ⟶ H) :
    moduleSheafHom J F G ⟶ moduleSheafHom J F H :=
  ⟨PresheafOfModules.homMk (moduleHomPresheafAbMap F.val a.val) (by
    intro U r φ
    apply moduleLocalHom_ext
    intro V x
    exact (a.val.app (op V.left)).hom.map_smul (S.obj.map V.hom.op r) _)⟩

/-- The contravariant map of module-valued internal Hom is actual local precomposition. -/
def moduleSheafHomPrecomp
    {E F : SheafOfModules.{u} (commRingSheafToRing J S)} (a : E ⟶ F)
    (G : SheafOfModules.{u} (commRingSheafToRing J S)) :
    moduleSheafHom J F G ⟶ moduleSheafHom J E G :=
  ⟨PresheafOfModules.homMk (moduleHomPresheafAbPrecomp a.val G.val) (by
    intro U r φ
    apply moduleLocalHom_ext
    intro V x
    rfl)⟩

/-- The module-valued internal Hom coefficient functor. -/
def moduleSheafHomFunctor (F : SheafOfModules.{u} (commRingSheafToRing J S)) :
    SheafOfModules.{u} (commRingSheafToRing J S) ⥤
      SheafOfModules.{u} (commRingSheafToRing J S) where
  obj G := moduleSheafHom J F G
  map a := moduleSheafHomMap J F a
  map_id _ := by ext U φ; rfl
  map_comp _ _ := by ext U φ; rfl

instance (F : SheafOfModules.{u} (commRingSheafToRing J S)) :
    (moduleSheafHomFunctor J F).Additive where
  map_add := by intros; ext U φ; rfl

/-- The scalar-valued coefficient functor lies over the original additive one. -/
def moduleSheafHomFunctorForgetIso (F : SheafOfModules.{u} (commRingSheafToRing J S)) :
    moduleSheafHomFunctor J F ⋙ SheafOfModules.toSheaf _ ≅ moduleSheafHomAbFunctor J F :=
  NatIso.ofComponents (fun G ↦ moduleSheafHomForgetIso J F G) (by intros; rfl)

end SGA.SGA2.ExposeVI
