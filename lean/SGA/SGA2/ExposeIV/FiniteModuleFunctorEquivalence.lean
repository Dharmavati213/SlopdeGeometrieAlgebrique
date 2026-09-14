/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.FiniteModuleRepresentation

/-!
# Modules and left-exact functors on finite modules

The categorical equivalence following IV.1.1. Restricted Hom is fully
faithful, and IV.1.1 supplies essential surjectivity over a noetherian ring.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Restricted additive Yoneda, allowing arbitrary target modules. -/
abbrev finiteModuleRepresentations : ModuleCat.{u} R ⥤
    ((FGModuleCat.{u} R)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  preadditiveYoneda ⋙
    (whiskeringLeft (FGModuleCat R)ᵒᵖ (ModuleCat R)ᵒᵖ AddCommGrpCat).obj
      (forget₂ (FGModuleCat R) (ModuleCat R)).op

private def modulePoint (H : ModuleCat.{u} R) (x : H) : ModuleCat.of R R ⟶ H :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R H x)

private theorem modulePoint_comp (M : FGModuleCat.{u} R) {H : ModuleCat.{u} R}
    (g : M.obj ⟶ H) (x : M) :
    (finiteModulePoint M x).hom ≫ g = modulePoint H (g x) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact g.hom.map_smul r x

variable {H K : ModuleCat.{u} R}

/-- A natural transformation between restricted Hom functors is determined
by its component at the ring and evaluation at one. -/
theorem finiteModuleRepresentations_naturality_point
    (α : (finiteModuleRepresentations (R := R)).obj H ⟶
      (finiteModuleRepresentations (R := R)).obj K)
    (M : FGModuleCat.{u} R) (g : M.obj ⟶ H) (x : M) :
    ModuleCat.Hom.hom (α.app (op M) g) x =
      ModuleCat.Hom.hom (α.app (op (FGModuleCat.of R R)) (modulePoint H (g x))) (1 : R) := by
  have h := ConcreteCategory.congr_hom (α.naturality (finiteModulePoint M x).op) g
  have h' := congrArg (fun f : ModuleCat.of R R ⟶ K ↦ f 1) h
  change ModuleCat.Hom.hom
      (α.app (op (FGModuleCat.of R R)) ((finiteModulePoint M x).hom ≫ g)) (1 : R) =
    ((finiteModulePoint M x).hom ≫ α.app (op M) g) 1 at h'
  rw [modulePoint_comp] at h'
  change ModuleCat.Hom.hom (α.app (op (FGModuleCat.of R R)) (modulePoint H (g x))) (1 : R) =
    ModuleCat.Hom.hom (α.app (op M) g) ((1 : R) • x) at h'
  simpa only [one_smul] using h'.symm

/-- Recover a genuine linear map from a natural transformation between
restricted Hom functors; linearity follows from naturality, not an extra assumption. -/
def finiteModuleRepresentationsPreimage
    (α : (finiteModuleRepresentations (R := R)).obj H ⟶
      (finiteModuleRepresentations (R := R)).obj K) : H ⟶ K :=
  ModuleCat.ofHom
    { toFun x := ModuleCat.Hom.hom (α.app (op (FGModuleCat.of R R)) (modulePoint H x)) (1 : R)
      map_add' x y := by
        have h : modulePoint H (x + y) = modulePoint H x + modulePoint H y := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro r
          exact smul_add r x y
        rw [h, _root_.map_add]
        rfl
      map_smul' r x := by
        have h := finiteModuleRepresentations_naturality_point α (FGModuleCat.of R R)
          (modulePoint H x) r
        change ModuleCat.Hom.hom (α.app (op (FGModuleCat.of R R)) (modulePoint H x)) r =
          ModuleCat.Hom.hom (α.app (op (FGModuleCat.of R R)) (modulePoint H (r • x))) (1 : R) at h
        rw [← h]
        simpa only [smul_eq_mul, mul_one, RingHom.id_apply] using
          (ModuleCat.Hom.hom (α.app (op (FGModuleCat.of R R))
            (modulePoint H x))).map_smul r (1 : R) }

@[simp] theorem finiteModuleRepresentations_map_preimage
    (α : (finiteModuleRepresentations (R := R)).obj H ⟶
      (finiteModuleRepresentations (R := R)).obj K) :
    (finiteModuleRepresentations (R := R)).map (finiteModuleRepresentationsPreimage α) = α := by
  apply NatTrans.ext
  funext M
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro g
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (finiteModuleRepresentations_naturality_point α M.unop g x).symm

@[simp] theorem finiteModuleRepresentations_preimage_map (f : H ⟶ K) :
    finiteModuleRepresentationsPreimage ((finiteModuleRepresentations (R := R)).map f) = f := by
  ext x
  exact congrArg f.hom (one_smul R x)

/-- Restricted Hom is fully faithful even before imposing noetherianity. -/
def finiteModuleRepresentationsFullyFaithful :
    (finiteModuleRepresentations (R := R)).FullyFaithful where
  preimage := finiteModuleRepresentationsPreimage
  map_preimage := finiteModuleRepresentations_map_preimage
  preimage_map := finiteModuleRepresentations_preimage_map

/-- The actual full subcategory of additive left-exact functors. -/
def leftExactFiniteModuleFunctorProperty :
    ObjectProperty ((FGModuleCat.{u} R)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  fun T ↦ T.Additive ∧ PreservesFiniteLimits T

abbrev LeftExactFiniteModuleFunctor (R : Type u) [CommRing R] :=
  (leftExactFiniteModuleFunctorProperty (R := R)).FullSubcategory

/-- The restricted Hom functor takes values in additive left-exact functors. -/
def moduleToLeftExactFiniteFunctor : ModuleCat.{u} R ⥤ LeftExactFiniteModuleFunctor R :=
  (leftExactFiniteModuleFunctorProperty (R := R)).lift finiteModuleRepresentations (fun H ↦ by
    change (finiteModuleHomFunctor H ⋙ forget₂ (ModuleCat R) AddCommGrpCat).Additive ∧
      PreservesFiniteLimits (finiteModuleHomFunctor H ⋙ forget₂ (ModuleCat R) AddCommGrpCat)
    exact ⟨inferInstance, comp_preservesFiniteLimits _ _⟩)

/-- Full faithfulness of the same restricted Hom functor with its
left-exact codomain recorded. -/
def moduleToLeftExactFiniteFunctorFullyFaithful :
    (moduleToLeftExactFiniteFunctor (R := R)).FullyFaithful where
  preimage α := finiteModuleRepresentationsPreimage α.hom
  map_preimage α := ObjectProperty.hom_ext _ (finiteModuleRepresentations_map_preimage α.hom)
  preimage_map f := finiteModuleRepresentations_preimage_map f

instance : (moduleToLeftExactFiniteFunctor (R := R)).Full :=
  moduleToLeftExactFiniteFunctorFullyFaithful.full

instance : (moduleToLeftExactFiniteFunctor (R := R)).Faithful :=
  moduleToLeftExactFiniteFunctorFullyFaithful.faithful

instance [IsNoetherianRing R] : (moduleToLeftExactFiniteFunctor (R := R)).EssSurj where
  mem_essImage T := by
    have : T.obj.Additive := T.property.1
    have : PreservesFiniteLimits T.obj := T.property.2
    refine ⟨(additiveFunctorModuleLift (R := R) T.obj).obj (op (FGModuleCat.of R R)), ?_⟩
    exact ⟨ObjectProperty.isoMk _ (additiveFiniteModuleRepresentationIso T.obj).symm⟩

instance [IsNoetherianRing R] : (moduleToLeftExactFiniteFunctor (R := R)).IsEquivalence where

/-- The equivalence following IV.1.1: arbitrary modules correspond to
additive left-exact contravariant functors on finite modules. Its forward
functor is the actual restricted Hom functor. -/
def finiteModuleFunctorEquivalence [IsNoetherianRing R] :
    ModuleCat.{u} R ≌ LeftExactFiniteModuleFunctor R :=
  (moduleToLeftExactFiniteFunctor (R := R)).asEquivalence

@[simp] theorem finiteModuleFunctorEquivalence_functor [IsNoetherianRing R] :
    (finiteModuleFunctorEquivalence (R := R)).functor = moduleToLeftExactFiniteFunctor := rfl

end SGA.SGA2.ExposeIV
