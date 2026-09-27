/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Topology.CoveringOfFunctor
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Action.Concrete

/-!
# Classification of finite coverings

Let `X` be a topological space. `TopCat.FiniteCovering X` is the category of finite covering
spaces of `X`: covering maps `E → X` with finite fibres, and continuous maps over `X`.

* `FiniteCovering.fiber x` is the fibre functor at `x : X`;
* `FiniteCovering.monodromy X` sends a finite covering to its monodromy functor
  `FundamentalGroupoid X ⥤ FintypeCat` (the fibres, with the lifting of paths), and
  `FiniteCovering.monodromyAction x` sends it to its fibre at `x` with the monodromy action of
  `π₁(X, x)`.

For `X` locally path-connected and semilocally simply connected:

* `FiniteCovering.equivalence X`: `monodromy X` is an equivalence of categories, with inverse
  the total space construction `FundamentalGroupoid.TotalSpace`;
* `FiniteCovering.equivalenceAction x`: if moreover `X` is path-connected, `monodromyAction x`
  is an equivalence between finite coverings of `X` and finite `π₁(X, x)`-sets, compatible with
  the fibre functor at `x` (`FiniteCovering.monodromyActionCompForgetIso`).

## References

* [A. Hatcher, *Algebraic Topology*, §1.3][hatcher02]
-/

noncomputable section

open CategoryTheory Topology Set FundamentalGroupoid

universe u

namespace FundamentalGroupoid

variable {X : Type u} [TopologicalSpace X] (x : X)

/-- The inclusion of the fundamental group `π₁(X, x)`, as a one-object category, into the
fundamental groupoid. -/
def singleObjFunctor : SingleObj (FundamentalGroup X x) ⥤ FundamentalGroupoid X :=
  SingleObj.functor (MonoidHom.id _)

instance : (singleObjFunctor x).Full where
  map_surjective {_ _} f := ⟨f, rfl⟩

instance : (singleObjFunctor x).Faithful where
  map_injective h := h

instance [PathConnectedSpace X] : (singleObjFunctor x).EssSurj where
  mem_essImage y :=
    ⟨SingleObj.star _, ⟨(Groupoid.isoEquivHom _ _).symm
      (fromPath (.mk (PathConnectedSpace.somePath x y.as)))⟩⟩

instance [PathConnectedSpace X] : (singleObjFunctor x).IsEquivalence where

end FundamentalGroupoid

namespace TopCat

/-- The category of finite covering spaces of a topological space `X`: covering maps `E → X`
with finite fibres, and continuous maps over `X`. -/
abbrev FiniteCovering (X : TopCat.{u}) : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun E : Over X ↦
    IsCoveringMap E.hom ∧ ∀ x, (E.hom ⁻¹' {x}).Finite

namespace FiniteCovering

variable {X : TopCat.{u}}

/-- The fibre functor of finite coverings at a point `x`. -/
def fiber (x : X) : FiniteCovering X ⥤ FintypeCat.{u} where
  obj E := have := (E.property.2 x).to_subtype; FintypeCat.of (E.obj.hom ⁻¹' {x})
  map {E F} f := FintypeCat.homMk fun e ↦ ⟨f.hom.left e.1, by
    have h₁ := congr($(Over.w f.hom) e.1)
    have h₂ : E.obj.hom e.1 = x := e.2
    simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at h₁
    simp only [mem_preimage, mem_singleton_iff]
    rw [h₁, h₂]⟩

/-- The covering map of a finite covering. -/
lemma isCoveringMap (E : FiniteCovering X) : IsCoveringMap E.obj.hom :=
  E.property.1

lemma hom_left_apply {E F : FiniteCovering X} (f : E ⟶ F) (e : E.obj.left) :
    F.obj.hom (f.hom.left e) = E.obj.hom e :=
  congr($(Over.w f.hom) e)

/-! ### The monodromy functor -/

/-- The monodromy functor of a finite covering: its fibres, as a functor on the fundamental
groupoid, with the monodromy (lifting of paths) as action on morphisms. -/
def monodromyFunctor (E : FiniteCovering X) : FundamentalGroupoid X ⥤ FintypeCat.{u} :=
  ObjectProperty.lift _ E.isCoveringMap.monodromyFunctor fun y ↦ (E.property.2 y.as).to_subtype

variable (X) in
/-- The monodromy functor, from finite coverings of `X` to functors from the fundamental
groupoid of `X` to finite sets. -/
def monodromy : FiniteCovering X ⥤ (FundamentalGroupoid X ⥤ FintypeCat.{u}) where
  obj E := monodromyFunctor E
  map {E F} f :=
    { app y := FintypeCat.homMk fun e ↦ ⟨f.hom.left e.1, (hom_left_apply f e.1).trans e.2⟩
      naturality {y z} γ := by
        ext e
        exact Subtype.ext (E.isCoveringMap.apply_monodromy F.isCoveringMap f.hom.left.hom
          (hom_left_apply f) γ e) }

variable (x : X)

/-- The monodromy action of `π₁(X, x)` on the fibres at `x` of finite coverings. -/
def monodromyAction : FiniteCovering X ⥤ Action FintypeCat.{u} (FundamentalGroup X x) :=
  monodromy X ⋙ (Functor.whiskeringLeft _ _ _).obj (singleObjFunctor x) ⋙
    Action.FunctorCategoryEquivalence.inverse

/-- The monodromy action at `x`, followed by the forgetful functor, is the fibre functor
at `x`. -/
def monodromyActionCompForgetIso :
    monodromyAction x ⋙ Action.forget FintypeCat.{u} (FundamentalGroup X x) ≅ fiber x :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

@[simp]
lemma monodromyAction_obj_V (E : FiniteCovering X) :
    ((monodromyAction x).obj E).V = (fiber x).obj E :=
  rfl

/-- A loop `γ` at `x` acts on the fibre at `x` by monodromy: `γ • e` is the endpoint of the lift
of `γ` starting at `e`. -/
lemma monodromyAction_smul (E : FiniteCovering X) (γ : FundamentalGroup X x)
    (e : ((monodromyAction x).obj E).V) :
    γ • e = E.isCoveringMap.monodromy γ e :=
  rfl

/-! ### The covering associated with a functor on the fundamental groupoid -/

section Classification

variable [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]

/-- The finite covering associated with a functor from the fundamental groupoid to finite sets:
its total space `FundamentalGroupoid.TotalSpace`. -/
def ofFunctor (L : FundamentalGroupoid X ⥤ FintypeCat.{u}) : FiniteCovering X :=
  ⟨Over.mk (Y := TopCat.of (TotalSpace (L ⋙ FintypeCat.incl)))
    (TopCat.ofHom ⟨TotalSpace.proj, TotalSpace.continuous_proj⟩),
    TotalSpace.isCoveringMap_proj _, fun y ↦ by
      have : Finite ((L ⋙ FintypeCat.incl).obj ⟨y⟩) := (L.obj ⟨y⟩).property
      exact Set.finite_coe_iff.mp
        (Finite.of_equiv _ (TotalSpace.fiberEquiv (L ⋙ FintypeCat.incl) y))⟩

variable (X) in
/-- The covering associated with a functor on the fundamental groupoid, as a functor. -/
def ofFunctorFunctor : (FundamentalGroupoid X ⥤ FintypeCat.{u}) ⥤ FiniteCovering X where
  obj := ofFunctor
  map α := ObjectProperty.homMk (Over.homMk (TopCat.ofHom
    ⟨TotalSpace.map (Functor.whiskerRight α FintypeCat.incl), TotalSpace.continuous_map _⟩) rfl)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A finite covering is isomorphic to the covering associated with its monodromy functor. -/
def isoOfFunctorMonodromy (E : FiniteCovering X) : E ≅ ofFunctor ((monodromy X).obj E) :=
  ObjectProperty.isoMk _
    (Over.isoMk (TopCat.isoOfHomeo E.isCoveringMap.homeomorphTotalSpace) rfl)

/-- The monodromy functor of the covering associated with `L` is `L`. -/
def monodromyOfFunctorIso (L : FundamentalGroupoid X ⥤ FintypeCat.{u}) :
    (monodromy X).obj (ofFunctor L) ≅ L :=
  NatIso.ofComponents
    (fun y ↦ FintypeCat.equivEquivIso (TotalSpace.fiberEquiv (L ⋙ FintypeCat.incl) y.as).symm)
    fun {y z} γ ↦ by
      obtain ⟨y⟩ := y
      obtain ⟨z⟩ := z
      obtain ⟨γ⟩ := γ
      ext e
      obtain ⟨s, rfl⟩ := (TotalSpace.fiberEquiv (L ⋙ FintypeCat.incl) y).surjective e
      change (TotalSpace.fiberEquiv (L ⋙ FintypeCat.incl) z).symm
        ((TotalSpace.isCoveringMap_proj _).monodromy (.mk γ)
          (TotalSpace.fiberEquiv (L ⋙ FintypeCat.incl) y s)) = _
      rw [TotalSpace.monodromy_mk, Equiv.symm_apply_apply]
      rfl

variable (X) in
/-- For `X` locally path-connected and semilocally simply connected, the monodromy functor is an
equivalence between finite coverings of `X` and functors from the fundamental groupoid of `X`
to finite sets. -/
def equivalence : FiniteCovering X ≌ (FundamentalGroupoid X ⥤ FintypeCat.{u}) :=
  CategoryTheory.Equivalence.mk (monodromy X) (ofFunctorFunctor X)
    (NatIso.ofComponents isoOfFunctorMonodromy fun {E F} f ↦ by
      ext e
      exact F.isCoveringMap.homeomorphTotalSpace.symm.injective rfl)
    (NatIso.ofComponents monodromyOfFunctorIso fun α ↦ by
      ext ⟨y⟩ ⟨⟨y', s⟩, h⟩
      obtain rfl : y' = y := h
      rfl)

@[simp]
lemma equivalence_functor : (equivalence X).functor = monodromy X :=
  rfl

instance : (monodromy X).IsEquivalence :=
  (equivalence X).isEquivalence_functor

/-- For `X` path-connected, locally path-connected and semilocally simply connected, the
monodromy action at `x` is an equivalence between finite coverings of `X` and finite
`π₁(X, x)`-sets, compatible with the fibre functor at `x`
(`monodromyActionCompForgetIso`). -/
def equivalenceAction [PathConnectedSpace X] :
    FiniteCovering X ≌ Action FintypeCat.{u} (FundamentalGroup X x) :=
  (equivalence X).trans ((singleObjFunctor x).asEquivalence.congrLeft.symm.trans
    (Action.functorCategoryEquivalence _ _).symm)

@[simp]
lemma equivalenceAction_functor [PathConnectedSpace X] :
    (equivalenceAction x).functor = monodromyAction x :=
  rfl

instance [PathConnectedSpace X] : (monodromyAction x).IsEquivalence :=
  (equivalenceAction x).isEquivalence_functor

end Classification

end FiniteCovering

end TopCat
