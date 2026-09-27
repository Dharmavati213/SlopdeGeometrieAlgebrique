/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import SGA.Foundations.StrictLocalizationLift

/-!
# Stalks of étale sheaves at geometric points

Let `x̄ : Spec Ω ⟶ X` be a geometric point, `Ω` separably closed, and
`Φ = AlgebraicGeometry.Scheme.pointSmallEtale x̄` the corresponding point of the small étale
site. The stalk (fibre) of a presheaf `P` at `Φ` is by definition the filtered colimit of
`P(W)` over the étale neighbourhoods `(W, w)` of `x̄`, i.e. over the category of elements of the
fibre functor `W ↦ Hom_X(Spec Ω, W)` (`CategoryTheory.GrothendieckTopology.Point.presheafFiber`,
SGA 4 VIII 3.2).

* `CategoryTheory.GrothendieckTopology.Point.presheafFiberYonedaIso`: the fibre of a
  representable presheaf `yoneda W` at a point `Φ` of any site is `Φ.fiber W`.
* `AlgebraicGeometry.Scheme.Hom.presheafFiberYonedaEquiv`: for `W` étale over `X`, the stalk at
  `x̄` of the sheaf represented by `W` is the set of `X`-morphisms
  `Spec 𝒪^{sh}_{X,x̄} ⟶ W` (SGA 4 VIII 4.5): stalks of representable étale sheaves are their
  sections over the strict localization.
-/

universe w v u

open CategoryTheory Limits Opposite

-- As in `SGA.Foundations.Etale.Functoriality`: elements of fibre functors and points of spectra
-- are only defeq beyond instance transparency.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)

/-- The cocone exhibiting `Φ.fiber.obj X` as the fibre of the representable presheaf
`CategoryTheory.yoneda.obj X`. -/
@[simps]
def yonedaCocone (X : C) :
    Cocone ((CategoryOfElements.π Φ.fiber).op ⋙ CategoryTheory.yoneda.obj X) where
  pt := Φ.fiber.obj X
  ι :=
    { app := fun y ↦ TypeCat.ofHom fun g ↦ Φ.fiber.map g y.unop.2
      naturality := fun y y' h ↦ by
        ext g
        change Φ.fiber.map (h.unop.1 ≫ g) y'.unop.2 = Φ.fiber.map g y.unop.2
        rw [Functor.map_comp, types_comp_apply, h.unop.2]
        rfl }

/-- The cocone `yonedaCocone` is a colimit: the fibre of a representable presheaf is the fibre
functor (co-Yoneda lemma for the category of elements). -/
def isColimitYonedaCocone (X : C) : IsColimit (Φ.yonedaCocone X) where
  desc s := TypeCat.ofHom fun x ↦ s.ι.app (op ⟨X, x⟩) (𝟙 X)
  fac s y := by
    ext g
    have := ConcreteCategory.congr_hom (s.ι.naturality
      (CategoryOfElements.homMk y.unop ⟨X, Φ.fiber.map g y.unop.2⟩ g rfl).op) (𝟙 X)
    change s.ι.app (op y.unop) (g ≫ 𝟙 X) = s.ι.app (op ⟨X, Φ.fiber.map g y.unop.2⟩) (𝟙 X) at this
    rw [Category.comp_id] at this
    exact this.symm
  uniq s m hm := by
    ext x
    have := ConcreteCategory.congr_hom (hm (op ⟨X, x⟩)) (𝟙 X)
    change m (Φ.fiber.map (𝟙 X) x) = _ at this
    rwa [Functor.map_id, types_id_apply] at this

/-- The fibre of the representable presheaf `yoneda.obj X` at a point `Φ` is `Φ.fiber.obj X`. -/
noncomputable def presheafFiberYonedaIso (X : C) :
    Φ.presheafFiber.obj (CategoryTheory.yoneda.obj X) ≅ Φ.fiber.obj X :=
  colimit.isoColimitCocone ⟨_, Φ.isColimitYonedaCocone X⟩

@[simp]
lemma toPresheafFiber_presheafFiberYonedaIso_hom (Y : C) (y : Φ.fiber.obj Y) (X : C)
    (g : Y ⟶ X) :
    (Φ.presheafFiberYonedaIso X).hom (Φ.toPresheafFiber Y y (CategoryTheory.yoneda.obj X) g) =
      Φ.fiber.map g y :=
  ConcreteCategory.congr_hom
    (colimit.isoColimitCocone_ι_hom ⟨_, Φ.isColimitYonedaCocone X⟩ (op ⟨Y, y⟩)) g

end CategoryTheory.GrothendieckTopology.Point

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The elements of the fibre functor of the point `x̄` of the small étale site at an étale
`X`-scheme `W` are the lifts of `x̄` to `W`. -/
def pointSmallEtaleFiberEquiv (W : X.Etale) :
    (pointSmallEtale ξ).fiber.obj W ≃ {w : Spec (.of Ω) ⟶ W.left // w ≫ W.hom = ξ} where
  toFun a := ⟨a.left, Over.w a⟩
  invFun w := Over.homMk w.1 w.2
  left_inv _ := Over.OverMorphism.ext rfl
  right_inv _ := rfl


/-- The morphism `Spec 𝒪^{sh}_{X,x̄} ⟶ V` over `X` determined by a point `v` over `x̄` of an étale
neighbourhood `V` (`strictLocalizationHomEquiv`). -/
def etaleNbhdHom (V : X.Etale) (v : (pointSmallEtale ξ).fiber.obj V) :
    Spec ξ.strictLocalization ⟶ V.left :=
  ((ξ.strictLocalizationHomEquiv V.hom).symm (ξ.pointSmallEtaleFiberEquiv V v)).1

@[reassoc (attr := simp)]
lemma etaleNbhdHom_comp_hom (V : X.Etale) (v : (pointSmallEtale ξ).fiber.obj V) :
    ξ.etaleNbhdHom V v ≫ V.hom = ξ.fromSpecStrictLocalization :=
  ((ξ.strictLocalizationHomEquiv V.hom).symm (ξ.pointSmallEtaleFiberEquiv V v)).2

@[reassoc (attr := simp)]
lemma toSpecStrictLocalization_etaleNbhdHom (V : X.Etale) (v : (pointSmallEtale ξ).fiber.obj V) :
    ξ.toSpecStrictLocalization ≫ ξ.etaleNbhdHom V v = v.left :=
  congrArg Subtype.val ((ξ.strictLocalizationHomEquiv V.hom).apply_symm_apply _)

/-- `etaleNbhdHom V v` is the unique `X`-morphism extending `v`. -/
lemma etaleNbhdHom_eq {V : X.Etale} {v : (pointSmallEtale ξ).fiber.obj V}
    (f : Spec ξ.strictLocalization ⟶ V.left) (hf : f ≫ V.hom = ξ.fromSpecStrictLocalization)
    (hv : ξ.toSpecStrictLocalization ≫ f = v.left) : ξ.etaleNbhdHom V v = f :=
  ξ.eq_of_comp_toSpecStrictLocalization V.hom (etaleNbhdHom_comp_hom ..) hf
    ((toSpecStrictLocalization_etaleNbhdHom ..).trans hv.symm)

lemma etaleNbhdHom_naturality {V W : X.Etale} (g : V ⟶ W)
    (v : (pointSmallEtale ξ).fiber.obj V) :
    ξ.etaleNbhdHom V v ≫ g.left = ξ.etaleNbhdHom W ((pointSmallEtale ξ).fiber.map g v) := by
  have hg : g.left ≫ W.hom = V.hom := Over.w ((Scheme.Etale.forget X).map g)
  refine (ξ.etaleNbhdHom_eq _ ?_ ?_).symm
  · rw [Category.assoc, hg, etaleNbhdHom_comp_hom]
  · rw [toSpecStrictLocalization_etaleNbhdHom_assoc]
    rfl

/-- SGA 4 VIII 4.5: the stalk at `x̄` of the (sheaf) represented by an étale `X`-scheme `W` is the
set of `X`-morphisms `Spec 𝒪^{sh}_{X,x̄} ⟶ W`, i.e. the sections of `W` over the strict
localization. -/
noncomputable def presheafFiberYonedaEquiv (W : X.Etale) :
    (pointSmallEtale ξ).presheafFiber.obj (yoneda.obj W) ≃
      {f : Spec ξ.strictLocalization ⟶ W.left // f ≫ W.hom = ξ.fromSpecStrictLocalization} :=
  ((pointSmallEtale ξ).presheafFiberYonedaIso W).toEquiv.trans
    ((ξ.pointSmallEtaleFiberEquiv W).trans (ξ.strictLocalizationHomEquiv W.hom).symm)

/-- The germ of a section `g : V ⟶ W` over an étale neighbourhood `(V, v)` of `x̄`, as a section of
`W` over the strict localization: it is `f_{V,v} ≫ g`, where `f_{V,v} : Spec 𝒪^{sh}_{X,x̄} ⟶ V` is
the morphism given by `v`. -/
lemma presheafFiberYonedaEquiv_toPresheafFiber (W V : X.Etale)
    (v : (pointSmallEtale ξ).fiber.obj V) (g : V ⟶ W) :
    (ξ.presheafFiberYonedaEquiv W
      ((pointSmallEtale ξ).toPresheafFiber V v (yoneda.obj W) g)).1 =
      ξ.etaleNbhdHom V v ≫ g.left := by
  rw [etaleNbhdHom_naturality]
  simp only [presheafFiberYonedaEquiv, Equiv.trans_apply, Iso.toEquiv_fun,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberYonedaIso_hom]
  rfl

end AlgebraicGeometry.Scheme.Hom

end
