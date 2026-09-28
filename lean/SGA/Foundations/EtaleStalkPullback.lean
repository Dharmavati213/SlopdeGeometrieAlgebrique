/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Sites.Point.Comap
import SGA.Foundations.Etale.Points

/-!
# Germs in the stalks of inverse images

Let `F : C ⥤ D` be a continuous functor between sites and `Φ` a point of `D`. The fibre at the
point `Φ.comap F` of a sheaf `G` on `C` is the fibre at `Φ` of its inverse image `F^* G`
(`CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso`). On germs, this isomorphism
sends the germ of a section `s ∈ G(U)` at a point `x ∈ Φ.fiber(F U)` to the germ at `x` of the
image of `s` in `(F^* G)(F U)` under the unit of the adjunction `F^* ⊣ F_*`
(`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app`).

For a morphism of schemes `f : X ⟶ Y` and a geometric point `s` of `X`, this describes the
isomorphism `(f^* G)_s ≅ G_{f ∘ s}` of `AlgebraicGeometry.Scheme.sheafFiberEtalePullbackIso` on
germs (`AlgebraicGeometry.Scheme.toPresheafFiber_sheafFiberEtalePullbackIso_hom_app`).
-/

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C D : Type*} [Category* C] [Category* D] {K : GrothendieckTopology D}
  (Φ : Point.{w} K) (F : C ⥤ D) [RepresentablyFlat F] {J : GrothendieckTopology C}
  (hF : CoverPreserving J K F) [InitiallySmall (F ⋙ Φ.fiber).Elements]
  (A : Type*) [Category.{v} A] [HasProducts.{w} A] [Functor.IsContinuous F J K]
  [(F.sheafPushforwardContinuous A J K).IsRightAdjoint] [HasColimitsOfSize.{w, w} A]

variable {Φ A} in
set_option backward.isDefEq.respectTransparency false in
/-- The unit of the adjunction between the fibre functor at a point and the skyscraper sheaf
functor, on components: it is the germ map. -/
@[reassoc]
lemma skyscraperSheafAdjunction_unit_app_hom_app_π {Ψ : Point.{w} J} (G : Sheaf J A) (U : C)
    (x : Ψ.fiber.obj U) :
    (Ψ.skyscraperSheafAdjunction.unit.app G).hom.app (op U) ≫ Pi.π _ x =
      Ψ.toPresheafFiber U x G.obj := by
  have hu : (Ψ.skyscraperSheafAdjunction.unit.app G).hom =
      Ψ.skyscraperPresheafHomEquiv (𝟙 (Ψ.presheafFiber.obj G.obj)) := rfl
  have := Ψ.skyscraperPresheafHomEquiv_app_π (P := G.obj) (𝟙 (Ψ.presheafFiber.obj G.obj)) U x
  rw [Category.comp_id] at this
  rw [hu]
  exact this

omit [HasColimitsOfSize.{w, w} A] in
variable {Φ A} in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma skyscraperSheafFunctor_map_hom_app_π {Ψ : Point.{w} J} {M N : A} (f : M ⟶ N) (U : C)
    (x : Ψ.fiber.obj U) :
    (Ψ.skyscraperSheafFunctor.map f).hom.app (op U) ≫ Pi.π _ x = Pi.π _ x ≫ f := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `(Φ.comap F).sheafFiber ≅ F^* ⋙ Φ.sheafFiber` on germs: the germ of
`s ∈ G(U)` at `x ∈ Φ.fiber(F U)` goes to the germ at `x` of the image of `s` under the unit
`G ⟶ F_* F^* G`. -/
@[reassoc]
lemma toPresheafFiber_sheafFiberComapIso_hom_app (G : Sheaf J A) (U : C)
    (x : (Φ.comap F hF).fiber.obj U) :
    (Φ.comap F hF).toPresheafFiber U x G.obj ≫ (Φ.sheafFiberComapIso F hF A).hom.app G =
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op U) ≫
        Φ.toPresheafFiber (F.obj U) x ((F.sheafPullback A J K).obj G).obj := by
  have h := unit_conjugateEquiv_symm
    ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
    (Φ.comap F hF).skyscraperSheafAdjunction
    (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous F hF A).hom G
  have h' := congrArg (fun φ : G ⟶ _ ↦ φ.hom.app (op U) ≫ Pi.π _ x) h
  have hθ : (Φ.sheafFiberComapIso F hF A).hom = (conjugateEquiv
      ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
      (Φ.comap F hF).skyscraperSheafAdjunction).symm
      (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous F hF A).hom := rfl
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, NatTrans.comp_app, Category.assoc, Category.assoc,
    skyscraperSheafFunctor_map_hom_app_π, skyscraperSheafAdjunction_unit_app_hom_app_π_assoc,
    ← hθ] at h'
  rw [← h']
  simp only [Adjunction.comp_unit_app, skyscraperSheafFunctorCompSheafPushforwardContinuous,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app, Iso.refl_hom, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom, Category.assoc]
  congr 1
  exact (congrArg _ (Category.id_comp _)).trans
    (skyscraperSheafAdjunction_unit_app_hom_app_π _ _ _)

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `G_{f ∘ s} ≅ (f^* G)_s` on germs: the germ of `t ∈ G(W)` at a point `w` of
`W` over `f ∘ s` goes to the germ of the image of `t` in `(f^* G)(X ×_Y W)` at the point `(s, w)`
of `X ×_Y W`. -/
lemma sheafFiberEtalePullbackIso_hom_app_toPresheafFiber (G : Sheaf Y.smallEtaleTopology (Type u))
    (W : Y.Etale) (w : (pointSmallEtale (s ≫ f)).fiber.obj W) (t : G.obj.obj (op W)) :
    (sheafFiberEtalePullbackIso f s).hom.app G
        ((pointSmallEtale (s ≫ f)).toPresheafFiber W w G.obj t) =
      (pointSmallEtale s).toPresheafFiber ((Etale.pullback f).obj W)
        ((pointSmallEtaleFiberHom f s).app W w) ((etalePullback f).obj G).obj
        (((etaleAdjunction f).unit.app G).hom.app (op W) t) := by
  have e₁ := ConcreteCategory.congr_hom
    ((pointSmallEtale (s ≫ f)).toPresheafFiber_presheafFiberDesc (P := G.obj)
      (fun W w ↦ ((pointSmallEtale s).comap (Etale.pullback f)
        (Etale.coverPreserving_pullback f)).toPresheafFiber W
          ((comapPointSmallEtaleIso f s).hom.hom.app W w) G.obj) (by simp) W w) t
  have e₂ := ConcreteCategory.congr_hom
    (GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app (pointSmallEtale s)
      (Etale.pullback f) (Etale.coverPreserving_pullback f) (Type u) G W
      ((comapPointSmallEtaleIso f s).hom.hom.app W w)) t
  change (sheafFiberComapIso f s).hom.app G
    ((comapPointSmallEtaleIso f s).hom.sheafFiber.app G
      ((pointSmallEtale (s ≫ f)).toPresheafFiber W w G.obj t)) = _
  erw [e₁]
  exact e₂

end AlgebraicGeometry.Scheme
