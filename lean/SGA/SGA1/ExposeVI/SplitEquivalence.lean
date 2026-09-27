/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.LaxCoGrothendieckCleavage
import SGA.SGA1.ExposeVI.Split
import SGA.SGA1.ExposeVI.Splittings

/-!
# SGA 1, Exposé VI, VI.9: split categories and functors `Eᵒᵖ ⥤ Cat`

A functor `φ : Eᵒᵖ ⥤ Cat` is a pseudofunctor with `c_{f,g} = id` (`laxOfFunctor φ`); the
category of VI.8 it defines (isomorphic to mathlib's `SplitFibered φ = ∫ᶜ φ`,
`splitFiberedIsoLax`) carries a canonical splitting (`isSplitting_cleavage_laxOfFunctor`), and
the functor `Eᵒᵖ ⥤ Cat` of this splitting is isomorphic to `φ` (`splittingFunctorIso`).
Conversely, a category `𝒳` with a splitting `K` is isomorphic over `E`, as a cloven category, to
the split category defined by the functor `S ↦ 𝒳_S`, `f ↦ f^*` of `K`
(`Cleavage.IsSplitting.laxCoGrothendieckIso`, `…isClovenFunctor_fromLaxCoGrothendieckBased`).
Together these are the two halves of SGA's "the category of split categories over `E` is
equivalent to `Hom(Eᵒᵖ, Cat)`" on objects; the equivalence of categories itself (with morphisms
the functors preserving transport morphisms) is `splitEquivalence` in `ClovenCategories.lean`.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Opposite Bicategory

variable {E : Type u₁} [Category.{v₁} E]

/-- VI.9: a functor `φ : Eᵒᵖ ⥤ Cat` as a normalized pseudofunctor with `c_{f,g} = id`. -/
def laxOfFunctor (φ : Eᵒᵖ ⥤ Cat.{v₂, u₂}) :
    StrictlyUnitaryLaxFunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂} where
  toLaxFunctor := φ.toPseudofunctor'.toLax
  map_id S := by
    obtain ⟨S⟩ := S
    exact φ.map_id S
  mapId_eq_eqToHom S := rfl

variable (φ : Eᵒᵖ ⥤ Cat.{v₂, u₂})

@[simp] theorem laxPullback_laxOfFunctor {T S : E} (f : T ⟶ S) :
    laxPullback (laxOfFunctor φ).toLaxFunctor f = (φ.map f.op).toFunctor := rfl

theorem laxPullback_laxOfFunctor_comp {U T S : E} (f : T ⟶ S) (g : U ⟶ T) :
    laxPullback (laxOfFunctor φ).toLaxFunctor f ⋙ laxPullback (laxOfFunctor φ).toLaxFunctor g =
      laxPullback (laxOfFunctor φ).toLaxFunctor (g ≫ f) := by
  change (φ.map f.op ≫ φ.map g.op).toFunctor = (φ.map (g ≫ f).op).toFunctor
  rw [← φ.map_comp]
  rfl

theorem laxComparison_laxOfFunctor_app {U T S : E} (f : T ⟶ S) (g : U ⟶ T)
    (ξ : φ.obj (op S)) :
    (laxComparison (laxOfFunctor φ).toLaxFunctor f g).app ξ =
      eqToHom (congrArg (fun G ↦ G.obj ξ) (laxPullback_laxOfFunctor_comp φ f g)) := by
  simp [laxComparison, laxOfFunctor]
  rfl

/-- The category `∫ᶜ P` is (by definition) the category of VI.8 defined by the lax functor of
`P`. -/
def coGrothendieckToLax (P : Pseudofunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂}) :
    Pseudofunctor.CoGrothendieck P ⥤ LaxCoGrothendieck P.toLax where
  obj X := ⟨X.base, X.fiber⟩
  map f := ⟨f.base, f.fiber⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inverse of `coGrothendieckToLax`. -/
def laxToCoGrothendieck (P : Pseudofunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂}) :
    LaxCoGrothendieck P.toLax ⥤ Pseudofunctor.CoGrothendieck P where
  obj X := ⟨X.base, X.fiber⟩
  map f := ⟨f.base, f.fiber⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `∫ᶜ P ≅ LaxCoGrothendieck P.toLax`, an isomorphism of categories over `E` (identity on data). -/
def coGrothendieckIsoLax (P : Pseudofunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂}) :
    IsoCat (Pseudofunctor.CoGrothendieck P) (LaxCoGrothendieck P.toLax) where
  functor := coGrothendieckToLax P
  inverse := laxToCoGrothendieck P
  unit_eq := rfl
  counit_eq := rfl

/-- VI.9: mathlib's split category `SplitFibered φ = ∫ᶜ φ` is the category of VI.8 defined by the
normalized pseudofunctor `laxOfFunctor φ`. -/
def splitFiberedIsoLax :
    IsoCat (SplitFibered φ) (LaxCoGrothendieck (laxOfFunctor φ).toLaxFunctor) :=
  coGrothendieckIsoLax φ.toPseudofunctor'

/-- VI.9: the canonical cleavage `(f, 𝟙)` of the category defined by a functor `Eᵒᵖ ⥤ Cat` is a
splitting. -/
theorem isSplitting_cleavage_laxOfFunctor :
    (LaxCoGrothendieck.cleavage (laxOfFunctor φ)).IsSplitting := by
  refine (Cleavage.isSplitting_iff _).mpr ⟨LaxCoGrothendieck.cleavage_isNormalized, ?_⟩
  rintro U T S f g ⟨⟨B, x⟩, h⟩
  change B = S at h
  subst h
  have e : ((LaxCoGrothendieck.cleavage (laxOfFunctor φ)).comparison f g
      ((LaxCoGrothendieck.fiberFunctor (laxOfFunctor φ) B).obj x)).val =
      (LaxCoGrothendieck.ι (laxOfFunctor φ) U).map
        ((laxComparison (laxOfFunctor φ).toLaxFunctor f g).app x) :=
    congrArg Subtype.val (LaxCoGrothendieck.cleavage_comparison f g x)
  erw [laxComparison_laxOfFunctor_app, eqToHom_map] at e
  exact ⟨_, e⟩

/-- A `Cat`-isomorphism from an isomorphism of categories. -/
def IsoCat.toCatIso {A B : Cat.{v₂, u₂}} (e : IsoCat A B) : A ≅ B where
  hom := Cat.Hom.ofFunctor e.functor
  inv := Cat.Hom.ofFunctor e.inverse
  hom_inv_id := Cat.Hom.ext e.unit_eq.symm
  inv_hom_id := Cat.Hom.ext e.counit_eq

/-- VI.9: the functor `Eᵒᵖ ⥤ Cat` of the canonical splitting of the category defined by `φ` is
isomorphic to `φ`, through the isomorphisms `i_S : φ(S) ≅ (∫ φ)_S`. -/
noncomputable def splittingFunctorIso (ψ : Eᵒᵖ ⥤ Cat.{max v₁ v₂, max u₁ u₂}) :
    ψ ≅ (isSplitting_cleavage_laxOfFunctor ψ).toFunctor :=
  NatIso.ofComponents
    (fun S ↦ IsoCat.toCatIso (A := ψ.obj S)
      (B := Cat.of (Fiber (LaxCoGrothendieck.forget (laxOfFunctor ψ).toLaxFunctor) S.unop))
      (LaxCoGrothendieck.fiberIso (F := laxOfFunctor ψ) S.unop))
    (fun f ↦ Cat.Hom.ext
      (LaxCoGrothendieck.fiberFunctor_comp_pullback (F := laxOfFunctor ψ) f.unop).symm)

/-! ### A split category is the category defined by its functor -/

namespace Cleavage

variable {C : Type u₂} [Category.{v₂} C] {p : C ⥤ E} {K : Cleavage p}

/-- The identification of the category defined by the functor of a splitting with the category
defined by the pseudofunctor of the underlying cleavage (identity on objects and arrows). -/
noncomputable def IsSplitting.toLax (hK : K.IsSplitting) :
    LaxCoGrothendieck (laxOfFunctor hK.toFunctor).toLaxFunctor ⥤
      LaxCoGrothendieck K.laxFunctor where
  obj X := ⟨X.base, X.fiber⟩
  map f := ⟨f.base, f.fiber⟩
  map_id X := by
    obtain ⟨B, ξ⟩ := X
    change Fiber p B at ξ
    refine LaxCoGrothendieck.Hom.ext _ _ rfl ?_
    change (laxUnit (laxOfFunctor hK.toFunctor).toLaxFunctor B).app ξ =
      (K.pullbackIdIso B).inv.app ξ ≫ eqToHom rfl
    erw [LaxCoGrothendieck.laxUnit_app, eqToHom_refl, Category.comp_id,
      hK.1.pullbackIdIso_inv_app]
    rfl
  map_comp {X Y Z} f g := by
    refine LaxCoGrothendieck.Hom.ext _ _ rfl ?_
    change f.fiber ≫ (K.pullback f.base).map g.fiber ≫
        (laxComparison (laxOfFunctor hK.toFunctor).toLaxFunctor g.base f.base).app Z.fiber =
      (f.fiber ≫ (K.pullback f.base).map g.fiber ≫ K.comparison g.base f.base Z.fiber) ≫
        eqToHom rfl
    erw [eqToHom_refl, Category.comp_id]
    congr 2
    erw [laxComparison_laxOfFunctor_app]
    obtain ⟨h, hc⟩ := ((K.isSplitting_iff).mp hK).2 g.base f.base Z.fiber
    apply Subtype.ext
    erw [hc, fiber_eqToHom_val]
    rfl

variable (hK : K.IsSplitting)

instance : hK.toLax.IsIso where
  faithful := ⟨fun {_ _} {f g} h ↦ by
    obtain ⟨fb, ff⟩ := f
    obtain ⟨gb, gf⟩ := g
    cases h
    rfl⟩
  full := ⟨fun {_ _} f ↦ ⟨⟨f.base, f.fiber⟩, rfl⟩⟩
  bijective_obj := ⟨fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by cases h; rfl, fun X ↦ ⟨⟨X.base, X.fiber⟩, rfl⟩⟩

/-- VI.9: the functor `(S, ξ) ↦ ξ`, `(f, u) ↦ α_f(ξ) ∘ u` from the split category defined by the
functor `S ↦ 𝒳_S` of a splitting of `𝒳` to `𝒳`. -/
noncomputable def IsSplitting.fromLaxCoGrothendieck :
    LaxCoGrothendieck (laxOfFunctor hK.toFunctor).toLaxFunctor ⥤ C :=
  hK.toLax ⋙ K.fromLaxCoGrothendieck

instance : hK.fromLaxCoGrothendieck.IsIso where
  faithful := inferInstanceAs (hK.toLax ⋙ K.fromLaxCoGrothendieck).Faithful
  full := inferInstanceAs (hK.toLax ⋙ K.fromLaxCoGrothendieck).Full
  bijective_obj := (K.fromLaxCoGrothendieck.bijective_obj).comp
    (Functor.IsIso.bijective_obj hK.toLax)

/-- VI.9: a split category `𝒳` is isomorphic to the split category defined by its functor
`Eᵒᵖ ⥤ Cat`. -/
noncomputable def IsSplitting.laxCoGrothendieckIso :
    IsoCat (LaxCoGrothendieck (laxOfFunctor hK.toFunctor).toLaxFunctor) C :=
  hK.fromLaxCoGrothendieck.asIsomorphism

/-- VI.9: the isomorphism is an `E`-functor. -/
noncomputable def IsSplitting.fromLaxCoGrothendieckBased :
    BasedFunctor
      (BasedCategory.ofFunctor (LaxCoGrothendieck.forget (laxOfFunctor hK.toFunctor).toLaxFunctor))
      (BasedCategory.ofFunctor p) where
  toFunctor := hK.fromLaxCoGrothendieck
  w := by
    change hK.toLax ⋙ (K.fromLaxCoGrothendieck ⋙ p) = _
    rw [fromLaxCoGrothendieck_comp_p]
    rfl

/-- VI.9: the isomorphism sends the canonical splitting to the given one. -/
theorem IsSplitting.isClovenFunctor_fromLaxCoGrothendieckBased :
    IsClovenFunctor (LaxCoGrothendieck.cleavage (laxOfFunctor hK.toFunctor)) K
      hK.fromLaxCoGrothendieckBased := by
  rintro R S f ⟨⟨B, x⟩, h⟩
  change B = S at h
  subst h
  refine ⟨rfl, ?_⟩
  change K.fromLaxCoGrothendieck.map (hK.toLax.map ((LaxCoGrothendieck.cleavage
    (laxOfFunctor hK.toFunctor)).transport f
      ((LaxCoGrothendieck.fiberFunctor (laxOfFunctor hK.toFunctor) B).obj x))) = _
  rw [LaxCoGrothendieck.cleavage_transport]
  change Subtype.val (𝟙 ((K.pullback f).obj x)) ≫ K.transport f x =
    eqToHom rfl ≫ K.transport f x
  simp

end Cleavage

end SGA.SGA1.ExposeVI
