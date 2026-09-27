/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Limits.Indization.Category

/-!
# Pro-objects

We define the category `Pro C` of pro-objects of a category `C` as the opposite of the category
`Ind Cᵒᵖ` of ind-objects of `Cᵒᵖ`. Its objects are "formal cofiltered limits" of objects of `C`.
For `C : Type u` with `Category.{v} C`, the category `Pro C` is again a `Category.{v}`.

## Main definitions

* `Pro.of : C ⥤ Pro C`: the embedding of `C`, which is fully faithful.
* `Pro.coyoneda : (Pro C)ᵒᵖ ⥤ C ⥤ Type v`: the pro-object `P` goes to the functor
  `X ↦ (P ⟶ Pro.of X)`. This functor is fully faithful (`Pro.coyonedaFullyFaithful`): a
  pro-object is determined by the functor it pro-represents.
* `Pro.lim I : (I ⥤ C) ⥤ Pro C`: the pro-object `“lim” F` of a small cofiltered diagram.

## Main results

* `Pro C` has cofiltered limits, and `Pro.coyoneda` sends them to filtered colimits.
* `Pro.isColimitLimCocone`: the Hom formula
  `(“lim” F ⟶ Pro.of X) = colim_i (F i ⟶ X)` for a small cofiltered diagram `F`.
* `Pro.presentation`: every pro-object is isomorphic to `“lim” F` for a small cofiltered
  diagram `F` in `C`.

## References

* [A. Grothendieck, *Technique de descente et théorèmes d'existence en géométrie algébrique II*,
  Séminaire Bourbaki 195][Grothendieck1960], §3
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], §6.1
-/

universe w v u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- The category of pro-objects of `C`: the opposite of the category of ind-objects of `Cᵒᵖ`. -/
abbrev Pro : Type (max u (v + 1)) := (Ind Cᵒᵖ)ᵒᵖ

namespace Pro

/-- The embedding of `C` into its category of pro-objects. -/
@[simps]
noncomputable def of : C ⥤ Pro C where
  obj X := op (Ind.yoneda.obj (op X))
  map f := (Ind.yoneda.map f.op).op
  map_id X := by simp
  map_comp f g := by simp

/-- The embedding `Pro.of` is fully faithful. -/
noncomputable def ofFullyFaithful : (of (C := C)).FullyFaithful where
  preimage {X Y} f := (Ind.yoneda.fullyFaithful.preimage (X := op Y) (Y := op X) f.unop).unop
  map_preimage {X Y} f := Quiver.Hom.unop_inj
    (Ind.yoneda.fullyFaithful.map_preimage (X := op Y) (Y := op X) f.unop)
  preimage_map f := Quiver.Hom.op_inj (Ind.yoneda.fullyFaithful.preimage_map f.op)

instance : (of (C := C)).Full := ofFullyFaithful.full
instance : (of (C := C)).Faithful := ofFullyFaithful.faithful

/-! ### The functor pro-represented by a pro-object -/

variable (C) in
/-- The pro-object `P` goes to the functor `X ↦ (P ⟶ Pro.of X)` from `C` to types. -/
noncomputable def coyoneda : (Pro C)ᵒᵖ ⥤ C ⥤ Type v :=
  CategoryTheory.coyoneda ⋙ (Functor.whiskeringLeft C (Pro C) (Type v)).obj of

@[simp]
lemma coyoneda_obj_obj (P : (Pro C)ᵒᵖ) (X : C) :
    ((coyoneda C).obj P).obj X = (P.unop ⟶ of.obj X) :=
  rfl

@[simp]
lemma coyoneda_obj_map (P : (Pro C)ᵒᵖ) {X Y : C} (f : X ⟶ Y) (u : P.unop ⟶ of.obj X) :
    ((coyoneda C).obj P).map f u = u ≫ of.map f :=
  rfl

@[simp]
lemma coyoneda_map_app {P Q : (Pro C)ᵒᵖ} (g : P ⟶ Q) (X : C) (u : P.unop ⟶ of.obj X) :
    ((coyoneda C).map g).app X u = g.unop ≫ u :=
  rfl

/-- Morphisms `P ⟶ Pro.of X` of pro-objects are morphisms `Ind.yoneda (op X) ⟶ P.unop` of
ind-objects of `Cᵒᵖ`. -/
noncomputable def homOfEquivInd (P : Pro C) (X : C) :
    (P ⟶ of.obj X) ≃ (Ind.yoneda.obj (op X) ⟶ P.unop) :=
  opEquiv _ _

lemma homOfEquivInd_comp_map (P : Pro C) {X Y : C} (u : P ⟶ of.obj X) (f : X ⟶ Y) :
    homOfEquivInd P Y (u ≫ of.map f) = Ind.yoneda.map f.op ≫ homOfEquivInd P X u :=
  rfl

lemma homOfEquivInd_comp {P Q : Pro C} (g : Q ⟶ P) {X : C} (u : P ⟶ of.obj X) :
    homOfEquivInd Q X (g ≫ u) = homOfEquivInd P X u ≫ g.unop :=
  rfl

/-- The Yoneda bijection between morphisms `P ⟶ Pro.of X` and elements of the presheaf on `Cᵒᵖ`
underlying the ind-object `P.unop`. -/
noncomputable def homOfEquiv (P : Pro C) (X : C) :
    (P ⟶ of.obj X) ≃ ((Ind.inclusion Cᵒᵖ).obj P.unop).obj (op (op X)) :=
  (homOfEquivInd P X).trans <|
    Ind.inclusion.fullyFaithful.homEquiv.trans <|
      ((Ind.yonedaCompInclusion.app (op X)).homCongr (Iso.refl _)).trans yonedaEquiv

lemma homOfEquiv_apply (P : Pro C) (X : C) (u : P ⟶ of.obj X) :
    homOfEquiv P X u = yonedaEquiv (Ind.yonedaCompInclusion.inv.app (op X) ≫
      (Ind.inclusion Cᵒᵖ).map (homOfEquivInd P X u)) := by
  simp only [homOfEquiv]
  rfl

lemma homOfEquiv_comp (P : Pro C) {X Y : C} (u : P ⟶ of.obj X) (f : X ⟶ Y) :
    homOfEquiv P Y (u ≫ of.map f) =
      ((Ind.inclusion Cᵒᵖ).obj P.unop).map f.op.op (homOfEquiv P X u) := by
  rw [homOfEquiv_apply, homOfEquiv_apply, yonedaEquiv_naturality, homOfEquivInd_comp_map,
    Functor.map_comp, ← Category.assoc, ← Category.assoc]
  congr 2
  exact (Ind.yonedaCompInclusion.inv.naturality f.op).symm

lemma comp_homOfEquiv {P Q : Pro C} (g : Q ⟶ P) {X : C} (u : P ⟶ of.obj X) :
    homOfEquiv Q X (g ≫ u) = ((Ind.inclusion Cᵒᵖ).map g.unop).app _ (homOfEquiv P X u) := by
  rw [homOfEquiv_apply, homOfEquiv_apply, homOfEquivInd_comp, Functor.map_comp,
    ← yonedaEquiv_comp, Category.assoc]

variable (C) in
/-- `Pro.coyoneda` is the inclusion of ind-objects of `Cᵒᵖ` into presheaves on `Cᵒᵖ`, up to the
identifications `(Pro C)ᵒᵖᵒᵖ = Pro C` and `Cᵒᵖᵒᵖ = C`. -/
noncomputable def coyonedaIso : coyoneda C ≅
    unopUnop (Ind Cᵒᵖ) ⋙ Ind.inclusion Cᵒᵖ ⋙
      (Functor.whiskeringLeft C Cᵒᵖᵒᵖ (Type v)).obj (opOp C) :=
  NatIso.ofComponents (fun P ↦ NatIso.ofComponents (fun X ↦ (homOfEquiv P.unop X).toIso)
    fun f ↦ by ext u; exact homOfEquiv_comp P.unop u f)
    fun g ↦ by ext X u; exact comp_homOfEquiv g.unop u

instance : ((Functor.whiskeringLeft C Cᵒᵖᵒᵖ (Type v)).obj (opOp C)).IsEquivalence :=
  inferInstanceAs ((opOpEquivalence C).congrLeft.functor.IsEquivalence)

variable (C) in
/-- A pro-object is determined by the functor it pro-represents: `Pro.coyoneda` is fully
faithful. -/
noncomputable def coyonedaFullyFaithful : (coyoneda C).FullyFaithful :=
  (((opOpEquivalence (Ind Cᵒᵖ)).fullyFaithfulFunctor.comp Ind.inclusion.fullyFaithful).comp
    ((opOpEquivalence C).congrLeft.fullyFaithfulFunctor)).ofIso (coyonedaIso C).symm

instance : (coyoneda C).Full := (coyonedaFullyFaithful C).full
instance : (coyoneda C).Faithful := (coyonedaFullyFaithful C).faithful

/-- `Pro.coyoneda` restricted to `C` is the co-Yoneda embedding. -/
noncomputable def ofOpCompCoyonedaIso :
    of.op ⋙ coyoneda C ≅ CategoryTheory.coyoneda (C := C) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ (ofFullyFaithful.homEquiv (X := X.unop) (Y := Y)).symm.toIso)
    fun {Y Y'} f ↦ by
      ext (u : of.obj X.unop ⟶ of.obj Y)
      apply ofFullyFaithful.map_injective
      change of.map (ofFullyFaithful.preimage (u ≫ of.map f)) =
        of.map (ofFullyFaithful.preimage u ≫ f)
      simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage])
    fun {X X'} g ↦ by
      ext Y (u : of.obj X.unop ⟶ of.obj Y)
      apply ofFullyFaithful.map_injective
      change of.map (ofFullyFaithful.preimage (of.map g.unop ≫ u)) =
        of.map (g.unop ≫ ofFullyFaithful.preimage u)
      simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]

/-! ### Cofiltered limits -/

example : HasCofilteredLimits (Pro C) := inferInstance

instance {J : Type v} [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (coyoneda C) :=
  preservesColimitsOfShape_of_natIso (coyonedaIso C).symm

section Lim

variable (I : Type v) [SmallCategory I] [IsCofiltered I]

/-- The pro-object `“lim” F` of a small cofiltered diagram `F` in `C`. -/
noncomputable def lim : (I ⥤ C) ⥤ Pro C :=
  (Functor.whiskeringRight _ _ _).obj of ⋙ Limits.lim

variable {I}

lemma lim_obj (F : I ⥤ C) : (lim I).obj F = limit (F ⋙ of) :=
  rfl

/-- The projection `“lim” F ⟶ Pro.of (F i)`. -/
noncomputable def limπ (F : I ⥤ C) (i : I) : (lim I).obj F ⟶ of.obj (F.obj i) :=
  limit.π (F ⋙ of) i

@[reassoc (attr := simp)]
lemma limπ_map (F : I ⥤ C) {i j : I} (f : i ⟶ j) : limπ F i ≫ of.map (F.map f) = limπ F j :=
  limit.w (F ⋙ of) f

/-- The cocone exhibiting the functor pro-represented by `“lim” F` as the colimit of the
functors `Hom(F i, -)`. -/
@[simps]
noncomputable def limCocone (F : I ⥤ C) : Cocone (F.op ⋙ CategoryTheory.coyoneda) where
  pt := (coyoneda C).obj (op ((lim I).obj F))
  ι :=
    { app i :=
        { app X := ↾fun (f : F.obj i.unop ⟶ X) ↦ limπ F i.unop ≫ of.map f
          naturality X Y g := by
            ext (f : F.obj i.unop ⟶ X)
            change limπ F i.unop ≫ of.map (f ≫ g) = (limπ F i.unop ≫ of.map f) ≫ of.map g
            rw [Functor.map_comp, Category.assoc] }
      naturality i j g := by
        ext X (f : F.obj i.unop ⟶ X)
        change limπ F j.unop ≫ of.map (F.map g.unop ≫ f) = limπ F i.unop ≫ of.map f
        rw [Functor.map_comp, limπ_map_assoc] }

/-- The Hom formula for pro-objects: for a small cofiltered diagram `F` in `C`,
`(“lim” F ⟶ Pro.of X) = colim_i (F i ⟶ X)`, functorially in `X`. -/
noncomputable def isColimitLimCocone (F : I ⥤ C) : IsColimit (limCocone F) := by
  have h := isColimitOfPreserves (coyoneda C) (limit.isLimit (F ⋙ of)).op
  exact (IsColimit.equivOfNatIsoOfIso (Functor.isoWhiskerLeft F.op ofOpCompCoyonedaIso) _ _
    (Cocone.ext (Iso.refl _) fun _ ↦ Category.comp_id _)).1 h

end Lim

/-! ### Presentations -/

/-- A choice of a small cofiltered diagram `F` in `C` with `P ≅ “lim” F`. -/
structure Presentation (P : Pro C) where
  /-- The (small, cofiltered) index category. -/
  I : Type v
  [ℐ : SmallCategory I]
  [hI : IsCofiltered I]
  /-- The diagram. -/
  F : I ⥤ C
  /-- The identification of `P` with `“lim” F`. -/
  iso : P ≅ (lim I).obj F

attribute [instance] Presentation.ℐ Presentation.hI

/-- Every pro-object is the pro-object `“lim” F` of a small cofiltered diagram in `C`. -/
noncomputable def presentation (P : Pro C) : Presentation P where
  I := P.unop.presentation.Iᵒᵖ
  F := P.unop.presentation.F.leftOp
  iso := (Ind.colimitPresentationCompYoneda P.unop).op ≪≫ (limitOpIsoOpColimit _).symm ≪≫
    HasLimit.isoOfNatIso (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
      (Category.comp_id _).trans (Category.id_comp _).symm)

end Pro

end CategoryTheory
