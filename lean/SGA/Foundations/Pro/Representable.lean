/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import SGA.Foundations.Pro.Basic

/-!
# Pro-representable functors

A functor `G : C ⥤ Type v` is pro-representable if it is a small filtered colimit of
corepresentable functors: `G = colim_i Hom(F i, -)` for a small cofiltered diagram `F` in `C`.
Equivalently (`isProRepresentable_iff_mem_essImage`), `G ≅ (P ⟶ Pro.of -)` for a pro-object `P`.
It is strictly pro-representable if the transition morphisms of `F` can be chosen to be
epimorphisms.

## Main results

* `Functor.IsProRepresentable.preservesFiniteLimits`: pro-representable functors are left exact.
* `Functor.isProRepresentable_iff_preservesFiniteLimits`: if `C` is essentially small and has
  finite limits, a functor `C ⥤ Type v` is pro-representable iff it is left exact.
* `Functor.isStrictlyProRepresentable_of_preservesFiniteLimits` (Grothendieck): if moreover every
  object of `C` is artinian, every left exact functor `C ⥤ Type v` is strictly
  pro-representable. It is pro-represented by its *minimal* elements (`Functor.IsMinimalElement`),
  i.e. the pairs `(X, x ∈ G(X))` such that `x` does not come from a proper subobject of `X`.

## References

* [A. Grothendieck, *Technique de descente et théorèmes d'existence en géométrie algébrique II*,
  Séminaire Bourbaki 195][Grothendieck1960], §3, Proposition 3.1
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], §6.1
-/

universe w w' v u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

namespace Functor

/-- A pro-representation of a functor `G : C ⥤ Type v`: a small cofiltered diagram `F` in `C`
together with a colimit cocone exhibiting `G` as `colim_i Hom(F i, -)`. -/
structure ProRepresentation (G : C ⥤ Type v) where
  /-- The (small, cofiltered) index category. -/
  I : Type v
  [ℐ : SmallCategory I]
  [hI : IsCofiltered I]
  /-- The diagram. -/
  F : I ⥤ C
  /-- The maps `Hom(F i, -) ⟶ G`. Use `ProRepresentation.cocone`. -/
  ι : F.op ⋙ coyoneda ⟶ (Functor.const Iᵒᵖ).obj G
  /-- `G` is the colimit of the functors `Hom(F i, -)`. -/
  isColimit : IsColimit (Cocone.mk G ι)

namespace ProRepresentation

attribute [instance] ℐ hI

variable {G G' : C ⥤ Type v} (R : G.ProRepresentation)

/-- The colimit cocone with point `G`. -/
@[simps pt]
def cocone : Cocone (R.F.op ⋙ coyoneda) where
  pt := G
  ι := R.ι

/-- A pro-representation is strict if its transition morphisms are epimorphisms. -/
def IsStrict : Prop :=
  ∀ ⦃i j : R.I⦄ (f : i ⟶ j), Epi (R.F.map f)

/-- The universal element of `G(F i)`, image of the identity of `F i`. -/
def elem (i : R.I) : G.obj (R.F.obj i) :=
  (R.ι.app (op i)).app _ (𝟙 _)

lemma ι_app_app (i : R.I) {X : C} (f : R.F.obj i ⟶ X) :
    (R.ι.app (op i)).app X f = G.map f (R.elem i) := by
  have := congrArg (fun φ ↦ φ (𝟙 (R.F.obj i))) ((R.ι.app (op i)).naturality f)
  simpa [elem] using this

lemma map_elem {i j : R.I} (f : i ⟶ j) : G.map (R.F.map f) (R.elem i) = R.elem j := by
  have h := congrArg (fun φ ↦ φ.app (R.F.obj j) (𝟙 (R.F.obj j))) (R.ι.naturality f.op)
  rw [← ι_app_app]
  simpa [elem] using h

/-- The colimit of the `Hom(F i, X)`, at an object `X`. -/
noncomputable def isColimitApp (X : C) :
    IsColimit (((evaluation C (Type v)).obj X).mapCocone R.cocone) :=
  isColimitOfPreserves ((evaluation C (Type v)).obj X) R.isColimit

/-- Every element of `G(X)` is the image of the universal element of some `G(F i)`. -/
lemma exists_map_elem {X : C} (x : G.obj X) :
    ∃ (i : R.I) (f : R.F.obj i ⟶ X), G.map f (R.elem i) = x := by
  obtain ⟨i, f, hf⟩ := Types.jointly_surjective_of_isColimit (R.isColimitApp X) x
  exact ⟨i.unop, f, (R.ι_app_app i.unop f).symm.trans hf⟩

/-- Two morphisms `F i ⟶ X`, `F j ⟶ X` define the same element of `G(X)` iff they agree on a
common refinement. -/
lemma map_elem_eq_iff {i j : R.I} {X : C} (f : R.F.obj i ⟶ X) (f' : R.F.obj j ⟶ X) :
    G.map f (R.elem i) = G.map f' (R.elem j) ↔
      ∃ (k : R.I) (p : k ⟶ i) (p' : k ⟶ j), R.F.map p ≫ f = R.F.map p' ≫ f' := by
  rw [← R.ι_app_app, ← R.ι_app_app]
  refine (Types.FilteredColimit.isColimit_eq_iff _ (R.isColimitApp X)).trans ?_
  exact ⟨fun ⟨k, p, p', h⟩ ↦ ⟨k.unop, p.unop, p'.unop, h⟩,
    fun ⟨k, p, p', h⟩ ↦ ⟨op k, p.op, p'.op, h⟩⟩

/-- Transport a pro-representation along an isomorphism of functors. -/
@[simps]
def ofIso (e : G ≅ G') : G'.ProRepresentation where
  I := R.I
  F := R.F
  ι := R.ι ≫ (Functor.const _).map e.hom
  isColimit := R.isColimit.ofIsoColimit (Cocone.ext e fun _ ↦ rfl)

/-- The pro-object `“lim” F` defined by a pro-representation. -/
noncomputable def pro : Pro C :=
  (Pro.lim R.I).obj R.F

/-- A pro-representation of `G` identifies `G` with the functor pro-represented by `R.pro`. -/
noncomputable def coyonedaIso : (Pro.coyoneda C).obj (op R.pro) ≅ G :=
  (Pro.isColimitLimCocone R.F).coconePointUniqueUpToIso R.isColimit

/-- A pro-representation indexed by an essentially small cofiltered category. -/
@[simps]
noncomputable def ofIsColimit {J : Type w} [Category.{w'} J] [IsCofiltered J]
    [EssentiallySmall.{v} J] (F : J ⥤ C) {c : Cocone (F.op ⋙ coyoneda)} (hc : IsColimit c) :
    c.pt.ProRepresentation where
  I := SmallModel.{v} J
  hI := IsCofiltered.of_equivalence (equivSmallModel.{v} J)
  F := (equivSmallModel.{v} J).inverse ⋙ F
  ι := (c.whisker (equivSmallModel.{v} J).inverse.op).ι
  isColimit := hc.whiskerEquivalence (equivSmallModel.{v} J).symm.op

lemma ofIsColimit_isStrict {J : Type w} [Category.{w'} J] [IsCofiltered J]
    [EssentiallySmall.{v} J] (F : J ⥤ C) {c : Cocone (F.op ⋙ coyoneda)} (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), Epi (F.map f)) : (ofIsColimit F hc).IsStrict :=
  fun _ _ _ ↦ hF _

end ProRepresentation

/-- A functor `G : C ⥤ Type v` is pro-representable if it is a small filtered colimit of
corepresentable functors `Hom(X, -)`. (This is Grothendieck's terminology for covariant
functors.) -/
def IsProRepresentable (G : C ⥤ Type v) : Prop :=
  Nonempty G.ProRepresentation

/-- A functor `G : C ⥤ Type v` is strictly pro-representable if it is pro-represented by a
small cofiltered diagram whose transition morphisms are epimorphisms. -/
def IsStrictlyProRepresentable (G : C ⥤ Type v) : Prop :=
  ∃ R : G.ProRepresentation, R.IsStrict

lemma IsStrictlyProRepresentable.isProRepresentable {G : C ⥤ Type v}
    (h : G.IsStrictlyProRepresentable) : G.IsProRepresentable :=
  ⟨h.choose⟩

lemma IsProRepresentable.of_iso {G G' : C ⥤ Type v} (h : G.IsProRepresentable) (e : G ≅ G') :
    G'.IsProRepresentable :=
  ⟨h.some.ofIso e⟩

lemma IsStrictlyProRepresentable.of_iso {G G' : C ⥤ Type v}
    (h : G.IsStrictlyProRepresentable) (e : G ≅ G') : G'.IsStrictlyProRepresentable :=
  ⟨h.choose.ofIso e, h.choose_spec⟩

end Functor

namespace Pro

/-- The functor pro-represented by a pro-object `P` is pro-representable, by any presentation
of `P`. -/
noncomputable def proRepresentation (P : Pro C) : ((coyoneda C).obj (op P)).ProRepresentation :=
  ({ I := P.presentation.I
     F := P.presentation.F
     ι := (limCocone P.presentation.F).ι
     isColimit := isColimitLimCocone P.presentation.F } :
      ((coyoneda C).obj (op ((lim _).obj P.presentation.F))).ProRepresentation).ofIso
    ((coyoneda C).mapIso P.presentation.iso.op)

end Pro

namespace Functor

section

variable {G : C ⥤ Type v}

/-- A functor is pro-representable iff it is isomorphic to the functor `X ↦ (P ⟶ Pro.of X)`
for a pro-object `P`. -/
theorem isProRepresentable_iff_mem_essImage :
    G.IsProRepresentable ↔ (Pro.coyoneda C).essImage G :=
  ⟨fun ⟨R⟩ ↦ ⟨op R.pro, ⟨R.coyonedaIso⟩⟩,
    fun ⟨P, ⟨e⟩⟩ ↦ ⟨(Pro.proRepresentation P.unop).ofIso e⟩⟩

/-- Pro-representable functors are left exact. -/
theorem IsProRepresentable.preservesFiniteLimits (h : G.IsProRepresentable) :
    PreservesFiniteLimits G := by
  obtain ⟨R⟩ := h
  let e : G ≅ (R.F.op ⋙ coyoneda).flip ⋙ colim :=
    R.isColimit.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫ colimitIsoFlipCompColim _
  have : PreservesFiniteLimits (R.F.op ⋙ coyoneda).flip :=
    ⟨fun J _ _ ↦ preservesLimitsOfShape_of_evaluation _ J fun i ↦
      inferInstanceAs (PreservesLimitsOfShape J (coyoneda.obj (op (R.F.obj i.unop))))⟩
  have : PreservesFiniteLimits (colim : (R.Iᵒᵖ ⥤ Type v) ⥤ Type v) := inferInstance
  have := comp_preservesFiniteLimits (R.F.op ⋙ coyoneda).flip colim
  exact preservesFiniteLimits_of_natIso e.symm

/-! ### Functors pro-represented by their elements -/

section Elements

variable (G) {J : Type w} [Category.{w'} J] (p : J ⥤ G.Elements)

/-- The cocone with point `G` over the functors `Hom(X, -)`, for `(X, x)` running over a diagram
of elements of `G`. -/
@[simps]
def elementsCocone : Cocone ((p ⋙ CategoryOfElements.π G).op ⋙ coyoneda) where
  pt := G
  ι :=
    { app j :=
        { app X := ↾fun (f : (p.obj j.unop).1 ⟶ X) ↦ G.map f (p.obj j.unop).2
          naturality X Y g := by
            ext (f : (p.obj j.unop).1 ⟶ X)
            exact G.map_comp_apply f g _ }
      naturality j j' g := by
        ext X (f : (p.obj j.unop).1 ⟶ X)
        change G.map ((p.map g.unop).1 ≫ f) (p.obj j'.unop).2 = G.map f (p.obj j.unop).2
        rw [G.map_comp_apply, (p.map g.unop).2] }

variable {G}

/-- A criterion for `elementsCocone G p` to be a colimit cocone, for `J` cofiltered: every
element of `G` comes from some `p j`, and two elements coming from `p j` and `p j'` which agree
already agree on a common refinement. -/
noncomputable def isColimitElementsCocone [IsCofilteredOrEmpty J]
    (h₁ : ∀ (X : C) (x : G.obj X), ∃ (j : J) (f : (p.obj j).1 ⟶ X), G.map f (p.obj j).2 = x)
    (h₂ : ∀ (j j' : J) {X : C} (f : (p.obj j).1 ⟶ X) (f' : (p.obj j').1 ⟶ X),
      G.map f (p.obj j).2 = G.map f' (p.obj j').2 →
        ∃ (k : J) (a : k ⟶ j) (b : k ⟶ j'), (p.map a).1 ≫ f = (p.map b).1 ≫ f') :
    IsColimit (elementsCocone G p) :=
  evaluationJointlyReflectsColimits _ fun X ↦ Types.FilteredColimit.isColimitOf _ _
    (fun x ↦ by
      obtain ⟨j, f, hf⟩ := h₁ X x
      exact ⟨op j, f, hf.symm⟩)
    (fun j j' f f' h ↦ by
      obtain ⟨k, a, b, hab⟩ := h₂ j.unop j'.unop f f' h
      exact ⟨op k, a.op, b.op, hab⟩)

end Elements

section LeftExact

variable [HasFiniteLimits C] (G) [PreservesFiniteLimits G]

/-- A left exact functor on an essentially small category with finite limits is
pro-representable (by its category of elements). -/
theorem isProRepresentable_of_preservesFiniteLimits [EssentiallySmall.{v} C] :
    G.IsProRepresentable := by
  have := Functor.isCofiltered_elements G
  refine ⟨ProRepresentation.ofIsColimit _ (isColimitElementsCocone (𝟭 G.Elements) ?_ ?_)⟩
  · exact fun X x ↦ ⟨⟨X, x⟩, 𝟙 X, show G.map (𝟙 X) x = x by simp⟩
  · intro j j' X f f' h
    obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs j j'
    let y : G.Elements := ⟨X, G.map f j.2⟩
    let u : k ⟶ y := ⟨a.1 ≫ f, by rw [Functor.map_comp_apply, a.2]⟩
    let u' : k ⟶ y := ⟨b.1 ≫ f', by rw [Functor.map_comp_apply, b.2]; exact h.symm⟩
    refine ⟨IsCofiltered.eq u u', IsCofiltered.eqHom u u' ≫ a, IsCofiltered.eqHom u u' ≫ b, ?_⟩
    have := congrArg Subtype.val (IsCofiltered.eq_condition u u')
    simpa [u, u'] using this

end LeftExact

/-- If `C` is essentially small and has finite limits, a functor `C ⥤ Type v` is
pro-representable iff it is left exact. -/
theorem isProRepresentable_iff_preservesFiniteLimits [HasFiniteLimits C] [EssentiallySmall.{v} C] :
    G.IsProRepresentable ↔ PreservesFiniteLimits G :=
  ⟨IsProRepresentable.preservesFiniteLimits, fun _ ↦ isProRepresentable_of_preservesFiniteLimits G⟩

end

/-! ### Minimal elements and Grothendieck's theorem -/

section Minimal

variable {G : C ⥤ Type w}

variable (G) in
/-- An element `x ∈ G(X)` is minimal if it does not come from a proper subobject of `X`: every
monomorphism `i : Y ⟶ X` such that `x` lies in the image of `G(i)` is an isomorphism. -/
def IsMinimalElement {X : C} (x : G.obj X) : Prop :=
  ∀ ⦃Y : C⦄ (i : Y ⟶ X) [Mono i], x ∈ Set.range (G.map i) → IsIso i

variable (G) in
/-- The category of minimal elements of `G`, a full subcategory of the category of elements. -/
abbrev MinimalElements : Type _ :=
  ObjectProperty.FullSubcategory fun p : G.Elements ↦ G.IsMinimalElement p.2

/-- Every element of `G(Y)`, for `Y` artinian, comes from a minimal element of a subobject
of `Y`. -/
lemma exists_isMinimalElement {Y : C} [IsArtinianObject Y] (y : G.obj Y) :
    ∃ (X : C) (i : X ⟶ Y) (x : G.obj X), Mono i ∧ G.map i x = y ∧ G.IsMinimalElement x := by
  let S : Set (Subobject Y) := {s | y ∈ Set.range (G.map s.arrow)}
  have hS : S.Nonempty := ⟨⊤, G.map (CategoryTheory.inv (⊤ : Subobject Y).arrow) y, by
    rw [← Functor.map_comp_apply, IsIso.inv_hom_id, Functor.map_id_apply]⟩
  obtain ⟨s, ⟨x, hx⟩, hmin⟩ := wellFounded_lt.has_min S hS
  refine ⟨s, s.arrow, x, inferInstance, hx, fun Z i _ ⟨z, hz⟩ ↦ ?_⟩
  by_contra hi
  have hlt := Subobject.mk_lt_mk_of_comm (i₂ := s.arrow) i rfl hi
  rw [Subobject.mk_arrow] at hlt
  refine hmin _ ⟨G.map (Subobject.underlyingIso (i ≫ s.arrow)).inv z, ?_⟩ hlt
  rw [← Functor.map_comp_apply, Subobject.underlyingIso_arrow, Functor.map_comp_apply, hz, hx]

variable [HasFiniteLimits C] [PreservesFiniteLimits G]

lemma exists_map_equalizer_ι {X Y : C} {f g : X ⟶ Y} {x : G.obj X}
    (h : G.map f x = G.map g x) : ∃ z, G.map (equalizer.ι f g) z = x :=
  ((Types.type_equalizer_iff_unique _ _).1
    ⟨isLimitForkMapOfIsLimit G (equalizer.condition f g) (equalizerIsEqualizer f g)⟩ x h).exists

lemma exists_map_fst_snd {A B : C} (a : G.obj A) (b : G.obj B) :
    ∃ p : G.obj (A ⨯ B), G.map prod.fst p = a ∧ G.map prod.snd p = b := by
  have h := (isLimitMapConeBinaryFanEquiv G prod.fst prod.snd)
    (isLimitOfPreserves G (prodIsProd A B))
  obtain ⟨l, h₁, h₂⟩ := BinaryFan.IsLimit.lift' h (↾fun _ : PUnit.{w + 1} ↦ a) (↾fun _ ↦ b)
  exact ⟨l PUnit.unit, ConcreteCategory.congr_hom h₁ PUnit.unit,
    ConcreteCategory.congr_hom h₂ PUnit.unit⟩

lemma nonempty_obj_terminal : Nonempty (G.obj (⊤_ C)) :=
  ⟨(Types.isTerminalEquivUnique _
    (IsTerminal.isTerminalObj G (⊤_ C) terminalIsTerminal)).default⟩

/-- Two morphisms out of `X` which agree on a minimal element of `G(X)` are equal. -/
lemma IsMinimalElement.hom_ext {X Y : C} {x : G.obj X} (hx : G.IsMinimalElement x)
    {f g : X ⟶ Y} (h : G.map f x = G.map g x) : f = g := by
  obtain ⟨z, hz⟩ := exists_map_equalizer_ι h
  have : IsIso (equalizer.ι f g) := hx _ ⟨z, hz⟩
  exact eq_of_epi_equalizer

/-- A morphism sending an element to a minimal element is an epimorphism. -/
lemma IsMinimalElement.epi {X Y : C} {x : G.obj X} {y : G.obj Y} (hy : G.IsMinimalElement y)
    (f : X ⟶ Y) (hf : G.map f x = y) : Epi f :=
  ⟨fun g h hgh ↦ hy.hom_ext (by rw [← hf, ← Functor.map_comp_apply, hgh,
    Functor.map_comp_apply])⟩

/-- The transition morphisms of the system of minimal elements are epimorphisms. -/
lemma epi_minimalElements_map {j j' : MinimalElements G} (f : j ⟶ j') : Epi f.hom.1 :=
  j'.property.epi _ f.hom.2

variable [∀ X : C, IsArtinianObject X]

instance : IsCofiltered (MinimalElements G) where
  cone_objs j j' := by
    obtain ⟨p, hp₁, hp₂⟩ := exists_map_fst_snd j.obj.2 j'.obj.2
    obtain ⟨X, i, x, _, hx, hmin⟩ := exists_isMinimalElement p
    refine ⟨⟨⟨X, x⟩, hmin⟩, ObjectProperty.homMk ⟨i ≫ prod.fst, ?_⟩,
      ObjectProperty.homMk ⟨i ≫ prod.snd, ?_⟩, trivial⟩
    · change G.map (i ≫ prod.fst) x = j.obj.2
      rw [Functor.map_comp_apply, hx, hp₁]
    · change G.map (i ≫ prod.snd) x = j'.obj.2
      rw [Functor.map_comp_apply, hx, hp₂]
  cone_maps j j' f g := ⟨j, 𝟙 _, by
    have : f = g := by
      ext
      exact j.property.hom_ext (f.hom.2.trans g.hom.2.symm)
    rw [this]⟩
  nonempty := by
    obtain ⟨t⟩ := nonempty_obj_terminal (G := G)
    obtain ⟨X, -, x, -, -, hmin⟩ := exists_isMinimalElement t
    exact ⟨⟨⟨X, x⟩, hmin⟩⟩

end Minimal

section MinimalColimit

variable {G : C ⥤ Type v} [HasFiniteLimits C] [PreservesFiniteLimits G]
  [∀ X : C, IsArtinianObject X]

/-- A left exact functor on an artinian category is the colimit of the functors `Hom(X, -)`, for
`(X, x)` running over its minimal elements. -/
noncomputable def isColimitMinimalElementsCocone :
    IsColimit (elementsCocone G (ObjectProperty.ι _ : MinimalElements G ⥤ G.Elements)) := by
  refine isColimitElementsCocone _ (fun X x ↦ ?_) (fun j j' X f f' h ↦ ?_)
  · obtain ⟨Z, i, z, -, hz, hmin⟩ := exists_isMinimalElement x
    exact ⟨⟨⟨Z, z⟩, hmin⟩, i, hz⟩
  · obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs j j'
    refine ⟨k, a, b, k.property.hom_ext ?_⟩
    change G.map (a.hom.1 ≫ f) k.obj.2 = G.map (b.hom.1 ≫ f') k.obj.2
    rw [Functor.map_comp_apply, Functor.map_comp_apply, a.hom.2, b.hom.2]
    exact h

variable [EssentiallySmall.{v} C]

instance : EssentiallySmall.{v} (MinimalElements G) :=
  essentiallySmall_of_fully_faithful (ObjectProperty.ι _)

variable (G) in
/-- The pro-representation of a left exact functor on an essentially small artinian category by
(a small model of) the system of its minimal elements. -/
noncomputable def minimalElementsProRepresentation : G.ProRepresentation :=
  ProRepresentation.ofIsColimit _ isColimitMinimalElementsCocone

lemma minimalElementsProRepresentation_isStrict :
    (minimalElementsProRepresentation G).IsStrict :=
  ProRepresentation.ofIsColimit_isStrict _ isColimitMinimalElementsCocone
    fun _ _ f ↦ epi_minimalElements_map f

/-- The terms of `minimalElementsProRepresentation G` are the objects carrying a minimal element
of `G`, up to isomorphism. -/
lemma exists_iso_minimalElementsProRepresentation_F_obj_iff (X : C) :
    (∃ i, Nonempty (X ≅ (minimalElementsProRepresentation G).F.obj i)) ↔
      ∃ x : G.obj X, G.IsMinimalElement x := by
  let e := equivSmallModel.{v} (MinimalElements G)
  let p : MinimalElements G ⥤ C := ObjectProperty.ι _ ⋙ CategoryOfElements.π G
  change (∃ i, Nonempty (X ≅ p.obj (e.inverse.obj i))) ↔ _
  constructor
  · rintro ⟨i, ⟨f₀⟩⟩
    let m := e.inverse.obj i
    let f : X ≅ m.obj.1 := f₀
    refine ⟨G.map f.inv m.obj.2, fun Y j _ hx ↦ ?_⟩
    obtain ⟨y, hy⟩ := hx
    have h1 : G.map (j ≫ f.hom) y = m.obj.2 := by
      rw [Functor.map_comp_apply, hy, ← Functor.map_comp_apply, f.inv_hom_id,
        Functor.map_id_apply]
    have : IsIso (j ≫ f.hom) := m.property (j ≫ f.hom) ⟨y, h1⟩
    exact IsIso.of_isIso_comp_right j f.hom
  · rintro ⟨x, hx⟩
    let m : MinimalElements G := ⟨⟨X, x⟩, hx⟩
    exact ⟨e.functor.obj m, ⟨p.mapIso (e.unitIso.app m)⟩⟩

/-- Grothendieck: if `C` is an essentially small category with finite limits in which every object
is artinian, then every left exact functor `G : C ⥤ Type v` is strictly pro-representable. It is
pro-represented by the (cofiltered) system of its minimal elements (`MinimalElements G`). -/
theorem isStrictlyProRepresentable_of_preservesFiniteLimits :
    G.IsStrictlyProRepresentable :=
  ⟨_, minimalElementsProRepresentation_isStrict⟩

end MinimalColimit

end Functor

end CategoryTheory
