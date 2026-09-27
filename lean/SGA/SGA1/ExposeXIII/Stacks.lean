/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sheafification
import SGA.Foundations.Etale.TorsorDescent

/-!
# SGA 1, Exposé XIII, §0: recollections on stacks

SGA 1 XIII 0 recalls from Giraud's *Cohomologie non abélienne* the notions of stack, gerbe,
stack in discrete categories attached to a sheaf of sets, and stack of torsors.

* Stacks are mathlib's `Pseudofunctor.IsStack` (descent of morphisms and effectivity of descent
  data, Giraud II 1.2.1), recorded as `isStack_iff`.
* `IsGerbe` is the notion of gerbe.
* `discreteStack P` is the stack in discrete categories attached to a presheaf of sets `P`
  (used in XIII 1.2); `isStack_discreteStack_iff` shows it is a stack exactly when `P` is a
  sheaf, and `isGerbe_discreteStack_iff` says when it is a gerbe.
* `isoClassesPresheaf F` is the presheaf `O` of isomorphism classes of objects, and
  `sheafOfMaximalSubgerbes J F` is the associated sheaf `SF`.
* Torsors under a sheaf of groups and the set `H¹` of their isomorphism classes are in
  `SGA.Foundations.Etale.Torsor` (`CategoryTheory.Torsor`, `CategoryTheory.H1`). The stack of
  torsors is the pseudofunctor `CategoryTheory.Torsor.stack J G`; it is a stack
  (`isStack_torsorStack`) and a gerbe (`isGerbe_torsorStack`), with the cartesian section given by
  the trivial torsors (`torsorStack_map_trivial`); a torsor is isomorphic to the trivial one iff
  it has a global section (`torsor_nonempty_iso_trivial_iff`).

Not formalized: the converse statement (a gerbe with a section is equivalent to the stack of
torsors under the automorphisms of the section), maximal subgerbes as substacks, and
constructible stacks.
-/

universe w v' u' v u

open CategoryTheory Opposite Limits

namespace SGA.SGA1.ExposeXIII

section Stacks

variable {C : Type u} [Category.{v} C]

/-- XIII 0: a stack over a site is a fibered category (here a pseudofunctor
`LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`) whose presheaves of morphisms are sheaves and whose descent data
relative to covering sieves are effective. This is mathlib's `Pseudofunctor.IsStack`. -/
theorem isStack_iff (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    (J : GrothendieckTopology C) :
    F.IsStack J ↔ F.IsPrestack J ∧ ∀ ⦃S : C⦄ (R : Sieve S), R ∈ J S →
      (F.toDescentData (fun (f : R.arrows.category) ↦ f.obj.hom)).EssSurj :=
  ⟨fun h ↦ ⟨h.toIsPrestack, fun _ R hR ↦ h.essSurj_of_sieve R hR⟩,
    fun ⟨h₁, h₂⟩ ↦ { toIsPrestack := h₁, essSurj_of_sieve := fun R hR ↦ h₂ R hR }⟩

/-- XIII 0: a gerbe is a stack whose fibers are groupoids, any two of whose objects are
locally isomorphic, and which has objects locally. -/
class IsGerbe (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    (J : GrothendieckTopology C) : Prop extends F.IsStack J where
  isIso {S : C} {x y : F.obj (.mk (op S))} (φ : x ⟶ y) : IsIso φ
  locallyIso {S : C} (x y : F.obj (.mk (op S))) : ∃ R ∈ J S, ∀ ⦃T : C⦄ (g : T ⟶ S), R g →
    Nonempty ((F.map g.op.toLoc).toFunctor.obj x ≅ (F.map g.op.toLoc).toFunctor.obj y)
  locallyNonempty (S : C) :
    ∃ R ∈ J S, ∀ ⦃T : C⦄ (g : T ⟶ S), R g → Nonempty (F.obj (.mk (op T)))

/-- XIII 0: the presheaf `O` of isomorphism classes of objects of the fibers of `F`,
`O(U) = Ob(F_U)/≅`. (SGA 1 XIII 0 recalls from Giraud III 2.1.4 that the sheaf of maximal
subgerbes `SF` is the sheaf associated with `O`.) -/
def isoClassesPresheaf (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) : Cᵒᵖ ⥤ Type u' where
  obj U := Quotient (isIsomorphicSetoid (F.obj (.mk U)))
  map {U V} g := ↾Quotient.map (F.map g.toLoc).toFunctor.obj
    (fun _ _ ⟨e⟩ ↦ ⟨(F.map g.toLoc).toFunctor.mapIso e⟩)
  map_id U := by
    ext x
    induction x using Quotient.inductionOn with | h x => ?_
    exact Quotient.sound ⟨(Cat.Hom.toNatIso (F.mapId (.mk U))).app x⟩
  map_comp {U V W} f g := by
    ext x
    induction x using Quotient.inductionOn with | h x => ?_
    exact Quotient.sound ⟨(Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc)).app x⟩

end Stacks

section Discrete

variable {C : Type u} [Category.{v} C]

/-- The stack in discrete categories associated with a presheaf of sets. -/
def discreteStack (P : Cᵒᵖ ⥤ Type w) : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w} :=
  (P ⋙ typeToCat).toPseudofunctor'

variable (P : Cᵒᵖ ⥤ Type w)

@[simp]
lemma discreteStack_map_obj {X Y : C} (g : Y ⟶ X) (x : (discreteStack P).obj (.mk (op X))) :
    ((discreteStack P).map g.op.toLoc).toFunctor.obj x = ⟨P.map g.op x.as⟩ := rfl

instance {X : C} (x y : (discreteStack P).obj (.mk (op X))) : Subsingleton (x ⟶ y) :=
  inferInstanceAs (Subsingleton (Discrete.mk x.as ⟶ Discrete.mk y.as))

example {X : C} (x y : (discreteStack P).obj (.mk (op X))) (h : x ⟶ y) : x.as = y.as :=
  Discrete.eq_of_hom h

instance {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    (D₁ D₂ : (discreteStack P).DescentData f) : Subsingleton (D₁ ⟶ D₂) :=
  ⟨fun _ _ ↦ Pseudofunctor.DescentData.hom_ext (fun _ ↦ Subsingleton.elim _ _)⟩

/-- A presheaf of sets which is a sheaf for a sieve gives effective descent for the associated
stack in discrete categories. -/
lemma isStackFor_discreteStack {S : C} {R : Sieve S} (hP : Presieve.IsSheafFor P R.arrows) :
    (discreteStack P).IsStackFor R.arrows := by
  rw [Pseudofunctor.isStackFor_iff]
  let Φ := (discreteStack P).toDescentData (fun (f : R.arrows.category) ↦ f.obj.hom)
  have faithful : Φ.Faithful := ⟨fun {M N} a b _ ↦ Subsingleton.elim a b⟩
  have full : Φ.Full := ⟨fun {M N} φ ↦ by
    refine ⟨Discrete.eqToHom ?_, Subsingleton.elim _ _⟩
    apply hP.isSeparatedFor.ext
    intro Y g hg
    exact Discrete.eq_of_hom (φ.hom (R.arrows.categoryMk g hg))⟩
  have essSurj : Φ.EssSurj := ⟨fun D ↦ by
    let x : Presieve.FamilyOfElements P R.arrows := fun Y g hg ↦
      (D.obj (R.arrows.categoryMk g hg)).as
    have hx : x.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
      exact Discrete.eq_of_hom (D.hom (g₁ ≫ f₁) (i₁ := R.arrows.categoryMk f₁ h₁)
        (i₂ := R.arrows.categoryMk f₂ h₂) g₁ g₂ rfl comm.symm)
    obtain ⟨t, ht, -⟩ := hP x hx
    exact ⟨⟨t⟩, ⟨Pseudofunctor.DescentData.isoMk
      (fun i ↦ Discrete.eqToIso (ht i.obj.hom i.property))
      (fun _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _)⟩⟩⟩
  exact { }

/-- Conversely, effective descent for the stack in discrete categories associated with `P`
means that `P` is a sheaf for the sieve. -/
lemma isSheafFor_of_isStackFor_discreteStack {S : C} {R : Sieve S}
    (hP : (discreteStack P).IsStackFor R.arrows) : Presieve.IsSheafFor P R.arrows := by
  rw [Pseudofunctor.isStackFor_iff] at hP
  let Φ := (discreteStack P).toDescentData (fun (f : R.arrows.category) ↦ f.obj.hom)
  intro x hx
  let D : (discreteStack P).DescentData (fun (f : R.arrows.category) ↦ f.obj.hom) :=
    { obj i := ⟨x i.obj.hom i.property⟩
      hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := Discrete.eqToHom (hx f₁ f₂ i₁.property i₂.property
        (hf₁.trans hf₂.symm))
      pullHom_hom := by intros; exact Subsingleton.elim _ _
      hom_self := by intros; exact Subsingleton.elim _ _
      hom_comp := by intros; exact Subsingleton.elim _ _ }
  let M := Φ.objPreimage D
  let e : Φ.obj M ≅ D := Φ.objObjPreimageIso D
  refine ⟨M.as, fun Y g hg ↦ Discrete.eq_of_hom (e.hom.hom (R.arrows.categoryMk g hg)), ?_⟩
  intro t ht
  have : Φ.obj ⟨t⟩ ≅ D :=
    Pseudofunctor.DescentData.isoMk (fun i ↦ Discrete.eqToIso (ht i.obj.hom i.property))
      (fun _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _)
  exact Discrete.eq_of_hom (Φ.preimage (this.hom ≫ e.inv))

variable {P} in
/-- XIII 0 (Giraud II 3.4): the stack in discrete categories associated with a presheaf of
sets `P` is a stack if and only if `P` is a sheaf. -/
theorem isStack_discreteStack_iff (J : GrothendieckTopology C) :
    (discreteStack P).IsStack J ↔ Presieve.IsSheaf J P := by
  refine ⟨fun h S R hR ↦ isSheafFor_of_isStackFor_discreteStack P
    ((discreteStack P).isStackFor' R hR), fun h ↦ ?_⟩
  exact Pseudofunctor.IsStack.of_isStackFor
    (fun S R hR ↦ isStackFor_discreteStack P (h R hR))

variable {P} in
/-- The stack in discrete categories attached to `P` is a gerbe if and only if `P` is a sheaf
which is locally a singleton: any two local sections are locally equal and sections exist
locally. -/
theorem isGerbe_discreteStack_iff (J : GrothendieckTopology C) :
    IsGerbe (discreteStack P) J ↔ Presieve.IsSheaf J P ∧
      (∀ ⦃S : C⦄ (x y : P.obj (op S)), ∃ R ∈ J S, ∀ ⦃T : C⦄ (g : T ⟶ S), R g →
        P.map g.op x = P.map g.op y) ∧
      (∀ S : C, ∃ R ∈ J S, ∀ ⦃T : C⦄ (g : T ⟶ S), R g → Nonempty (P.obj (op T))) := by
  constructor
  · intro h
    refine ⟨(isStack_discreteStack_iff J).1 h.toIsStack, fun S x y ↦ ?_, fun S ↦ ?_⟩
    · obtain ⟨R, hR, hxy⟩ := h.locallyIso (S := S) ⟨x⟩ ⟨y⟩
      exact ⟨R, hR, fun T g hg ↦ Discrete.eq_of_hom (hxy g hg).some.hom⟩
    · obtain ⟨R, hR, hne⟩ := h.locallyNonempty S
      exact ⟨R, hR, fun T g hg ↦ ⟨(hne g hg).some.as⟩⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact
      { toIsStack := (isStack_discreteStack_iff J).2 h₁
        isIso := fun φ ↦ ⟨⟨Discrete.eqToHom (Discrete.eq_of_hom φ).symm,
          Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
        locallyIso := fun x y ↦ by
          obtain ⟨R, hR, hxy⟩ := h₂ x.as y.as
          exact ⟨R, hR, fun T g hg ↦ ⟨Discrete.eqToIso (hxy g hg)⟩⟩
        locallyNonempty := fun S ↦ by
          obtain ⟨R, hR, hne⟩ := h₃ S
          exact ⟨R, hR, fun T g hg ↦ ⟨⟨(hne g hg).some⟩⟩⟩ }

/-- For the stack in discrete categories attached to `P`, the presheaf of isomorphism classes of
objects is `P` itself. -/
def isoClassesPresheafDiscreteStackIso : isoClassesPresheaf (discreteStack P) ≅ P :=
  NatIso.ofComponents (fun U ↦ Equiv.toIso
    { toFun := Quotient.lift (fun x ↦ Discrete.as x)
        (fun _ _ ⟨e⟩ ↦ Discrete.eq_of_hom e.hom)
      invFun x := Quotient.mk _ ⟨x⟩
      left_inv x := by
        induction x using Quotient.inductionOn with | h x => rfl
      right_inv _ := rfl }) (by
    intro U V g
    ext x
    induction x using Quotient.inductionOn with | h x => rfl)

/-- XIII 0: the sheaf `SF` of maximal subgerbes of a stack `F`. SGA recalls (Giraud III 2.1.4)
that the map `O ⟶ SF` sending an object to the maximal subgerbe it generates makes `SF` the sheaf
associated with the presheaf `O` of isomorphism classes of objects; this is taken as the
definition here (maximal subgerbes themselves are not formalized). -/
noncomputable def sheafOfMaximalSubgerbes (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', w}) : Sheaf J (Type w) :=
  (presheafToSheaf J (Type w)).obj (isoClassesPresheaf F)

/-- For the stack in discrete categories attached to a sheaf `P`, the sheaf of maximal subgerbes
is `P` itself. -/
noncomputable def sheafOfMaximalSubgerbesDiscreteStackIso (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)] (hP : Presheaf.IsSheaf J P) :
    sheafOfMaximalSubgerbes J (discreteStack P) ≅ ⟨P, hP⟩ :=
  (presheafToSheaf J (Type w)).mapIso (isoClassesPresheafDiscreteStackIso P) ≪≫
    (sheafificationIso ⟨P, hP⟩).symm

end Discrete

section Torsors

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat.{w}}

/-- XIII 0 (Giraud III 1.4.2): the torsors under a sheaf of groups `G` form a stack: the fibered
category `U ↦ Tors(C/U, G|U)` satisfies descent of morphisms and effective descent. -/
theorem isStack_torsorStack (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat)) :
    (Torsor.stack J G).IsStack J :=
  Torsor.isStack_stack hG

/-- XIII 0 (the stack of torsors under a sheaf of groups is a gerbe, first condition): every
morphism of `G`-torsors is an isomorphism (Giraud III 1.4.5). -/
theorem torsor_isIso {P Q : Torsor J G} (φ : P ⟶ Q) : IsIso φ :=
  inferInstance

/-- XIII 0 (the stack of torsors is a gerbe, second condition): any two torsors over `U` are
locally isomorphic. -/
theorem torsors_locallyIsomorphic (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat)) {U : C}
    (P Q : Torsor (J.over U) (PresheafOfGroups.over G U)) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Nonempty (P.overMap f ≅ Q.overMap f) := by
  obtain ⟨R, hR, h⟩ := H1.exists_covering_map_eq hG P.class Q.class
  exact ⟨R, hR, fun V f hf ↦ (Torsor.class_eq_class_iff _ _).1 (h f hf)⟩

/-- XIII 0 (the stack of torsors has a cartesian section): the trivial torsor, and a torsor is
isomorphic to it if and only if it has a global section (Giraud III 1.4.3). -/
theorem torsor_nonempty_iso_trivial_iff (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat))
    (P : Torsor J G) :
    Nonempty (P ≅ Torsor.trivial J G hG) ↔ Nonempty P.obj.sections :=
  Torsor.nonempty_iso_trivial_iff hG P

/-- XIII 0: the stack of torsors under a sheaf of groups is a gerbe: its fibers are groupoids, any
two torsors are locally isomorphic, and torsors exist locally (the trivial torsors). -/
theorem isGerbe_torsorStack (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat)) :
    IsGerbe (Torsor.stack J G) J where
  toIsStack := Torsor.isStack_stack hG
  isIso φ := Torsor.isIso φ
  locallyIso x y := torsors_locallyIsomorphic hG x y
  locallyNonempty S := ⟨⊤, J.top_mem S, fun T _ _ ↦
    ⟨Torsor.trivial (J.over T) (PresheafOfGroups.over G T) (H1.isSheaf_over hG T)⟩⟩

/-- XIII 0: the stack of torsors has a cartesian section, the trivial torsors: the restriction of
the trivial torsor over `U` to `V` is the trivial torsor over `V`. -/
def torsorStack_map_trivial (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat)) {U V : C}
    (g : V ⟶ U) :
    ((Torsor.stack J G).map g.op.toLoc).toFunctor.obj
        (Torsor.trivial (J.over U) (PresheafOfGroups.over G U) (H1.isSheaf_over hG U)) ≅
      Torsor.trivial (J.over V) (PresheafOfGroups.over G V) (H1.isSheaf_over hG V) :=
  H1.overMapTrivialIso hG g

end Torsors

end SGA.SGA1.ExposeXIII
