/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Fibers

/-!
# SGA 1, Exposé VI, VI.4.2–3: equivalences over a base

`BasedQuasiInverse F` is precisely the data in VI.4.2(i). We construct
these data from full faithfulness and vertical essential surjectivity,
and prove equivalence with VI.4.2(iii). The construction keeps the chosen
inverse objects in their required fibers; an arbitrary ordinary
quasi-inverse need not do this.
-/

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E]
  {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₂, u₂} E}

/-- VI.4.2(i): a quasi-inverse over `E`, with unit and counit over `E`. -/
structure BasedQuasiInverse (F : BasedFunctor X Y) where
  inverse : BasedFunctor Y X
  unitIso : BasedFunctor.id X ≅ BasedFunctor.comp F inverse
  counitIso : BasedFunctor.comp inverse F ≅ BasedFunctor.id Y

/-- VI.4.3: being an equivalence of categories over `E`. -/
def IsBasedEquivalence (F : BasedFunctor X Y) : Prop := Nonempty (BasedQuasiInverse F)

/-- VI.4.2(iii bis): every object has a preimage up to an isomorphism over its base identity. -/
def VerticallyEssSurj (F : BasedFunctor X Y) : Prop :=
  ∀ y : Y.obj, ∃ x : X.obj, ∃ e : F.obj x ≅ y, IsHomLift Y.p (𝟙 (Y.p.obj y)) e.hom

namespace BasedQuasiInverse

variable {F : BasedFunctor X Y} (Q : BasedQuasiInverse F)

/-- Forget the condition of lying over the base. -/
def toEquivalence : X.obj ≌ Y.obj :=
  CategoryTheory.Equivalence.mk F.toFunctor Q.inverse.toFunctor
    ((BasedNatTrans.forgetful X X).mapIso Q.unitIso)
    ((BasedNatTrans.forgetful Y Y).mapIso Q.counitIso)

/-- The inverse based functor is likewise a based equivalence. -/
def symm : BasedQuasiInverse Q.inverse where
  inverse := F
  unitIso := Q.counitIso.symm
  counitIso := Q.unitIso.symm

theorem isBasedEquivalence_inverse : IsBasedEquivalence Q.inverse := ⟨Q.symm⟩

include Q in
/-- VI.4.2(i) implies vertical essential surjectivity. -/
theorem verticallyEssSurj : VerticallyEssSurj F := by
  intro y
  exact ⟨Q.inverse.obj y,
    ((BasedNatTrans.forgetful Y Y).mapIso Q.counitIso).app y,
    Q.counitIso.hom.isHomLift' y⟩

/-- VI.4.2(i): a based quasi-inverse restricts to every fiber. -/
def fiberEquivalence (S : E) : Fiber X.p S ≌ Fiber Y.p S :=
  CategoryTheory.Equivalence.mk (fiberMap F S) (fiberMap Q.inverse S)
    ((fiberHom (X := X) (Y := X) S).mapIso Q.unitIso)
    ((fiberHom (X := Y) (Y := Y) S).mapIso Q.counitIso)

/-- VI.4.2(i) is preserved by arbitrary change of base. -/
def changeOfBase {D : Type u₃} [Category.{v₃} D] (L : D ⥤ E) :
    BasedQuasiInverse (changeOfBaseMap F L) where
  inverse := changeOfBaseMap Q.inverse L
  unitIso := (changeOfBaseHom (X := X) (Y := X) L).mapIso Q.unitIso
  counitIso := (changeOfBaseHom (X := Y) (Y := Y) L).mapIso Q.counitIso

end BasedQuasiInverse

section Choices

variable (F : BasedFunctor X Y)
  (g : Y.obj → X.obj) (ε : ∀ y, F.obj (g y) ≅ y)
  (hε : ∀ y, IsHomLift Y.p (𝟙 (Y.p.obj y)) (ε y).hom)

include F ε hε in
private theorem inverseChoice_obj_over (y : Y.obj) : X.p.obj (g y) = Y.p.obj y := by
  have := hε y
  exact (F.w_obj (g y)).symm.trans
    (IsHomLift.domain_eq Y.p (𝟙 (Y.p.obj y)) (ε y).hom)

variable [F.toFunctor.Full] [F.toFunctor.Faithful]

include hε in
private theorem inverseChoice_map_over {y z : Y.obj} (f : y ⟶ z) :
    IsHomLift X.p (Y.p.map f) ((inverseOfChoices F.toFunctor g ε).map f) := by
  have := hε y
  have := hε z
  have : IsHomLift Y.p (𝟙 (Y.p.obj z)) (ε z).inv := by infer_instance
  have : IsHomLift Y.p (Y.p.map f) (f ≫ (ε z).inv) := by infer_instance
  have : IsHomLift Y.p (Y.p.map f) ((ε y).hom ≫ f ≫ (ε z).inv) :=
    IsHomLift.comp_lift_id_left Y.p (Y.p.map f) (f ≫ (ε z).inv) (ε y).hom
  exact preimage_isHomLift F (Y.p.map f) ((ε y).hom ≫ f ≫ (ε z).inv)

/-- The ordinary inverse constructed in VI.1 commutes strictly with the base. -/
noncomputable def basedInverseOfChoices : BasedFunctor Y X where
  toFunctor := inverseOfChoices F.toFunctor g ε
  w := by
    let i : inverseOfChoices F.toFunctor g ε ⋙ X.p ≅ Y.p :=
      NatIso.ofComponents (fun y ↦ eqToIso (inverseChoice_obj_over F g ε hε y))
        (fun {y z} f ↦ by
          have := inverseChoice_map_over F g ε hε f
          exact (IsHomLift.commSq X.p (Y.p.map f)
            ((inverseOfChoices F.toFunctor g ε).map f)).w)
    exact Functor.ext_of_iso i (inverseChoice_obj_over F g ε hε)

/-- VI.4.2(iii bis) ⇒ (i): extend vertical object preimages to a based quasi-inverse. -/
noncomputable def basedQuasiInverseOfChoices : BasedQuasiInverse F where
  inverse := basedInverseOfChoices F g ε hε
  unitIso := BasedNatIso.mkNatIso (unitOfChoices F.toFunctor g ε) (fun x ↦ by
    change IsHomLift X.p (𝟙 (X.p.obj x)) (F.toFunctor.preimage (ε (F.obj x)).inv)
    have := hε (F.obj x)
    have : IsHomLift Y.p (𝟙 (X.p.obj x)) (ε (F.obj x)).inv := by
      rw [← F.w_obj x]
      infer_instance
    exact preimage_isHomLift F _ _)
  counitIso := BasedNatIso.mkNatIso (counitOfChoices F.toFunctor g ε) hε

end Choices

/-- VI.4.2(i) ⇔ (iii bis), and hence a practical criterion for VI.4.3. -/
theorem isBasedEquivalence_iff (F : BasedFunctor X Y) : IsBasedEquivalence F ↔
    F.toFunctor.Full ∧ F.toFunctor.Faithful ∧ VerticallyEssSurj F := by
  constructor
  · rintro ⟨Q⟩
    exact ⟨Q.toEquivalence.full_functor, Q.toEquivalence.faithful_functor,
      Q.verticallyEssSurj⟩
  · rintro ⟨hfull, hfaithful, hess⟩
    choose g ε hε using hess
    exact ⟨basedQuasiInverseOfChoices F g ε hε⟩

/-- VI.4.2(i) ⇔ (iii): an ordinary equivalence whose restrictions to all
fibers are equivalences is exactly an equivalence over the base. -/
theorem isBasedEquivalence_iff_fiberwise (F : BasedFunctor X Y) :
    IsBasedEquivalence F ↔ F.toFunctor.IsEquivalence ∧ ∀ S, (fiberMap F S).IsEquivalence := by
  constructor
  · rintro ⟨Q⟩
    exact ⟨Q.toEquivalence.isEquivalence_functor,
      fun S ↦ (Q.fiberEquivalence S).isEquivalence_functor⟩
  · rintro ⟨hF, hfib⟩
    apply (isBasedEquivalence_iff F).mpr
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro y
    let b : Fiber Y.p (Y.p.obj y) := ⟨y, rfl⟩
    let a := (fiberMap F (Y.p.obj y)).objPreimage b
    let e := (fiberMap F (Y.p.obj y)).objObjPreimageIso b
    exact ⟨a.val, Fiber.fiberInclusion.mapIso e, e.hom.property⟩

/-- VI.4.4: transportability means that every base isomorphism lifts to an
isomorphism with prescribed source. -/
def IsTransportable {C : Type u₁} [Category.{v₁} C] (p : C ⥤ E) : Prop :=
  ∀ (x : C) (S : E) (e : p.obj x ≅ S),
    ∃ (x' : C) (e' : x ≅ x'), IsHomLift p e.hom e'.hom

/-- VI.4.4: an ordinary equivalence from a transportable category is a based equivalence. -/
theorem isBasedEquivalence_of_transportable (F : BasedFunctor X Y)
    [F.toFunctor.IsEquivalence] (hp : IsTransportable X.p) : IsBasedEquivalence F := by
  apply (isBasedEquivalence_iff F).mpr
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro y
  let x := F.toFunctor.objPreimage y
  let e := F.toFunctor.objObjPreimageIso y
  let b : X.p.obj x ≅ Y.p.obj y := (eqToIso (F.w_obj x)).symm ≪≫ Y.p.mapIso e
  have he : IsHomLift Y.p b.hom e.hom := by
    apply IsHomLift.of_fac Y.p b.hom e.hom (F.w_obj x) rfl
    simp [b]
  obtain ⟨x', e', he'⟩ := hp x (Y.p.obj y) b
  have hFe' : IsHomLift Y.p b.hom (F.toFunctor.mapIso e').hom :=
    BasedFunctor.preserves_isHomLift F b.hom e'.hom
  have hFe'inv : IsHomLift Y.p b.inv (F.toFunctor.mapIso e').inv :=
    IsHomLift.inv_lift_inv Y.p b (F.toFunctor.mapIso e')
  refine ⟨x', (F.toFunctor.mapIso e').symm ≪≫ e, ?_⟩
  have h := IsHomLift.comp Y.p b.inv b.hom (F.toFunctor.mapIso e').inv e.hom
  simpa using h

namespace BasedQuasiInverse

variable {F : BasedFunctor X Y} (Q : BasedQuasiInverse F)
  (Z : BasedCategory.{v₃, u₃} E)

/-- VI.4.5: precomposition with a based equivalence is an equivalence
of based-functor categories. -/
def precompEquivalence : BasedFunctor Y Z ≌ BasedFunctor X Z :=
  CategoryTheory.Equivalence.mk (basedPrecomp F) (basedPrecomp Q.inverse)
    (NatIso.ofComponents
      (fun G ↦ (basedPostcomp G).mapIso Q.counitIso.symm)
      (fun {G H} α ↦ by
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext y
        change α.app y ≫ H.map (Q.counitIso.inv.app y) =
          G.map (Q.counitIso.inv.app y) ≫ α.app (F.obj (Q.inverse.obj y))
        exact (α.naturality (Q.counitIso.inv.app y)).symm))
    (NatIso.ofComponents
      (fun G ↦ (basedPostcomp G).mapIso Q.unitIso.symm)
      (fun {G H} α ↦ by
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext x
        change α.app (Q.inverse.obj (F.obj x)) ≫ H.map (Q.unitIso.inv.app x) =
          G.map (Q.unitIso.inv.app x) ≫ α.app x
        exact (α.naturality (Q.unitIso.inv.app x)).symm))

/-- VI.4.5: postcomposition with a based equivalence is an equivalence
of based-functor categories. -/
def postcompEquivalence : BasedFunctor Z X ≌ BasedFunctor Z Y :=
  CategoryTheory.Equivalence.mk (basedPostcomp F) (basedPostcomp Q.inverse)
    (NatIso.ofComponents
      (fun G ↦ (basedPrecomp G).mapIso Q.unitIso)
      (fun {G H} α ↦ by
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext z
        change α.app z ≫ Q.unitIso.hom.app (H.obj z) =
          Q.unitIso.hom.app (G.obj z) ≫ Q.inverse.map (F.map (α.app z))
        exact Q.unitIso.hom.naturality (α.app z)))
    (NatIso.ofComponents
      (fun G ↦ (basedPrecomp G).mapIso Q.counitIso)
      (fun {G H} α ↦ by
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext z
        change F.map (Q.inverse.map (α.app z)) ≫ Q.counitIso.hom.app (H.obj z) =
          Q.counitIso.hom.app (G.obj z) ≫ α.app z
        exact Q.counitIso.hom.naturality (α.app z)))

end BasedQuasiInverse

section SmallBase

variable {B : Type u} [SmallCategory B]
  {U : BasedCategory.{v₁, u₁} B} {V : BasedCategory.{v₂, u₂} B}

/-- VI.4.2(i) ⇔ (ii): a based functor is an equivalence over the base iff
every change of base is an ordinary equivalence. As in SGA, the test bases
are small categories in the universe containing the base. -/
theorem isBasedEquivalence_iff_all_baseChange (F : BasedFunctor U V) :
    IsBasedEquivalence F ↔
      ∀ (D : Type u) [SmallCategory D] (L : D ⥤ B),
        (changeOfBaseMap F L).toFunctor.IsEquivalence := by
  constructor
  · rintro ⟨Q⟩ D _ L
    exact (Q.changeOfBase L).toEquivalence.isEquivalence_functor
  · intro h
    have hF' : (changeOfBaseMap F (𝟭 B)).toFunctor.IsEquivalence := h B (𝟭 B)
    -- `SmallCategory B` is `Category.{u} B`, while the ambient morphism universe is `v`.
    have hV : (BaseChange.fst V.p (𝟭 B)).IsEquivalence :=
      @identityBaseChange_isEquivalence.{u, v₂, u, u₂}
        B inferInstance V.obj inferInstance V.p
    have hU : (BaseChange.fst U.p (𝟭 B)).IsEquivalence :=
      @identityBaseChange_isEquivalence.{u, v₁, u, u₁}
        B inferInstance U.obj inferInstance U.p
    have hcomp : (changeOfBaseMap F (𝟭 B)).toFunctor ⋙ BaseChange.fst V.p (𝟭 B) =
        BaseChange.fst U.p (𝟭 B) ⋙ F.toFunctor := rfl
    have hFcomp : (BaseChange.fst U.p (𝟭 B) ⋙ F.toFunctor).IsEquivalence :=
      hcomp ▸ @Functor.isEquivalence_trans _ _ _ _ _ _
        (changeOfBaseMap F (𝟭 B)).toFunctor (BaseChange.fst V.p (𝟭 B)) hF' hV
    have : F.toFunctor.IsEquivalence :=
      @Functor.isEquivalence_of_comp_left _ _ _ _ _ _
        (BaseChange.fst U.p (𝟭 B)) F.toFunctor hU hFcomp
    apply (isBasedEquivalence_iff F).mpr
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro y
    let L : Discrete PUnit.{u + 1} ⥤ B := (Functor.const _).obj (V.p.obj y)
    have := h (Discrete PUnit.{u + 1}) L
    let F' := (changeOfBaseMap F L).toFunctor
    let b : BaseChange V.p L := ⟨(y, Discrete.mk PUnit.unit), rfl⟩
    let a := F'.objPreimage b
    let e := F'.objObjPreimageIso b
    exact ⟨a.val.1, (BaseChange.fst V.p L).mapIso e, e.hom.over⟩

end SmallBase

end SGA.SGA1.ExposeVI
