/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Tactic.IrreducibleDef
import SGA.Foundations.Limits.EtaleSectionsGluing
import SGA.Foundations.EtaleStalkBaseChange
import SGA.Foundations.StrictLocalizationFunctorial
import SGA.Foundations.Etale.LocalAcyclicityBaseChange

/-!
# Base change morphisms on stalks, through strict localizations

Let `h ≫ f = f' ≫ g` be a commutative square (`X' ⟶ X` over `Y' ⟶ Y`), `F` an étale sheaf of sets
on `X` and `ȳ'` a geometric point of `Y'`. Write `Ỹ' = Spec 𝒪^{sh}_{Y',ȳ'}` and
`Ỹ = Spec 𝒪^{sh}_{Y,g(ȳ')}` for the strict localizations, `P' = Ỹ' ×_{Y'} X'` and `P = Ỹ ×_Y X`.
The morphism of strict localizations `Hom.strictLocalizationMap g ȳ' : Ỹ' ⟶ Ỹ` induces
`strictLocalizationPullbackMap : P' ⟶ P` (cartesian over `Ỹ' ⟶ Ỹ` when the square is,
`isPullback_strictLocalizationPullbackMap`), hence a restriction map
`Γ(P, F) ⟶ Γ(P', h^* F)` (`etaleSquareRestrict`, defined for any commutative square).

The main result (`pushforwardStalkToStrictLocalization_sheafFiber_etaleBaseChangeMap`) says that,
through the maps `(f_* F)_{s̄} ⟶ Γ(Ỹ ×_Y X, F)` of SGA 4 VIII 5.2
(`Hom.pushforwardStalkToStrictLocalization`), the stalk at `ȳ'` of the base change
morphism `g^* f_* F ⟶ f'_* h^* F` is this restriction. Consequences:

* `mono_etaleBaseChangeMap_of_forall_injective`: for `f` quasi-compact, the base change morphism is
  a monomorphism if all the restrictions `Γ(P, F) ⟶ Γ(P', h^* F)` are injective (only the
  injectivity half of SGA 4 VIII 5.2 is used);
* `isIso_etaleBaseChangeMap_of_forall_bijective` (given the surjectivity half of SGA 4 VIII 5.2
  at `g(ȳ')`), and `isIso_etaleBaseChangeMap_of_forall_bijective_of_quasiSeparated` (`f` qcqs,
  using SGA 4 VIII 5.2, `Scheme.Hom.bijective_pushforwardStalkToStrictLocalization`): it is an
  isomorphism if they are bijective.

So the formation of `f_* F` commutes with a base change as soon as the sections of `F` over the
"strictly local" pieces `Ỹ ×_Y X` do; this is how SGA 4 XII, XV and SGA 1 XIII §3 reduce base change
statements to strictly local bases. The restriction is bijective when `Ỹ' ⟶ Ỹ` is flat,
quasi-compact and geometrically connected (Stacks 0A3H,
`bijective_etaleSectionsRestrict_of_geometricallyConnected`, `bijective_etaleSquareRestrict`), e.g.
when `Y` is the spectrum of a field: then `Ỹ` is the spectrum of a separably closed field
(`Hom.bijective_residue_strictLocalization`, `isField_stalk_spec`).

The comparison of inverse images along two equal morphisms goes through the isomorphism
`etalePullbackCongr`, an `irreducible_def`: with a plain `eqToIso` the kernel tries to reduce the
transport, and so to decide whether two inverse image sheaves are definitionally equal, which does
not terminate in practice.

## References

* [SGA 4, Exposé VIII, 5.2][sga4]
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
-/

universe u

open CategoryTheory Limits Opposite

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry.Scheme

section SectionAlong

variable {T X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (Type u))

/-- The morphism `T ⟶ T ×_X A` of étale `T`-schemes given by a morphism `a : T ⟶ A` over `X`. -/
def Etale.sectionOfHom (u : T ⟶ X) (A : X.Etale) (a : T ⟶ A.left) (ha : a ≫ A.hom = u) :
    Etale.top T ⟶ (Etale.pullback u).obj A :=
  MorphismProperty.Over.homMk (pullback.lift a (𝟙 T) (ha.trans (Category.id_comp u).symm))
    (pullback.lift_snd _ _ _) trivial

@[reassoc (attr := simp)]
lemma Etale.sectionOfHom_left_fst (u : T ⟶ X) (A : X.Etale) (a : T ⟶ A.left)
    (ha : a ≫ A.hom = u) :
    (Etale.sectionOfHom u A a ha).left ≫ pullback.fst A.hom u = a :=
  pullback.lift_fst _ _ _

/-- The section over `T` of the inverse image `u^* F` along `u : T ⟶ X` given by a section
`t ∈ F(A)` over an étale `X`-scheme `A` and a morphism `a : T ⟶ A` over `X`. -/
def sectionAlong (u : T ⟶ X) (A : X.Etale) (a : T ⟶ A.left) (ha : a ≫ A.hom = u)
    (t : F.obj.obj (op A)) : ((etalePullback u).obj F).obj.obj (op (Etale.top T)) :=
  ((etalePullback u).obj F).obj.map (Etale.sectionOfHom u A a ha).op
    (((etaleAdjunction u).unit.app F).hom.app (op A) t)

/-- A morphism `top T ⟶ T ×_X A` of étale `T`-schemes is the section given by its first
projection. -/
lemma Etale.eq_sectionOfHom (u : T ⟶ X) (A : X.Etale) (φ : Etale.top T ⟶ (Etale.pullback u).obj A) :
    φ = Etale.sectionOfHom u A (φ.left ≫ pullback.fst A.hom u)
      (by rw [Category.assoc, pullback.condition, ← Category.assoc]
          erw [MorphismProperty.Over.w φ]
          exact Category.id_comp u) := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp
  · change φ.left ≫ ((Etale.pullback u).obj A).hom = _ ≫ ((Etale.pullback u).obj A).hom
    exact (MorphismProperty.Over.w φ).trans (MorphismProperty.Over.w
      (Etale.sectionOfHom u A (φ.left ≫ pullback.fst A.hom u) _)).symm

lemma sectionAlong_congr (u : T ⟶ X) (A : X.Etale) {a a' : T ⟶ A.left} (ha : a ≫ A.hom = u)
    (h : a = a') (t : F.obj.obj (op A)) :
    sectionAlong F u A a ha t = sectionAlong F u A a' (h ▸ ha) t := by
  subst h
  rfl

/-- Naturality of `sectionAlong` in the étale `X`-scheme. -/
lemma sectionAlong_map (u : T ⟶ X) {A B : X.Etale} (c : B ⟶ A) (b : T ⟶ B.left)
    (hb : b ≫ B.hom = u) (t : F.obj.obj (op A)) :
    sectionAlong F u B b hb (F.obj.map c.op t) =
      sectionAlong F u A (b ≫ c.left)
        (by rw [Category.assoc, MorphismProperty.Over.w c]; exact hb) t := by
  simp only [sectionAlong]
  erw [NatTrans.naturality_apply ((etaleAdjunction u).unit.app F).hom c.op]
  change ((etalePullback u).obj F).obj.map _ (((etalePullback u).obj F).obj.map _ _) = _
  rw [← Functor.map_comp_apply]
  congr 2
  congr 1
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op, Functor.op_map]
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · rw [MorphismProperty.Comma.comp_left, Category.assoc, Etale.pullback_map_left_fst]
    simp [Etale.sectionOfHom]
  · rw [MorphismProperty.Comma.comp_left, Category.assoc, Etale.pullback_map_left_snd]
    simp [Etale.sectionOfHom]

/-- The unit of `(b ≫ u)^* ⊣ (b ≫ u)_*` is the composite of the units of `u` and `b`, through
`etalePullbackComp b u : b^* ∘ u^* ≅ (b ≫ u)^*`. -/
lemma etalePullbackComp_hom_app_unit_unit {T' : Scheme.{u}} (b : T' ⟶ T) (u : T ⟶ X)
    (A : X.Etale) (t : F.obj.obj (op A)) :
    ((etalePullbackComp b u).hom.app F).hom.app
        (op ((Etale.pullback b).obj ((Etale.pullback u).obj A)))
      (((etaleAdjunction b).unit.app ((etalePullback u).obj F)).hom.app
        (op ((Etale.pullback u).obj A)) (((etaleAdjunction u).unit.app F).hom.app (op A) t)) =
    ((etalePullback (b ≫ u)).obj F).obj.map ((Etale.pullbackComp b u).inv.app A).op
      (((etaleAdjunction (b ≫ u)).unit.app F).hom.app (op A) t) := by
  have H := unit_conjugateEquiv (etaleAdjunction (b ≫ u))
    ((etaleAdjunction u).comp (etaleAdjunction b)) (etalePullbackComp b u).hom F
  rw [conjugateEquiv_etalePullbackComp_hom, Adjunction.comp_unit_app] at H
  have H' := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (·.hom) H) (op A)) t
  exact H'.symm

/-- The inverse image along `b : T' ⟶ T` of a `sectionAlong`: composition of the units of `u`
and `b`. -/
lemma etalePullbackComp_hom_app_sectionAlong {T' : Scheme.{u}} (b : T' ⟶ T) (u : T ⟶ X)
    (A : X.Etale) (a : T' ⟶ ((Etale.pullback u).obj A).left)
    (ha : a ≫ ((Etale.pullback u).obj A).hom = b) (t : F.obj.obj (op A)) :
    ((etalePullbackComp b u).hom.app F).hom.app (op (Etale.top T'))
        (sectionAlong ((etalePullback u).obj F) b ((Etale.pullback u).obj A) a ha
          (((etaleAdjunction u).unit.app F).hom.app (op A) t)) =
      sectionAlong F (b ≫ u) A (a ≫ pullback.fst A.hom u)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc]
            erw [ha]) t := by
  simp only [sectionAlong]
  erw [NatTrans.naturality_apply ((etalePullbackComp b u).hom.app F).hom]
  erw [etalePullbackComp_hom_app_unit_unit]
  change ((etalePullback (b ≫ u)).obj F).obj.map _
    (((etalePullback (b ≫ u)).obj F).obj.map _ _) = _
  rw [← Functor.map_comp_apply]
  congr 2
  congr 1
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · rw [MorphismProperty.Comma.comp_left, Category.assoc,
      Etale.pullbackComp_inv_app_left_fst]
    simp [Etale.sectionOfHom]
  · change _ ≫ ((Etale.pullback (b ≫ u)).obj A).hom = _ ≫ ((Etale.pullback (b ≫ u)).obj A).hom
    rw [MorphismProperty.Over.w, MorphismProperty.Over.w]

/-- Restriction of global sections along `b : T' ⟶ T`: `Γ(T, G) ⟶ Γ(T', b^* G)`. -/
def etaleSectionsRestrict {T' : Scheme.{u}} (b : T' ⟶ T) (G : Sheaf T.smallEtaleTopology (Type u))
    (x : G.obj.obj (op (Etale.top T))) : ((etalePullback b).obj G).obj.obj (op (Etale.top T')) :=
  sectionAlong G b (Etale.top T) b (Category.comp_id b) x

/-- Restriction of a `sectionAlong`. -/
lemma etalePullbackComp_hom_app_etaleSectionsRestrict {T' : Scheme.{u}} (b : T' ⟶ T) (u : T ⟶ X)
    (A : X.Etale) (a : T ⟶ A.left) (ha : a ≫ A.hom = u) (t : F.obj.obj (op A)) :
    ((etalePullbackComp b u).hom.app F).hom.app (op (Etale.top T'))
        (etaleSectionsRestrict b ((etalePullback u).obj F) (sectionAlong F u A a ha t)) =
      sectionAlong F (b ≫ u) A (b ≫ a) (by rw [Category.assoc, ha]) t := by
  have e : sectionAlong F u A a ha t = ((etalePullback u).obj F).obj.map
      (Etale.sectionOfHom u A a ha).op (((etaleAdjunction u).unit.app F).hom.app (op A) t) := rfl
  rw [etaleSectionsRestrict, e]
  erw [sectionAlong_map]
  rw [etalePullbackComp_hom_app_sectionAlong]
  apply sectionAlong_congr
  simp

/-- The isomorphism `u^* F ≅ u'^* F` given by an equality `u = u'`. (A definition, so that the
transport is always the same term: the kernel cannot compare two different proofs inside an
`eqToHom` between sheaves which are not definitionally equal.) -/
irreducible_def etalePullbackCongr {u u' : T ⟶ X} (e : u = u') :
    (etalePullback u).obj F ≅ (etalePullback u').obj F :=
  eqToIso (by rw [e])

/-- Restriction of global sections along a composite: `Γ(T, G) ⟶ Γ(T', b^* G) ⟶ Γ(T'', c^* b^* G)`
is the restriction along `c ≫ b`, through `etalePullbackComp c b`. -/
lemma etalePullbackComp_hom_app_etaleSectionsRestrict_etaleSectionsRestrict {T' T'' : Scheme.{u}}
    (c : T'' ⟶ T') (b : T' ⟶ T) (G : Sheaf T.smallEtaleTopology (Type u))
    (x : G.obj.obj (op (Etale.top T))) :
    ((etalePullbackComp c b).hom.app G).hom.app (op (Etale.top T''))
        (etaleSectionsRestrict c ((etalePullback b).obj G) (etaleSectionsRestrict b G x)) =
      etaleSectionsRestrict (c ≫ b) G x :=
  etalePullbackComp_hom_app_etaleSectionsRestrict G c b (Etale.top T) b (Category.comp_id b) x

/-- Transport of a `sectionAlong` along an equality of morphisms. -/
lemma etalePullbackCongr_hom_app_sectionAlong {u u' : T ⟶ X} (e : u = u') (A : X.Etale)
    (a : T ⟶ A.left) (ha : a ≫ A.hom = u) (t : F.obj.obj (op A)) :
    ((etalePullbackCongr F e).hom.hom.app (op (Etale.top T)))
        (sectionAlong F u A a ha t) = sectionAlong F u' A a (ha.trans e) t := by
  subst e
  rw [etalePullbackCongr_def]
  rfl

/-- Restriction of sections along a commutative square `q ≫ p = p' ≫ h`:
`Γ(P, p^* F) ⟶ Γ(P', q^* p^* F) = Γ(P', p'^* h^* F)`. -/
def etaleSquareRestrict {P P' X' : Scheme.{u}} (p : P ⟶ X) (p' : P' ⟶ X') (h : X' ⟶ X)
    (q : P' ⟶ P) (e : q ≫ p = p' ≫ h)
    (x : ((etalePullback p).obj F).obj.obj (op (Etale.top P))) :
    ((etalePullback p').obj ((etalePullback h).obj F)).obj.obj (op (Etale.top P')) :=
  ((etalePullbackComp p' h).inv.app F).hom.app (op (Etale.top P'))
    ((etalePullbackCongr F e).hom.hom.app (op (Etale.top P'))
      (((etalePullbackComp q p).hom.app F).hom.app (op (Etale.top P'))
        (etaleSectionsRestrict q ((etalePullback p).obj F) x)))

lemma etalePullbackComp_hom_app_inv_app_apply {T' T : Scheme.{u}} (b : T' ⟶ T) (u : T ⟶ X)
    (W : T'.Etale) (z : ((etalePullback (b ≫ u)).obj F).obj.obj (op W)) :
    ((etalePullbackComp b u).hom.app F).hom.app (op W)
      (((etalePullbackComp b u).inv.app F).hom.app (op W) z) = z := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app]
  rfl

lemma etalePullbackComp_inv_app_hom_app_apply {T' T : Scheme.{u}} (b : T' ⟶ T) (u : T ⟶ X)
    (W : T'.Etale) (z : ((etalePullback b).obj ((etalePullback u).obj F)).obj.obj (op W)) :
    ((etalePullbackComp b u).inv.app F).hom.app (op W)
      (((etalePullbackComp b u).hom.app F).hom.app (op W) z) = z := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app]
  rfl

/-- `etaleSquareRestrict` of a `sectionAlong`. -/
lemma etalePullbackComp_hom_app_etaleSquareRestrict {P P' X' : Scheme.{u}} (p : P ⟶ X)
    (p' : P' ⟶ X') (h : X' ⟶ X) (q : P' ⟶ P) (e : q ≫ p = p' ≫ h) (A : X.Etale)
    (a : P ⟶ A.left) (ha : a ≫ A.hom = p) (t : F.obj.obj (op A)) :
    ((etalePullbackComp p' h).hom.app F).hom.app (op (Etale.top P'))
        (etaleSquareRestrict F p p' h q e (sectionAlong F p A a ha t)) =
      sectionAlong F (p' ≫ h) A (q ≫ a) (by rw [Category.assoc, ha, e]) t := by
  rw [etaleSquareRestrict, etalePullbackComp_hom_app_inv_app_apply,
    etalePullbackComp_hom_app_etaleSectionsRestrict, etalePullbackCongr_hom_app_sectionAlong]

end SectionAlong

section StrictLocalization

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}
  (w : h ≫ f = f' ≫ g) (F : Sheaf X.smallEtaleTopology (Type u)) {Ω : Type u} [Field Ω]
  (y : Spec (.of Ω) ⟶ Y')

/-- The morphism `Ỹ' ×_{Y'} X' ⟶ Ỹ ×_Y X` induced by the morphism of strict localizations
`Ỹ' = Spec 𝒪^{sh}_{Y',ȳ'} ⟶ Ỹ = Spec 𝒪^{sh}_{Y,g(ȳ')}` and `h : X' ⟶ X`. -/
def strictLocalizationPullbackMap :
    pullback y.fromSpecStrictLocalization f' ⟶ pullback (y ≫ g).fromSpecStrictLocalization f :=
  pullback.map _ _ _ _ (g.strictLocalizationMap y) h g
    (Hom.strictLocalizationMap_fromSpecStrictLocalization y g).symm w.symm

@[reassoc (attr := simp)]
lemma strictLocalizationPullbackMap_fst :
    strictLocalizationPullbackMap w y ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ g.strictLocalizationMap y :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma strictLocalizationPullbackMap_snd :
    strictLocalizationPullbackMap w y ≫ pullback.snd _ _ = pullback.snd _ _ ≫ h :=
  pullback.lift_snd _ _ _

/-- For a cartesian square `X' = X ×_Y Y'`, the square
`Ỹ' ×_{Y'} X' ⟶ Ỹ ×_Y X` over `Ỹ' ⟶ Ỹ` (strict localizations at `ȳ'` and `g(ȳ')`) is cartesian:
both are `Ỹ' ×_Y X`. -/
lemma isPullback_strictLocalizationPullbackMap (hsq : IsPullback h f' f g) :
    IsPullback (strictLocalizationPullbackMap hsq.w y) (pullback.fst _ _) (pullback.fst _ _)
      (g.strictLocalizationMap y) := by
  have outer := (IsPullback.of_hasPullback y.fromSpecStrictLocalization f').flip.paste_horiz hsq
  have right := (IsPullback.of_hasPullback (y ≫ g).fromSpecStrictLocalization f).flip
  refine IsPullback.of_right ?_ (strictLocalizationPullbackMap_fst hsq.w y) right
  rw [strictLocalizationPullbackMap_snd, Hom.strictLocalizationMap_fromSpecStrictLocalization]
  exact outer

variable [IsSepClosed Ω]

/-- The étale neighbourhood `(Y' ×_Y V, (ȳ', v))` of `ȳ'` and the étale neighbourhood `(V, v)` of
`g ∘ ȳ'` induce compatible morphisms from the strict localizations. -/
lemma Hom.etaleNbhdHom_pullback_fst (V : Y.Etale) (v : (pointSmallEtale (y ≫ g)).fiber.obj V) :
    y.etaleNbhdHom ((Etale.pullback g).obj V) ((pointSmallEtaleFiberHom g y).app V v) ≫
        pullback.fst V.hom g = g.strictLocalizationMap y ≫ (y ≫ g).etaleNbhdHom V v := by
  have hc : (g.strictLocalizationMap y ≫ (y ≫ g).etaleNbhdHom V v) ≫ V.hom =
      y.fromSpecStrictLocalization ≫ g := by
    rw [Category.assoc, Hom.etaleNbhdHom_comp_hom,
      Hom.strictLocalizationMap_fromSpecStrictLocalization]
  let φ := pullback.lift _ _ hc
  have : y.etaleNbhdHom ((Etale.pullback g).obj V) ((pointSmallEtaleFiberHom g y).app V v) = φ := by
    refine y.etaleNbhdHom_eq (V := (Etale.pullback g).obj V) φ (pullback.lift_snd _ _ _) ?_
    apply pullback.hom_ext
    · simp [φ, pointSmallEtaleFiberHom]
    · simp [φ, pointSmallEtaleFiberHom]
  rw [this, pullback.lift_fst]


/-- The section of the inverse image of `F` on `Ỹ ×_Y X` given by the image of a germ
(`Hom.pushforwardStalkToStrictLocalization`) is a `sectionAlong`. -/
lemma Hom.pushforwardStalkToStrictLocalization_toPresheafFiber_eq_sectionAlong {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (Type u)) (s : Spec (.of Ω) ⟶ Y) (V : Y.Etale)
    (v : (pointSmallEtale s).fiber.obj V) (t : F.obj.obj (op ((Etale.pullback f).obj V))) :
    f.pushforwardStalkToStrictLocalization s F
        ((pointSmallEtale s).toPresheafFiber V v ((etalePushforward f).obj F).obj t) =
      sectionAlong F (pullback.snd s.fromSpecStrictLocalization f) ((Etale.pullback f).obj V)
        (f.strictLocalizationPullbackHom s V v) (Hom.strictLocalizationPullbackHom_snd f s V v) t :=
  Hom.pushforwardStalkToStrictLocalization_toPresheafFiber f s F V v t

/-- The first half of `pushforwardStalkToStrictLocalization_sheafFiber_etaleBaseChangeMap`. -/
private lemma pushforwardStalkToStrictLocalization_sheafFiber_etaleBaseChangeMap_aux (V : Y.Etale)
    (v : (pointSmallEtale (y ≫ g)).fiber.obj V) (t : F.obj.obj (op ((Etale.pullback f).obj V))) :
    f'.pushforwardStalkToStrictLocalization y ((etalePullback h).obj F)
        ((pointSmallEtale y).sheafFiber.map ((etaleBaseChangeMap w).app F)
          ((sheafFiberEtalePullbackIso g y).hom.app ((etalePushforward f).obj F)
            ((pointSmallEtale (y ≫ g)).toPresheafFiber V v ((etalePushforward f).obj F).obj t))) =
      sectionAlong ((etalePullback h).obj F) (pullback.snd y.fromSpecStrictLocalization f')
        ((Etale.pullback h).obj ((Etale.pullback f).obj V))
        (Hom.strictLocalizationPullbackHom f' y ((Etale.pullback g).obj V)
            ((pointSmallEtaleFiberHom g y).app V v) ≫
          ((Etale.baseChangeComparison w).app V).left)
        (by rw [Category.assoc]
            exact (congrArg _ (Etale.baseChangeComparisonHom_snd' w V)).trans
              (Hom.strictLocalizationPullbackHom_snd _ _ _ _))
        (((etaleAdjunction h).unit.app F).hom.app (op ((Etale.pullback f).obj V)) t) := by
  rw [sheafFiberEtalePullbackIso_hom_app_toPresheafFiber]
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  erw [etaleBaseChangeMap_app_unit]
  erw [Hom.pushforwardStalkToStrictLocalization_toPresheafFiber_eq_sectionAlong]
  erw [sectionAlong_map]
  rfl

/-- **The stalk of the base change morphism through strict localizations.** For a commutative
square `h ≫ f = f' ≫ g`, a geometric point `ȳ'` of `Y'` and a germ `a` at `g(ȳ')` of `f_* F`, the
image under `Hom.pushforwardStalkToStrictLocalization f'` of the image of `a` by the stalk at `ȳ'`
of the base change morphism `g^* f_* F ⟶ f'_* h^* F` is the restriction (`etaleSquareRestrict`)
along `strictLocalizationPullbackMap : Ỹ' ×_{Y'} X' ⟶ Ỹ ×_Y X` of the image of `a` under
`Hom.pushforwardStalkToStrictLocalization f`. -/
theorem pushforwardStalkToStrictLocalization_sheafFiber_etaleBaseChangeMap (V : Y.Etale)
    (v : (pointSmallEtale (y ≫ g)).fiber.obj V) (t : F.obj.obj (op ((Etale.pullback f).obj V))) :
    f'.pushforwardStalkToStrictLocalization y ((etalePullback h).obj F)
        ((pointSmallEtale y).sheafFiber.map ((etaleBaseChangeMap w).app F)
          ((sheafFiberEtalePullbackIso g y).hom.app ((etalePushforward f).obj F)
            ((pointSmallEtale (y ≫ g)).toPresheafFiber V v ((etalePushforward f).obj F).obj t))) =
      etaleSquareRestrict F (pullback.snd _ _) (pullback.snd _ _) h
        (strictLocalizationPullbackMap w y) (strictLocalizationPullbackMap_snd w y)
        (f.pushforwardStalkToStrictLocalization (y ≫ g) F
          ((pointSmallEtale (y ≫ g)).toPresheafFiber V v ((etalePushforward f).obj F).obj t)) := by
  rw [pushforwardStalkToStrictLocalization_sheafFiber_etaleBaseChangeMap_aux,
    Hom.pushforwardStalkToStrictLocalization_toPresheafFiber_eq_sectionAlong]
  apply Function.LeftInverse.injective
    (etalePullbackComp_inv_app_hom_app_apply F (pullback.snd y.fromSpecStrictLocalization f') h _)
  erw [etalePullbackComp_hom_app_sectionAlong]
  rw [etalePullbackComp_hom_app_etaleSquareRestrict]
  apply sectionAlong_congr
  apply pullback.hom_ext
  · simp only [Category.assoc, Etale.baseChangeComparison_app_left,
      Etale.baseChangeComparisonHom_fst_fst', Hom.strictLocalizationPullbackHom_fst_assoc,
      Hom.etaleNbhdHom_pullback_fst, Hom.strictLocalizationPullbackHom_fst,
      strictLocalizationPullbackMap_fst_assoc]
  · simp only [Category.assoc, Etale.baseChangeComparison_app_left,
      Etale.baseChangeComparisonHom_fst_snd', Hom.strictLocalizationPullbackHom_snd_assoc,
      Hom.strictLocalizationPullbackHom_snd, strictLocalizationPullbackMap_snd]

/-- **Injectivity of the base change morphism on stalks** (`f` quasi-compact): if the restriction
`Γ(Ỹ ×_Y X, F) ⟶ Γ(Ỹ' ×_{Y'} X', h^* F)` along `strictLocalizationPullbackMap` is injective, then
so is the stalk at `ȳ'` of `g^* f_* F ⟶ f'_* h^* F`. -/
theorem injective_sheafFiber_etaleBaseChangeMap_of_injective [QuasiCompact f]
    (hρ : Function.Injective (etaleSquareRestrict F (pullback.snd _ _) (pullback.snd _ _) h
      (strictLocalizationPullbackMap w y) (strictLocalizationPullbackMap_snd w y))) :
    Function.Injective ((pointSmallEtale y).sheafFiber.map ((etaleBaseChangeMap w).app F)) := by
  let e₁ := (sheafFiberEtalePullbackIso g y).app ((etalePushforward f).obj F)
  have he₁ : Function.Bijective e₁.hom := (isIso_iff_bijective _).mp inferInstance
  intro a b hab
  obtain ⟨a, rfl⟩ := he₁.2 a
  obtain ⟨b, rfl⟩ := he₁.2 b
  obtain ⟨V, v, t₁, t₂, rfl, rfl⟩ := (pointSmallEtale (y ≫ g)).toPresheafFiber_jointly_surjective₂
    (P := ((etalePushforward f).obj F).obj) a b
  have := congrArg (f'.pushforwardStalkToStrictLocalization y ((etalePullback h).obj F)) hab
  simp only [e₁, Iso.app_hom] at this
  rw [pushforwardStalkToStrictLocalization_sheafFiber_etaleBaseChangeMap,
    pushforwardStalkToStrictLocalization_sheafFiber_etaleBaseChangeMap] at this
  rw [Hom.injective_pushforwardStalkToStrictLocalization f (y ≫ g) F (hρ this)]

/-- **Bijectivity of the base change morphism on stalks** (`f` and `f'` quasi-compact): if the
map `(f_* F)_{g(ȳ')} ⟶ Γ(Ỹ ×_Y X, F)` of SGA 4 VIII 5.2 is surjective and the restriction
`Γ(Ỹ ×_Y X, F) ⟶ Γ(Ỹ' ×_{Y'} X', h^* F)` is bijective, then the stalk at `ȳ'` of
`g^* f_* F ⟶ f'_* h^* F` is bijective. -/
theorem bijective_sheafFiber_etaleBaseChangeMap_of_bijective [QuasiCompact f] [QuasiCompact f']
    (hm : Function.Surjective (f.pushforwardStalkToStrictLocalization (y ≫ g) F))
    (hρ : Function.Bijective (etaleSquareRestrict F (pullback.snd _ _) (pullback.snd _ _) h
      (strictLocalizationPullbackMap w y) (strictLocalizationPullbackMap_snd w y))) :
    Function.Bijective ((pointSmallEtale y).sheafFiber.map ((etaleBaseChangeMap w).app F)) := by
  refine ⟨injective_sheafFiber_etaleBaseChangeMap_of_injective w F y hρ.1, fun b ↦ ?_⟩
  let e₁ := (sheafFiberEtalePullbackIso g y).app ((etalePushforward f).obj F)
  obtain ⟨x, hx⟩ := hρ.2 (f'.pushforwardStalkToStrictLocalization y ((etalePullback h).obj F) b)
  obtain ⟨a, rfl⟩ := hm x
  obtain ⟨V, v, t, rfl⟩ := (pointSmallEtale (y ≫ g)).toPresheafFiber_jointly_surjective
    (P := ((etalePushforward f).obj F).obj) a
  refine ⟨e₁.hom ((pointSmallEtale (y ≫ g)).toPresheafFiber V v ((etalePushforward f).obj F).obj t),
    ?_⟩
  apply Hom.injective_pushforwardStalkToStrictLocalization f' y ((etalePullback h).obj F)
  simp only [e₁, Iso.app_hom]
  rw [pushforwardStalkToStrictLocalization_sheafFiber_etaleBaseChangeMap, hx]

end StrictLocalization

section Criterion

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}
  (F : Sheaf X.smallEtaleTopology (Type u))

/-- **Base change morphisms through strict localizations, injectivity** (consequence of SGA 4
VIII 5.2): for a commutative square `h ≫ f = f' ≫ g` with `f` quasi-compact, if for every
geometric point `ȳ'` of `Y'` the restriction `Γ(Ỹ ×_Y X, F) ⟶ Γ(Ỹ' ×_{Y'} X', h^* F)` along the
morphism induced by the strict localizations at `ȳ'` and `g(ȳ')` is injective, then the base change
morphism `g^* f_* F ⟶ f'_* h^* F` is a monomorphism. -/
theorem mono_etaleBaseChangeMap_of_forall_injective (w : h ≫ f = f' ≫ g) [QuasiCompact f]
    (H : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y'),
      Function.Injective (etaleSquareRestrict F (pullback.snd _ _) (pullback.snd _ _) h
        (strictLocalizationPullbackMap w y) (strictLocalizationPullbackMap_snd w y))) :
    Mono ((etaleBaseChangeMap w).app F) := by
  have hcons := isConservative_pointSmallEtale (fun y : Y' ↦ Y'.fromSpecAlgClosure y) (by
    refine Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨y, _, Y'.fromSpecAlgClosure_apply y⟩)
  rw [hcons.jointlyReflectIsomorphisms_type.jointlyReflectMonomorphisms.mono_iff]
  rintro ⟨Ψ, hΨ⟩
  obtain ⟨y, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hΨ
  rw [mono_iff_injective]
  exact injective_sheafFiber_etaleBaseChangeMap_of_injective w F _ (H _ _)

/-- **Base change morphisms through strict localizations** (consequence of SGA 4 VIII 5.2): for a
cartesian square `X' = X ×_Y Y'` with `f` quasi-compact, if for every geometric point `ȳ'` of `Y'`
the map `(f_* F)_{g(ȳ')} ⟶ Γ(Ỹ ×_Y X, F)` is surjective and the restriction
`Γ(Ỹ ×_Y X, F) ⟶ Γ(Ỹ' ×_{Y'} X', h^* F)` is bijective, then the base change morphism
`g^* f_* F ⟶ f'_* h^* F` is an isomorphism. -/
theorem isIso_etaleBaseChangeMap_of_forall_bijective (hsq : IsPullback h f' f g) [QuasiCompact f]
    (H : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y'),
      Function.Surjective (f.pushforwardStalkToStrictLocalization (y ≫ g) F) ∧
        Function.Bijective (etaleSquareRestrict F (pullback.snd _ _) (pullback.snd _ _) h
          (strictLocalizationPullbackMap hsq.w y) (strictLocalizationPullbackMap_snd hsq.w y))) :
    IsIso ((etaleBaseChangeMap hsq.w).app F) := by
  have : QuasiCompact f' := MorphismProperty.of_isPullback hsq inferInstance
  have hcons := isConservative_pointSmallEtale (fun y : Y' ↦ Y'.fromSpecAlgClosure y) (by
    refine Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨y, _, Y'.fromSpecAlgClosure_apply y⟩)
  rw [hcons.jointlyReflectIsomorphisms_type.isIso_iff]
  rintro ⟨Ψ, hΨ⟩
  obtain ⟨y, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hΨ
  rw [isIso_iff_bijective]
  exact bijective_sheafFiber_etaleBaseChangeMap_of_bijective hsq.w F _ (H _ _).1 (H _ _).2

/-- **Base change morphisms through strict localizations** (SGA 4 VIII 5.2 in the form
`Scheme.Hom.bijective_pushforwardStalkToStrictLocalization`): for a cartesian square
`X' = X ×_Y Y'` with `f` quasi-compact and quasi-separated, if all the restrictions
`Γ(Ỹ ×_Y X, F) ⟶ Γ(Ỹ' ×_{Y'} X', h^* F)` (at the geometric points `ȳ'` of `Y'`) are bijective, the
base change morphism `g^* f_* F ⟶ f'_* h^* F` is an isomorphism. -/
theorem isIso_etaleBaseChangeMap_of_forall_bijective_of_quasiSeparated (hsq : IsPullback h f' f g)
    [QuasiCompact f] [QuasiSeparated f]
    (H : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y'),
      Function.Bijective (etaleSquareRestrict F (pullback.snd _ _) (pullback.snd _ _) h
        (strictLocalizationPullbackMap hsq.w y) (strictLocalizationPullbackMap_snd hsq.w y))) :
    IsIso ((etaleBaseChangeMap hsq.w).app F) :=
  isIso_etaleBaseChangeMap_of_forall_bijective F hsq fun Ω _ _ y ↦
    ⟨(f.bijective_pushforwardStalkToStrictLocalization (y ≫ g) F).2, H Ω y⟩

end Criterion

section Bijective

variable {T X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (Type u))

lemma Etale.pullbackTopIso_inv_eq {T' : Scheme.{u}} (b : T' ⟶ T) :
    (Etale.pullbackTopIso b).inv = Etale.sectionOfHom b (Etale.top T) b (Category.comp_id b) := by
  conv_lhs => rw [Etale.eq_sectionOfHom b (Etale.top T) (Etale.pullbackTopIso b).inv]
  congr 1
  have h₁ : pullback.fst (Etale.top T).hom b = pullback.snd (Etale.top T).hom b ≫ b :=
    (Category.comp_id _).symm.trans pullback.condition
  have h₂ : (Etale.pullbackTopIso b).inv.left ≫ pullback.snd (Etale.top T).hom b = 𝟙 T' :=
    MorphismProperty.Over.w (Etale.pullbackTopIso b).inv
  rw [h₁, ← Category.assoc, h₂, Category.id_comp]

lemma etaleSectionsRestrict_eq {T' : Scheme.{u}} (b : T' ⟶ T)
    (G : Sheaf T.smallEtaleTopology (Type u)) (x : G.obj.obj (op (Etale.top T))) :
    etaleSectionsRestrict b G x = ((etalePullback b).obj G).obj.map (Etale.pullbackTopIso b).inv.op
      (((etaleAdjunction b).unit.app G).hom.app (op (Etale.top T)) x) := by
  rw [Etale.pullbackTopIso_inv_eq]
  rfl

/-- **Stacks 0A3H** for the restriction of global sections along `b`: if `b` is flat,
quasi-compact and geometrically connected, `Γ(T, G) ⟶ Γ(T', b^* G)` is bijective. -/
theorem bijective_etaleSectionsRestrict_of_geometricallyConnected {T' : Scheme.{u}} (b : T' ⟶ T)
    [Flat b] [QuasiCompact b] [GeometricallyConnected b] (G : Sheaf T.smallEtaleTopology (Type u)) :
    Function.Bijective (etaleSectionsRestrict b G) := by
  have := bijective_sections_etalePullback_of_geometricallyConnected b G
  convert this using 1
  funext x
  exact etaleSectionsRestrict_eq b G x

lemma etaleSquareRestrict_eq {P P' X' : Scheme.{u}} (p : P ⟶ X) (p' : P' ⟶ X')
    (h : X' ⟶ X) (q : P' ⟶ P) (e : q ≫ p = p' ≫ h) :
    etaleSquareRestrict F p p' h q e = fun x ↦
  ((etalePullbackComp p' h).inv.app F).hom.app (op (Etale.top P'))
    ((etalePullbackCongr F e).hom.hom.app (op (Etale.top P'))
      (((etalePullbackComp q p).hom.app F).hom.app (op (Etale.top P'))
        (etaleSectionsRestrict q ((etalePullback p).obj F) x))) := rfl

private lemma sheafIso_hom_inv_apply {G G' : Sheaf X.smallEtaleTopology (Type u)} (e : G ≅ G')
    (U : X.Etaleᵒᵖ) (z : G.obj.obj U) : e.inv.hom.app U (e.hom.hom.app U z) = z := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.hom_inv_id]
  rfl

private lemma sheafIso_inv_hom_apply {G G' : Sheaf X.smallEtaleTopology (Type u)} (e : G ≅ G')
    (U : X.Etaleᵒᵖ) (z : G'.obj.obj U) : e.hom.hom.app U (e.inv.hom.app U z) = z := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.inv_hom_id]
  rfl

/-- `etaleSquareRestrict` is bijective as soon as the restriction along `q` is. -/
lemma bijective_etaleSquareRestrict {P P' X' : Scheme.{u}} (p : P ⟶ X) (p' : P' ⟶ X')
    (h : X' ⟶ X) (q : P' ⟶ P) (e : q ≫ p = p' ≫ h)
    (hq : Function.Bijective (etaleSectionsRestrict q ((etalePullback p).obj F))) :
    Function.Bijective (etaleSquareRestrict F p p' h q e) := by
  refine ⟨fun x y hxy ↦ hq.1 ?_, fun z ↦ ?_⟩
  · have h₁ := congrArg (((etalePullbackComp p' h).hom.app F).hom.app (op (Etale.top P'))) hxy
    rw [etaleSquareRestrict_eq] at h₁
    dsimp only at h₁
    rw [etalePullbackComp_hom_app_inv_app_apply, etalePullbackComp_hom_app_inv_app_apply] at h₁
    have h₂ := congrArg ((etalePullbackCongr F e).inv.hom.app (op (Etale.top P'))) h₁
    rw [sheafIso_hom_inv_apply, sheafIso_hom_inv_apply] at h₂
    have h₃ := congrArg (((etalePullbackComp q p).inv.app F).hom.app (op (Etale.top P'))) h₂
    rwa [etalePullbackComp_inv_app_hom_app_apply, etalePullbackComp_inv_app_hom_app_apply] at h₃
  · obtain ⟨x, hx⟩ := hq.2 (((etalePullbackComp q p).inv.app F).hom.app (op (Etale.top P'))
      ((etalePullbackCongr F e).inv.hom.app (op (Etale.top P'))
        (((etalePullbackComp p' h).hom.app F).hom.app (op (Etale.top P')) z)))
    refine ⟨x, ?_⟩
    rw [etaleSquareRestrict_eq]
    dsimp only
    rw [hx, etalePullbackComp_hom_app_inv_app_apply, sheafIso_inv_hom_apply,
      etalePullbackComp_inv_app_hom_app_apply]

end Bijective

section FlatGeometricallyConnected

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}
  {Ω : Type u} [Field Ω] (y : Spec (.of Ω) ⟶ Y')

/-- If the morphism of strict localizations `Ỹ' ⟶ Ỹ` at `ȳ'` is flat and geometrically connected,
then for every cartesian square `X' = X ×_Y Y'` the restriction
`Γ(Ỹ ×_Y X, F) ⟶ Γ(Ỹ' ×_{Y'} X', h^* F)` is bijective (Stacks 0A3H for its base change
`Ỹ' ×_{Y'} X' ⟶ Ỹ ×_Y X`). -/
theorem bijective_etaleSquareRestrict_of_flat_of_geometricallyConnected
    (hsq : IsPullback h f' f g) [Flat (g.strictLocalizationMap y)]
    [GeometricallyConnected (g.strictLocalizationMap y)] (F : Sheaf X.smallEtaleTopology (Type u)) :
    Function.Bijective (etaleSquareRestrict F (pullback.snd _ _) (pullback.snd _ _) h
      (strictLocalizationPullbackMap hsq.w y) (strictLocalizationPullbackMap_snd hsq.w y)) := by
  have hpb := isPullback_strictLocalizationPullbackMap y hsq
  have : QuasiCompact (g.strictLocalizationMap y) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
  have : Flat (strictLocalizationPullbackMap hsq.w y) :=
    MorphismProperty.of_isPullback hpb.flip inferInstance
  have : QuasiCompact (strictLocalizationPullbackMap hsq.w y) :=
    MorphismProperty.of_isPullback hpb.flip inferInstance
  have : GeometricallyConnected (strictLocalizationPullbackMap hsq.w y) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb.flip inferInstance
  exact bijective_etaleSquareRestrict F _ _ _ _ _
    (bijective_etaleSectionsRestrict_of_geometricallyConnected _ _)

end FlatGeometricallyConnected

section Field

/-- The stalks of the spectrum of a field are fields. -/
lemma isField_stalk_spec (k : Type u) [Field k] (x : Spec (.of k)) :
    IsField ((Spec (.of k)).presheaf.stalk x) := by
  have hsub (a b : Spec (.of k)) : a = b := by
    have := a.isPrime
    have := b.isPrime
    exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime a.asIdeal).trans
      (Ideal.eq_bot_of_prime b.asIdeal).symm)
  have hx : closure {x} ∈ irreducibleComponents (Spec (.of k)) := by
    have : closure ({x} : Set (Spec (.of k))) = Set.univ :=
      Set.eq_univ_of_forall fun y ↦ subset_closure (hsub y x)
    rw [this, irreducibleComponents_eq_singleton]
    rfl
  exact isField_stalk_of_closure_mem_irreducibleComponents _ x hx

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- If the local ring of `X` at the image of `x̄` is a field, then so is the strict localization at
`x̄`: its maximal ideal is generated by that of `𝒪_{X,x}`
(`IsLocalRing.StrictHenselization.map_maximalIdeal`). -/
lemma Hom.maximalIdeal_strictLocalization_eq_bot
    (h : IsField (X.presheaf.stalk ξ.imagePoint)) :
    IsLocalRing.maximalIdeal ξ.strictLocalization = ⊥ := by
  let := ξ.residueFieldAlgebra
  let := ξ.stalkAlgebra
  have := ξ.isScalarTower_stalkAlgebra
  have := IsLocalRing.isLocalHom_algebraMap_of_isScalarTower
    (R := X.presheaf.stalk ξ.imagePoint) (K := Ω)
  have hm := IsLocalRing.StrictHenselization.map_maximalIdeal
    (R := X.presheaf.stalk ξ.imagePoint) (K := Ω)
  rw [(IsLocalRing.isField_iff_maximalIdeal_eq).1 h, Ideal.map_bot] at hm
  exact hm.symm

/-- If the local ring of `X` at the image of `x̄` is a field, the strict localization at `x̄` is
its own residue field. -/
lemma Hom.bijective_residue_strictLocalization (h : IsField (X.presheaf.stalk ξ.imagePoint)) :
    Function.Bijective (IsLocalRing.residue ξ.strictLocalization) := by
  refine ⟨?_, IsLocalRing.residue_surjective⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  have : a ∈ IsLocalRing.maximalIdeal ξ.strictLocalization := by
    rwa [← IsLocalRing.ker_residue, RingHom.mem_ker]
  rwa [ξ.maximalIdeal_strictLocalization_eq_bot h, Ideal.mem_bot] at this

end Field

end AlgebraicGeometry.Scheme
