/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Etale.TorsorTwist

/-!
# Direct images of torsors and of twisted groups

Let `u : C ⥤ D` be a continuous functor between sites, `F` a sheaf of groups on `D`, and `G` a
presheaf of groups on `C` with an isomorphism `ι : G ≅ u_* F = u.op ⋙ F`.

* An `F`-torsor `R` which is locally trivial along `u` (every object `T` of `C` is covered by
  objects `V` over which `R(u V)` is nonempty) has a direct image `u_* R`, a `G`-torsor
  (`Torsor.pushforward`).
* Twisting commutes with direct images: `^{u_* R} G ≅ u_*(^R F)` (`Torsor.twistPushforwardIso`).
  The comparison map sends an automorphism of `R|u(T)` to its restriction to the objects
  `u(V)`, `V` over `T`. It is bijective where `R` has a section (`Torsor.autEvalAt_bijective`),
  hence everywhere since bijectivity is local (`bijective_app_of_forall_mem`).
* Conversely every `G`-torsor `Q` trivialized by a family `U` covering the final object, whose
  image under `u` still covers the final object, is the direct image of an `F`-torsor
  (`Torsor.exists_pushforward_iso`). This `F`-torsor is glued from trivial torsors on the
  `u(U i)` with the cocycle of `Q` (`pushCocycle`); it is the torsor deduced from `u^* Q` by
  extension of the structure group `u^* u_* F → F`.
* Isomorphic torsors have isomorphic twists (`Torsor.twistSheafIsoOfIso`).

For a cartesian square `X₁ = X ×_Y Y₁` of schemes with `Y₁ ⟶ Y` étale, this gives, for every
torsor `Q` under `(f_* F)|Y₁`, a torsor `R` under `F|X₁` with `^Q(f_* F) ≅ (f₁)_*(^R F)`
(`Scheme.exists_twistSheaf_iso_etalePushforward`), as used in SGA 1 XIII 1.7.

## References

* [J. Giraud, *Cohomologie non abélienne*, III 2.3 and V 3.1][giraud1971]
* [SGA 1, Exposé XIII, 1.7][sga1]
-/

universe w v' u' v u

open CategoryTheory Opposite Limits

namespace CategoryTheory

section LocalBijective

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A B : Cᵒᵖ ⥤ Type w}

/-- A morphism of sheaves of sets which is bijective on the sections over the members of a
covering sieve of `T` is bijective on the sections over `T`. -/
lemma bijective_app_of_forall_mem (hA : Presieve.IsSheaf J A) (hB : Presieve.IsSheaf J B)
    (φ : A ⟶ B) {T : C} {S : Sieve T} (hS : S ∈ J T)
    (h : ∀ ⦃V : C⦄ (f : V ⟶ T), S f → Function.Bijective (φ.app (op V))) :
    Function.Bijective (φ.app (op T)) := by
  refine ⟨fun x y hxy ↦ (hA S hS).isSeparatedFor.ext fun V f hf ↦ (h f hf).1 ?_, fun b ↦ ?_⟩
  · rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  · let a : Presieve.FamilyOfElements A S.arrows := fun V f hf ↦
      (Equiv.ofBijective _ (h f hf)).symm (B.map f.op b)
    have ha (V : C) (f : V ⟶ T) (hf : S f) : φ.app (op V) (a f hf) = B.map f.op b :=
      (Equiv.ofBijective _ (h f hf)).apply_symm_apply _
    have hc : a.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
      apply (h (g₁ ≫ f₁) (S.downward_closed h₁ g₁)).1
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ha _ _ h₁, ha _ _ h₂,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, w]
    obtain ⟨t, ht, -⟩ := hA S hS a hc
    refine ⟨t, (hB S hS).isSeparatedFor.ext fun V f hf ↦ ?_⟩
    rw [← NatTrans.naturality_apply, ht f hf, ha _ _ hf]

end LocalBijective

namespace Torsor

section Eval

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat.{w}}
  (P : Torsor J G) {T : C}

/-- The value on a section over `T` of an endomorphism of `P|T`. -/
def overEval (β : P.over T ⟶ P.over T) (x : P.obj.obj (op T)) : P.obj.obj (op T) :=
  β.hom.app (op (Over.mk (𝟙 T))) x

lemma over_hom_app_eq (β : P.over T ⟶ P.over T) (p : P.obj.obj (op T)) (Y : Over T)
    (x : P.obj.obj (op Y.left)) :
    β.hom.app (op Y) x = P.diff (P.obj.map Y.hom.op p) x • P.obj.map Y.hom.op (P.overEval β p) := by
  have h := hom_app_naturality P β (Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 T)) p
  exact (congrArg (β.hom.app (op Y)) (P.diff_smul (P.obj.map Y.hom.op p) x).symm).trans
    ((β.map_smul (op Y) _ _).trans (congrArg _ h))

/-- An automorphism of `P|T` is determined by the element `g` with `β(p) = g • p`, for a section
`p` over `T`. -/
noncomputable def autEvalAt (p : P.obj.obj (op T)) (β : Aut (P.over T)) : G.obj (op T) :=
  P.diff p (P.overEval β.hom p)

/-- The endomorphism of `P|T` sending the section `p` to `g • p`. -/
noncomputable def overMulAt (p : P.obj.obj (op T)) (g : G.obj (op T)) : P.over T ⟶ P.over T where
  hom :=
    { app Y := ↾fun x ↦ P.diff (P.obj.map Y.unop.hom.op p) x •
        (G.map Y.unop.hom.op g • P.obj.map Y.unop.hom.op p)
      naturality Y Y' a := by
        ext (x : P.obj.obj (op Y.unop.left))
        change P.diff (P.obj.map Y'.unop.hom.op p) (P.obj.map a.unop.left.op x) •
            (G.map Y'.unop.hom.op g • P.obj.map Y'.unop.hom.op p) =
          P.obj.map a.unop.left.op (P.diff (P.obj.map Y.unop.hom.op p) x •
            (G.map Y.unop.hom.op g • P.obj.map Y.unop.hom.op p))
        have hw : a.unop.left ≫ Y.unop.hom = Y'.unop.hom := Over.w a.unop
        have e₁ : P.obj.map a.unop.left.op (P.obj.map Y.unop.hom.op p) =
            P.obj.map Y'.unop.hom.op p := by
          rw [← Functor.map_comp_apply, ← op_comp, hw]
        have e₂ : G.map a.unop.left.op (G.map Y.unop.hom.op g) = G.map Y'.unop.hom.op g := by
          rw [← Functor.map_comp_apply, ← op_comp, hw]
        rw [P.map_smul', P.map_smul', P.map_diff, e₁, e₂] }
  map_smul Y g' x := by
    change P.diff (P.obj.map Y.unop.hom.op p) ((show G.obj (op Y.unop.left) from g') •
        (show P.obj.obj (op Y.unop.left) from x)) •
          (G.map Y.unop.hom.op g • P.obj.map Y.unop.hom.op p) =
      (show G.obj (op Y.unop.left) from g') • (P.diff (P.obj.map Y.unop.hom.op p)
        (show P.obj.obj (op Y.unop.left) from x) •
          (G.map Y.unop.hom.op g • P.obj.map Y.unop.hom.op p))
    rw [diff_smul_right, ← smul_smul]

lemma overEval_overMulAt (p : P.obj.obj (op T)) (g : G.obj (op T)) :
    P.overEval (P.overMulAt p g) p = g • p := by
  change P.diff (P.obj.map (𝟙 T).op p) p • (G.map (𝟙 T).op g • P.obj.map (𝟙 T).op p) = g • p
  simp only [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, diff_self,
    _root_.one_smul]

lemma autEvalAt_bijective (p : P.obj.obj (op T)) : Function.Bijective (P.autEvalAt p) := by
  refine ⟨fun β β' h ↦ ?_, fun g ↦ ⟨asIso (P.overMulAt p g), ?_⟩⟩
  · have h' : P.overEval β.hom p = P.overEval β'.hom p := by
      rw [← P.diff_smul p (P.overEval β.hom p), ← P.diff_smul p (P.overEval β'.hom p)]
      exact congrArg (· • p) h
    apply Iso.ext
    apply Torsor.hom_ext
    ext Y (x : P.obj.obj (op Y.unop.left))
    change β.hom.hom.app (op Y.unop) x = β'.hom.hom.app (op Y.unop) x
    rw [over_hom_app_eq P β.hom p, over_hom_app_eq P β'.hom p, h']
  · change P.diff p (P.overEval (P.overMulAt p g) p) = g
    rw [overEval_overMulAt, diff_smul_self]

end Eval

section Pushforward

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (u : C ⥤ D) [u.IsContinuous J K]
  {F : Dᵒᵖ ⥤ GrpCat.{w}} {G : Cᵒᵖ ⥤ GrpCat.{w}} (ι : G ≅ u.op ⋙ F)

variable (J) in
/-- A torsor on `D` is locally trivial along `u : C ⥤ D` if every object `T` of `C` is covered
by objects `V` such that the torsor has a section over `u V`. -/
def IsLocallyTrivialAlong (R : Torsor K F) : Prop :=
  ∀ T : C, Sieve.functorPullback u (R.nonemptySieve (u.obj T)) ∈ J T

/-- The direct image `u_* R` of an `F`-torsor `R` which is locally trivial along `u`: a torsor
under `u_* F`, here identified with `G` through `ι`. -/
noncomputable def pushforward (R : Torsor K F) (hR : R.IsLocallyTrivialAlong J u) :
    Torsor J G where
  obj := u.op ⋙ R.obj
  isSheaf := u.op_comp_isSheaf_of_isSheaf_type J R.isSheaf
  smul T g x := R.smul (u.op.obj T) (ι.hom.app T g) x
  one_smul T x := by
    rw [map_one]
    exact R.one_smul _ x
  mul_smul T g h x := by
    rw [map_mul]
    exact R.mul_smul _ _ _ x
  map_smul f g x := by
    have h : ι.hom.app _ (G.map f g) = F.map (u.op.map f) (ι.hom.app _ g) :=
      ConcreteCategory.congr_hom (ι.hom.naturality f) g
    change R.obj.map (u.op.map f) (R.smul _ (ι.hom.app _ g) x) =
      R.smul _ (ι.hom.app _ (G.map f g)) (R.obj.map (u.op.map f) x)
    rw [h]
    exact R.map_smul (u.op.map f) _ x
  existsUnique_smul T x y := by
    have e : ι.hom.app T (ι.inv.app T (R.diff x y)) = R.diff x y := by
      rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app]
      rfl
    refine ⟨ι.inv.app T (R.diff x y), ?_, fun g hg ↦ ?_⟩
    · change R.smul _ (ι.hom.app T (ι.inv.app T (R.diff x y))) x = y
      rw [e]
      exact R.diff_smul x y
    · have h : ι.hom.app T g = R.diff x y := (R.diff_eq_iff.2 hg).symm
      rw [← h, ← ConcreteCategory.comp_apply, Iso.hom_inv_id_app]
      rfl
  locallyNonempty T := ⟨_, hR T, fun _ _ hf ↦ hf⟩

variable {u ι} {R : Torsor K F} {hR : R.IsLocallyTrivialAlong J u}

lemma pushforward_diff {T : Cᵒᵖ} (x y : (R.pushforward u ι hR).obj.obj T) :
    (R.pushforward u ι hR).diff x y =
      ι.inv.app T (R.diff (show R.obj.obj (u.op.obj T) from x) y) := by
  rw [diff_eq_iff]
  change R.smul _ (ι.hom.app T (ι.inv.app T (R.diff x y))) x = y
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app]
  exact R.diff_smul x y

/-- An endomorphism of `R|u(T)` induces an endomorphism of `(u_* R)|T`. -/
def overPushforwardHom {T : C} (β : R.over (u.obj T) ⟶ R.over (u.obj T)) :
    (R.pushforward u ι hR).over T ⟶ (R.pushforward u ι hR).over T where
  hom := Functor.whiskerLeft (Over.post u).op β.hom
  map_smul Y g x := β.map_smul (op ((Over.post u).obj Y.unop)) (ι.hom.app _ g) x

variable (u ι hR) in
/-- The homomorphism `Aut(R|u(T)) ⟶ Aut((u_* R)|T)`. -/
noncomputable def autPushforward (T : C) :
    Aut (R.over (u.obj T)) →* Aut ((R.pushforward u ι hR).over T) where
  toFun β := asIso (overPushforwardHom β.hom)
  map_one' := by
    apply Iso.ext
    rfl
  map_mul' _ _ := by
    apply Iso.ext
    rfl

lemma autPushforward_hom_app {T : C} (β : Aut (R.over (u.obj T))) (Y : Over T)
    (x : R.obj.obj (op (u.obj Y.left))) :
    (autPushforward u ι hR T β).hom.hom.app (op Y) x =
      β.hom.hom.app (op ((Over.post u).obj Y)) x :=
  rfl

lemma autEvalAt_autPushforward {T : C} (r : R.obj.obj (op (u.obj T)))
    (β : Aut (R.over (u.obj T))) :
    (R.pushforward u ι hR).autEvalAt r (autPushforward u ι hR T β) =
      ι.inv.app (op T) (R.autEvalAt r β) := by
  have h : β.hom.hom.app (op ((Over.post u).obj (Over.mk (𝟙 T)))) r = R.overEval β.hom r := by
    have h₀ := over_hom_app_eq R β.hom r ((Over.post u).obj (Over.mk (𝟙 T))) r
    have e : R.obj.map ((Over.post u).obj (Over.mk (𝟙 T))).hom.op = 𝟙 _ := by
      change R.obj.map (u.map (𝟙 T)).op = 𝟙 _
      rw [u.map_id, op_id, R.obj.map_id]
    rw [e] at h₀
    refine h₀.trans ?_
    change R.diff r r • R.overEval β.hom r = _
    rw [diff_self, _root_.one_smul]
  exact (pushforward_diff (R := R) _ _).trans
    (congrArg (ι.inv.app (op T)) (congrArg (R.diff r) h))

lemma autPushforward_bijective {T : C} (r : R.obj.obj (op (u.obj T))) :
    Function.Bijective (autPushforward u ι hR T) := by
  have hι : Function.Bijective (ι.inv.app (op T)) :=
    ConcreteCategory.bijective_of_isIso (ι.inv.app (op T))
  have hcomp : (R.pushforward u ι hR).autEvalAt r ∘ autPushforward u ι hR T =
      ι.inv.app (op T) ∘ R.autEvalAt r :=
    funext fun β ↦ autEvalAt_autPushforward r β
  have h₁ := autEvalAt_bijective (R.pushforward u ι hR) r
  have h₂ := hι.comp (R.autEvalAt_bijective r)
  rw [← hcomp] at h₂
  exact (Function.Bijective.of_comp_iff' h₁ _).1 h₂

lemma autPushforward_autRestrict {T T' : C} (f : T' ⟶ T) (β : Aut (R.over (u.obj T))) :
    autPushforward u ι hR T' (autRestrict R (u.map f) β) =
      autRestrict (R.pushforward u ι hR) f (autPushforward u ι hR T β) := by
  apply Iso.ext
  apply Torsor.hom_ext
  ext Y (x : R.obj.obj (op (u.obj Y.unop.left)))
  change β.hom.hom.app (op ((Over.map (u.map f)).obj ((Over.post u).obj Y.unop))) x =
    β.hom.hom.app (op ((Over.post u).obj ((Over.map f).obj Y.unop))) x
  have h : β.hom.hom.app (op ((Over.post u).obj ((Over.map f).obj Y.unop)))
      (R.obj.map (𝟙 (u.obj Y.unop.left)).op x) = R.obj.map (𝟙 (u.obj Y.unop.left)).op
        (β.hom.hom.app (op ((Over.map (u.map f)).obj ((Over.post u).obj Y.unop))) x) :=
    hom_app_naturality R β.hom (Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ u.map Y.unop.hom ≫ u.map f = u.map (Y.unop.hom ≫ f)
      rw [Category.id_comp, u.map_comp]) :
    (Over.post u).obj ((Over.map f).obj Y.unop) ⟶
      (Over.map (u.map f)).obj ((Over.post u).obj Y.unop)) x
  have e : R.obj.map (𝟙 (u.obj Y.unop.left)).op = 𝟙 _ := by rw [op_id, R.obj.map_id]
  rw [e] at h
  exact h.symm

section Twist

variable (u ι R hR)
variable [∀ T : D, Small.{w} (Aut (R.over T))]
  [∀ T : C, Small.{w} (Aut ((R.pushforward u ι hR).over T))]

/-- The comparison map `u_* (^R F) ⟶ ^{u_* R} G` of twisted groups, as presheaves of sets. -/
noncomputable def twistPushforwardHom :
    u.op ⋙ twist R ⋙ CategoryTheory.forget GrpCat ⟶
      twist (R.pushforward u ι hR) ⋙ CategoryTheory.forget GrpCat where
  app T := ↾fun a ↦ (twistEquiv _ T.unop).symm
    (autPushforward u ι hR T.unop (twistEquiv R (u.obj T.unop) a))
  naturality T T' f := by
    ext a
    change (twistEquiv _ T'.unop).symm (autPushforward u ι hR T'.unop (twistEquiv R _
        ((twistEquiv R _).symm (autRestrict R (u.map f.unop) (twistEquiv R _ a))))) =
      (twistEquiv _ T'.unop).symm (autRestrict _ f.unop ((twistEquiv _ T.unop)
        ((twistEquiv _ T.unop).symm (autPushforward u ι hR T.unop (twistEquiv R _ a)))))
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, autPushforward_autRestrict]

lemma bijective_twistPushforwardHom_app (T : Cᵒᵖ) :
    Function.Bijective ((twistPushforwardHom u ι R hR).app T) := by
  have hA : Presieve.IsSheaf J (u.op ⋙ twist R ⋙ CategoryTheory.forget GrpCat) :=
    u.op_comp_isSheaf_of_isSheaf_type J (isSheaf_twist (P := R))
  refine bijective_app_of_forall_mem hA (isSheaf_twist (P := R.pushforward u ι hR)) _ (hR T.unop)
    fun V f hf ↦ ?_
  obtain ⟨r⟩ := hf
  exact ((twistEquiv _ V).symm.bijective.comp (autPushforward_bijective r)).comp
    (twistEquiv R (u.obj V)).bijective

/-- The twist of the direct image: `^{u_* R} G ≅ u_*(^R F)`. -/
noncomputable def twistPushforwardIso :
    (u.sheafPushforwardContinuous (Type w) J K).obj (twistSheaf R) ≅
      twistSheaf (R.pushforward u ι hR) :=
  have : IsIso (twistPushforwardHom u ι R hR) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun T ↦ (isIso_iff_bijective _).2 (bijective_twistPushforwardHom_app u ι R hR T)
  have : IsIso ((sheafToPresheaf J (Type w)).map
      (ObjectProperty.homMk (twistPushforwardHom u ι R hR) :
        (u.sheafPushforwardContinuous (Type w) J K).obj (twistSheaf R) ⟶
          twistSheaf (R.pushforward u ι hR))) := this
  have := isIso_of_fully_faithful (sheafToPresheaf J (Type w))
    (ObjectProperty.homMk (twistPushforwardHom u ι R hR) :
      (u.sheafPushforwardContinuous (Type w) J K).obj (twistSheaf R) ⟶
        twistSheaf (R.pushforward u ι hR))
  asIso (ObjectProperty.homMk (twistPushforwardHom u ι R hR) :
    (u.sheafPushforwardContinuous (Type w) J K).obj (twistSheaf R) ⟶
      twistSheaf (R.pushforward u ι hR))

end Twist

end Pushforward

section IsoInvariance

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat.{w}}
  {P P' : Torsor J G} (e : P ≅ P')

/-- An isomorphism of torsors `P ≅ P'` restricts to `P|T ≅ P'|T`. -/
def overIso (T : C) : P.over T ≅ P'.over T :=
  (restrictFunctor (J.over T) (Over.forget T)).mapIso e

lemma autRestrict_conjAut {T T' : C} (f : T' ⟶ T) (β : Aut (P.over T)) :
    autRestrict P' f ((overIso e T).conjAut β) = (overIso e T').conjAut (autRestrict P f β) := by
  simp only [Iso.conjAut_apply]
  rfl

variable [∀ T : C, Small.{w} (Aut (P.over T))] [∀ T : C, Small.{w} (Aut (P'.over T))]

/-- Isomorphic torsors have isomorphic twists. -/
noncomputable def twistSheafIsoOfIso : twistSheaf P ≅ twistSheaf P' :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun T ↦ Equiv.toIso
    ((twistEquiv P T.unop).toEquiv.trans (((overIso e T.unop).conjAut).toEquiv.trans
      (twistEquiv P' T.unop).symm.toEquiv))) (fun {T T'} f ↦ by
    ext a
    change (twistEquiv P' T'.unop).symm ((overIso e T'.unop).conjAut ((twistEquiv P T'.unop)
        ((twistEquiv P T'.unop).symm (autRestrict P f.unop (twistEquiv P T.unop a))))) =
      (twistEquiv P' T'.unop).symm (autRestrict P' f.unop ((twistEquiv P' T.unop)
        ((twistEquiv P' T.unop).symm ((overIso e T.unop).conjAut (twistEquiv P T.unop a)))))
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, autRestrict_conjAut]))

end IsoInvariance

end Torsor

section PushCocycle

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (u : C ⥤ D) {F : Dᵒᵖ ⥤ GrpCat.{w}} {G : Cᵒᵖ ⥤ GrpCat.{w}} (ι : G ≅ u.op ⋙ F)
  [HasBinaryProducts C] [PreservesLimitsOfShape (Discrete WalkingPair) u]
  {I : Type w'} {U : I → C}

/-- The morphism `W ⟶ u(A ⨯ B)` given by `a : W ⟶ u A` and `b : W ⟶ u B`. -/
noncomputable def liftToProd {A B : C} {W : D} (a : W ⟶ u.obj A) (b : W ⟶ u.obj B) :
    W ⟶ u.obj (A ⨯ B) :=
  prod.lift a b ≫ (PreservesLimitPair.iso u A B).inv

@[reassoc (attr := simp)]
lemma liftToProd_fst {A B : C} {W : D} (a : W ⟶ u.obj A) (b : W ⟶ u.obj B) :
    liftToProd u a b ≫ u.map prod.fst = a := by
  simp [liftToProd]

@[reassoc (attr := simp)]
lemma liftToProd_snd {A B : C} {W : D} (a : W ⟶ u.obj A) (b : W ⟶ u.obj B) :
    liftToProd u a b ≫ u.map prod.snd = b := by
  simp [liftToProd]

lemma liftToProd_eq {A B V : C} {W : D} (p : V ⟶ A) (q : V ⟶ B) (t : W ⟶ u.obj V) :
    liftToProd u (t ≫ u.map p) (t ≫ u.map q) = t ≫ u.map (prod.lift p q) := by
  rw [← cancel_mono (PreservesLimitPair.iso u A B).hom]
  apply prod.hom_ext <;> simp [liftToProd, ← Functor.map_comp]

lemma liftToProd_comp {A B : C} {W W' : D} (φ : W' ⟶ W) (a : W ⟶ u.obj A) (b : W ⟶ u.obj B) :
    liftToProd u (φ ≫ a) (φ ≫ b) = φ ≫ liftToProd u a b := by
  rw [liftToProd, liftToProd, ← Category.assoc, prod.comp_lift]

variable {u} (γ : PresheafOfGroups.OneCocycle G U)

/-- The value of the pushed cocycle: `γ(a, b)` for `a : W ⟶ u(U i)` and `b : W ⟶ u(U j)`. -/
noncomputable def pushCocycleEv (i j : I) ⦃W : D⦄ (a : W ⟶ u.obj (U i)) (b : W ⟶ u.obj (U j)) :
    F.obj (op W) :=
  F.map (liftToProd u a b).op (ι.hom.app (op (U i ⨯ U j)) (γ.ev i j prod.fst prod.snd))

lemma pushCocycleEv_eq (i j : I) {V : C} (p : V ⟶ U i) (q : V ⟶ U j) {W : D}
    (t : W ⟶ u.obj V) :
    pushCocycleEv ι γ i j (t ≫ u.map p) (t ≫ u.map q) =
      F.map t.op (ι.hom.app (op V) (γ.ev i j p q)) := by
  rw [pushCocycleEv, liftToProd_eq, op_comp, Functor.map_comp_apply]
  refine congrArg (F.map t.op) ?_
  have h := NatTrans.naturality_apply ι.hom (prod.lift p q).op (γ.ev i j prod.fst prod.snd)
  rw [γ.ev_precomp, prod.lift_fst, prod.lift_snd] at h
  exact h.symm

/-- The pushforward of a `1`-cocycle of `G ≅ u_* F` on the `U i` to a `1`-cocycle of `F` on the
`u(U i)`. -/
noncomputable def pushCocycle : PresheafOfGroups.OneCocycle F (fun i ↦ u.obj (U i)) where
  ev := pushCocycleEv ι γ
  ev_precomp i j W W' φ a b := by
    simp only [pushCocycleEv, liftToProd_comp, op_comp, Functor.map_comp_apply]
  ev_trans i j k W a b c := by
    let t : W ⟶ u.obj ((U i ⨯ U j) ⨯ U k) := liftToProd u (liftToProd u a b) c
    have ha : t ≫ u.map (prod.fst ≫ prod.fst) = a := by simp [t]
    have hb : t ≫ u.map (prod.fst ≫ prod.snd) = b := by simp [t]
    have hc : t ≫ u.map prod.snd = c := by simp [t]
    change pushCocycleEv ι γ i j a b * pushCocycleEv ι γ j k b c = pushCocycleEv ι γ i k a c
    rw [← ha, ← hb, ← hc, pushCocycleEv_eq, pushCocycleEv_eq, pushCocycleEv_eq, ← map_mul,
      ← map_mul, γ.ev_trans]

end PushCocycle

namespace Torsor

section Existence

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (u : C ⥤ D) [u.IsContinuous J K] {F : Dᵒᵖ ⥤ GrpCat.{w}} {G : Cᵒᵖ ⥤ GrpCat.{w}}
  (ι : G ≅ u.op ⋙ F) [HasBinaryProducts C] [PreservesLimitsOfShape (Discrete WalkingPair) u]
  {I : Type w} {U : I → C}

/-- Every torsor `Q` under `G ≅ u_* F` which is trivialized by a family `U` covering the final
object, whose image under `u` also covers the final object, is the direct image of an `F`-torsor
locally trivial along `u`: glue trivial `F`-torsors on the `u(U i)` with the cocycle of `Q`. -/
theorem exists_pushforward_iso (hF : Presieve.IsSheaf K (F ⋙ CategoryTheory.forget GrpCat))
    (Q : Torsor J G) (hU : J.CoversTop U) (e : ∀ i, Q.obj.obj (op (U i)))
    (hU' : K.CoversTop (fun i ↦ u.obj (U i))) :
    ∃ (R : Torsor K F) (hR : R.IsLocallyTrivialAlong J u),
      Nonempty (R.pushforward u ι hR ≅ Q) := by
  let γ' := pushCocycle ι (Q.cocycle e)
  let R := γ'.torsor hF hU'
  have hR : R.IsLocallyTrivialAlong J u := fun T ↦ by
    refine J.superset_covering (S := Sieve.ofObjects U T) (fun V f hf ↦ ?_) (hU T)
    obtain ⟨i, ⟨a⟩⟩ := hf
    exact ⟨R.obj.map (u.map a).op (γ'.torsorSection hF hU' i)⟩
  refine ⟨R, hR, ?_⟩
  have hev : ∀ (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j),
      ((R.pushforward u ι hR).cocycle (fun i ↦ γ'.torsorSection hF hU' i)).ev i j a b =
        (Q.cocycle e).ev i j a b := by
    intro i j T a b
    rw [cocycle_ev]
    refine (pushforward_diff (R := R) _ _).trans ?_
    have h₁ := γ'.torsor_cocycle_ev hF hU' i j (u.map a) (u.map b)
    rw [cocycle_ev] at h₁
    change ι.inv.app (op T) (R.diff (R.obj.map (u.map b).op (γ'.torsorSection hF hU' j))
      (R.obj.map (u.map a).op (γ'.torsorSection hF hU' i))) = _
    rw [h₁]
    change ι.inv.app (op T) (pushCocycleEv ι (Q.cocycle e) i j (u.map a) (u.map b)) = _
    have h₂ := pushCocycleEv_eq ι (Q.cocycle e) i j a b (𝟙 (u.obj T))
    rw [Category.id_comp, Category.id_comp, op_id, CategoryTheory.Functor.map_id] at h₂
    rw [h₂]
    change ι.inv.app (op T) (ι.hom.app (op T) ((Q.cocycle e).ev i j a b)) = _
    rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id_app]
    rfl
  exact nonempty_iso_of_isCohomologous (R.pushforward u ι hR)
    (fun i ↦ γ'.torsorSection hF hU' i) hU e ⟨1, fun i j T a b ↦ by simp [hev]⟩

end Existence

end Torsor

end CategoryTheory

-- See the comment in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

open Torsor

variable {X Y X₁ Y₁ : Scheme.{u}} {f : X ⟶ Y} {eX : X₁ ⟶ X} {eY : Y₁ ⟶ Y} {f₁ : X₁ ⟶ Y₁}
  [Etale eX] [Etale eY] (hsq : IsPullback eX f₁ f eY)

/-- For a cartesian square `X₁ = X ×_Y Y₁` with `Y₁ ⟶ Y` étale, the étale `X`-schemes
`X ×_Y V` and `X₁ ×_{Y₁} V` agree, for `V` étale over `Y₁`. -/
noncomputable def etalePullbackMapIso (V : Y₁.Etale) :
    (Etale.map eX).obj ((Etale.pullback f₁).obj V) ≅
      (Etale.pullback f).obj ((Etale.map eY).obj V) :=
  MorphismProperty.Over.isoMk
    (((IsPullback.of_hasPullback V.hom f₁).paste_vert hsq.flip).isoPullback)
    (IsPullback.isoPullback_hom_snd _)

@[reassoc]
lemma etalePullbackMapIso_hom_left_fst (V : Y₁.Etale) :
    (etalePullbackMapIso hsq V).hom.left ≫ pullback.fst (V.hom ≫ eY) f =
      pullback.fst V.hom f₁ :=
  IsPullback.isoPullback_hom_fst _

@[reassoc]
lemma etalePullbackMapIso_hom_left_snd (V : Y₁.Etale) :
    (etalePullbackMapIso hsq V).hom.left ≫ pullback.snd (V.hom ≫ eY) f =
      pullback.snd V.hom f₁ ≫ eX :=
  IsPullback.isoPullback_hom_snd _

lemma etalePullbackMapIso_naturality {V V' : Y₁.Etale} (φ : V' ⟶ V) :
    (etalePullbackMapIso hsq V').hom ≫ (Etale.pullback f).map ((Etale.map eY).map φ) =
      (Etale.map eX).map ((Etale.pullback f₁).map φ) ≫ (etalePullbackMapIso hsq V).hom := by
  have a₁ : ((Etale.pullback f).map ((Etale.map eY).map φ)).left ≫ pullback.fst (V.hom ≫ eY) f =
      pullback.fst (V'.hom ≫ eY) f ≫ φ.left := Etale.pullback_map_left_fst f _
  have a₂ : ((Etale.pullback f).map ((Etale.map eY).map φ)).left ≫ pullback.snd (V.hom ≫ eY) f =
      pullback.snd (V'.hom ≫ eY) f := Etale.pullback_map_left_snd f _
  have b₁ : ((Etale.pullback f₁).map φ).left ≫ pullback.fst V.hom f₁ =
      pullback.fst V'.hom f₁ ≫ φ.left := Etale.pullback_map_left_fst f₁ _
  have b₂ : ((Etale.pullback f₁).map φ).left ≫ pullback.snd V.hom f₁ =
      pullback.snd V'.hom f₁ := Etale.pullback_map_left_snd f₁ _
  have c₁ := etalePullbackMapIso_hom_left_fst hsq V
  have c₂ := etalePullbackMapIso_hom_left_snd hsq V
  have d₁ := etalePullbackMapIso_hom_left_fst hsq V'
  have d₂ := etalePullbackMapIso_hom_left_snd hsq V'
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · change (etalePullbackMapIso hsq V').hom.left ≫
        ((Etale.pullback f).map ((Etale.map eY).map φ)).left ≫ pullback.fst (V.hom ≫ eY) f =
      ((Etale.pullback f₁).map φ).left ≫ (etalePullbackMapIso hsq V).hom.left ≫
        pullback.fst (V.hom ≫ eY) f
    rw [a₁, c₁, b₁, reassoc_of% d₁]
  · change (etalePullbackMapIso hsq V').hom.left ≫
        ((Etale.pullback f).map ((Etale.map eY).map φ)).left ≫ pullback.snd (V.hom ≫ eY) f =
      ((Etale.pullback f₁).map φ).left ≫ (etalePullbackMapIso hsq V).hom.left ≫
        pullback.snd (V.hom ≫ eY) f
    rw [a₂, c₂, d₂, reassoc_of% b₂]

variable (F : X.Etaleᵒᵖ ⥤ GrpCat.{u})

/-- The identification of `(f_* F)|Y₁` with `(f₁)_*(F|X₁)` for a cartesian square
`X₁ = X ×_Y Y₁` with `Y₁ ⟶ Y` étale. -/
noncomputable def pushforwardRestrictIso :
    (Etale.map eY).op ⋙ (Etale.pullback f).op ⋙ F ≅
      (Etale.pullback f₁).op ⋙ (Etale.map eX).op ⋙ F :=
  NatIso.ofComponents (fun V ↦ F.mapIso (etalePullbackMapIso hsq V.unop).op) (fun {V V'} φ ↦ by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    exact etalePullbackMapIso_naturality hsq φ.unop)

omit [Etale eX] [Etale eY] in
/-- The base change of an étale covering family is an étale covering family. -/
lemma coversTop_etalePullback {I : Type*} {U : I → Y₁.Etale}
    (hU : Y₁.smallEtaleTopology.CoversTop U) (g : X₁ ⟶ Y₁) :
    X₁.smallEtaleTopology.CoversTop (fun i ↦ (Etale.pullback g).obj (U i)) := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ (Etale.isTerminalTop Y₁),
    mem_smallEtaleTopology_iff] at hU
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ (Etale.isTerminalTop X₁),
    mem_smallEtaleTopology_iff]
  intro x
  obtain ⟨V, a, v, ⟨i, ⟨b⟩⟩, hv⟩ := hU (g x)
  have ha : a.left ≫ 𝟙 Y₁ = V.hom := MorphismProperty.Over.w a
  have hb : b.left ≫ (U i).hom = V.hom := MorphismProperty.Over.w b
  have h : (U i).hom (b.left v) = g x := by
    have e₁ : (U i).hom (b.left v) = V.hom v := by
      rw [← hb]
      rfl
    have e₂ : V.hom v = a.left v := by
      rw [← ha]
      rfl
    rw [e₁, e₂, hv]
  obtain ⟨w, -, hw⟩ := Pullback.exists_preimage_pullback (f := (U i).hom) (g := g) _ x h
  exact ⟨(Etale.pullback g).obj (U i), (Etale.isTerminalTop X₁).from _, w, ⟨i, ⟨𝟙 _⟩⟩, hw⟩

include hsq in
/-- Twisting commutes with the direct image: for a torsor `Q` under `(f_* F)|Y₁` there is a
torsor `R` under `F|X₁` with `^Q(f_* F)|Y₁ ≅ (f₁)_*(^R F|X₁)` (the argument of XIII 1.7: `R` is
deduced from `Q` by extension of the structure group `f₁^* f₁_* F → F`). -/
theorem exists_twistSheaf_iso_etalePushforward
    (hF : Presieve.IsSheaf X.smallEtaleTopology (F ⋙ CategoryTheory.forget GrpCat))
    (Q : Torsor Y₁.smallEtaleTopology ((Etale.map eY).op ⋙ (Etale.pullback f).op ⋙ F)) :
    ∃ R : Torsor X₁.smallEtaleTopology ((Etale.map eX).op ⋙ F),
      Nonempty (twistSheaf Q ≅ (etalePushforward f₁).obj (twistSheaf R)) := by
  obtain ⟨U, hU, hQ⟩ := exists_etale_trivialization Q
  have hF' : Presieve.IsSheaf X₁.smallEtaleTopology
      (((Etale.map eX).op ⋙ F) ⋙ CategoryTheory.forget GrpCat) :=
    (Etale.map eX).op_comp_isSheaf_of_isSheaf_type _ hF
  obtain ⟨R, hR, ⟨i⟩⟩ := Torsor.exists_pushforward_iso (Etale.pullback f₁)
    (pushforwardRestrictIso hsq F) hF' Q hU (fun y ↦ (hQ y).some) (coversTop_etalePullback hU f₁)
  exact ⟨R, ⟨twistSheafIsoOfIso i.symm ≪≫ (twistPushforwardIso _ _ R hR).symm⟩⟩

end AlgebraicGeometry.Scheme
