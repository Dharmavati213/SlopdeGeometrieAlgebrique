/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import SGA.Foundations.EtaleStalkBaseChange
import SGA.Foundations.Etale.Restriction

/-!
# Base change for universally closed morphisms: injectivity

For a cartesian square
```
X' --h--> X
|f'       |f
Y' --g--> Y
```
with `f` universally closed, the base change morphism `g^* f_* F ⟶ f'_* h^* F` of étale sheaves
of sets is a monomorphism (`AlgebraicGeometry.Scheme.mono_etaleBaseChangeMap_of_universallyClosed`).
This is the injectivity half of the proper base change theorem in degree `0` (SGA 4 XII 5.1;
Stacks 0A3T, injectivity part), and holds without any noetherian or finiteness hypothesis.

The proof uses the *agreement locus* of two sections `s t ∈ F(W)` over an étale `X`-scheme `W`
(`AlgebraicGeometry.Scheme.etaleAgreementLocus`, compare Stacks 09XM): the set of points of `W`
having an étale neighbourhood on which `s` and `t` agree. It is open, and `s`, `t` agree on every
étale `W`-scheme whose image lies in it. If the germs of `s` and `t` at the geometric points of
`X ×_Y V` lying over a point `v₀` of an étale `Y`-scheme `V` agree, then the agreement locus
contains the fibre of `X ×_Y V ⟶ V` over `v₀`; since `X ×_Y V ⟶ V` is closed, `s` and `t` agree
over `X ×_Y V₀` for an open neighbourhood `V₀` of `v₀`
(`AlgebraicGeometry.Scheme.toPresheafFiber_etalePushforward_eq_of_universallyClosed`).

## References

* [SGA 4, Exposé XII, 5.1][sga4]
* [Stacks Project, Tag 0A3T](https://stacks.math.columbia.edu/tag/0A3T)
* [Stacks Project, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)
-/

universe u

open CategoryTheory Limits Opposite

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry.Scheme

section AgreementLocus

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (Type u)) {W : X.Etale}

/-- The agreement locus of two sections `s t ∈ F(W)` of an étale sheaf over an étale `X`-scheme
`W`: the points of `W` in the image of an étale `W`-scheme on which `s` and `t` agree. -/
def etaleAgreementLocus (s t : F.obj.obj (op W)) : Set W.left :=
  {w | ∃ (V : X.Etale) (g : V ⟶ W) (v : V.left), F.obj.map g.op s = F.obj.map g.op t ∧
    g.left v = w}

variable {F}

lemma isOpen_etaleAgreementLocus (s t : F.obj.obj (op W)) :
    IsOpen (etaleAgreementLocus F s t) := by
  rw [isOpen_iff_forall_mem_open]
  rintro w ⟨V, g, v, hst, rfl⟩
  refine ⟨Set.range g.left, ?_, ?_, ⟨v, rfl⟩⟩
  · rintro _ ⟨v', rfl⟩
    exact ⟨V, g, v', hst, rfl⟩
  · exact (isOpenMap_of_generalizingMap g.left (Flat.generalizingMap g.left)).isOpen_range

/-- Two sections agree on every étale `W`-scheme whose image lies in their agreement locus. -/
lemma map_eq_of_range_subset_etaleAgreementLocus {s t : F.obj.obj (op W)} {U : X.Etale}
    (q : U ⟶ W) (hq : Set.range q.left ⊆ etaleAgreementLocus F s t) :
    F.obj.map q.op s = F.obj.map q.op t := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  let R : Sieve U := Presheaf.equalizerSieve (F := F.obj) (X := op U) (F.obj.map q.op s)
    (F.obj.map q.op t)
  have hR : R ∈ X.smallEtaleTopology U := by
    rw [mem_smallEtaleTopology_iff]
    intro u
    obtain ⟨V, g, v, hst, hv⟩ := hq ⟨u, rfl⟩
    obtain ⟨z, hz₁, hz₂⟩ := Pullback.exists_preimage_pullback (f := g.left) (g := q.left) v u hv
    let T : X.Etale := Etale.mk (pullback.snd g.left q.left ≫ U.hom)
    let a : T ⟶ U := MorphismProperty.Over.homMk (pullback.snd g.left q.left) rfl trivial
    let b : T ⟶ V := MorphismProperty.Over.homMk (pullback.fst g.left q.left) (by
      change pullback.fst g.left q.left ≫ V.hom = pullback.snd g.left q.left ≫ U.hom
      rw [← MorphismProperty.Over.w g, pullback.condition_assoc, MorphismProperty.Over.w q])
      trivial
    have hab : a ≫ q = b ≫ g := by
      apply MorphismProperty.Over.Hom.ext
      exact pullback.condition.symm
    refine ⟨T, a, z, ?_, hz₂⟩
    change F.obj.map a.op (F.obj.map q.op s) = F.obj.map a.op (F.obj.map q.op t)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, hab,
      op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hst]
  exact (hF R hR).isSeparatedFor.ext fun _ f hf ↦ hf

/-- If the germs of `s` and `t` at a geometric point `w` of `W` agree, the image of `w` lies in
the agreement locus of `s` and `t`. -/
lemma apply_mem_etaleAgreementLocus {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {x : Spec (.of Ω) ⟶ X} (w : (pointSmallEtale x).fiber.obj W) {s t : F.obj.obj (op W)}
    (h : (pointSmallEtale x).toPresheafFiber W w F.obj s =
      (pointSmallEtale x).toPresheafFiber W w F.obj t) (p : Spec (.of Ω)) :
    w.left p ∈ etaleAgreementLocus F s t := by
  obtain ⟨V, g, v, hv, hst⟩ :=
    ((pointSmallEtale x).toPresheafFiber_eq_iff' (P := F.obj) W w s t).1 h
  refine ⟨V, g, v.left p, hst, ?_⟩
  rw [← hv, pointSmallEtale_fiber_map_apply]
  rfl

end AgreementLocus

section UniversallyClosed

variable {X Y : Scheme.{u}} {F : Sheaf X.smallEtaleTopology (Type u)}

/-- Let `f : X ⟶ Y` be universally closed, `(V, v)` an étale neighbourhood of a geometric point
`ȳ` of `Y`, and `s t` two sections of `F` over `X ×_Y V` whose agreement locus contains the fibre of
`X ×_Y V ⟶ V` over the image of `v`. Then the germs of `s` and `t` at `ȳ`, as sections of `f_* F`,
agree. -/
lemma toPresheafFiber_etalePushforward_eq_of_universallyClosed (f : X ⟶ Y) [UniversallyClosed f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] {y : Spec (.of Ω) ⟶ Y} {V : Y.Etale}
    (v : (pointSmallEtale y).fiber.obj V) {s t : F.obj.obj (op ((Etale.pullback f).obj V))}
    (h : ∀ (x : ((Etale.pullback f).obj V).left) (p : Spec (.of Ω)),
      pullback.fst V.hom f x = v.left p → x ∈ etaleAgreementLocus F s t) :
    (pointSmallEtale y).toPresheafFiber V v ((etalePushforward f).obj F).obj s =
      (pointSmallEtale y).toPresheafFiber V v ((etalePushforward f).obj F).obj t := by
  let Z : Set ((Etale.pullback f).obj V).left := (etaleAgreementLocus F s t)ᶜ
  have hZ : IsClosed (pullback.fst V.hom f '' Z) :=
    (pullback.fst V.hom f).isClosedMap _ (isOpen_etaleAgreementLocus s t).isClosed_compl
  let O : V.left.Opens := ⟨(pullback.fst V.hom f '' Z)ᶜ, hZ.isOpen_compl⟩
  have hvO : Set.range v.left ⊆ (O : Set V.left) := by
    rintro _ ⟨p, rfl⟩ ⟨x, hx, hxp⟩
    exact hx (h x p hxp)
  let V₀ : Y.Etale := Etale.mk (O.ι ≫ V.hom)
  let ι : V₀ ⟶ V := MorphismProperty.Over.homMk O.ι rfl trivial
  let v₀ : (pointSmallEtale y).fiber.obj V₀ :=
    Over.homMk (IsOpenImmersion.lift O.ι v.left (hvO.trans_eq (Scheme.Opens.range_ι O).symm)) (by
      change IsOpenImmersion.lift O.ι v.left _ ≫ O.ι ≫ V.hom = y
      rw [IsOpenImmersion.lift_fac_assoc]
      exact Over.w v)
  refine ((pointSmallEtale y).toPresheafFiber_eq_iff' _ _ _ _).2 ⟨V₀, ι, v₀, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    rw [pointSmallEtale_fiber_map_apply]
    exact IsOpenImmersion.lift_fac _ _ _
  · refine map_eq_of_range_subset_etaleAgreementLocus ((Etale.pullback f).map ι) ?_
    rintro _ ⟨z, rfl⟩
    by_contra hz
    have h₁ : pullback.fst V.hom f (((Etale.pullback f).map ι).left z) =
        O.ι (pullback.fst V₀.hom f z) := by
      have := congrArg (fun φ ↦ φ z) (Etale.pullback_map_left_fst f ι)
      simp only [Scheme.Hom.comp_apply] at this
      exact this
    have h₂ : O.ι (pullback.fst V₀.hom f z) ∈ (O : Set V.left) :=
      (Scheme.Opens.range_ι O).le ⟨_, rfl⟩
    exact h₂ ⟨_, hz, h₁⟩

end UniversallyClosed

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}
  {F : Sheaf X.smallEtaleTopology (Type u)}

/-- If the images of two sections `s t ∈ F(W)` in `(h^* F)(X' ×_X W)` agree after restriction
along `k : W' ⟶ X' ×_X W`, then the image of `W'` in `W` lies in the agreement locus of `s`
and `t`. -/
lemma range_subset_etaleAgreementLocus (h : X' ⟶ X) {W : X.Etale} {s t : F.obj.obj (op W)}
    {W' : X'.Etale} (k : W' ⟶ (Etale.pullback h).obj W)
    (hk : ((etalePullback h).obj F).obj.map k.op
        (((etaleAdjunction h).unit.app F).hom.app (op W) s) =
      ((etalePullback h).obj F).obj.map k.op
        (((etaleAdjunction h).unit.app F).hom.app (op W) t)) :
    Set.range (k.left ≫ pullback.fst W.hom h) ⊆ etaleAgreementLocus F s t := by
  rintro _ ⟨w', rfl⟩
  let x := W'.left.fromSpecAlgClosure w'
  let ŵ : (pointSmallEtale (x ≫ W'.hom)).fiber.obj W' := Over.homMk x rfl
  obtain ⟨w₀, hb⟩ : ∃ w₀, (pointSmallEtaleFiberHom h (x ≫ W'.hom)).app W w₀ =
      (pointSmallEtale (x ≫ W'.hom)).fiber.map k ŵ := by
    refine ⟨(pointSmallEtaleFiberInv h (x ≫ W'.hom)).app W
      ((pointSmallEtale (x ≫ W'.hom)).fiber.map k ŵ), ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp [pointSmallEtaleFiberHom, pointSmallEtaleFiberInv]
    · have : ((pointSmallEtale (x ≫ W'.hom)).fiber.map k ŵ).left ≫ pullback.snd W.hom h =
          x ≫ W'.hom := Over.w ((pointSmallEtale (x ≫ W'.hom)).fiber.map k ŵ)
      simpa [pointSmallEtaleFiberHom, pointSmallEtaleFiberInv] using this.symm
  have H := congrArg ((pointSmallEtale (x ≫ W'.hom)).toPresheafFiber W' ŵ
    ((etalePullback h).obj F).obj) hk
  rw [GrothendieckTopology.Point.toPresheafFiber_w_apply,
    GrothendieckTopology.Point.toPresheafFiber_w_apply, ← hb,
    ← sheafFiberEtalePullbackIso_hom_app_toPresheafFiber,
    ← sheafFiberEtalePullbackIso_hom_app_toPresheafFiber] at H
  have H' := ((isIso_iff_bijective _).1 inferInstance).1 H
  have hw₀ : w₀.left = (x ≫ k.left) ≫ pullback.fst W.hom h := by
    have e : ((pointSmallEtaleFiberHom h (x ≫ W'.hom)).app W w₀).left = x ≫ k.left :=
      congrArg (fun a ↦ a.left) hb
    rw [← e]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨p, hp⟩ : ∃ p, x p = w' := ⟨_, Scheme.fromSpecAlgClosure_apply _ _⟩
  have := apply_mem_etaleAgreementLocus w₀ H' p
  rw [hw₀] at this
  rw [← hp]
  simp only [Scheme.Hom.comp_apply] at this ⊢
  exact this

/-- For a cartesian square `X' = X ×_Y Y'` and an étale `Y'`-morphism `φ : V' ⟶ Y' ×_Y V`, every
point of `X ×_Y V` lying over the image of a point `q` of `V'` comes from a point of
`X' ×_{Y'} V'`. -/
lemma exists_preimage_etalePullback_baseChange (hsq : IsPullback h f' f g) {V : Y.Etale}
    {V' : Y'.Etale} (φ : V' ⟶ (Etale.pullback g).obj V) (x : ((Etale.pullback f).obj V).left)
    (q : V'.left) (hxq : pullback.fst V.hom f x = pullback.fst V.hom g (φ.left q)) :
    ∃ w : ((Etale.pullback f').obj V').left,
      (((Etale.pullback f').map φ).left ≫ ((Etale.baseChangeComparison hsq.w).app V).left ≫
        pullback.fst ((Etale.pullback f).obj V).hom h) w = x := by
  let a := ((Etale.pullback f').map φ).left ≫ ((Etale.baseChangeComparison hsq.w).app V).left ≫
    pullback.fst ((Etale.pullback f).obj V).hom h
  have ha₁ : a ≫ pullback.snd V.hom f = pullback.snd V'.hom f' ≫ h := by
    simp [a]
  have ha₂ : a ≫ pullback.fst V.hom f = pullback.fst V'.hom f' ≫ φ.left ≫
      pullback.fst V.hom g := by
    simp [a]
  have hc : (φ.left ≫ pullback.fst V.hom g) ≫ V.hom = V'.hom ≫ g := by
    rw [Category.assoc, pullback.condition, ← MorphismProperty.Over.w φ, Category.assoc]
    rfl
  have hpb : IsPullback a (pullback.fst V'.hom f') (pullback.fst V.hom f)
      (φ.left ≫ pullback.fst V.hom g) := by
    refine IsPullback.of_right ?_ ha₂ (IsPullback.of_hasPullback V.hom f).flip
    have := (IsPullback.of_hasPullback V'.hom f').flip.paste_horiz hsq
    rwa [← ha₁, ← hc] at this
  obtain ⟨w, hw, -⟩ := exists_preimage_of_isPullback hpb x q hxq
  exact ⟨w, hw⟩

/-- **Base change for universally closed morphisms, injectivity on stalks** (Stacks 0A3T,
injectivity part): for a cartesian square with `f` universally closed, the base change morphism
`g^* f_* F ⟶ f'_* h^* F` is injective on the stalks at every geometric point of `Y'`. -/
theorem injective_sheafFiber_etaleBaseChangeMap_of_universallyClosed [UniversallyClosed f]
    (hsq : IsPullback h f' f g) (F : Sheaf X.smallEtaleTopology (Type u)) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y') :
    Function.Injective ((pointSmallEtale y).sheafFiber.map ((etaleBaseChangeMap hsq.w).app F)) := by
  let e₁ := (sheafFiberEtalePullbackIso g y).app ((etalePushforward f).obj F)
  have he₁ : Function.Bijective e₁.hom := (isIso_iff_bijective _).mp inferInstance
  have key (V : Y.Etale) (v : (pointSmallEtale (y ≫ g)).fiber.obj V)
      (σ : F.obj.obj (op ((Etale.pullback f).obj V))) :
      (pointSmallEtale y).sheafFiber.map ((etaleBaseChangeMap hsq.w).app F)
        (e₁.hom ((pointSmallEtale (y ≫ g)).toPresheafFiber V v
          ((etalePushforward f).obj F).obj σ)) =
      (pointSmallEtale y).toPresheafFiber ((Etale.pullback g).obj V)
        ((pointSmallEtaleFiberHom g y).app V v)
        ((etalePushforward f').obj ((etalePullback h).obj F)).obj
        (((etalePullback h).obj F).obj.map ((Etale.baseChangeComparison hsq.w).app V).op
          (((etaleAdjunction h).unit.app F).hom.app (op ((Etale.pullback f).obj V)) σ)) := by
    simp only [e₁, Iso.app_hom]
    rw [sheafFiberEtalePullbackIso_hom_app_toPresheafFiber]
    erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
    erw [etaleBaseChangeMap_app_unit]
    rfl
  intro a b hab
  obtain ⟨a, rfl⟩ := he₁.2 a
  obtain ⟨b, rfl⟩ := he₁.2 b
  obtain ⟨V, v, s, t, rfl, rfl⟩ := (pointSmallEtale (y ≫ g)).toPresheafFiber_jointly_surjective₂
    (P := ((etalePushforward f).obj F).obj) a b
  rw [key, key] at hab
  obtain ⟨V', φ, v', hv', hst⟩ := ((pointSmallEtale y).toPresheafFiber_eq_iff' _ _ _ _).1 hab
  congr 1
  refine toPresheafFiber_etalePushforward_eq_of_universallyClosed f v fun x p hx ↦ ?_
  let k := (Etale.pullback f').map φ ≫ (Etale.baseChangeComparison hsq.w).app V
  have hk : ((etalePullback h).obj F).obj.map k.op
        (((etaleAdjunction h).unit.app F).hom.app (op ((Etale.pullback f).obj V)) s) =
      ((etalePullback h).obj F).obj.map k.op
        (((etaleAdjunction h).unit.app F).hom.app (op ((Etale.pullback f).obj V)) t) := by
    simp only [k, op_comp, Functor.map_comp_apply]
    exact hst
  have h₁ : v'.left ≫ φ.left ≫ pullback.fst V.hom g = v.left := by
    have := congrArg (fun a ↦ a.left ≫ pullback.fst V.hom g) hv'
    simp only [pointSmallEtaleFiberHom, pointSmallEtale_fiber_map_apply] at this
    simpa using this
  have hq : pullback.fst V.hom f x = pullback.fst V.hom g (φ.left (v'.left p)) := by
    rw [hx, ← h₁]
    simp only [Scheme.Hom.comp_apply]
    rfl
  obtain ⟨w, hw⟩ := exists_preimage_etalePullback_baseChange hsq φ x (v'.left p) hq
  exact range_subset_etaleAgreementLocus h k hk ⟨w, hw⟩

/-- **Base change for universally closed morphisms, injectivity** (SGA 4 XII 5.1 in degree `0`,
injectivity part; Stacks 0A3T): for a cartesian square with `f` universally closed, the base
change morphism `g^* f_* F ⟶ f'_* h^* F` of étale sheaves of sets is a monomorphism. -/
theorem mono_etaleBaseChangeMap_of_universallyClosed [UniversallyClosed f]
    (hsq : IsPullback h f' f g) (F : Sheaf X.smallEtaleTopology (Type u)) :
    Mono ((etaleBaseChangeMap hsq.w).app F) := by
  have hcons := isConservative_pointSmallEtale (fun y : Y' ↦ Y'.fromSpecAlgClosure y) (by
    refine Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨y, _, Y'.fromSpecAlgClosure_apply y⟩)
  rw [hcons.jointlyReflectIsomorphisms_type.jointlyReflectMonomorphisms.mono_iff]
  rintro ⟨Ψ, hΨ⟩
  obtain ⟨y, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hΨ
  rw [mono_iff_injective]
  exact injective_sheafFiber_etaleBaseChangeMap_of_universallyClosed hsq F _

end BaseChange

end AlgebraicGeometry.Scheme
