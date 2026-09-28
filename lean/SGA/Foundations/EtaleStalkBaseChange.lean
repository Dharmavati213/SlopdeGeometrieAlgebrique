/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.BaseChange
import SGA.Foundations.EtaleStalkPullback
import SGA.Foundations.EtaleStalkPushforward

/-!
# Base change for finite morphisms

For a cartesian square
```
X' --h--> X
|f'       |f
Y' --g--> Y
```
with `f` finite, the base change morphism `g^* f_* F ⟶ f'_* h^* F` of étale sheaves of sets is an
isomorphism (`AlgebraicGeometry.Scheme.isIso_etaleBaseChangeMap_of_isFinite`; SGA 4 VIII 5.6 for
finite morphisms, Stacks 095T). On the stalks at a geometric point `ȳ'` of `Y'` with `Ω`
algebraically closed, both sides are `∏ F_x̄` over the geometric points `x̄` of `X` over `g ∘ ȳ'`,
which are the images of the geometric points of `X'` over `ȳ'`
(`AlgebraicGeometry.Scheme.Hom.bijective_etalePushforwardStalkMap`); the base change morphism is
compatible with these descriptions, as one sees on germs
(`AlgebraicGeometry.Scheme.etaleBaseChangeMap_app_unit`,
`AlgebraicGeometry.Scheme.sheafFiberEtalePullbackIso_hom_app_toPresheafFiber`).
-/

universe u

open CategoryTheory Limits Opposite

noncomputable section

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}

/-- The base change morphism on sections coming from `f_* F`: the image under
`g^* f_* F ⟶ f'_* h^* F`
of the image of `s ∈ (f_* F)(V) = F(X ×_Y V)` in `(g^* f_* F)(Y' ×_Y V)` is the restriction of the
image of `s` in `(h^* F)(X' ×_X (X ×_Y V))` to `X' ×_{Y'} (Y' ×_Y V)`. -/
lemma etaleBaseChangeMap_app_unit (w : h ≫ f = f' ≫ g) (F : Sheaf X.smallEtaleTopology (Type u))
    (V : Y.Etale) (s : F.obj.obj (op ((Etale.pullback f).obj V))) :
    ((etaleBaseChangeMap w).app F).hom.app (op ((Etale.pullback g).obj V))
        (((etaleAdjunction g).unit.app ((etalePushforward f).obj F)).hom.app (op V) s) =
      ((etalePullback h).obj F).obj.map ((Etale.baseChangeComparison w).app V).op
        (((etaleAdjunction h).unit.app F).hom.app (op ((Etale.pullback f).obj V)) s) := by
  have H := unit_mateEquiv (etaleAdjunction h) (etaleAdjunction g) (etaleBaseChangeMap w) F
  rw [mateEquiv_etaleBaseChangeMap] at H
  have H' := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (·.hom) H) (op V)) s
  exact H'.symm

variable [IsFinite f] (hsq : IsPullback h f' f g) (F : Sheaf X.smallEtaleTopology (Type u))

omit [IsFinite f] in
include hsq in
/-- The geometric points of `X'` over `ȳ'` are the geometric points of `X` over `g ∘ ȳ'`. -/
lemma bijective_pointsOver_of_isPullback {Ω : Type u} [Field Ω] (y : Spec (.of Ω) ⟶ Y') :
    Function.Bijective (fun x : {x : Spec (.of Ω) ⟶ X' // x ≫ f' = y} ↦
      (⟨x.1 ≫ h, by rw [Category.assoc, hsq.w, reassoc_of% x.2]⟩ :
        {x : Spec (.of Ω) ⟶ X // x ≫ f = y ≫ g})) := by
  refine ⟨fun x₁ x₂ hx ↦ Subtype.ext ?_, fun x ↦ ?_⟩
  · have hx' : x₁.1 ≫ h = x₂.1 ≫ h := congrArg Subtype.val hx
    exact hsq.hom_ext hx' (x₁.2.trans x₂.2.symm)
  · exact ⟨⟨hsq.lift x.1 y x.2, hsq.lift_snd _ _ _⟩, Subtype.ext (hsq.lift_fst _ _ _)⟩

/-- **Finite base change on stalks**: at a geometric point `ȳ'` of `Y'` with `Ω` algebraically
closed, the base change morphism `g^* f_* F ⟶ f'_* h^* F` is bijective. -/
theorem bijective_sheafFiber_etaleBaseChangeMap {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y') :
    Function.Bijective
      ((pointSmallEtale y).sheafFiber.map ((etaleBaseChangeMap hsq.w).app F)) := by
  classical
  have : IsFinite f' := MorphismProperty.of_isPullback hsq inferInstance
  let Φ := pointSmallEtale y
  -- the maps
  let e₁ := (sheafFiberEtalePullbackIso g y).app ((etalePushforward f).obj F)
  let β := Φ.sheafFiber.map ((etaleBaseChangeMap hsq.w).app F)
  let m := f.etalePushforwardStalkMap F (y ≫ g)
  let m' := f'.etalePushforwardStalkMap ((etalePullback h).obj F) y
  let φ := fun x : {x : Spec (.of Ω) ⟶ X' // x ≫ f' = y} ↦
    (⟨x.1 ≫ h, by rw [Category.assoc, hsq.w, reassoc_of% x.2]⟩ :
      {x : Spec (.of Ω) ⟶ X // x ≫ f = y ≫ g})
  have hφ := bijective_pointsOver_of_isPullback hsq y
  let e₂ (x : {x : Spec (.of Ω) ⟶ X' // x ≫ f' = y}) :=
    (sheafFiberEtalePullbackIso h x.1).app F
  let R := fun (a : (pointSmallEtale (y ≫ g)).presheafFiber.obj ((etalePushforward f).obj F).obj)
    (x : {x : Spec (.of Ω) ⟶ X' // x ≫ f' = y}) ↦ (e₂ x).hom (m a (φ x))
  -- `R` is bijective
  have hR : Function.Bijective R := by
    let E := Equiv.ofBijective φ hφ
    have h₁ : Function.Bijective (fun (v : ∀ x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y ≫ g},
        (pointSmallEtale x.1).presheafFiber.obj F.obj) (x : {x : Spec (.of Ω) ⟶ X' // x ≫ f' = y})
          ↦ v (φ x)) :=
      (Equiv.piCongrLeft' (fun x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y ≫ g} ↦
        (pointSmallEtale x.1).presheafFiber.obj F.obj) E.symm).bijective
    have h₂ : Function.Bijective (fun (v : ∀ x : {x : Spec (.of Ω) ⟶ X' // x ≫ f' = y},
        (pointSmallEtale (x.1 ≫ h)).presheafFiber.obj F.obj) x ↦ (e₂ x).hom (v x)) :=
      (Equiv.piCongrRight fun x ↦ ((e₂ x).toEquiv)).bijective
    exact h₂.comp (h₁.comp (Hom.bijective_etalePushforwardStalkMap f (y ≫ g) F))
  -- the compatibility on germs
  have key : m' ∘ β ∘ e₁.hom = R := by
    funext a
    obtain ⟨V, v, s, rfl⟩ := (pointSmallEtale (y ≫ g)).toPresheafFiber_jointly_surjective
      (P := ((etalePushforward f).obj F).obj) a
    funext x
    simp only [Function.comp_apply, R, e₁, e₂, m, m', β, Iso.app_hom]
    rw [sheafFiberEtalePullbackIso_hom_app_toPresheafFiber]
    erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
    erw [etaleBaseChangeMap_app_unit]
    rw [Hom.etalePushforwardStalkMap_toPresheafFiber]
    erw [Hom.etalePushforwardStalkMap_toPresheafFiber]
    erw [GrothendieckTopology.Point.toPresheafFiber_w_apply]
    rw [sheafFiberEtalePullbackIso_hom_app_toPresheafFiber]
    have hpt : (pointSmallEtale x.1).fiber.map ((Etale.baseChangeComparison hsq.w).app V)
        (f'.pullbackPoint x.2 ((pointSmallEtaleFiberHom g y).app V v)) =
        (pointSmallEtaleFiberHom h x.1).app ((Etale.pullback f).obj V)
          (f.pullbackPoint (φ x).2 v) := by
      apply Over.OverMorphism.ext
      rw [pointSmallEtale_fiber_map_apply]
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp [pointSmallEtaleFiberHom]
        · simp [pointSmallEtaleFiberHom]
          rfl
      · simp [pointSmallEtaleFiberHom]
    exact congrArg (fun p ↦ (pointSmallEtale x.1).toPresheafFiber _ p ((etalePullback h).obj F).obj
      (((etaleAdjunction h).unit.app F).hom.app (op ((Etale.pullback f).obj V)) s)) hpt
  have hm' : Function.Bijective m' :=
    Hom.bijective_etalePushforwardStalkMap f' y ((etalePullback h).obj F)
  have he₁ : Function.Bijective e₁.hom := (isIso_iff_bijective _).mp inferInstance
  refine ⟨fun a b hab ↦ ?_, fun b ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := he₁.2 a
    obtain ⟨b, rfl⟩ := he₁.2 b
    have := congrArg m' hab
    change (m' ∘ β ∘ e₁.hom) a = (m' ∘ β ∘ e₁.hom) b at this
    rw [key] at this
    rw [hR.1 this]
  · obtain ⟨a, ha⟩ := hR.2 (m' b)
    refine ⟨e₁.hom a, hm'.1 ?_⟩
    change (m' ∘ β ∘ e₁.hom) a = m' b
    rw [key, ha]

include hsq in
/-- **SGA 4 VIII 5.6 for finite morphisms** (Stacks 095T): for a cartesian square with `f`
finite, the base change morphism `g^* f_* F ⟶ f'_* h^* F` is an isomorphism, i.e. the formation
of `f_* F` commutes with every base change. -/
theorem isIso_etaleBaseChangeMap_of_isFinite : IsIso ((etaleBaseChangeMap hsq.w).app F) := by
  have hcons := isConservative_pointSmallEtale (fun y : Y' ↦ Y'.fromSpecAlgClosure y) (by
    refine Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨y, _, Y'.fromSpecAlgClosure_apply y⟩)
  rw [hcons.jointlyReflectIsomorphisms_type.isIso_iff]
  rintro ⟨Ψ, hΨ⟩
  obtain ⟨y, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hΨ
  rw [isIso_iff_bijective]
  exact bijective_sheafFiber_etaleBaseChangeMap hsq F _

end AlgebraicGeometry.Scheme
