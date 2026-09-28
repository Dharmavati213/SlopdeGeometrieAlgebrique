/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.TorsorEtale
import SGA.Foundations.Etale.TorsorPushforward
import SGA.Foundations.EtaleStalkPushforward
import SGA.Foundations.Limits.IntegralApproximation

/-!
# Torsors are locally trivial along integral morphisms

Let `f : X ⟶ Y` be integral and `P` a torsor under a sheaf of groups on the small étale site of
`X`. Then `P` is locally trivial over `Y`: every étale `Y`-scheme `T` is covered by étale
`V ⟶ T` such that `P` has a section over `X ×_Y V`
(`AlgebraicGeometry.Scheme.isLocallyTrivialAlong_etalePullback_of_isIntegralHom`; SGA 4 VIII 5.8,
i.e. `R¹f_* G = 1` for sheaves of groups).

* For `f` finite (`AlgebraicGeometry.Scheme.isLocallyTrivialAlong_etalePullback_of_isFinite`), the
  stalks of `P` at all geometric points are nonempty, so by SGA 4 VIII 5.5
  (`AlgebraicGeometry.Scheme.Hom.bijective_etalePushforwardStalkMap`) the stalks of `f_* P` are
  nonempty.
* For `f` integral and `Y` affine, finitely many affine étale `U i ⟶ X` on which `P` has sections
  cover `X`; they come from étale `W i ⟶ X'` for a factorization `X ⟶ X' ⟶ Y` of `f` through a
  finite `X'` (`AlgebraicGeometry.Scheme.exists_isFinite_etale_isPullback_of_isIntegralHom`), and
  the finite case applies to the direct image of `P` on `X'`. The general case reduces to affine
  opens of `Y`.
-/

universe u

open CategoryTheory Limits Opposite IsLocalRing

noncomputable section

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {G : X.Etaleᵒᵖ ⥤ GrpCat.{u}}
  (P : Torsor X.smallEtaleTopology G)

/-- The stalks of a torsor at geometric points are nonempty. -/
lemma _root_.CategoryTheory.Torsor.nonempty_presheafFiber {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) : Nonempty ((pointSmallEtale x).presheafFiber.obj P.obj) := by
  let U : X.Etale := Etale.mk (𝟙 X)
  let u : (pointSmallEtale x).fiber.obj U := Over.homMk x (Category.comp_id x)
  obtain ⟨V, g, ⟨p⟩, v, -⟩ := (pointSmallEtale x).jointly_surjective _ (P.nonemptySieve_mem U) u
  exact ⟨(pointSmallEtale x).toPresheafFiber V v P.obj p⟩

/-- A torsor is locally trivial along `f` as soon as every geometric point of `Y` (with
algebraically closed field) has an étale neighbourhood `V` such that the torsor has a section over
`X ×_Y V`. -/
lemma isLocallyTrivialAlong_etalePullback_of_forall
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      ∃ (V : Y.Etale) (_ : (pointSmallEtale y).fiber.obj V),
        Nonempty (P.obj.obj (op ((Etale.pullback f).obj V)))) :
    P.IsLocallyTrivialAlong Y.smallEtaleTopology (Etale.pullback f) := by
  intro T
  rw [mem_smallEtaleTopology_iff]
  intro t
  -- a geometric point at `t` with algebraically closed field
  let Ω := AlgebraicClosure (T.left.residueField t)
  let yb : Spec (.of Ω) ⟶ T.left := T.left.fromSpecAlgClosure t
  let y : Spec (.of Ω) ⟶ Y := yb ≫ T.hom
  let vT : (pointSmallEtale y).fiber.obj T := Over.homMk yb rfl
  obtain ⟨V, v, ⟨s⟩⟩ := h Ω y
  -- a common refinement of `(V, v)` and `(T, vT)`
  let e₁ : (pointSmallEtale y).fiber.Elements := ⟨V, v⟩
  let e₂ : (pointSmallEtale y).fiber.Elements := ⟨T, vT⟩
  let W := IsCofiltered.min e₁ e₂
  let a₁ : W ⟶ e₁ := IsCofiltered.minToLeft e₁ e₂
  let a₂ : W ⟶ e₂ := IsCofiltered.minToRight e₁ e₂
  refine ⟨W.1, a₂.1, W.2.left (closedPoint Ω), ⟨P.obj.map ((Etale.pullback f).map a₁.1).op s⟩, ?_⟩
  have h₂ : W.2 ≫ (Etale.forget Y).map a₂.1 = vT := a₂.2
  have h₂' : W.2.left ≫ a₂.1.left = yb := congrArg (fun φ ↦ φ.left) h₂
  change (W.2.left ≫ a₂.1.left) (closedPoint Ω) = t
  rw [h₂']
  exact T.left.fromSpecAlgClosure_apply t

/-- For `f` finite, a sheaf of sets on `X` with nonempty stalks at all geometric points has a
section over `X ×_Y V` for some étale neighbourhood `V` of any geometric point of `Y`. -/
lemma exists_etaleNbhd_nonempty_of_isFinite [IsFinite f] (F : Sheaf X.smallEtaleTopology (Type u))
    (hF : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale x).presheafFiber.obj F.obj))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    ∃ (V : Y.Etale) (_ : (pointSmallEtale y).fiber.obj V),
      Nonempty (F.obj.obj (op ((Etale.pullback f).obj V))) := by
  have hne : Nonempty (∀ x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y},
      (pointSmallEtale x.1).presheafFiber.obj F.obj) :=
    ⟨fun x ↦ (hF Ω x.1).some⟩
  obtain ⟨a, -⟩ := (Hom.bijective_etalePushforwardStalkMap f y F).2 hne.some
  obtain ⟨V, v, s, -⟩ := (pointSmallEtale y).toPresheafFiber_jointly_surjective
    (P := ((etalePushforward f).obj F).obj) a
  exact ⟨V, v, ⟨s⟩⟩

/-- **SGA 4 VIII 5.8 for finite morphisms**: a torsor on the small étale site of `X` is locally
trivial along a finite morphism `f : X ⟶ Y`: every étale `Y`-scheme is covered by étale
`V` such that the torsor has a section over `X ×_Y V`. -/
theorem isLocallyTrivialAlong_etalePullback_of_isFinite [IsFinite f] :
    P.IsLocallyTrivialAlong Y.smallEtaleTopology (Etale.pullback f) :=
  isLocallyTrivialAlong_etalePullback_of_forall f P fun _ _ _ y ↦
    exists_etaleNbhd_nonempty_of_isFinite f
      ⟨P.obj, (isSheaf_iff_isSheaf_of_type _ _).2 P.isSheaf⟩
      (fun _ _ _ x ↦ P.nonempty_presheafFiber x) y

/-- For `f` integral with `Y` affine, every geometric point of `Y` has an étale neighbourhood
`V` such that a given torsor on `X` has a section over `X ×_Y V`. -/
lemma exists_etaleNbhd_nonempty_of_isIntegralHom_of_isAffine [IsIntegralHom f] [IsAffine Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    ∃ (V : Y.Etale) (_ : (pointSmallEtale y).fiber.obj V),
      Nonempty (P.obj.obj (op ((Etale.pullback f).obj V))) := by
  classical
  have : IsAffine X := isAffine_of_isAffineHom f
  -- affine étale `X`-schemes with sections of `P`, covering `X`
  have hcov := (mem_smallEtaleTopology_iff _ _).1 (P.nonemptySieve_mem (Etale.mk (𝟙 X)))
  choose V g z hVg hz using hcov
  have hVz (x : X) : (V x).hom (z x) = x := by
    have := hz x
    rwa [show (g x).left = (V x).hom from
      (Category.comp_id _).symm.trans (MorphismProperty.Over.w (g x))] at this
  have hex (x : X) : ∃ W : (V x).left.Opens, IsAffineOpen W ∧ z x ∈ W := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ :=
      (V x).left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (z x)) isOpen_univ
    exact ⟨W, hW, hzW⟩
  choose O' hO' hzO' using hex
  let u (x : X) : (O' x : Scheme.{u}) ⟶ X := (O' x).ι ≫ (V x).hom
  have hPu (x : X) : Nonempty (P.obj.obj (op (Etale.mk (u x)))) :=
    ⟨P.obj.map (MorphismProperty.Over.homMk (O' x).ι rfl :
      Etale.mk (u x) ⟶ V x).op (hVg x).some⟩
  -- finitely many suffice
  have hopen (x : X) : IsOpen (Set.range (u x)) := (u x).isOpenMap.isOpen_range
  have hmem (x : X) : x ∈ Set.range (u x) := ⟨⟨z x, hzO' x⟩, hVz x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ Set.range (u x)) hopen
    fun x _ ↦ Set.mem_iUnion.2 ⟨x, hmem x⟩
  have : ∀ i : t, IsAffine (O' i.1 : Scheme.{u}) := fun i ↦ hO' i.1
  obtain ⟨X', π, f', W, w, e, hπf, hf', hπ, hw, hpb⟩ :=
    exists_isFinite_etale_isPullback_of_isIntegralHom f (fun i : t ↦ u i.1)
  -- the stalks of `π_* P` are nonempty
  let F : Sheaf X.smallEtaleTopology (Type u) :=
    ⟨P.obj, (isSheaf_iff_isSheaf_of_type _ _).2 P.isSheaf⟩
  let F' := (etalePushforward π).obj F
  have hF' (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (x' : Spec (.of Ω') ⟶ X') :
      Nonempty ((pointSmallEtale x').presheafFiber.obj F'.obj) := by
    obtain ⟨x, hx⟩ := hπ (x' (closedPoint Ω'))
    obtain ⟨i, hi⟩ : ∃ i : t, x ∈ Set.range (u i.1) := by
      have := ht (Set.mem_univ x)
      simp only [Set.mem_iUnion] at this
      obtain ⟨i, hi, hx⟩ := this
      exact ⟨⟨i, hi⟩, hx⟩
    obtain ⟨z', hz'⟩ := hi
    have := hw i
    have hwz : w i (e i z') = x' (closedPoint Ω') := by
      rw [← Scheme.Hom.comp_apply, (hpb i).w, Scheme.Hom.comp_apply, hz', hx]
    obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (w i) x' (e i z')
      (hwz.trans (congrArg x' (Subsingleton.elim _ _)))
    let Wo : X'.Etale := Etale.mk (w i)
    let wo : (pointSmallEtale x').fiber.obj Wo := Over.homMk l hl
    let φ : (Etale.pullback π).obj Wo ⟶ Etale.mk (u i.1) :=
      MorphismProperty.Over.homMk (hpb i).isoPullback.inv (by simp; rfl)
    exact ⟨(pointSmallEtale x').toPresheafFiber Wo wo F'.obj
      (P.obj.map φ.op (hPu i.1).some)⟩
  obtain ⟨V₁, v₁, ⟨s⟩⟩ := exists_etaleNbhd_nonempty_of_isFinite f' F' hF' y
  -- `X ×_Y V₁` maps to `X ×_{X'} (X' ×_Y V₁)`
  let ψ : (Etale.pullback f).obj V₁ ⟶ (Etale.pullback π).obj ((Etale.pullback f').obj V₁) :=
    MorphismProperty.Over.homMk
      (pullback.lift (pullback.lift (pullback.fst V₁.hom f) (pullback.snd V₁.hom f ≫ π)
        (by rw [pullback.condition, Category.assoc, hπf]))
        (pullback.snd V₁.hom f) (pullback.lift_snd _ _ _))
      (pullback.lift_snd _ _ _)
  exact ⟨V₁, v₁, ⟨P.obj.map ψ.op s⟩⟩

/-- For `f` integral, every geometric point of `Y` has an étale neighbourhood `V` such that a
given torsor on `X` has a section over `X ×_Y V`. -/
lemma exists_etaleNbhd_nonempty_of_isIntegralHom [IsIntegralHom f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    ∃ (V : Y.Etale) (_ : (pointSmallEtale y).fiber.obj V),
      Nonempty (P.obj.obj (op ((Etale.pullback f).obj V))) := by
  have hex : ∃ Y₀ : Y.Opens, IsAffineOpen Y₀ ∧ y (closedPoint Ω) ∈ Y₀ := by
    obtain ⟨_, ⟨Y₀, hY₀, rfl⟩, hyY₀, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (y (closedPoint Ω))) isOpen_univ
    exact ⟨Y₀, hY₀, hyY₀⟩
  obtain ⟨Y₀, hY₀, hyY₀⟩ := hex
  have : IsAffine Y₀ := hY₀
  have hrange : Set.range y ⊆ Set.range Y₀.ι := by
    rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim a (closedPoint Ω)]
    exact hyY₀
  let y₀ : Spec (.of Ω) ⟶ Y₀ := IsOpenImmersion.lift Y₀.ι y hrange
  have hy₀ : y₀ ≫ Y₀.ι = y := IsOpenImmersion.lift_fac _ _ _
  let X₀ := f ⁻¹ᵁ Y₀
  let f₀ : (X₀ : Scheme.{u}) ⟶ Y₀ := f ∣_ Y₀
  let P₀ := etaleRestrictTorsor X₀.ι P
  obtain ⟨V₀, v₀, ⟨s⟩⟩ := exists_etaleNbhd_nonempty_of_isIntegralHom_of_isAffine f₀ P₀ y₀
  let V : Y.Etale := Etale.mk (V₀.hom ≫ Y₀.ι)
  let v : (pointSmallEtale y).fiber.obj V :=
    Over.homMk v₀.left (by
      change v₀.left ≫ V₀.hom ≫ Y₀.ι = y
      rw [← Category.assoc, show v₀.left ≫ V₀.hom = y₀ from Over.w v₀, hy₀])
  -- `X ×_Y V` maps to `X₀ ×_{Y₀} V₀`
  have hr : Set.range (pullback.snd (V₀.hom ≫ Y₀.ι) f) ⊆ Set.range X₀.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (pullback.snd (V₀.hom ≫ Y₀.ι) f p) ∈ Y₀
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact (V₀.hom (pullback.fst (V₀.hom ≫ Y₀.ι) f p)).2
  let a := IsOpenImmersion.lift X₀.ι (pullback.snd (V₀.hom ≫ Y₀.ι) f) hr
  have ha : a ≫ X₀.ι = pullback.snd _ _ := IsOpenImmersion.lift_fac _ _ _
  have hcond : pullback.fst (V₀.hom ≫ Y₀.ι) f ≫ V₀.hom = a ≫ f₀ := by
    have : (pullback.fst (V₀.hom ≫ Y₀.ι) f ≫ V₀.hom) ≫ Y₀.ι = (a ≫ f₀) ≫ Y₀.ι := by
      rw [Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc a, ha]
      exact pullback.condition
    exact (cancel_mono Y₀.ι).mp this
  let ψ : (Etale.pullback f).obj V ⟶ (Etale.map X₀.ι).obj ((Etale.pullback f₀).obj V₀) :=
    MorphismProperty.Over.homMk (pullback.lift (pullback.fst _ _) a hcond) (by
      change pullback.lift _ a hcond ≫ pullback.snd V₀.hom f₀ ≫ X₀.ι = pullback.snd _ _
      rw [pullback.lift_snd_assoc, ha])
  exact ⟨V, v, ⟨P.obj.map ψ.op s⟩⟩

/-- **SGA 4 VIII 5.8**: a torsor on the small étale site of `X` is locally trivial along an
integral morphism `f : X ⟶ Y`: every étale `Y`-scheme is covered by étale `V` such that the torsor
has a section over `X ×_Y V` (i.e. `R¹f_* G = 1`). -/
theorem isLocallyTrivialAlong_etalePullback_of_isIntegralHom [IsIntegralHom f] :
    P.IsLocallyTrivialAlong Y.smallEtaleTopology (Etale.pullback f) :=
  isLocallyTrivialAlong_etalePullback_of_forall f P fun _ _ _ y ↦
    exists_etaleNbhd_nonempty_of_isIntegralHom f P y

end AlgebraicGeometry.Scheme
