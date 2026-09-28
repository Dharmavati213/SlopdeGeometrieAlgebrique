/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.EffectiveNearPoint
import SGA.SGA1.ExposeIX.QuasiAffineDescent

/-!
# SGA 1, Exposé IX, 4.2: effectiveness after a faithfully flat base change

IX.4.2: let `g : S' ⟶ S` be universally submersive, `X'` étale, separated and of finite type over
`S'` with a descent datum `D`, and `t : S₁ ⟶ S` faithfully flat and quasi-compact. Then `D` is
effective iff its base change `D₁` to `S₁` is.

SGA deduces this from "the theory of descent in categories", IX.4.1 and IX.3.3. We follow that
argument concretely. Let `X₁` be the descent of `D₁`, with projection `v₁ : X'₁ = X' ×_S S₁ ⟶ X₁`.

* `X₁` carries a descent datum relative to `t` (`FlatBaseChange.act`): on points,
  `(v₁(x', s₁), s₁') ↦ v₁(x', s₁')`; it is obtained by descending this morphism along the
  universally submersive map `v₁ ×_S S₁`, using IX.3.2.
* By IX.4.1 this datum is effective, giving `X` over `S` with `X₁ = X ×_S S₁`.
* The composite `X'₁ ⟶ X₁ ⟶ X` descends along `X'₁ ⟶ X'` (IX.3.2) to `v : X' ⟶ X`; the square is
  cartesian since the comparison map `X' ⟶ X ×_S S'` is étale and becomes an isomorphism after the
  surjective base change `S' ×_S S₁ ⟶ S'`, and `v` is compatible with `D` since it is so after
  base change.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc pullback.condition pullback.condition_assoc

namespace FlatBaseChange

variable {S' S X' S₁ X₁ : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'} (D : DescentDatum g a)
  (t : S₁ ⟶ S) {b₁ : X₁ ⟶ S₁} {v₁ : pullback a (pullback.fst g t) ⟶ X₁}

/-- (Implementation) `X'₁ ×_S S₁ ⟶ X₁ ×_S S₁`, the base change of `v₁`. -/
noncomputable abbrev π (hv₁ : IsPullback v₁ (pullback.snd a (pullback.fst g t)) b₁
    (pullback.snd g t)) :
    pullback (pullback.fst a (pullback.fst g t) ≫ a ≫ g) t ⟶ pullback (b₁ ≫ t) t :=
  pullback.map _ _ _ _ v₁ (𝟙 _) (𝟙 _) (by
    rw [Category.comp_id, reassoc_of% hv₁.w, pullback.condition_assoc, pullback.condition])
    (by simp)

/-- (Implementation) `(x'₁, s₁') ↦ (pr(x'₁), s₁')`, from `X'₁ ×_S S₁` to `X'₁`. -/
noncomputable abbrev m :
    pullback (pullback.fst a (pullback.fst g t) ≫ a ≫ g) t ⟶ pullback a (pullback.fst g t) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst a (pullback.fst g t))
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst a (pullback.fst g t) ≫ a)
      (pullback.snd _ _) (by simpa only [Category.assoc] using pullback.condition))
    (by simp)

variable (hv₁ : IsPullback v₁ (pullback.snd a (pullback.fst g t)) b₁ (pullback.snd g t))
  (hact₁ : (D.baseChange t).act ≫ v₁ =
    pullback.fst (pullback.snd a (pullback.fst g t) ≫ pullback.snd g t) (pullback.snd g t) ≫ v₁)

set_option backward.isDefEq.respectTransparency false in
include hact₁ in
/-- (Implementation) The kernel-pair condition for descending `(x'₁, s₁') ↦ v₁(pr(x'₁), s₁')`
along `v₁ ×_S S₁`. -/
lemma kernelPair_condition :
    pullback.fst (π t hv₁) (π t hv₁) ≫ m t ≫ v₁ = pullback.snd (π t hv₁) (π t hv₁) ≫ m t ≫ v₁ := by
  have hK := DescentDatum.isPullback_act hv₁ hact₁
  have e₁ : (pullback.fst (π t hv₁) (π t hv₁) ≫ pullback.fst _ _) ≫ v₁ =
      (pullback.snd (π t hv₁) (π t hv₁) ≫ pullback.fst _ _) ≫ v₁ := by
    have := congrArg (· ≫ pullback.fst (b₁ ≫ t) t) (pullback.condition (f := π t hv₁)
      (g := π t hv₁))
    simpa [-pullback.condition, -pullback.condition_assoc] using this
  have e₂ : pullback.fst (π t hv₁) (π t hv₁) ≫ pullback.snd _ _ =
      pullback.snd (π t hv₁) (π t hv₁) ≫ pullback.snd _ _ := by
    have := congrArg (· ≫ pullback.snd (b₁ ≫ t) t) (pullback.condition (f := π t hv₁)
      (g := π t hv₁))
    simpa [-pullback.condition, -pullback.condition_assoc] using this
  let r := hK.lift _ _ e₁
  have hr₁ : r ≫ (D.baseChange t).act = pullback.fst (π t hv₁) (π t hv₁) ≫ pullback.fst _ _ :=
    hK.lift_fst _ _ _
  have hr₂ : r ≫ pullback.fst _ _ = pullback.snd (π t hv₁) (π t hv₁) ≫ pullback.fst _ _ :=
    hK.lift_snd _ _ _
  have hact := (D.baseChange t).act_comp
  have hactX : (D.baseChange t).act ≫ pullback.fst a (pullback.fst g t) =
      DescentDatum.baseChangeAux g a t ≫ D.act := pullback.lift_fst _ _ _
  have hX'₁ := pullback.condition (f := a) (g := pullback.fst g t)
  have hS'₁ := pullback.condition (f := g) (g := t)
  have hX'' := pullback.condition (f := pullback.snd a (pullback.fst g t) ≫ pullback.snd g t)
    (g := pullback.snd g t)
  have hZ := pullback.condition (f := pullback.fst a (pullback.fst g t) ≫ a ≫ g) (g := t)
  have hσ : (r ≫ pullback.snd _ _ ≫ pullback.fst g t) ≫ g =
      (pullback.fst (π t hv₁) (π t hv₁) ≫ pullback.snd _ _) ≫ t := by
    calc (r ≫ pullback.snd _ _ ≫ pullback.fst g t) ≫ g
        = r ≫ pullback.snd _ _ ≫ pullback.snd g t ≫ t := by
          simp only [Category.assoc, hS'₁]
      _ = r ≫ pullback.fst _ _ ≫ pullback.snd a (pullback.fst g t) ≫ pullback.snd g t ≫ t := by
          rw [reassoc_of% hX''.symm]
      _ = pullback.snd (π t hv₁) (π t hv₁) ≫ pullback.fst _ _ ≫
            pullback.fst a (pullback.fst g t) ≫ a ≫ g := by
          rw [reassoc_of% hr₂, ← hS'₁, reassoc_of% hX'₁.symm]
      _ = _ := by rw [hZ, e₂, Category.assoc]
  let σ : pullback (π t hv₁) (π t hv₁) ⟶ pullback g t :=
    pullback.lift (r ≫ pullback.snd _ _ ≫ pullback.fst g t)
      (pullback.fst (π t hv₁) (π t hv₁) ≫ pullback.snd _ _) hσ
  have hρ : (pullback.snd (π t hv₁) (π t hv₁) ≫ m t) ≫
      pullback.snd a (pullback.fst g t) ≫ pullback.snd g t = σ ≫ pullback.snd g t := by
    simp only [Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd, σ, e₂]
  let ρ : pullback (π t hv₁) (π t hv₁) ⟶
      pullback (pullback.snd a (pullback.fst g t) ≫ pullback.snd g t) (pullback.snd g t) :=
    pullback.lift (pullback.snd (π t hv₁) (π t hv₁) ≫ m t) σ hρ
  have hρ₂ : ρ ≫ pullback.fst _ _ = pullback.snd (π t hv₁) (π t hv₁) ≫ m t :=
    pullback.lift_fst _ _ _
  have hbc : ρ ≫ DescentDatum.baseChangeAux g a t = r ≫ DescentDatum.baseChangeAux g a t := by
    apply pullback.hom_ext
    · simp only [Category.assoc, DescentDatum.baseChangeAux_fst, reassoc_of% hρ₂,
        reassoc_of% hr₂]
      simp
    · simp only [Category.assoc, DescentDatum.baseChangeAux_snd, ρ, σ, pullback.lift_snd_assoc,
        pullback.lift_fst]
  have hρ₁ : ρ ≫ (D.baseChange t).act = pullback.fst (π t hv₁) (π t hv₁) ≫ m t := by
    apply pullback.hom_ext
    · rw [Category.assoc, hactX, reassoc_of% hbc, ← hactX, reassoc_of% hr₁]
      simp
    · rw [Category.assoc, hact]
      simp only [ρ, pullback.lift_snd]
      apply pullback.hom_ext
      · simp only [σ, pullback.lift_fst, Category.assoc]
        rw [← hact]
        simp only [Category.assoc]
        rw [← hX'₁, reassoc_of% hr₁]
        simp
      · simp [σ]
  calc pullback.fst (π t hv₁) (π t hv₁) ≫ m t ≫ v₁ = ρ ≫ (D.baseChange t).act ≫ v₁ := by
        rw [reassoc_of% hρ₁]
    _ = ρ ≫ pullback.fst _ _ ≫ v₁ := by rw [hact₁]
    _ = _ := by rw [reassoc_of% hρ₂]

lemma isPullback_π :
    IsPullback (pullback.fst _ _) (π t hv₁) v₁ (pullback.fst (b₁ ≫ t) t) := by
  refine (IsPullback.of_right (h₁₂ := pullback.snd (b₁ ≫ t) t) (v₁₃ := t) (h₂₂ := b₁ ≫ t) ?_
    (by simp) (IsPullback.of_hasPullback (b₁ ≫ t) t).flip).flip
  have := (IsPullback.of_hasPullback (pullback.fst a (pullback.fst g t) ≫ a ≫ g) t).flip
  convert this using 1
  · simp
  · rw [reassoc_of% hv₁.w, pullback.condition_assoc, pullback.condition]

lemma universallySubmersive_π [UniversallySubmersive g] : UniversallySubmersive (π t hv₁) :=
  have : UniversallySubmersive v₁ := MorphismProperty.of_isPullback hv₁.flip inferInstance
  MorphismProperty.of_isPullback (isPullback_π t hv₁) inferInstance

lemma m_comp_v₁_b₁ : (m t ≫ v₁) ≫ b₁ = π t hv₁ ≫ pullback.snd (b₁ ≫ t) t := by
  rw [Category.assoc, hv₁.w]
  simp

include hact₁ in
lemma existsUnique_act [UniversallySubmersive g] [Etale b₁] :
    ∃! φ : pullback (b₁ ≫ t) t ⟶ X₁, φ ≫ b₁ = pullback.snd _ _ ∧ π t hv₁ ≫ φ = m t ≫ v₁ :=
  have := universallySubmersive_π t hv₁
  existsUnique_hom_of_kernelPair (π t hv₁) (pullback.snd (b₁ ≫ t) t) b₁ (m t ≫ v₁)
    (m_comp_v₁_b₁ t hv₁) (kernelPair_condition D t hv₁ hact₁)

/-- The descent datum on `X₁` relative to `t : S₁ ⟶ S`: `(v₁(x', s₁), s₁') ↦ v₁(x', s₁')`. -/
noncomputable def act [UniversallySubmersive g] [Etale b₁] : pullback (b₁ ≫ t) t ⟶ X₁ :=
  (existsUnique_act D t hv₁ hact₁).exists.choose

@[reassoc (attr := simp)]
lemma act_b₁ [UniversallySubmersive g] [Etale b₁] :
    act D t hv₁ hact₁ ≫ b₁ = pullback.snd _ _ :=
  (existsUnique_act D t hv₁ hact₁).exists.choose_spec.1

@[reassoc (attr := simp)]
lemma π_act [UniversallySubmersive g] [Etale b₁] :
    π t hv₁ ≫ act D t hv₁ hact₁ = m t ≫ v₁ :=
  (existsUnique_act D t hv₁ hact₁).exists.choose_spec.2

/-- (Implementation) `x'₁ ↦ (x'₁, s₁(x'₁))`, from `X'₁` to `X'₁ ×_S S₁`. -/
noncomputable abbrev zd : pullback a (pullback.fst g t) ⟶
    pullback (pullback.fst a (pullback.fst g t) ≫ a ≫ g) t :=
  pullback.lift (𝟙 _) (pullback.snd a (pullback.fst g t) ≫ pullback.snd g t) (by
    rw [Category.id_comp, Category.assoc, ← pullback.condition, pullback.condition_assoc])

lemma zd_m : zd (g := g) (a := a) t ≫ m t = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · apply pullback.hom_ext
    · simp [pullback.condition]
    · simp

lemma act_unit [UniversallySubmersive g] [Etale b₁] :
    pullback.lift (f := b₁ ≫ t) (g := t) (𝟙 X₁) b₁ (by simp) ≫ act D t hv₁ hact₁ = 𝟙 X₁ := by
  have : UniversallySubmersive v₁ := MorphismProperty.of_isPullback hv₁.flip inferInstance
  refine hom_ext_of_surjective v₁ b₁ (by simp) ?_
  have e : v₁ ≫ pullback.lift (f := b₁ ≫ t) (g := t) (𝟙 X₁) b₁ (by simp) = zd t ≫ π t hv₁ := by
    apply pullback.hom_ext
    · simp
    · simp [hv₁.w]
  rw [reassoc_of% e, π_act, reassoc_of% (zd_m t), Category.comp_id]

/-- (Implementation) The base change of `π` to the triple product. -/
noncomputable abbrev π₂ :
    pullback (pullback.snd (pullback.fst a (pullback.fst g t) ≫ a ≫ g) t ≫ t) t ⟶
      pullback (pullback.snd (b₁ ≫ t) t ≫ t) t :=
  pullback.map _ _ _ _ (π t hv₁) (𝟙 _) (𝟙 _) (by simp) (by simp)

lemma isPullback_π₂ :
    IsPullback (pullback.fst _ _) (π₂ t hv₁) (π t hv₁)
      (pullback.fst (pullback.snd (b₁ ≫ t) t ≫ t) t) := by
  refine (IsPullback.of_right (h₁₂ := pullback.snd (pullback.snd (b₁ ≫ t) t ≫ t) t) (v₁₃ := t)
    (h₂₂ := pullback.snd (b₁ ≫ t) t ≫ t) ?_ (by simp)
    (IsPullback.of_hasPullback (pullback.snd (b₁ ≫ t) t ≫ t) t).flip).flip
  have := (IsPullback.of_hasPullback
    (pullback.snd (pullback.fst a (pullback.fst g t) ≫ a ≫ g) t ≫ t) t).flip
  convert this using 1
  · simp
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) The descent datum on `X₁` relative to `t`. -/
noncomputable def datum [UniversallySubmersive g] [Etale b₁] : DescentDatum t b₁ where
  act := act D t hv₁ hact₁
  act_comp := act_b₁ D t hv₁ hact₁
  unit := act_unit D t hv₁ hact₁
  assoc := by
    have : UniversallySubmersive (π t hv₁) := universallySubmersive_π t hv₁
    have : Surjective (π₂ t hv₁) :=
      MorphismProperty.of_isPullback (isPullback_π₂ t hv₁) inferInstance
    refine hom_ext_of_surjective (π₂ t hv₁) b₁ (by simp) ?_
    have hZ := pullback.condition (f := pullback.fst a (pullback.fst g t) ≫ a ≫ g) (g := t)
    have hZ₂ := pullback.condition
      (f := pullback.snd (pullback.fst a (pullback.fst g t) ≫ a ≫ g) t ≫ t) (g := t)
    let z₁ : pullback (pullback.snd (pullback.fst a (pullback.fst g t) ≫ a ≫ g) t ≫ t) t ⟶
        pullback (pullback.fst a (pullback.fst g t) ≫ a ≫ g) t :=
      pullback.lift (pullback.fst _ _ ≫ m t) (pullback.snd _ _) (by
        simp only [Category.assoc, pullback.lift_fst_assoc]
        rw [hZ]
        exact hZ₂)
    let z₂ : pullback (pullback.snd (pullback.fst a (pullback.fst g t) ≫ a ≫ g) t ≫ t) t ⟶
        pullback (pullback.fst a (pullback.fst g t) ≫ a ≫ g) t :=
      pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
        simp only [Category.assoc]
        rw [hZ]
        exact hZ₂)
    have h₁ : π₂ t hv₁ ≫ pullback.lift (f := b₁ ≫ t) (g := t)
        (pullback.fst (pullback.snd (b₁ ≫ t) t ≫ t) t ≫ act D t hv₁ hact₁)
        (pullback.snd (pullback.snd (b₁ ≫ t) t ≫ t) t) (by simp) = z₁ ≫ π t hv₁ := by
      apply pullback.hom_ext
      · simp [z₁]
      · simp [z₁]
    have h₂ : π₂ t hv₁ ≫ pullback.lift (f := b₁ ≫ t) (g := t)
        (pullback.fst (pullback.snd (b₁ ≫ t) t ≫ t) t ≫ pullback.fst (b₁ ≫ t) t)
        (pullback.snd (pullback.snd (b₁ ≫ t) t ≫ t) t) (by simp) = z₂ ≫ π t hv₁ := by
      apply pullback.hom_ext
      · simp [z₂]
      · simp [z₂]
    have h₃ : z₁ ≫ m t = z₂ ≫ m t := by
      apply pullback.hom_ext
      · simp [z₁, z₂]
      · apply pullback.hom_ext
        · simp [z₁, z₂]
        · simp [z₁, z₂]
    rw [reassoc_of% h₁, reassoc_of% h₂, π_act, reassoc_of% h₃]

end FlatBaseChange

variable {S' S X' S₁ : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'}

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.2, sufficiency, in the form of the "sorites of descent" (IX.4.8, IX.4.9): let
`g : S' ⟶ S` be universally submersive, `X'` étale, separated and of finite type over `S'` with a
descent datum `D`, and `t : S₁ ⟶ S` universally submersive and an effective descent morphism
for étale separated schemes of finite type. If the base change of `D` to `S₁` is effective, so
is `D`. -/
theorem DescentDatum.isEffective_of_isEffective_baseChange [UniversallySubmersive g]
    (D : DescentDatum g a) (t : S₁ ⟶ S) [UniversallySubmersive t]
    (ht : IsEffectiveDescentMorphism t etaleSeparatedFiniteType)
    (ha : etaleSeparatedFiniteType a)
    (h : (D.baseChange t).IsEffective etaleSeparatedFiniteType) :
    D.IsEffective etaleSeparatedFiniteType := by
  obtain ⟨X₁, b₁, v₁, hb₁, hv₁, hact₁⟩ := h
  have : Etale b₁ := hb₁.1.1
  -- `X₁` descends along `t` (IX.4.1 for `t` faithfully flat)
  obtain ⟨X, b, w, hb, hw, hactw⟩ := ht.2 _ (FlatBaseChange.datum D t hv₁ hact₁) hb₁
  have : Etale b := hb.1.1
  have hactw' : FlatBaseChange.act D t hv₁ hact₁ ≫ w = pullback.fst (b₁ ≫ t) t ≫ w := hactw
  -- the projection `X'₁ ⟶ X₁ ⟶ X` descends along `X'₁ ⟶ X'`
  have : UniversallySubmersive (pullback.fst g t) := inferInstance
  have : UniversallySubmersive (pullback.fst a (pullback.fst g t)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback a (pullback.fst g t)).flip
      inferInstance
  have hφ : (v₁ ≫ w) ≫ b = pullback.fst a (pullback.fst g t) ≫ a ≫ g := by
    rw [Category.assoc, hw.w, reassoc_of% hv₁.w, pullback.condition_assoc, pullback.condition]
  have hker : pullback.fst (pullback.fst a (pullback.fst g t))
      (pullback.fst a (pullback.fst g t)) ≫ v₁ ≫ w =
      pullback.snd (pullback.fst a (pullback.fst g t))
        (pullback.fst a (pullback.fst g t)) ≫ v₁ ≫ w := by
    let ζ := pullback.lift (f := pullback.fst a (pullback.fst g t) ≫ a ≫ g) (g := t)
      (pullback.fst (pullback.fst a (pullback.fst g t)) (pullback.fst a (pullback.fst g t)))
      (pullback.snd (pullback.fst a (pullback.fst g t)) (pullback.fst a (pullback.fst g t)) ≫
        pullback.snd a (pullback.fst g t) ≫ pullback.snd g t) (by
        rw [pullback.condition_assoc, pullback.condition_assoc]
        simp [pullback.condition])
    have hkk := pullback.condition (f := pullback.fst a (pullback.fst g t))
      (g := pullback.fst a (pullback.fst g t))
    have hζm : ζ ≫ FlatBaseChange.m t = pullback.snd _ _ := by
      apply pullback.hom_ext
      · simp only [ζ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        exact hkk
      · apply pullback.hom_ext
        · simp only [ζ, Category.assoc, pullback.lift_snd, pullback.lift_fst,
            pullback.lift_fst_assoc]
          rw [reassoc_of% hkk, pullback.condition]
        · simp [ζ]
    have hζπ : ζ ≫ FlatBaseChange.π t hv₁ ≫ pullback.fst (b₁ ≫ t) t = pullback.fst _ _ ≫ v₁ := by
      simp [ζ]
    rw [← reassoc_of% hζm, ← FlatBaseChange.π_act_assoc D t hv₁ hact₁, hactw', reassoc_of% hζπ]
  obtain ⟨v, ⟨hvb, hvk⟩, -⟩ := existsUnique_hom_of_kernelPair
    (pullback.fst a (pullback.fst g t)) (a ≫ g) b (v₁ ≫ w) hφ hker
  refine ⟨X, b, v, hb, ?_, ?_⟩
  · -- the square is cartesian: the comparison map is étale, and an isomorphism after base change
    have hvb' : v ≫ b = a ≫ g := hvb
    let c : X' ⟶ pullback b g := pullback.lift v a hvb'
    let c₁ : pullback a (pullback.fst g t) ⟶ pullback b₁ (pullback.snd g t) :=
      pullback.lift v₁ (pullback.snd a (pullback.fst g t)) hv₁.w
    have hc₁ : c₁ = hv₁.isoPullback.hom := by
      apply pullback.hom_ext <;> simp [c₁]
    have : IsIso c₁ := hc₁ ▸ inferInstance
    let ψ : pullback b₁ (pullback.snd g t) ⟶ pullback b g :=
      pullback.map _ _ _ _ w (pullback.fst g t) t hw.w.symm pullback.condition.symm
    have hr : IsPullback ψ (pullback.snd b₁ (pullback.snd g t)) (pullback.snd b g)
        (pullback.fst g t) := by
      refine IsPullback.of_right (h₁₂ := pullback.fst b g) (v₁₃ := b) (h₂₂ := g) ?_ (by simp [ψ])
        (IsPullback.of_hasPullback b g)
      have := (IsPullback.of_hasPullback b₁ (pullback.snd g t)).paste_horiz hw
      convert this using 1
      · simp [ψ]
      · exact pullback.condition
    have SQ : IsPullback c₁ (pullback.fst a (pullback.fst g t)) ψ c := by
      refine IsPullback.of_right (h₁₂ := pullback.snd b₁ (pullback.snd g t))
        (v₁₃ := pullback.fst g t) (h₂₂ := pullback.snd b g) ?_ ?_ hr.flip
      · have := (IsPullback.of_hasPullback a (pullback.fst g t)).flip
        convert this using 1
        · simp [c₁]
        · simp [c]
      · apply pullback.hom_ext
        · simp [c₁, ψ, c, hvk]
        · simp [c₁, ψ, c, pullback.condition]
    have : Surjective ψ := MorphismProperty.of_isPullback hr.flip inferInstance
    have : UniversallyInjective c :=
      of_isPullback_of_descendsAlong (P := @UniversallyInjective) (Q := @Surjective) SQ
        inferInstance inferInstance
    have : Surjective c :=
      of_isPullback_of_descendsAlong (P := @Surjective) (Q := @Surjective) SQ
        inferInstance inferInstance
    have : Etale a := ha.1.1
    have : Etale (c ≫ pullback.snd b g) := by
      rw [pullback.lift_snd]
      infer_instance
    have : Etale c := Etale.of_comp c (pullback.snd b g)
    have := isIso_of_etale_of_universallyInjective_of_surjective c
    exact IsPullback.of_iso_pullback ⟨hvb'⟩ (asIso c) (by simp [c]) (by simp [c])
  · -- compatibility with the descent datum, checked after the surjective base change to `S₁`
    have hbc := isPullback_baseChangeAux g a t
    have : Surjective (DescentDatum.baseChangeAux g a t) :=
      MorphismProperty.of_isPullback hbc.flip inferInstance
    refine hom_ext_of_surjective (DescentDatum.baseChangeAux g a t) b ?_ ?_
    · simp only [Category.assoc, hvb]
      rw [reassoc_of% D.act_comp, pullback.condition]
    · have h₁ : DescentDatum.baseChangeAux g a t ≫ D.act =
          (D.baseChange t).act ≫ pullback.fst a (pullback.fst g t) :=
        (pullback.lift_fst _ _ _).symm
      rw [reassoc_of% h₁, DescentDatum.baseChangeAux_fst_assoc, hvk, reassoc_of% hact₁]

/-- IX.4.2, sufficiency: let `g : S' ⟶ S` be universally submersive, `X'` étale, separated and of
finite type over `S'` with a descent datum `D`, and `t : S₁ ⟶ S` faithfully flat and
quasi-compact. If the base change of `D` to `S₁` is effective, so is `D`. -/
theorem DescentDatum.isEffective_of_isEffective_baseChange_of_flat [UniversallySubmersive g]
    (D : DescentDatum g a) (t : S₁ ⟶ S) [Flat t] [QuasiCompact t] [Surjective t]
    (ha : etaleSeparatedFiniteType a)
    (h : (D.baseChange t).IsEffective etaleSeparatedFiniteType) :
    D.IsEffective etaleSeparatedFiniteType :=
  D.isEffective_of_isEffective_baseChange t (isEffectiveDescentMorphism_of_flat t) ha h

/-- IX.4.2: for `g` universally submersive, `X'` étale, separated and of finite type over `S'`
with a descent datum `D`, and `t : S₁ ⟶ S` faithfully flat and quasi-compact, `D` is effective
iff its base change to `S₁` is. -/
theorem DescentDatum.isEffective_iff_isEffective_baseChange_of_flat [UniversallySubmersive g]
    (D : DescentDatum g a) (t : S₁ ⟶ S) [Flat t] [QuasiCompact t] [Surjective t]
    (ha : etaleSeparatedFiniteType a) :
    D.IsEffective etaleSeparatedFiniteType ↔
      (D.baseChange t).IsEffective etaleSeparatedFiniteType :=
  ⟨fun h ↦ h.baseChange t, D.isEffective_of_isEffective_baseChange_of_flat t ha⟩

end SGA.SGA1.ExposeIX
