/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigher
import SGA.SGA1.ExposeXII.RiemannFull
import SGA.SGA1.ExposeXII.RiemannCurvesSeparable
import SGA.SGA1.ExposeIX.ProperEffectiveDescent

/-!
# SGA 1, Exposé XII, 5.1, proof of 2) a): descent along finite surjective morphisms

Let `g : X' → X` be a finite surjective morphism of schemes locally of finite type over `ℂ` (in
SGA, the normalization of `X`), and `E` a finite covering of `X(ℂ)`. If the pullback `g^*E` of `E`
to `X'(ℂ)` is isomorphic to `Y'(ℂ)` for a finite étale covering `Y'` of `X'`, then `E` is
isomorphic to `Y(ℂ)` for a finite étale covering `Y` of `X`
(`RiemannHigher.mem_essImage_schemePointsFunctor_of_isFinite`). This is the reduction to normal
`X` in SGA's proof of XII.5.1:

* the canonical descent datum of `g^*E` (a point `(y', s')` of `Y' ×_X X'` goes to the point of
  `Y'` over `s'` with the same image in `E`) is algebraic by step 1) of the proof
  (`SchemePoints.exists_hom_map_eq`), and its axioms hold because `Ψ` is faithful
  (`SchemePoints.eq_of_forall_comp_eq`);
* it is effective, `g` being an effective descent morphism for étale coverings (SGA quotes IX.4.7;
  we use IX.4.12 over a locally noetherian base,
  `ExposeIX.DescentDatum.isEffective_etaleCovering_of_isProper`);
* the descended covering `Y` has `Y(ℂ) ≅ E`: the map `Y'(ℂ) → Y(ℂ)` is proper (it comes from a
  finite morphism) and surjective, hence a quotient map, through which `Y'(ℂ) ≅ g^*E → E`
  factors (SGA: "IX.3.2, whose proof is valid in the analytic case").

The finiteness of `g` is used only to know that `Y'(ℂ) → Y(ℂ)` is proper
(`SchemePoints.isProperMap_map`); the algebraic descent holds for proper surjective `g`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Topology Set

namespace SGA.SGA1.ExposeXII

namespace RiemannHigher

/-- The continuous map `X'(ℂ) → X(ℂ)` induced by a `ℂ`-morphism `g`, as a morphism of `TopCat`. -/
abbrev schemePointsHom {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [X'.Over (Spec (.of ℂ))]
    (g : X' ⟶ X) [g.IsOver (Spec (.of ℂ))] :
    TopCat.of (SchemePoints ℂ X') ⟶ TopCat.of (SchemePoints ℂ X) :=
  TopCat.ofHom ⟨SchemePoints.map g, SchemePoints.continuous_map g⟩

section FiniteDescent

variable {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [X'.Over (Spec (.of ℂ))]
  [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [LocallyOfFiniteType (X' ↘ Spec (.of ℂ))]
  (g : X' ⟶ X) [g.IsOver (Spec (.of ℂ))]
  (E : TopCat.FiniteCovering (TopCat.of (SchemePoints ℂ X)))

open SchemePoints

attribute [local instance] pullbackOver isOver_pullback_fst isOver_pullback_snd

/-- XII.5.1, proof of 2) a): descent of the Riemann existence theorem, for one covering, along a
finite surjective morphism `g : X' → X` (e.g. the normalization of a reduced `X`): if the pullback
of a finite covering `E` of `X(ℂ)` to `X'(ℂ)` is `Y'(ℂ)` for a finite étale covering `Y'` of `X'`,
then `E` is `Y(ℂ)` for a finite étale covering `Y` of `X`. -/
theorem mem_essImage_schemePointsFunctor_of_isFinite [IsFinite g] [Surjective g]
    (h : (schemePointsFunctor ℂ X').essImage
      ((TopCat.FiniteCovering.baseChange (schemePointsHom g)).obj E)) :
    (schemePointsFunctor ℂ X).essImage E := by
  obtain ⟨Y', ⟨α⟩⟩ := h
  let := overOfCovering ℂ X' Y'
  have := isOver_hom ℂ X' Y'
  set a : Y'.left ⟶ X' := Y'.hom' with ha_def
  have : IsFinite a := Y'.prop.1
  have : Etale a := Y'.prop.2
  have : LocallyOfFiniteType (Y'.left ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (a ≫ X' ↘ Spec (.of ℂ))
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  let G := TopCat.FiniteCovering.baseChange (schemePointsHom g)
  -- the points of `Y'` as points of `g^*E`
  let A : SchemePoints ℂ Y'.left → ((G.obj E).obj.left) := fun y ↦ α.hom.hom.left y
  let A' : (G.obj E).obj.left → SchemePoints ℂ Y'.left := fun q ↦ α.inv.hom.left q
  have hAA' (q) : A (A' q) = q := congr($(α.inv_hom_id).hom.left q)
  have hA'A (y) : A' (A y) = y := congr($(α.hom_inv_id).hom.left y)
  have hA (y) : (G.obj E).obj.hom (A y) = map a y := TopCat.FiniteCovering.hom_left_apply α.hom y
  have hA' (q) : map a (A' q) = (G.obj E).obj.hom q :=
    TopCat.FiniteCovering.hom_left_apply α.inv q
  -- the point of `E` under a point of `Y'`, and the point of `Y'` with given images
  let eOf : SchemePoints ℂ Y'.left → E.obj.left := fun y ↦
    TopCat.FiniteCovering.baseChangeSnd _ E (A y)
  have heOf (y) : E.obj.hom (eOf y) = map g (map a y) := by
    rw [TopCat.FiniteCovering.hom_baseChangeSnd, hA]
    rfl
  have hceOf : Continuous eOf :=
    (TopCat.FiniteCovering.baseChangeSnd _ E).hom.continuous.comp α.hom.hom.left.hom.continuous
  let mk (s : SchemePoints ℂ X') (e : E.obj.left) (h : map g s = E.obj.hom e) :
      SchemePoints ℂ Y'.left :=
    A' (TopCat.FiniteCovering.baseChangeMk _ E s e h)
  have hmk_a (s e h) : map a (mk s e h) = s := hA' _
  have hmk_e (s e h) : eOf (mk s e h) = e := by
    simp only [eOf, mk, hAA']
    rfl
  have hmk_eta (y) : mk (map a y) (eOf y) (heOf y).symm = y := by
    have : TopCat.FiniteCovering.baseChangeMk _ E (map a y) (eOf y) (heOf y).symm = A y :=
      TopCat.FiniteCovering.baseChange_ext (hA y).symm rfl
    simp only [mk, this, hA'A]
  have hmk_congr {s s' e e' h h'} (hs : s = s') (he : e = e') : mk s e h = mk s' e' h' := by
    subst hs he
    rfl
  -- the descent datum: `(y, s') ↦` the point of `Y'` over `s'` with the same image in `E`
  have : (a ≫ g).IsOver (Spec (.of ℂ)) := inferInstance
  let P := pullback (a ≫ g) g
  have : LocallyOfFiniteType (P ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (pullback.fst (a ≫ g) g ≫ Y'.left ↘ Spec (.of ℂ))
    infer_instance
  have hPcond (r : SchemePoints ℂ P) :
      map g (map (pullback.snd (a ≫ g) g) r) =
        E.obj.hom (eOf (map (pullback.fst (a ≫ g) g) r)) := by
    rw [heOf]
    exact SchemePoints.ext (by simp only [map, Category.assoc, pullback.condition])
  let u : SchemePoints ℂ P → SchemePoints ℂ Y'.left := fun r ↦
    mk (map (pullback.snd (a ≫ g) g) r) (eOf (map (pullback.fst (a ≫ g) g) r)) (hPcond r)
  have hu : Continuous u := by
    refine α.inv.hom.left.hom.continuous.comp ?_
    exact Continuous.subtype_mk ((continuous_map _).prodMk (hceOf.comp (continuous_map _))) _
  have hpu (r : SchemePoints ℂ P) : map a (u r) = map (pullback.snd (a ≫ g) g) r := hmk_a _ _ _
  obtain ⟨act, hact, _, hactu⟩ := SchemePoints.exists_hom_map_eq (pullback.snd (a ≫ g) g) a u hu hpu
  have hactpt (r : SchemePoints ℂ P) : r.1 ≫ act = (u r).1 := congrArg Subtype.val (hactu r)
  -- points of `P` from morphisms
  have hPover (q : Spec (.of ℂ) ⟶ P)
      (hq : (q ≫ pullback.fst (a ≫ g) g) ≫ Y'.left ↘ Spec (.of ℂ) = 𝟙 _) :
      q ≫ P ↘ Spec (.of ℂ) = 𝟙 _ := by
    rw [← hq, Category.assoc]
    rfl
  have hPfst (q : Spec (.of ℂ) ⟶ P) (hq) :
      map (pullback.fst (a ≫ g) g) (⟨q, hPover q hq⟩ : SchemePoints ℂ P) =
        ⟨q ≫ pullback.fst (a ≫ g) g, hq⟩ := rfl
  have hu_eq (r : SchemePoints ℂ P) {y s} (hy : map (pullback.fst (a ≫ g) g) r = y)
      (hs : map (pullback.snd (a ≫ g) g) r = s) (h) : u r = mk s (eOf y) h :=
    hmk_congr hs (by rw [hy])
  have hunit : pullback.lift (𝟙 Y'.left) a (by simp) ≫ act = 𝟙 Y'.left := by
    have hl₁ : pullback.lift (𝟙 Y'.left) a (by simp) ≫ pullback.fst (a ≫ g) g = 𝟙 _ :=
      pullback.lift_fst _ _ _
    have hl₂ : pullback.lift (𝟙 Y'.left) a (by simp) ≫ pullback.snd (a ≫ g) g = a :=
      pullback.lift_snd _ _ _
    refine SchemePoints.eq_of_forall_comp_eq (K := ℂ) a _ _
      (by rw [Category.assoc, hact, hl₂, Category.id_comp]) fun p ↦ ?_
    have hp₁ : (p.1 ≫ pullback.lift (𝟙 Y'.left) a (by simp)) ≫ pullback.fst (a ≫ g) g = p.1 := by
      rw [Category.assoc, hl₁, Category.comp_id]
    have hq : ((p.1 ≫ pullback.lift (𝟙 Y'.left) a (by simp)) ≫ pullback.fst (a ≫ g) g) ≫
        Y'.left ↘ Spec (.of ℂ) = 𝟙 _ := by
      rw [hp₁]
      exact p.2
    let r : SchemePoints ℂ P := ⟨_, hPover _ hq⟩
    have h1 : map (pullback.fst (a ≫ g) g) r = p := SchemePoints.ext (by
      change (p.1 ≫ _) ≫ _ = _
      rw [Category.assoc, hl₁, Category.comp_id])
    have h2 : map (pullback.snd (a ≫ g) g) r = map a p := SchemePoints.ext (by
      change (p.1 ≫ _) ≫ _ = _
      rw [Category.assoc, hl₂]
      rfl)
    rw [← Category.assoc, hactpt r, Category.comp_id, hu_eq r h1 h2 (heOf p).symm, hmk_eta]
  have : LocallyOfFiniteType
      (pullback (pullback.snd (a ≫ g) g ≫ g) g ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (pullback.fst (pullback.snd (a ≫ g) g ≫ g) g ≫ P ↘ Spec (.of ℂ))
    infer_instance
  let D : ExposeIX.DescentDatum g a := ⟨act, hact, hunit, by
    have h₁ : (pullback.fst (pullback.snd (a ≫ g) g ≫ g) g ≫ act) ≫ a ≫ g =
        pullback.snd (pullback.snd (a ≫ g) g ≫ g) g ≫ g := by
      rw [Category.assoc, reassoc_of% hact, pullback.condition]
    have h₂ : (pullback.fst (pullback.snd (a ≫ g) g ≫ g) g ≫ pullback.fst (a ≫ g) g) ≫ a ≫ g =
        pullback.snd (pullback.snd (a ≫ g) g ≫ g) g ≫ g := by
      simp only [Category.assoc, pullback.condition]
    change pullback.lift _ _ h₁ ≫ act = pullback.lift _ _ h₂ ≫ act
    have hL₁f := pullback.lift_fst _ _ h₁
    have hL₁s := pullback.lift_snd _ _ h₁
    have hL₂f := pullback.lift_fst _ _ h₂
    have hL₂s := pullback.lift_snd _ _ h₂
    refine SchemePoints.eq_of_forall_comp_eq (K := ℂ) a _ _
      (by rw [Category.assoc, Category.assoc, hact, hL₁s, hL₂s]) fun p₂ ↦ ?_
    let q := map (pullback.fst (pullback.snd (a ≫ g) g ≫ g) g) p₂
    have hc₁ : (p₂.1 ≫ pullback.lift _ _ h₁) ≫ pullback.fst (a ≫ g) g = (u q).1 := by
      rw [Category.assoc, hL₁f, ← Category.assoc]
      exact hactpt q
    have hc₂ : (p₂.1 ≫ pullback.lift _ _ h₂) ≫ pullback.fst (a ≫ g) g =
        (map (pullback.fst (a ≫ g) g) q).1 := by
      rw [Category.assoc, hL₂f, ← Category.assoc]
      rfl
    have hq₁ : ((p₂.1 ≫ pullback.lift _ _ h₁) ≫ pullback.fst (a ≫ g) g) ≫
        Y'.left ↘ Spec (.of ℂ) = 𝟙 _ := by
      rw [hc₁]
      exact (u q).2
    have hq₂ : ((p₂.1 ≫ pullback.lift _ _ h₂) ≫ pullback.fst (a ≫ g) g) ≫
        Y'.left ↘ Spec (.of ℂ) = 𝟙 _ := by
      rw [hc₂]
      exact (map (pullback.fst (a ≫ g) g) q).2
    let r₁ : SchemePoints ℂ P := ⟨_, hPover _ hq₁⟩
    let r₂ : SchemePoints ℂ P := ⟨_, hPover _ hq₂⟩
    have e₁f : map (pullback.fst (a ≫ g) g) r₁ = u q := SchemePoints.ext hc₁
    have e₁s : map (pullback.snd (a ≫ g) g) r₁ =
        map (pullback.snd (pullback.snd (a ≫ g) g ≫ g) g) p₂ := SchemePoints.ext (by
      change (p₂.1 ≫ _) ≫ _ = _
      rw [Category.assoc, hL₁s]
      rfl)
    have e₂f : map (pullback.fst (a ≫ g) g) r₂ = map (pullback.fst (a ≫ g) g) q :=
      SchemePoints.ext hc₂
    have e₂s : map (pullback.snd (a ≫ g) g) r₂ =
        map (pullback.snd (pullback.snd (a ≫ g) g ≫ g) g) p₂ := SchemePoints.ext (by
      change (p₂.1 ≫ _) ≫ _ = _
      rw [Category.assoc, hL₂s]
      rfl)
    have heq : u r₁ = u r₂ := by
      rw [hu_eq r₁ e₁f e₁s (by rw [← e₁s, ← e₁f]; exact hPcond r₁),
        hu_eq r₂ e₂f e₂s (by rw [← e₂s, ← e₂f]; exact hPcond r₂)]
      exact hmk_congr rfl (hmk_e _ _ _)
    rw [← Category.assoc, ← Category.assoc]
    exact (hactpt r₁).trans ((congrArg Subtype.val heq).trans (hactpt r₂).symm)⟩
  -- effectiveness (IX.4.12): the descended finite étale covering `Y` of `X`
  obtain ⟨X₀, b, v, ⟨hbfin, hbet⟩, hv, hactv⟩ := D.isEffective_etaleCovering_of_isProper
  let Y : FiniteEtaleCovering X := MorphismProperty.Over.mk ⊤ b ⟨hbfin, hbet⟩
  let : X₀.Over (Spec (.of ℂ)) := .ofHom (b ≫ X ↘ Spec (.of ℂ))
  have hbo : b.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : LocallyOfFiniteType (X₀ ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (b ≫ X ↘ Spec (.of ℂ))
    infer_instance
  have hvo : v.IsOver (Spec (.of ℂ)) := ⟨by
    change v ≫ b ≫ X ↘ Spec (.of ℂ) = a ≫ X' ↘ Spec (.of ℂ)
    rw [reassoc_of% hv.w, comp_over]⟩
  have : IsFinite v := MorphismProperty.of_isPullback hv.flip (inferInstanceAs (IsFinite g))
  have : Surjective v := MorphismProperty.of_isPullback hv.flip (inferInstanceAs (Surjective g))
  have hVs : Function.Surjective (map (K := ℂ) v) := surjective_map_of_surjective v v.surjective
  have hVq : IsQuotientMap (map (K := ℂ) v) :=
    (isProperMap_map v).isClosedMap.isQuotientMap (continuous_map v) hVs
  have hvb (y : SchemePoints ℂ Y'.left) : map b (map v y) = map g (map a y) :=
    SchemePoints.ext (by simp only [map, Category.assoc, hv.w])
  have hpt {y₁ y₂ : SchemePoints ℂ Y'.left} (h₁ : map v y₁ = map v y₂)
      (h₂ : map a y₁ = map a y₂) : y₁ = y₂ :=
    SchemePoints.ext (hv.hom_ext (congrArg Subtype.val h₁) (congrArg Subtype.val h₂))
  -- the action moves a point of `Y'` within its fibre over `X₀`, keeping its image in `E`
  have hmove (y₁ : SchemePoints ℂ Y'.left) (s : SchemePoints ℂ X')
      (hs : map (a ≫ g) y₁ = map g s) (h' : map g s = E.obj.hom (eOf y₁)) :
      map v (mk s (eOf y₁) h') = map v y₁ := by
    let r : SchemePoints ℂ P := (pullbackEquiv (a ≫ g) g).symm ⟨(y₁, s), hs⟩
    have hr := (pullbackEquiv (K := ℂ) (a ≫ g) g).apply_symm_apply ⟨(y₁, s), hs⟩
    have hr₁ : map (pullback.fst (a ≫ g) g) r = y₁ := congrArg (fun x ↦ x.1.1) hr
    have hr₂ : map (pullback.snd (a ≫ g) g) r = s := congrArg (fun x ↦ x.1.2) hr
    rw [← hu_eq r hr₁ hr₂ h']
    refine SchemePoints.ext ?_
    change (u r).1 ≫ v = y₁.1 ≫ v
    rw [← hactpt r, Category.assoc, hactv, ← Category.assoc]
    exact congrArg (· ≫ v) (congrArg Subtype.val hr₁)
  have hga (y₁ y₂ : SchemePoints ℂ Y'.left) (h : map v y₁ = map v y₂) :
      map (a ≫ g) y₁ = map g (map a y₂) := by
    rw [map_comp, Function.comp_apply, ← hvb, h, hvb]
  have hconst : Function.FactorsThrough eOf (map (K := ℂ) v) := by
    intro y₁ y₂ h
    have h' : map g (map a y₂) = E.obj.hom (eOf y₁) := by
      rw [heOf, ← hvb, ← hvb, h]
    have hy₃ := hmove y₁ (map a y₂) (hga y₁ y₂ h) h'
    rw [← hmk_e (map a y₂) (eOf y₁) h', hpt (hy₃.trans h) (hmk_a _ _ _)]
  have hinj {y₁ y₂ : SchemePoints ℂ Y'.left} (h : eOf y₁ = eOf y₂) : map v y₁ = map v y₂ := by
    have hs : map (a ≫ g) y₁ = map g (map a y₂) := by
      rw [map_comp, Function.comp_apply, ← heOf, ← heOf, h]
    have h' : map g (map a y₂) = E.obj.hom (eOf y₁) := by rw [h, heOf]
    have hy₃ := hmove y₁ (map a y₂) hs h'
    rw [hmk_congr (s' := map a y₂) (e' := eOf y₂) (h' := (heOf y₂).symm) rfl h, hmk_eta] at hy₃
    exact hy₃.symm
  -- the comparison `Y(ℂ) ≅ E`
  let e₀ : C(SchemePoints ℂ Y'.left, E.obj.left) := ⟨eOf, hceOf⟩
  let V : C(SchemePoints ℂ Y'.left, SchemePoints ℂ X₀) := ⟨map v, continuous_map v⟩
  have hVq' : IsQuotientMap V := hVq
  have hconst' : Function.FactorsThrough e₀ V := hconst
  let β : C(SchemePoints ℂ X₀, E.obj.left) := hVq'.lift e₀ hconst'
  have hβ (y) : β (map v y) = eOf y := congr($(hVq'.lift_comp e₀ hconst') y)
  have hβi : Function.Injective β := by
    intro x₁ x₂ h
    obtain ⟨y₁, rfl⟩ := hVs x₁
    obtain ⟨y₂, rfl⟩ := hVs x₂
    rw [hβ, hβ] at h
    exact hinj h
  have hβs : Function.Surjective β := by
    intro e
    obtain ⟨s, hs⟩ := surjective_map_of_surjective g g.surjective (E.obj.hom e)
    exact ⟨map v (mk s e hs), by rw [hβ, hmk_e]⟩
  have hβo (x : SchemePoints ℂ X₀) : E.obj.hom (β x) = map b x := by
    obtain ⟨y, rfl⟩ := hVs x
    rw [hβ, heOf, hvb]
  exact ⟨Y, ⟨TopCat.FiniteCovering.isoOfBijective β hβo ⟨hβi, hβs⟩⟩⟩

end FiniteDescent

end RiemannHigher

end SGA.SGA1.ExposeXII
