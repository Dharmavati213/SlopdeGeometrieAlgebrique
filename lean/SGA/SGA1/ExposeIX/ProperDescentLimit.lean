/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.FiniteEtaleEffectiveDescent
import SGA.Foundations.Limits.BaseChange

/-!
# SGA 1, Exposé IX, 4.12 and 6.9: descent data over a limit of noetherian schemes

Let `c.pt = lim E i` be the limit of a cofiltered diagram of affine noetherian schemes (with
affine transition maps), `g_j : S_j ⟶ E j` proper and surjective, and `g : S' ⟶ c.pt` its base
change. We show that every descent datum relative to `g` on an étale covering of `S'` is
effective (`DescentDatum.isEffective_of_isLimit`), by the limit methods of EGA IV 8: the étale
covering, its descent datum (the action of IX.4) and the identities it satisfies come from some
`E k` (EGA IV 8.8.2), where the datum is effective by IX.4.12 over a noetherian base.

As an application, a proper surjective morphism to a locally noetherian scheme is a *universal*
effective descent morphism for étale coverings (IX.6.9, `UniversalProperDescentStatement`): after
localizing with IX.4.5, the base is the spectrum of an algebra over a noetherian ring, the union of
its finitely generated subalgebras.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeIX

/-! ### Fibre products and base change -/

set_option backward.isDefEq.respectTransparency false in
/-- The base change of a fibre product: if `W ⟶ B` and `S' ⟶ B` are the base changes of
`W_j ⟶ B_j` and `S_j ⟶ B_j` along `t : B ⟶ B_j`, then `W ×_B S'` is the base change of
`W_j ×_{B_j} S_j`. -/
lemma isPullback_pullbackMap_fst_of_isPullback {W Wj S' Sj B Bj : Scheme.{u}} {w : W ⟶ B}
    {wj : Wj ⟶ Bj} {g : S' ⟶ B} {gj : Sj ⟶ Bj} {t : B ⟶ Bj} {eW : W ⟶ Wj} {eS : S' ⟶ Sj}
    (hW : IsPullback eW w wj t) (hS : IsPullback eS g gj t) :
    IsPullback (pullback.map w g wj gj eW eS t hW.w.symm hS.w.symm)
      (pullback.fst w g ≫ w) (pullback.fst wj gj ≫ wj) t := by
  have hleft : IsPullback (pullback.map w g wj gj eW eS t hW.w.symm hS.w.symm)
      (pullback.fst w g) (pullback.fst wj gj) eW := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback wj gj).flip
    rw [pullback.lift_snd, hW.w]
    exact (IsPullback.of_hasPullback w g).flip.paste_horiz hS
  exact hleft.paste_vert hW

/-! ### The descent datum at a finite level

Let `E : I ⥤ Scheme`, `g_j : S_j ⟶ E j` and `a_j : X_j ⟶ S_j`. For `k : Over j` we write
`X_j ×_{E j} E k` etc. for the base changes (the objects of `Scheme.baseChangeDiagram`). Given a
morphism `b : P_j ×_{E j} E k ⟶ X_j` (`P_j = X_j ×_{E j} S_j`) satisfying, after base change to
some `l ⟶ k`, the identities of a descent datum, we build a descent datum at level `l`. -/

section LevelDatum

variable {I : Type u} [Category.{u} I] (E : I ⥤ Scheme.{u}) {j : I} {Sj Xj : Scheme.{u}}
  (gj : Sj ⟶ E.obj j) (aj : Xj ⟶ Sj)

/-- `P_j = X_j ×_{E j} S_j ⟶ E j`. -/
noncomputable abbrev spreadP : pullback (aj ≫ gj) gj ⟶ E.obj j :=
  pullback.fst (aj ≫ gj) gj ≫ aj ≫ gj

/-- `Q_j = P_j ×_{E j} S_j ⟶ E j`. -/
noncomputable abbrev spreadQ :
    pullback (pullback.snd (aj ≫ gj) gj ≫ gj) gj ⟶ E.obj j :=
  pullback.fst (pullback.snd (aj ≫ gj) gj ≫ gj) gj ≫ pullback.snd (aj ≫ gj) gj ≫ gj

/-- The structure morphism `S_l = S_j ×_{E j} E l ⟶ E l`. -/
noncomputable abbrev lvlG (l : Over j) : pullback gj (E.map l.hom) ⟶ E.obj l.left :=
  pullback.snd gj (E.map l.hom)

/-- The étale covering `X_l = X_j ×_{S_j} S_l ⟶ S_l`. -/
noncomputable abbrev lvlA (l : Over j) :
    pullback aj (pullback.fst gj (E.map l.hom)) ⟶ pullback gj (E.map l.hom) :=
  pullback.snd aj (pullback.fst gj (E.map l.hom))

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal `x ↦ (x, a(x))` at level `k`. -/
noncomputable def spreadDiag (k : Over j) :
    pullback (aj ≫ gj) (E.map k.hom) ⟶ pullback (spreadP E gj aj) (E.map k.hom) :=
  pullback.map _ _ _ _ (pullback.lift (𝟙 Xj) aj (by simp)) (𝟙 _) (𝟙 _)
    (by rw [spreadP, pullback.lift_fst_assoc, Category.id_comp, Category.comp_id]) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The projection `(x, s₁, s₂) ↦ (x, s₁)` at level `k`. -/
noncomputable def spreadPr12 (k : Over j) :
    pullback (spreadQ E gj aj) (E.map k.hom) ⟶ pullback (spreadP E gj aj) (E.map k.hom) :=
  pullback.map _ _ _ _ (pullback.fst (pullback.snd (aj ≫ gj) gj ≫ gj) gj) (𝟙 _) (𝟙 _)
    (by rw [spreadQ, spreadP, Category.comp_id, pullback.condition (f := aj ≫ gj) (g := gj)])
    (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The projection `(x, s₁, s₂) ↦ (x, s₂)` at level `k`. -/
noncomputable def spreadPr13 (k : Over j) :
    pullback (spreadQ E gj aj) (E.map k.hom) ⟶ pullback (spreadP E gj aj) (E.map k.hom) :=
  pullback.map _ _ _ _
    (pullback.lift (pullback.fst (pullback.snd (aj ≫ gj) gj ≫ gj) gj ≫ pullback.fst (aj ≫ gj) gj)
      (pullback.snd (pullback.snd (aj ≫ gj) gj ≫ gj) gj) (by
        rw [Category.assoc, pullback.condition (f := aj ≫ gj) (g := gj)]
        exact pullback.condition)) (𝟙 _) (𝟙 _)
    (by rw [spreadQ, spreadP, Category.comp_id, pullback.lift_fst_assoc, Category.assoc,
      pullback.condition (f := aj ≫ gj) (g := gj)]) (by simp)

/-- The projection `(x, s₁, s₂) ↦ s₂` at level `k`. -/
noncomputable abbrev spreadPr3 (k : Over j) : pullback (spreadQ E gj aj) (E.map k.hom) ⟶ Sj :=
  pullback.fst _ _ ≫ pullback.snd (pullback.snd (aj ≫ gj) gj ≫ gj) gj

variable {E gj aj}

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadPr12_snd (k : Over j) :
    spreadPr12 E gj aj k ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [spreadPr12]

set_option backward.isDefEq.respectTransparency false in
/-- `(x·s₁, s₂)` at level `k`, for a morphism `b` representing the action. -/
noncomputable def spreadActPr12 {k : Over j} (b : pullback (spreadP E gj aj) (E.map k.hom) ⟶ Xj)
    (hb : b ≫ aj ≫ gj = pullback.snd _ _ ≫ E.map k.hom) :
    pullback (spreadQ E gj aj) (E.map k.hom) ⟶ pullback (spreadP E gj aj) (E.map k.hom) :=
  pullback.lift (pullback.lift (spreadPr12 E gj aj k ≫ b) (spreadPr3 E gj aj k) (by
      rw [Category.assoc, hb, spreadPr12_snd_assoc, spreadPr3, Category.assoc,
        ← pullback.condition (f := pullback.snd (aj ≫ gj) gj ≫ gj) (g := gj)]
      exact pullback.condition.symm))
    (pullback.snd _ _) (by simp only [spreadP, pullback.lift_fst_assoc, Category.assoc, hb,
      spreadPr12_snd_assoc])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadDiag_fst (k : Over j) :
    spreadDiag E gj aj k ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.lift (𝟙 Xj) aj (by simp) := by
  simp [spreadDiag]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadDiag_snd (k : Over j) :
    spreadDiag E gj aj k ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [spreadDiag]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadPr12_fst (k : Over j) :
    spreadPr12 E gj aj k ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst (pullback.snd (aj ≫ gj) gj ≫ gj) gj := by
  simp [spreadPr12]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadPr13_fst (k : Over j) :
    spreadPr13 E gj aj k ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.lift
        (pullback.fst (pullback.snd (aj ≫ gj) gj ≫ gj) gj ≫ pullback.fst (aj ≫ gj) gj)
        (pullback.snd (pullback.snd (aj ≫ gj) gj ≫ gj) gj) (by
          rw [Category.assoc, pullback.condition (f := aj ≫ gj) (g := gj)]
          exact pullback.condition) := by
  simp [spreadPr13]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadPr13_snd (k : Over j) :
    spreadPr13 E gj aj k ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [spreadPr13]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadActPr12_fst {k : Over j} (b : pullback (spreadP E gj aj) (E.map k.hom) ⟶ Xj)
    (hb : b ≫ aj ≫ gj = pullback.snd _ _ ≫ E.map k.hom) :
    spreadActPr12 b hb ≫ pullback.fst _ _ =
      pullback.lift (spreadPr12 E gj aj k ≫ b) (spreadPr3 E gj aj k) (by
        rw [Category.assoc, hb, spreadPr12_snd_assoc, spreadPr3, Category.assoc,
          ← pullback.condition (f := pullback.snd (aj ≫ gj) gj ≫ gj) (g := gj)]
        exact pullback.condition.symm) := by
  simp [spreadActPr12]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadActPr12_snd {k : Over j} (b : pullback (spreadP E gj aj) (E.map k.hom) ⟶ Xj)
    (hb : b ≫ aj ≫ gj = pullback.snd _ _ ≫ E.map k.hom) :
    spreadActPr12 b hb ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [spreadActPr12]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_fst {X : Scheme.{u}} (p : X ⟶ E.obj j) {k k' : Over j}
    (g : k ⟶ k') :
    (Scheme.baseChangeDiagram E p).map g ≫ pullback.fst p (E.map k'.hom) =
      pullback.fst p (E.map k.hom) := by
  simp [pullback.map]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_snd {X : Scheme.{u}} (p : X ⟶ E.obj j) {k k' : Over j}
    (g : k ⟶ k') :
    (Scheme.baseChangeDiagram E p).map g ≫ pullback.snd p (E.map k'.hom) =
      pullback.snd p (E.map k.hom) ≫ E.map g.left := by
  simp [pullback.map]

/-! The comparison of the objects of a descent datum at level `l` with the base changes of the
objects at level `j`. -/

section Comparison

variable (l : Over j)

set_option backward.isDefEq.respectTransparency false in
/-- `X_l = X_j ×_{S_j} S_l ⟶ X_j ×_{E j} E l`. -/
noncomputable def spreadCompX :
    pullback aj (pullback.fst gj (E.map l.hom)) ⟶ pullback (aj ≫ gj) (E.map l.hom) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
    rw [pullback.condition_assoc, Category.assoc, pullback.condition])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadCompX_fst : spreadCompX (gj := gj) (aj := aj) l ≫ pullback.fst _ _ =
    pullback.fst _ _ := pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadCompX_snd : spreadCompX (gj := gj) (aj := aj) l ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ pullback.snd _ _ := pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- `P_l ⟶ P_j ×_{E j} E l`. -/
noncomputable def spreadCompP :
    pullback (pullback.snd aj (pullback.fst gj (E.map l.hom)) ≫ pullback.snd gj (E.map l.hom))
        (pullback.snd gj (E.map l.hom)) ⟶ pullback (spreadP E gj aj) (E.map l.hom) :=
  pullback.lift (DescentDatum.baseChangeAux gj aj (E.map l.hom))
    (pullback.snd _ _ ≫ pullback.snd gj (E.map l.hom)) (by
      rw [spreadP, DescentDatum.baseChangeAux_fst_assoc, pullback.condition_assoc,
        pullback.condition (f := gj) (g := E.map l.hom),
        ← Category.assoc (pullback.snd aj (pullback.fst gj (E.map l.hom))), ← Category.assoc,
        pullback.condition])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadCompP_fst : spreadCompP (gj := gj) (aj := aj) l ≫ pullback.fst _ _ =
    DescentDatum.baseChangeAux gj aj (E.map l.hom) := pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadCompP_snd : spreadCompP (gj := gj) (aj := aj) l ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ pullback.snd gj (E.map l.hom) := pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- `Q_l ⟶ Q_j`. -/
noncomputable def spreadAuxQ :
    pullback (pullback.snd (pullback.snd aj (pullback.fst gj (E.map l.hom)) ≫
        pullback.snd gj (E.map l.hom)) (pullback.snd gj (E.map l.hom)) ≫
          pullback.snd gj (E.map l.hom)) (pullback.snd gj (E.map l.hom)) ⟶
      pullback (pullback.snd (aj ≫ gj) gj ≫ gj) gj :=
  pullback.lift (pullback.fst _ _ ≫ DescentDatum.baseChangeAux gj aj (E.map l.hom))
    (pullback.snd _ _ ≫ pullback.fst gj (E.map l.hom)) (by
      have hQ := pullback.condition (f := pullback.snd (pullback.snd aj
        (pullback.fst gj (E.map l.hom)) ≫ pullback.snd gj (E.map l.hom))
          (pullback.snd gj (E.map l.hom)) ≫ pullback.snd gj (E.map l.hom))
        (g := pullback.snd gj (E.map l.hom))
      simp only [Category.assoc] at hQ ⊢
      rw [DescentDatum.baseChangeAux_snd_assoc, pullback.condition (f := gj) (g := E.map l.hom),
        reassoc_of% hQ])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadAuxQ_fst : spreadAuxQ (gj := gj) (aj := aj) l ≫ pullback.fst _ _ =
    pullback.fst _ _ ≫ DescentDatum.baseChangeAux gj aj (E.map l.hom) := pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadAuxQ_snd : spreadAuxQ (gj := gj) (aj := aj) l ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ pullback.fst gj (E.map l.hom) := pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- `Q_l ⟶ Q_j ×_{E j} E l`. -/
noncomputable def spreadCompQ :
    pullback (pullback.snd (pullback.snd aj (pullback.fst gj (E.map l.hom)) ≫
        pullback.snd gj (E.map l.hom)) (pullback.snd gj (E.map l.hom)) ≫
          pullback.snd gj (E.map l.hom)) (pullback.snd gj (E.map l.hom)) ⟶
      pullback (spreadQ E gj aj) (E.map l.hom) :=
  pullback.lift (spreadAuxQ l) (pullback.snd _ _ ≫ pullback.snd gj (E.map l.hom)) (by
    have hQ := pullback.condition (f := pullback.snd (pullback.snd aj
      (pullback.fst gj (E.map l.hom)) ≫ pullback.snd gj (E.map l.hom))
        (pullback.snd gj (E.map l.hom)) ≫ pullback.snd gj (E.map l.hom))
      (g := pullback.snd gj (E.map l.hom))
    rw [spreadQ, spreadAuxQ_fst_assoc, Category.assoc, DescentDatum.baseChangeAux_snd_assoc,
      pullback.condition (f := gj) (g := E.map l.hom), reassoc_of% hQ])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadCompQ_fst : spreadCompQ (gj := gj) (aj := aj) l ≫ pullback.fst _ _ =
    spreadAuxQ l := pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadCompQ_snd : spreadCompQ (gj := gj) (aj := aj) l ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ pullback.snd gj (E.map l.hom) := pullback.lift_snd _ _ _

end Comparison

section Datum

variable {k l : Over j} (g : l ⟶ k) (b : pullback (spreadP E gj aj) (E.map k.hom) ⟶ Xj)

set_option backward.isDefEq.respectTransparency false in
/-- The action at level `l`, `(x, s) ↦ b(x, s)`. -/
noncomputable def spreadAct
    (h1 : (Scheme.baseChangeDiagram E (spreadP E gj aj)).map g ≫ b ≫ aj =
      (Scheme.baseChangeDiagram E (spreadP E gj aj)).map g ≫ pullback.fst _ _ ≫
        pullback.snd (aj ≫ gj) gj) :
    pullback (pullback.snd aj (pullback.fst gj (E.map l.hom)) ≫ pullback.snd gj (E.map l.hom))
        (pullback.snd gj (E.map l.hom)) ⟶ pullback aj (pullback.fst gj (E.map l.hom)) :=
  pullback.lift (spreadCompP l ≫ (Scheme.baseChangeDiagram E (spreadP E gj aj)).map g ≫ b)
    (pullback.snd _ _) (by
      rw [Category.assoc, Category.assoc, h1, baseChangeDiagram_map_fst_assoc,
        spreadCompP_fst_assoc, DescentDatum.baseChangeAux_snd])

variable {g b}

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadAct_fst (h1) : spreadAct g b h1 ≫ pullback.fst _ _ =
    spreadCompP l ≫ (Scheme.baseChangeDiagram E (spreadP E gj aj)).map g ≫ b :=
  pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma spreadAct_snd (h1) : spreadAct g b h1 ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

variable (g) in
set_option backward.isDefEq.respectTransparency false in
lemma spread_unit_key :
    pullback.lift (𝟙 _) (pullback.snd aj (pullback.fst gj (E.map l.hom))) (by simp) ≫
        spreadCompP l ≫ (Scheme.baseChangeDiagram E (spreadP E gj aj)).map g =
      spreadCompX l ≫ (Scheme.baseChangeDiagram E (aj ≫ gj)).map g ≫ spreadDiag E gj aj k := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeDiagram_map_fst, spreadCompP_fst, spreadDiag_fst,
      baseChangeDiagram_map_fst_assoc, spreadCompX_fst_assoc]
    apply pullback.hom_ext
    · simp [DescentDatum.baseChangeAux_fst]
      exact Category.id_comp _
    · simp [DescentDatum.baseChangeAux_snd, pullback.condition]
  · simp

variable (g) in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma spread_pr12_key :
    pullback.fst (pullback.snd (pullback.snd aj (pullback.fst gj (E.map l.hom)) ≫
        pullback.snd gj (E.map l.hom)) (pullback.snd gj (E.map l.hom)) ≫
          pullback.snd gj (E.map l.hom)) (pullback.snd gj (E.map l.hom)) ≫
        spreadCompP l ≫ (Scheme.baseChangeDiagram E (spreadP E gj aj)).map g =
      spreadCompQ l ≫ (Scheme.baseChangeDiagram E (spreadQ E gj aj)).map g ≫
        spreadPr12 E gj aj k := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, baseChangeDiagram_map_snd, spreadCompP_snd_assoc,
      spreadPr12_snd, baseChangeDiagram_map_snd, spreadCompQ_snd_assoc]
    have hQ := pullback.condition (f := pullback.snd (pullback.snd aj
      (pullback.fst gj (E.map l.hom)) ≫ pullback.snd gj (E.map l.hom))
        (pullback.snd gj (E.map l.hom)) ≫ pullback.snd gj (E.map l.hom))
      (g := pullback.snd gj (E.map l.hom))
    rw [reassoc_of% hQ]

set_option backward.isDefEq.respectTransparency false in
lemma spread_actPr12_key (hb : b ≫ aj ≫ gj = pullback.snd _ _ ≫ E.map k.hom) (h1) :
    pullback.lift (f := lvlA E gj aj l ≫ lvlG E gj l) (g := lvlG E gj l)
        (pullback.fst (pullback.snd (lvlA E gj aj l ≫ lvlG E gj l) (lvlG E gj l) ≫ lvlG E gj l)
          (lvlG E gj l) ≫ spreadAct g b h1)
        (pullback.snd (pullback.snd (lvlA E gj aj l ≫ lvlG E gj l) (lvlG E gj l) ≫ lvlG E gj l)
          (lvlG E gj l)) (by rw [Category.assoc, spreadAct_snd_assoc]; exact pullback.condition) ≫
        spreadCompP l ≫ (Scheme.baseChangeDiagram E (spreadP E gj aj)).map g =
      spreadCompQ l ≫ (Scheme.baseChangeDiagram E (spreadQ E gj aj)).map g ≫
        spreadActPr12 b hb := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeDiagram_map_fst, spreadCompP_fst, spreadActPr12_fst]
    apply pullback.hom_ext
    · simp only [Category.assoc, DescentDatum.baseChangeAux_fst, pullback.lift_fst_assoc,
        pullback.lift_fst, spreadAct_fst]
      exact spread_pr12_key_assoc g b
    · simp only [Category.assoc, DescentDatum.baseChangeAux_snd, pullback.lift_snd_assoc,
        pullback.lift_snd, spreadPr3, baseChangeDiagram_map_fst_assoc,
        spreadCompQ_fst_assoc, spreadAuxQ_snd]
  · simp only [Category.assoc, baseChangeDiagram_map_snd, spreadCompP_snd_assoc,
      pullback.lift_snd_assoc, spreadActPr12_snd, spreadCompQ_snd_assoc]

variable (g) in
set_option backward.isDefEq.respectTransparency false in
lemma spread_pr13_key :
    pullback.lift (f := lvlA E gj aj l ≫ lvlG E gj l) (g := lvlG E gj l)
        (pullback.fst (pullback.snd (lvlA E gj aj l ≫ lvlG E gj l) (lvlG E gj l) ≫ lvlG E gj l)
          (lvlG E gj l) ≫ pullback.fst (lvlA E gj aj l ≫ lvlG E gj l) (lvlG E gj l))
        (pullback.snd (pullback.snd (lvlA E gj aj l ≫ lvlG E gj l) (lvlG E gj l) ≫ lvlG E gj l)
          (lvlG E gj l)) (by simp only [Category.assoc, pullback.condition]) ≫
        spreadCompP l ≫ (Scheme.baseChangeDiagram E (spreadP E gj aj)).map g =
      spreadCompQ l ≫ (Scheme.baseChangeDiagram E (spreadQ E gj aj)).map g ≫
        spreadPr13 E gj aj k := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeDiagram_map_fst, spreadCompP_fst, spreadPr13_fst,
      baseChangeDiagram_map_fst_assoc, spreadCompQ_fst_assoc]
    apply pullback.hom_ext
    · simp [DescentDatum.baseChangeAux_fst]
    · simp [DescentDatum.baseChangeAux_snd]
  · simp only [Category.assoc, baseChangeDiagram_map_snd, spreadCompP_snd_assoc,
      pullback.lift_snd_assoc, spreadPr13_snd, spreadCompQ_snd_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The descent datum at level `l`, given the identities of a descent datum for `b` after base
change to `l`. -/
noncomputable def spreadDatum (hb : b ≫ aj ≫ gj = pullback.snd _ _ ≫ E.map k.hom)
    (h1 : (Scheme.baseChangeDiagram E (spreadP E gj aj)).map g ≫ b ≫ aj =
      (Scheme.baseChangeDiagram E (spreadP E gj aj)).map g ≫ pullback.fst _ _ ≫
        pullback.snd (aj ≫ gj) gj)
    (h2 : (Scheme.baseChangeDiagram E (aj ≫ gj)).map g ≫ spreadDiag E gj aj k ≫ b =
      (Scheme.baseChangeDiagram E (aj ≫ gj)).map g ≫ pullback.fst _ _)
    (h3 : (Scheme.baseChangeDiagram E (spreadQ E gj aj)).map g ≫ spreadActPr12 b hb ≫ b =
      (Scheme.baseChangeDiagram E (spreadQ E gj aj)).map g ≫ spreadPr13 E gj aj k ≫ b) :
    DescentDatum (lvlG E gj l) (lvlA E gj aj l) where
  act := spreadAct g b h1
  act_comp := spreadAct_snd h1
  unit := by
    apply pullback.hom_ext
    · rw [Category.assoc, spreadAct_fst, reassoc_of% (spread_unit_key g), h2]
      simp
    · simp
  assoc := by
    apply pullback.hom_ext
    · simp only [Category.assoc, spreadAct_fst]
      rw [reassoc_of% (spread_actPr12_key hb h1), reassoc_of% (spread_pr13_key g), h3]
    · simp

end Datum

end LevelDatum

/-! ### Descent data over a limit -/

section Limit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, CompactSpace (E.obj i)]
  [∀ i, QuasiSeparatedSpace (E.obj i)] {c : Cone E}

set_option backward.isDefEq.respectTransparency false in
/-- **EGA IV 8 for IX.4.12**: let `c.pt = lim E i` (cofiltered, affine transition maps,
quasi-compact quasi-separated locally noetherian `E i`), `g_j : S_j ⟶ E j` proper and
surjective, `g : S' ⟶ c.pt` its base change, and `X'` an étale covering of `S'` which is the base
change of an étale covering `X_j` of `S_j`. Every descent datum on `X'` relative to `g` is
effective: the datum descends to some `E l` (EGA IV 8.8.2), where it is effective by IX.4.12 over
a noetherian base. -/
theorem DescentDatum.isEffective_of_isLimit_of_isPullback (hc : IsLimit c)
    [∀ i, IsLocallyNoetherian (E.obj i)] {j : I} {S' Sj X' Xj : Scheme.{u}} {g : S' ⟶ c.pt}
    {gj : Sj ⟶ E.obj j} [IsProper gj] [Surjective gj] {a : X' ⟶ S'} {aj : Xj ⟶ Sj} [IsFinite aj]
    [Etale aj] {eS : S' ⟶ Sj} {eX : X' ⟶ Xj} (hS : IsPullback eS g gj (c.π.app j))
    (hX : IsPullback eX a aj eS) (D : DescentDatum g a) : D.IsEffective etaleCovering := by
  -- the cartesian squares for `X'`, `P = X' ×_{c.pt} S'` and `Q = P ×_{c.pt} S'`
  have hXg : IsPullback eX (a ≫ g) (aj ≫ gj) (c.π.app j) := hX.paste_vert hS
  have hP := isPullback_pullbackMap_fst_of_isPullback hXg hS
  set eP := pullback.map (a ≫ g) g (aj ≫ gj) gj eX eS (c.π.app j) hXg.w.symm hS.w.symm with heP
  have hP' : IsPullback eP (pullback.snd (a ≫ g) g ≫ g) (pullback.snd (aj ≫ gj) gj ≫ gj)
      (c.π.app j) := by
    have e₁ : pullback.fst (a ≫ g) g ≫ a ≫ g = pullback.snd (a ≫ g) g ≫ g := pullback.condition
    have e₂ : pullback.fst (aj ≫ gj) gj ≫ aj ≫ gj = pullback.snd (aj ≫ gj) gj ≫ gj :=
      pullback.condition
    rw [← e₁, ← e₂]
    exact hP
  have hQ := isPullback_pullbackMap_fst_of_isPullback hP' hS
  -- finiteness conditions
  have : IsProper (pullback.fst (aj ≫ gj) gj) := MorphismProperty.pullback_fst _ _ inferInstance
  have : IsProper (pullback.fst (pullback.snd (aj ≫ gj) gj ≫ gj) gj) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  -- the action descends to some `k` (EGA IV 8.8.2)
  have hact : D.act ≫ a ≫ g = pullback.fst (a ≫ g) g ≫ a ≫ g := by
    rw [reassoc_of% D.act_comp, pullback.condition]
  obtain ⟨k, b, hb, hbc⟩ := Scheme.exists_hom_of_isPullback hc (aj ≫ gj) hP (D.act ≫ eX) (by
    rw [Category.assoc, hXg.w, ← Category.assoc, hact])
  -- the identities of a descent datum hold at some level (EGA IV 8.8.2 (i))
  obtain ⟨l₁, g₁, h₁⟩ := Scheme.exists_map_comp_eq_of_isPullback hc gj hP (b ≫ aj)
    (pullback.fst _ _ ≫ pullback.snd (aj ≫ gj) gj) (by rw [Category.assoc, hb])
    (by rw [Category.assoc, ← pullback.condition (f := aj ≫ gj) (g := gj)]
        exact pullback.condition) (by
      rw [reassoc_of% hbc, hX.w, reassoc_of% D.act_comp]
      simp [heP])
  have e₂ : (Scheme.baseChangeCone hXg).π.app k ≫ spreadDiag E gj aj k =
      pullback.lift (𝟙 X') a (by simp) ≫ (Scheme.baseChangeCone hP).π.app k := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [heP]
        exact (Category.id_comp _).symm
      · simp [heP, hX.w]
    · simp
      exact (Category.id_comp _).symm
  obtain ⟨l₂, g₂, h₂⟩ := Scheme.exists_map_comp_eq_of_isPullback hc (aj ≫ gj) hXg
    (spreadDiag E gj aj k ≫ b) (pullback.fst _ _) (by rw [Category.assoc, hb, spreadDiag_snd_assoc])
    pullback.condition (by
      rw [reassoc_of% e₂, hbc, reassoc_of% D.unit]
      simp)
  have e₃ : (Scheme.baseChangeCone hQ).π.app k ≫ spreadPr12 E gj aj k =
      pullback.fst _ _ ≫ (Scheme.baseChangeCone hP).π.app k := by
    apply pullback.hom_ext
    · simp [heP]
    · simp [pullback_fst_comp_comp_assoc]
  have e₄ : (Scheme.baseChangeCone hQ).π.app k ≫ spreadActPr12 b hb =
      pullback.lift (f := a ≫ g) (g := g)
        (pullback.fst (pullback.snd (a ≫ g) g ≫ g) g ≫ D.act)
        (pullback.snd (pullback.snd (a ≫ g) g ≫ g) g)
        (by rw [Category.assoc, reassoc_of% D.act_comp, pullback.condition]) ≫
        (Scheme.baseChangeCone hP).π.app k := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, spreadActPr12_fst, pullback.lift_fst]
        rw [reassoc_of% e₃, hbc]
        simp [heP]
      · simp [heP]
    · simp [pullback_fst_comp_comp_assoc]
  have e₅ : (Scheme.baseChangeCone hQ).π.app k ≫ spreadPr13 E gj aj k =
      pullback.lift (f := a ≫ g) (g := g)
        (pullback.fst (pullback.snd (a ≫ g) g ≫ g) g ≫ pullback.fst (a ≫ g) g)
        (pullback.snd (pullback.snd (a ≫ g) g ≫ g) g)
        (by simp only [Category.assoc, pullback.condition]) ≫
        (Scheme.baseChangeCone hP).π.app k := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [heP]
      · simp [heP]
    · simp [pullback_fst_comp_comp_assoc]
  obtain ⟨l₃, g₃, h₃⟩ := Scheme.exists_map_comp_eq_of_isPullback hc (aj ≫ gj) hQ
    (spreadActPr12 b hb ≫ b) (spreadPr13 E gj aj k ≫ b)
    (by rw [Category.assoc, hb, spreadActPr12_snd_assoc])
    (by rw [Category.assoc, hb, spreadPr13_snd_assoc]) (by
      rw [reassoc_of% e₄, reassoc_of% e₅, hbc, reassoc_of% D.assoc])
  -- a common level `l`
  obtain ⟨m, i₁, i₂, hi⟩ := IsCofiltered.cospan g₁ g₂
  obtain ⟨l, i, i₃, hi'⟩ := IsCofiltered.cospan (i₁ ≫ g₁) g₃
  have H₁ : (Scheme.baseChangeDiagram E (spreadP E gj aj)).map (i ≫ i₁ ≫ g₁) ≫ b ≫ aj =
      (Scheme.baseChangeDiagram E (spreadP E gj aj)).map (i ≫ i₁ ≫ g₁) ≫ pullback.fst _ _ ≫
        pullback.snd (aj ≫ gj) gj := by
    simp only [Functor.map_comp, Category.assoc, h₁]
  have H₂ : (Scheme.baseChangeDiagram E (aj ≫ gj)).map (i ≫ i₁ ≫ g₁) ≫ spreadDiag E gj aj k ≫ b =
      (Scheme.baseChangeDiagram E (aj ≫ gj)).map (i ≫ i₁ ≫ g₁) ≫ pullback.fst _ _ := by
    rw [hi]
    simp only [Functor.map_comp, Category.assoc, h₂]
  have H₃ : (Scheme.baseChangeDiagram E (spreadQ E gj aj)).map (i ≫ i₁ ≫ g₁) ≫
      spreadActPr12 b hb ≫ b = (Scheme.baseChangeDiagram E (spreadQ E gj aj)).map
        (i ≫ i₁ ≫ g₁) ≫ spreadPr13 E gj aj k ≫ b := by
    rw [hi']
    simp only [Functor.map_comp, Category.assoc, h₃]
  set G : l ⟶ k := i ≫ i₁ ≫ g₁ with hG
  -- the descent datum at level `l` is effective (IX.4.12 over a noetherian base)
  have : IsProper (lvlG E gj l) := MorphismProperty.pullback_snd _ _ inferInstance
  have : Surjective (lvlG E gj l) := MorphismProperty.pullback_snd _ _ inferInstance
  have : IsFinite (lvlA E gj aj l) := MorphismProperty.pullback_snd _ _ inferInstance
  have : Etale (lvlA E gj aj l) := MorphismProperty.pullback_snd _ _ inferInstance
  obtain ⟨Xl, bl, vl, hbl, hvl, hactl⟩ := (isEffectiveDescentMorphism_of_isProper
    (lvlG E gj l)).2 (lvlA E gj aj l) (spreadDatum hb H₁ H₂ H₃) ⟨inferInstance, inferInstance⟩
  -- base change of the descended covering to `c.pt`
  set eSl := (Scheme.baseChangeCone hS).π.app l with heSl
  have hSl : IsPullback eSl g (lvlG E gj l) (c.π.app l.left) :=
    Scheme.isPullback_baseChangeCone hS l
  have heSl₁ : eSl ≫ pullback.fst gj (E.map l.hom) = eS := by simp [heSl]
  let κ : X' ⟶ pullback aj (pullback.fst gj (E.map l.hom)) :=
    pullback.lift eX (a ≫ eSl) (by rw [Category.assoc, heSl₁, hX.w])
  have hκ₁ : κ ≫ pullback.fst _ _ = eX := pullback.lift_fst _ _ _
  have hκ₂ : κ ≫ lvlA E gj aj l = a ≫ eSl := pullback.lift_snd _ _ _
  have sq₁ : IsPullback κ a (lvlA E gj aj l) eSl := by
    refine IsPullback.of_right ?_ hκ₂
      (IsPullback.of_hasPullback aj (pullback.fst gj (E.map l.hom)))
    rw [hκ₁, heSl₁]
    exact hX
  have hv := sq₁.paste_horiz hvl
  let v : X' ⟶ pullback bl (c.π.app l.left) :=
    pullback.lift (κ ≫ vl) (a ≫ g) (by rw [hv.w, hSl.w, Category.assoc])
  refine ⟨pullback bl (c.π.app l.left), pullback.snd _ _, v,
    etaleCovering.pullback_snd _ _ hbl, ?_, ?_⟩
  · refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback bl (c.π.app l.left))
    simp only [v, pullback.lift_fst]
    rw [← hSl.w]
    exact hv
  · -- compatibility with the descent data
    let κP : pullback (a ≫ g) g ⟶
        pullback (lvlA E gj aj l ≫ lvlG E gj l) (lvlG E gj l) :=
      pullback.map _ _ _ _ κ eSl (c.π.app l.left)
        (by rw [Category.assoc, reassoc_of% hκ₂, hSl.w]) hSl.w.symm
    have hκP : κP ≫ spreadCompP l ≫ (Scheme.baseChangeDiagram E (spreadP E gj aj)).map G =
        (Scheme.baseChangeCone hP).π.app k := by
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp [κP, heP, hκ₁, DescentDatum.baseChangeAux_fst, pullback.map]
        · simp [κP, heP, heSl₁, DescentDatum.baseChangeAux_snd, pullback.map]
      · have hc' : c.π.app l.left ≫ E.map G.left = c.π.app k.left := c.w G.left
        simp [κP, hSl.w_assoc, hc', pullback_fst_comp_comp_assoc]
    have hK : D.act ≫ κ = κP ≫ (spreadDatum hb H₁ H₂ H₃).act := by
      apply pullback.hom_ext
      · change D.act ≫ κ ≫ pullback.fst _ _ = κP ≫ spreadAct G b H₁ ≫ pullback.fst _ _
        rw [hκ₁, spreadAct_fst, reassoc_of% hκP, hbc]
      · change D.act ≫ κ ≫ lvlA E gj aj l = κP ≫ spreadAct G b H₁ ≫ lvlA E gj aj l
        rw [hκ₂, spreadAct_snd, reassoc_of% D.act_comp]
        simp [κP]
    apply pullback.hom_ext
    · simp only [v, Category.assoc, pullback.lift_fst]
      rw [reassoc_of% hK, hactl]
      simp [κP]
    · simp only [v, Category.assoc, pullback.lift_snd]
      exact hact

set_option backward.isDefEq.respectTransparency false in
/-- **IX.4.12 over a limit of noetherian schemes** (EGA IV 8): let `c.pt = lim E i` be the limit
of a cofiltered diagram of quasi-compact, quasi-separated, locally noetherian schemes with affine
transition maps, `g_j : S_j ⟶ E j` proper and surjective and `g : S' ⟶ c.pt` its base change. Every
descent datum relative to `g` on an étale covering of `S'` is effective. -/
theorem DescentDatum.isEffective_of_isLimit (hc : IsLimit c) [∀ i, IsLocallyNoetherian (E.obj i)]
    {j : I} {S' Sj X' : Scheme.{u}} {g : S' ⟶ c.pt} {gj : Sj ⟶ E.obj j} [IsProper gj]
    [Surjective gj] {eS : S' ⟶ Sj} (hS : IsPullback eS g gj (c.π.app j)) {a : X' ⟶ S'}
    [IsFinite a] [Etale a] (D : DescentDatum g a) : D.IsEffective etaleCovering := by
  have := Scheme.compactSpace_baseChangeDiagram (E := E) gj
  have := Scheme.quasiSeparatedSpace_baseChangeDiagram (E := E) gj
  -- the étale covering `X'` comes from some `S_j ×_{E j} E k` (EGA IV 8.8.2, 17.7.8)
  let a' : X' ⟶ (Scheme.baseChangeCone hS).pt := a
  have : IsFinite a' := ‹IsFinite a›
  have : Etale a' := ‹Etale a›
  obtain ⟨k, Xk, qk, e, hqf, hqe, hpb⟩ := Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale
    (Scheme.isLimitBaseChangeCone hc hS) a'
  have : IsProper (pullback.snd gj (E.map k.hom)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : Surjective (pullback.snd gj (E.map k.hom)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact D.isEffective_of_isLimit_of_isPullback hc (Scheme.isPullback_baseChangeCone hS k) hpb

end Limit

/-! ### Algebras over a noetherian ring -/

section FGSubalgebra

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

/-- The finitely generated `R`-subalgebras of `A`, ordered by inclusion. -/
abbrev FGSubalg : Type u := {B : Subalgebra R A // B.FG}

instance : IsDirectedOrder (FGSubalg R A) where
  directed B C := ⟨⟨B.1 ⊔ C.1, B.2.sup C.2⟩, (le_sup_left : B.1 ≤ B.1 ⊔ C.1),
    (le_sup_right : C.1 ≤ B.1 ⊔ C.1)⟩

instance : Nonempty (FGSubalg R A) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

/-- The diagram `B ↦ B` of the finitely generated `R`-subalgebras of `A`. -/
@[simps]
noncomputable abbrev fgSubalgDiagram : FGSubalg R A ⥤ CommRingCat.{u} where
  obj B := CommRingCat.of B.1
  map f := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom

/-- The cocone of the inclusions `B ⟶ A`. -/
@[simps]
noncomputable abbrev fgSubalgCocone : Cocone (fgSubalgDiagram R A) where
  pt := CommRingCat.of A
  ι := { app B := CommRingCat.ofHom B.1.val.toRingHom }

/-- An `R`-algebra is the filtered colimit of its finitely generated subalgebras. -/
noncomputable def isColimitFgSubalgCocone : IsColimit (fgSubalgCocone R A) := by
  have : ReflectsColimit (fgSubalgDiagram R A) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{u})
    (Types.FilteredColimit.isColimitOf _ _ (fun (x : A) ↦ ?_)
    fun (i j : FGSubalg R A) xi xj hij ↦ ?_)
  · classical
    exact ⟨⟨Algebra.adjoin R {x}, ⟨{x}, by simp⟩⟩, ⟨x, Algebra.subset_adjoin rfl⟩, rfl⟩
  · obtain ⟨m, him, hjm⟩ := exists_ge_ge i j
    exact ⟨m, homOfLE him, homOfLE hjm, Subtype.ext hij⟩

instance [IsNoetherianRing R] (B : FGSubalg R A) : IsNoetherianRing B.1 :=
  have : Algebra.FiniteType R B.1 := (Subalgebra.fg_iff_finiteType B.1).mp B.2
  Algebra.FiniteType.isNoetherianRing R B.1

end FGSubalgebra

set_option backward.isDefEq.respectTransparency false in
/-- **IX.4.12 after base change to an algebra over a noetherian ring** (EGA IV 8): let
`f : X ⟶ S` be proper and surjective, `ψ : Spec R ⟶ S` with `R` noetherian, `A` an `R`-algebra and
`g : S' ⟶ Spec A` the base change of `f` along `Spec A ⟶ Spec R ⟶ S`. Every descent datum relative
to `g` on an étale covering of `S'` is effective: `A` is the union of its finitely generated (hence
noetherian) `R`-subalgebras. -/
theorem DescentDatum.isEffective_of_isPullback_specMap {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [Surjective f] {R : CommRingCat.{u}} [IsNoetherianRing R] (ψ : Spec R ⟶ S) {A : CommRingCat.{u}}
    (φ : R ⟶ A) {S' X' : Scheme.{u}} {g : S' ⟶ Spec A} {e : S' ⟶ X}
    (h : IsPullback e g f (Spec.map φ ≫ ψ)) {a : X' ⟶ S'} [IsFinite a] [Etale a]
    (D : DescentDatum g a) : D.IsEffective etaleCovering := by
  let _ : Algebra R A := φ.hom.toAlgebra
  let c := Scheme.Spec.mapCone (fgSubalgCocone R A).op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (isColimitFgSubalgCocone R A).op
  let j₀ : (FGSubalg R A)ᵒᵖ := Opposite.op ⟨⊥, Subalgebra.fg_bot⟩
  let ψ₀ : Spec (CommRingCat.of (⊥ : Subalgebra R A)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap R (⊥ : Subalgebra R A))) ≫ ψ
  have (i : (FGSubalg R A)ᵒᵖ) : IsAffine (((fgSubalgDiagram R A).op ⋙ Scheme.Spec).obj i) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of i.unop.1)))
  have (i : (FGSubalg R A)ᵒᵖ) :
      IsLocallyNoetherian (((fgSubalgDiagram R A).op ⋙ Scheme.Spec).obj i) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of i.unop.1)))
  have : ∀ {i j : (FGSubalg R A)ᵒᵖ} (f : i ⟶ j),
      IsAffineHom (((fgSubalgDiagram R A).op ⋙ Scheme.Spec).map f) :=
    fun _ ↦ isAffineHom_of_isAffine _
  have hψ : c.π.app j₀ ≫ ψ₀ = Spec.map φ ≫ ψ := by
    change Spec.map (CommRingCat.ofHom (⊥ : Subalgebra R A).val.toRingHom) ≫ Spec.map _ ≫ ψ = _
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
  let g' : S' ⟶ c.pt := g
  let eS : S' ⟶ pullback f ψ₀ := pullback.lift e (g' ≫ c.π.app j₀) (by
    rw [Category.assoc, hψ]
    exact h.w)
  have hS : IsPullback eS g' (pullback.snd f ψ₀) (c.π.app j₀) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f ψ₀)
    rw [pullback.lift_fst, hψ]
    exact h
  have : IsProper (pullback.snd f ψ₀) := MorphismProperty.pullback_snd _ _ inferInstance
  have : Surjective (pullback.snd f ψ₀) := MorphismProperty.pullback_snd _ _ inferInstance
  exact DescentDatum.isEffective_of_isLimit (g := g') (j := j₀) (gj := pullback.snd f ψ₀)
    (eS := eS) hc hS D

/-! ### Universal effective descent -/

set_option backward.isDefEq.respectTransparency false in
/-- **IX.6.9** (and IX.4.12 after any base change): a proper surjective morphism `f : X ⟶ S` to a
locally noetherian scheme is a universal effective descent morphism for étale coverings: for every
`t : T ⟶ S`, `X ×_S T ⟶ T` is an effective descent morphism for them. By IX.4.5 it suffices to
treat the base changes to the `Spec 𝒪_{T,x}`; `Spec 𝒪_{T,x} ⟶ S` factors through an affine open
`Spec R` of `S`, `R` noetherian, and `DescentDatum.isEffective_of_isPullback_specMap` applies. -/
theorem isEffectiveDescentMorphism_pullback_snd_of_isProper {X S T : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Surjective f] [IsLocallyNoetherian S] (t : T ⟶ S) :
    IsEffectiveDescentMorphism (pullback.snd f t) etaleCovering := by
  have : IsProper (pullback.snd f t) := MorphismProperty.pullback_snd _ _ inferInstance
  have : Surjective (pullback.snd f t) := MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFinitePresentation (pullback.snd f t) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  refine ⟨isDescentMorphism_of_isProper, fun X' a D ha ↦ ?_⟩
  have : IsFinite a := ha.1
  have : Etale a := ha.2
  have ha' : etaleFinitePresentation a := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hfp : D.IsEffective etaleFinitePresentation := by
    rw [D.isEffective_iff_forall_fromSpecStalk ha']
    intro x
    -- `Spec 𝒪_{T,x} ⟶ S` factors through an affine open `Spec R` of `S`
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (t x)) isOpen_univ
    have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let φ : Γ(S, U) ⟶ T.presheaf.stalk x := S.presheaf.germ U (t x) hxU ≫ t.stalkMap x
    have hφ : Spec.map φ ≫ hU.fromSpec = T.fromSpecStalk x ≫ t := by
      have e : Spec.map (S.presheaf.germ U (t x) hxU) ≫ hU.fromSpec = S.fromSpecStalk (t x) :=
        hU.fromSpecStalk_eq_fromSpecStalk hxU
      rw [Spec.map_comp, Category.assoc, e, Scheme.SpecMap_stalkMap_fromSpecStalk]
    have h : IsPullback (pullback.fst (pullback.snd f t) (T.fromSpecStalk x) ≫ pullback.fst f t)
        (pullback.snd (pullback.snd f t) (T.fromSpecStalk x)) f (Spec.map φ ≫ hU.fromSpec) := by
      rw [hφ]
      exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback f t)
    have : IsFinite (pullback.snd a (pullback.fst (pullback.snd f t) (T.fromSpecStalk x))) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have : Etale (pullback.snd a (pullback.fst (pullback.snd f t) (T.fromSpecStalk x))) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    exact ((D.baseChange (T.fromSpecStalk x)).isEffective_of_isPullback_specMap f hU.fromSpec φ
      h).of_le fun _ _ f h ↦ have : IsFinite f := h.1; ⟨⟨h.2, inferInstance⟩, inferInstance⟩
  -- the descended scheme is finite over `T`: proper, since `X' = Y ×_T (X ×_S T)` is, and
  -- quasi-finite
  obtain ⟨Y, b, v, hb, hv, hact⟩ := hfp
  have : Etale b := hb.1.1
  have : IsProper b := (isProper_iff_of_isPullback hv.flip).mp inferInstance
  have : LocallyQuasiFinite b := locallyQuasiFinite_of_formallyUnramified b
  exact ⟨Y, b, v, ⟨.of_isProper_of_locallyQuasiFinite b, inferInstance⟩, hv, hact⟩

/-- **IX.6.9**: `UniversalProperDescentStatement` holds: for `f : X ⟶ S` proper and surjective
with `S` locally noetherian and any `t : T ⟶ S`, base change along `X ×_S T ⟶ T` is an equivalence
of the étale coverings of `T` with the étale coverings of `X ×_S T` endowed with descent data. -/
theorem universalProperDescentStatement : UniversalProperDescentStatement.{u} :=
  fun _ _ f _ _ _ _ t ↦ isEquivalence_fetComparison_of_isEffectiveDescentMorphism _
    (isEffectiveDescentMorphism_pullback_snd_of_isProper f t)

end SGA.SGA1.ExposeIX
