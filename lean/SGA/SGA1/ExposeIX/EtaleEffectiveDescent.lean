/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.AdicCompletion.Algebra
import SGA.SGA1.ExposeIX.EtaleMorphismDescent

/-!
# SGA 1, Exposé IX, §4: effectiveness criteria for descent of étale schemes

A descent datum on an `S'`-scheme `X'` relative to `g : S' ⟶ S` is recorded here as an action
of the groupoid `S' ×_S S' ⇉ S'` on `X'` (`DescentDatum`): a morphism
`X' ×_S S' ⟶ X'`, `(x', s') ↦ x'·s'`, lying over the second projection, with the unit and
associativity laws. This is equivalent to the usual isomorphism `p₁^* X' ≅ p₂^* X'` over
`S' ×_S S'` satisfying the cocycle condition. A datum is *effective* if it is isomorphic to the
canonical datum on `X ×_S S'` for an `S`-scheme `X` (`DescentDatum.IsEffective`).

What is proved:

* IX.3.3 in the language of descent data: for an effective datum `(X, v)`, morphisms from `X`
  to étale `S`-schemes are the compatible morphisms from `X'`, and the descended `X` is unique
  up to unique isomorphism;
* the canonical descent datum on `X ×_S S'` and its effectiveness; base change of descent data
  along any `T ⟶ S`, and the fact that effective data stay effective (the "trivial" halves of
  IX.4.2–IX.4.5);
* effectiveness when `g` has a section (the case to which the proof of IX.4.9 reduces), and
  effectiveness for open subschemes of `S'` along any universally submersive `g` (a special
  case of IX.4.1 and IX.4.7–IX.4.9);
* the descent half of IX.4.1, IX.4.7, IX.4.8, IX.4.9, IX.4.12 (all these `g` are universally
  submersive, so IX.3.3 applies), and the part of the proof of IX.4.1 showing that an
  `S`-scheme is étale, separated and of finite type as soon as its base change along a
  faithfully flat quasi-compact morphism is;
* for IX.4.10 and IX.4.11: full faithfulness (in `EtaleMorphismDescent.lean`); along a radicial
  `g`, every étale `S'`-scheme carries one and only one descent datum, so that essential
  surjectivity reduces to effectiveness of these data; essential surjectivity on open
  subschemes.

The remaining statements of §4 are recorded as `...Statement` definitions: IX.4.6 in SGA's form
with algebraically closed residue fields (needs flat local extensions with prescribed residue
field, EGA 0_III 10.3.1; the form with separably closed residue fields is proved), IX.4.9 (proved
from quasi-sections, EGA IV 14.5.4, in `SGA.SGA1.ExposeIX.UniversallyOpenDescent`) and IX.4.12
(needs the comparison theorem IX.1.10).

Elsewhere: IX.4.3 (effectiveness is local on `S`) is proved by gluing in
`SGA.SGA1.ExposeIX.EffectiveGluing`; IX.4.1 and IX.4.11 (via quasi-affine descent, VIII.7.9) are
in `SGA.SGA1.ExposeIX.QuasiAffineDescent`; IX.4.4 and the
first assertion of IX.4.5 are in `SGA.SGA1.ExposeIX.EffectiveNearPoint`; IX.4.2 is in
`SGA.SGA1.ExposeIX.FlatBaseChange`; the second assertion of IX.4.5 (completed local rings) is in
`SGA.SGA1.ExposeIX.CompletedLocalRings`; IX.4.7 and IX.4.10 over a locally noetherian base are in
`SGA.SGA1.ExposeIX.FiniteEffectiveDescent`, and IX.4.7 over any base in
`SGA.SGA1.ExposeIX.HenselianFiniteDescent`; IX.4.6 is in `SGA.SGA1.ExposeIX.StrictlyLocalDescent`;
IX.4.8 is in `SGA.SGA1.ExposeIX.QuasiFiniteDescent`; IX.4.10 over any base is in
`SGA.SGA1.ExposeIX.TopologicalInvariance`.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc pullback.condition pullback.condition_assoc

/-- The pullback square condition for a pullback along a composite, in the form produced by
`simp`'s reassociation. -/
@[reassoc (attr := local simp)]
lemma pullback_fst_comp_comp {X Y Z W : Scheme.{u}} (f₁ : X ⟶ Y) (f₂ : Y ⟶ W) (h : Z ⟶ W) :
    pullback.fst (f₁ ≫ f₂) h ≫ f₁ ≫ f₂ = pullback.snd (f₁ ≫ f₂) h ≫ h :=
  pullback.condition

variable {S' S X' : Scheme.{u}} (g : S' ⟶ S) (a : X' ⟶ S')

/-- A descent datum on the `S'`-scheme `a : X' ⟶ S'` relative to `g : S' ⟶ S`, as an action of
the groupoid `S' ×_S S' ⇉ S'`: a morphism `act : X' ×_S S' ⟶ X'` sending `(x', s')` (with
`g(a(x')) = g(s')`) to a point over `s'`, such that `x'·a(x') = x'` and
`(x'·s'₁)·s'₂ = x'·s'₂`. -/
structure DescentDatum where
  /-- The action `(x', s') ↦ x'·s'`. -/
  act : pullback (a ≫ g) g ⟶ X'
  /-- `x'·s'` lies over `s'`. -/
  act_comp : act ≫ a = pullback.snd (a ≫ g) g
  /-- `x'·a(x') = x'`. -/
  unit : pullback.lift (𝟙 X') a (by simp) ≫ act = 𝟙 X'
  /-- `(x'·s'₁)·s'₂ = x'·s'₂`. -/
  assoc :
    pullback.lift (f := a ≫ g) (g := g)
        (pullback.fst (pullback.snd (a ≫ g) g ≫ g) g ≫ act)
        (pullback.snd (pullback.snd (a ≫ g) g ≫ g) g)
        (by rw [Category.assoc, reassoc_of% act_comp, pullback.condition]) ≫ act =
      pullback.lift (f := a ≫ g) (g := g)
        (pullback.fst (pullback.snd (a ≫ g) g ≫ g) g ≫ pullback.fst (a ≫ g) g)
        (pullback.snd (pullback.snd (a ≫ g) g ≫ g) g)
        (by simp only [Category.assoc, pullback.condition]) ≫ act

variable {g a}

namespace DescentDatum

/-- The associativity law of a descent datum, evaluated on `T`-valued points. -/
lemma act_lift_act (D : DescentDatum g a) {T : Scheme.{u}} (k : T ⟶ pullback (a ≫ g) g)
    (s : T ⟶ S') (hs : k ≫ pullback.snd (a ≫ g) g ≫ g = s ≫ g) :
    pullback.lift (f := a ≫ g) (g := g) (k ≫ D.act) s
        (by rw [Category.assoc, reassoc_of% D.act_comp, hs]) ≫ D.act =
      pullback.lift (f := a ≫ g) (g := g) (k ≫ pullback.fst (a ≫ g) g) s
        (by simp only [Category.assoc, pullback.condition, hs]) ≫ D.act := by
  have := congrArg (pullback.lift (f := pullback.snd (a ≫ g) g ≫ g) (g := g) k s hs ≫ ·) D.assoc
  simp only [← Category.assoc] at this
  convert this using 2 <;> apply pullback.hom_ext <;> simp

end DescentDatum

variable (g) in
/-- The canonical descent datum on `X ×_S S'`: `((x, s'₁), s'₂) ↦ (x, s'₂)`. -/
noncomputable def DescentDatum.canonical {X : Scheme.{u}} (b : X ⟶ S) :
    DescentDatum g (pullback.snd b g) where
  act := pullback.lift (pullback.fst _ _ ≫ pullback.fst b g) (pullback.snd _ _)
    (by simp only [Category.assoc, pullback.condition])
  act_comp := by simp
  unit := by apply pullback.hom_ext <;> simp
  assoc := by apply pullback.hom_ext <;> simp

/-- A descent datum on `X'` is *effective* for the class `P` if there is an `S`-scheme
`b : X ⟶ S` with `P b` and a cartesian square `X' ⟶ X` over `S' ⟶ S` identifying the datum
with the canonical one on `X ×_S S'`. Since `X' ≅ X ×_S S'`, compatibility of the actions
only concerns the component in `X`. -/
def DescentDatum.IsEffective (D : DescentDatum g a) (P : MorphismProperty Scheme.{u}) : Prop :=
  ∃ (X : Scheme.{u}) (b : X ⟶ S) (v : X' ⟶ X), P b ∧ IsPullback v a b g ∧
    D.act ≫ v = pullback.fst (a ≫ g) g ≫ v

/-- Effectiveness for a class `P` implies effectiveness for any larger class. -/
lemma DescentDatum.IsEffective.of_le {D : DescentDatum g a} {P Q : MorphismProperty Scheme.{u}}
    (h : D.IsEffective P) (hPQ : P ≤ Q) : D.IsEffective Q :=
  let ⟨X, b, v, hb, hv, hact⟩ := h
  ⟨X, b, v, hPQ _ hb, hv, hact⟩

/-- For an effective descent datum, `X' ×_S S'` is the kernel pair of `X' ⟶ X`, with the
action and the first projection as the two projections. -/
lemma DescentDatum.isPullback_act {D : DescentDatum g a} {X : Scheme.{u}} {b : X ⟶ S}
    {v : X' ⟶ X} (hv : IsPullback v a b g) (hact : D.act ≫ v = pullback.fst (a ≫ g) g ≫ v) :
    IsPullback D.act (pullback.fst (a ≫ g) g) v v := by
  have houter : IsPullback (D.act ≫ a) (pullback.fst (a ≫ g) g) g (v ≫ b) := by
    rw [D.act_comp, hv.w]
    exact (IsPullback.of_hasPullback (a ≫ g) g).flip
  exact houter.of_right hact hv.flip

/-- IX.3.3 in the language of descent data: if `(X, v)` is an effective descent of `D` along a
universally submersive `g`, then `S`-morphisms from `X` to an étale `S`-scheme `Y` correspond to
`S`-morphisms `φ' : X' ⟶ Y` compatible with the descent datum (`x'·s'` and `x'` have the same
image). -/
theorem DescentDatum.existsUnique_hom [UniversallySubmersive g] {D : DescentDatum g a}
    {X : Scheme.{u}} {b : X ⟶ S} {v : X' ⟶ X} (hv : IsPullback v a b g)
    (hact : D.act ≫ v = pullback.fst (a ≫ g) g ≫ v) {Y : Scheme.{u}} (q : Y ⟶ S) [Etale q]
    (φ' : X' ⟶ Y) (hφ : φ' ≫ q = v ≫ b) (hD : D.act ≫ φ' = pullback.fst (a ≫ g) g ≫ φ') :
    ∃! φ : X ⟶ Y, φ ≫ q = b ∧ v ≫ φ = φ' := by
  have : UniversallySubmersive v := MorphismProperty.of_isPullback hv.flip ‹_›
  have hK := DescentDatum.isPullback_act hv hact
  refine existsUnique_hom_of_kernelPair v b q φ' hφ ?_
  rw [← cancel_epi hK.isoPullback.hom, reassoc_of% hK.isoPullback_hom_fst,
    reassoc_of% hK.isoPullback_hom_snd, hD]

/-- IX.3.3, uniqueness of descent: two effective descents `(X₁, v₁)`, `(X₂, v₂)` of the same
descent datum along a universally submersive `g`, with `X₁`, `X₂` étale over `S`, are
isomorphic by a unique isomorphism compatible with `v₁` and `v₂`. -/
theorem DescentDatum.existsUnique_iso [UniversallySubmersive g] {D : DescentDatum g a}
    {X₁ X₂ : Scheme.{u}} {b₁ : X₁ ⟶ S} {b₂ : X₂ ⟶ S} [Etale b₁] [Etale b₂] {v₁ : X' ⟶ X₁}
    {v₂ : X' ⟶ X₂} (hv₁ : IsPullback v₁ a b₁ g) (hv₂ : IsPullback v₂ a b₂ g)
    (hact₁ : D.act ≫ v₁ = pullback.fst (a ≫ g) g ≫ v₁)
    (hact₂ : D.act ≫ v₂ = pullback.fst (a ≫ g) g ≫ v₂) :
    ∃ e : X₁ ≅ X₂, e.hom ≫ b₂ = b₁ ∧ v₁ ≫ e.hom = v₂ := by
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩, hφu⟩ := DescentDatum.existsUnique_hom hv₁ hact₁ b₂ v₂
    (by rw [hv₂.w, hv₁.w]) hact₂
  obtain ⟨ψ, ⟨hψ₁, hψ₂⟩, hψu⟩ := DescentDatum.existsUnique_hom hv₂ hact₂ b₁ v₁
    (by rw [hv₁.w, hv₂.w]) hact₁
  obtain ⟨i₁, -, hid₁⟩ := DescentDatum.existsUnique_hom hv₁ hact₁ b₁ v₁ rfl hact₁
  obtain ⟨i₂, -, hid₂⟩ := DescentDatum.existsUnique_hom hv₂ hact₂ b₂ v₂ rfl hact₂
  refine ⟨⟨φ, ψ, ?_, ?_⟩, hφ₁, hφ₂⟩
  · exact (hid₁ (φ ≫ ψ) ⟨by rw [Category.assoc, hψ₁, hφ₁], by rw [reassoc_of% hφ₂, hψ₂]⟩).trans
      (hid₁ (𝟙 _) ⟨Category.id_comp _, Category.comp_id _⟩).symm
  · exact (hid₂ (ψ ≫ φ) ⟨by rw [Category.assoc, hφ₁, hψ₁], by rw [reassoc_of% hψ₂, hφ₂]⟩).trans
      (hid₂ (𝟙 _) ⟨Category.id_comp _, Category.comp_id _⟩).symm

/-- The canonical descent datum is effective. -/
lemma DescentDatum.isEffective_canonical {X : Scheme.{u}} (b : X ⟶ S)
    (P : MorphismProperty Scheme.{u}) (hb : P b) :
    (DescentDatum.canonical g b).IsEffective P :=
  ⟨X, b, pullback.fst b g, hb, .of_hasPullback b g, by simp [DescentDatum.canonical]⟩

namespace DescentDatum

variable (D : DescentDatum g a) {σ : S ⟶ S'} (hσ : σ ≫ g = 𝟙 S)
include hσ

/-- Given a section `σ` of `g`, the morphism `x' ↦ (x', σ(g(a(x'))))`. -/
noncomputable def toSection : X' ⟶ pullback (a ≫ g) g :=
  pullback.lift (𝟙 X') (a ≫ g ≫ σ) (by simp [hσ])

/-- Given a section `σ` of `g`, the morphism `X' ⟶ σ^* X'`, `x' ↦ x'·σ(g(a(x')))`. -/
noncomputable def toPullbackSection : X' ⟶ pullback a σ :=
  pullback.lift (toSection hσ ≫ D.act) (a ≫ g) (by
    rw [Category.assoc, D.act_comp, toSection, pullback.lift_snd, Category.assoc])

lemma act_toSection_act :
    D.act ≫ toSection hσ ≫ D.act = pullback.fst (a ≫ g) g ≫ toSection hσ ≫ D.act := by
  have hs : 𝟙 (pullback (a ≫ g) g) ≫ pullback.snd (a ≫ g) g ≫ g =
      (pullback.snd (a ≫ g) g ≫ g ≫ σ) ≫ g := by
    simp only [Category.id_comp, Category.assoc, hσ, Category.comp_id]
  have h₁ : D.act ≫ toSection hσ = pullback.lift (f := a ≫ g) (g := g) (𝟙 _ ≫ D.act)
      (pullback.snd (a ≫ g) g ≫ g ≫ σ)
      (by simp [reassoc_of% D.act_comp, hσ]) := by
    apply pullback.hom_ext
    · simp [toSection]
    · simp [toSection, reassoc_of% D.act_comp]
  have h₂ : pullback.fst (a ≫ g) g ≫ toSection hσ = pullback.lift (f := a ≫ g) (g := g)
      (𝟙 _ ≫ pullback.fst _ _) (pullback.snd (a ≫ g) g ≫ g ≫ σ) (by simp [hσ]) := by
    apply pullback.hom_ext
    · simp [toSection]
    · simp [toSection]
  rw [reassoc_of% h₁, reassoc_of% h₂]
  exact D.act_lift_act _ _ hs

lemma fst_toSection_act :
    pullback.fst a σ ≫ toSection hσ ≫ D.act = pullback.fst a σ := by
  have : pullback.fst a σ ≫ toSection hσ =
      pullback.fst a σ ≫ pullback.lift (f := a ≫ g) (g := g) (𝟙 X') a (by simp) := by
    apply pullback.hom_ext
    · simp [toSection]
    · simp [toSection, reassoc_of% hσ]
  rw [reassoc_of% this, D.unit, Category.comp_id]

/-- If `g` has a section, every descent datum relative to `g` is effective (IX.4.9, end of
proof: "the statement is trivial"). The descended scheme is `σ^* X'`. -/
theorem isEffective_of_section (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (ha : P a) : D.IsEffective P := by
  set v := D.toPullbackSection hσ
  set E := pullback (a ≫ g) g
  have hv₂ : v ≫ pullback.snd a σ = a ≫ g := by simp [v, toPullbackSection]
  let m : pullback (pullback.snd a σ) g ⟶ E :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst a σ) (pullback.snd _ _) (by simp [hσ])
  have hm₁ : m ≫ pullback.fst (a ≫ g) g = pullback.fst _ _ ≫ pullback.fst a σ := by simp [m]
  have hm₂ : m ≫ pullback.snd (a ≫ g) g = pullback.snd _ _ := by simp [m]
  refine ⟨pullback a σ, pullback.snd a σ, v, P.pullback_snd a σ ha, ?_, ?_⟩
  · refine IsPullback.of_iso_pullback ⟨hv₂⟩
      { hom := pullback.lift v a hv₂
        inv := m ≫ D.act
        hom_inv_id := ?_
        inv_hom_id := ?_ } (by simp) (by simp)
    · have : pullback.lift v a hv₂ ≫ m = pullback.lift (toSection hσ ≫ D.act) a
          (by simp [reassoc_of% D.act_comp, toSection, hσ]) := by
        apply pullback.hom_ext <;> simp [m, v, toPullbackSection]
      rw [reassoc_of% this, D.act_lift_act _ _ (by simp [toSection, hσ])]
      convert D.unit using 2
      apply pullback.hom_ext <;> simp [toSection]
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, v, toPullbackSection,
            act_toSection_act, reassoc_of% hm₁, fst_toSection_act, Category.id_comp]
        · simp only [Category.assoc, pullback.lift_fst, hv₂, reassoc_of% D.act_comp,
            reassoc_of% hm₂, Category.id_comp, pullback.condition]
      · simp [D.act_comp, hm₂]
  · apply pullback.hom_ext
    · simp only [Category.assoc, v, toPullbackSection, pullback.lift_fst, act_toSection_act]
    · simp only [Category.assoc, hv₂, reassoc_of% D.act_comp, pullback_fst_comp_comp]

end DescentDatum

namespace DescentDatum

variable (D : DescentDatum g a) {T : Scheme.{u}} (t : T ⟶ S)

variable (g a) in
/-- The comparison map `(X' ×_S T) ×_T (S' ×_S T) ⟶ X' ×_S S'` used to base change a descent
datum. -/
noncomputable def baseChangeAux :
    pullback (pullback.snd a (pullback.fst g t) ≫ pullback.snd g t) (pullback.snd g t) ⟶
      pullback (a ≫ g) g :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst a (pullback.fst g t))
    (pullback.snd _ _ ≫ pullback.fst g t) (by
      simp only [Category.assoc, pullback.condition_assoc, pullback.condition,
        pullback_fst_comp_comp_assoc])

@[reassoc]
lemma baseChangeAux_fst :
    baseChangeAux g a t ≫ pullback.fst (a ≫ g) g =
      pullback.fst _ _ ≫ pullback.fst a (pullback.fst g t) := pullback.lift_fst _ _ _

@[reassoc]
lemma baseChangeAux_snd :
    baseChangeAux g a t ≫ pullback.snd (a ≫ g) g =
      pullback.snd _ _ ≫ pullback.fst g t := pullback.lift_snd _ _ _

/-- The base change of a descent datum along `t : T ⟶ S`: a descent datum on
`X' ×_S T = X' ×_{S'} (S' ×_S T)` relative to `S' ×_S T ⟶ T`. -/
noncomputable def baseChange :
    DescentDatum (pullback.snd g t) (pullback.snd a (pullback.fst g t)) where
  act := pullback.lift (baseChangeAux g a t ≫ D.act) (pullback.snd _ _) (by
    rw [Category.assoc, D.act_comp, baseChangeAux_snd])
  act_comp := pullback.lift_snd _ _ _
  unit := by
    apply pullback.hom_ext
    · have : pullback.lift (f := pullback.snd a (pullback.fst g t) ≫ pullback.snd g t)
          (g := pullback.snd g t) (𝟙 _) (pullback.snd a (pullback.fst g t)) (by simp) ≫
          baseChangeAux g a t =
          pullback.fst a (pullback.fst g t) ≫ pullback.lift (f := a ≫ g) (g := g) (𝟙 X') a
            (by simp) := by
        apply pullback.hom_ext
        · simp [baseChangeAux_fst]
        · simp [baseChangeAux_snd, pullback.condition]
      simp only [Category.assoc, pullback.lift_fst, reassoc_of% this, D.unit, Category.comp_id,
        Category.id_comp]
    · simp
  assoc := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      have hs : (pullback.fst (pullback.snd (pullback.snd a (pullback.fst g t) ≫
          pullback.snd g t) (pullback.snd g t) ≫ pullback.snd g t) (pullback.snd g t) ≫
          baseChangeAux g a t) ≫ pullback.snd (a ≫ g) g ≫ g =
          (pullback.snd (pullback.snd (pullback.snd a (pullback.fst g t) ≫
            pullback.snd g t) (pullback.snd g t) ≫ pullback.snd g t) (pullback.snd g t) ≫
            pullback.fst g t) ≫ g := by
        simp [baseChangeAux_snd_assoc, pullback.condition]
      have key := D.act_lift_act _ _ hs
      simp only [← Category.assoc] at key ⊢
      convert key using 2 <;> apply pullback.hom_ext <;>
        simp [baseChangeAux_fst, baseChangeAux_snd]
    · simp

end DescentDatum

/-- An effective descent datum stays effective after any base change `T ⟶ S` (the "trivial"
necessity in IX.4.2–IX.4.5). -/
theorem DescentDatum.IsEffective.baseChange {D : DescentDatum g a}
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange] (h : D.IsEffective P)
    {T : Scheme.{u}} (t : T ⟶ S) :
    (D.baseChange t).IsEffective P := by
  obtain ⟨X, b, v, hb, hv, hact⟩ := h
  have hcond : pullback.fst a (pullback.fst g t) ≫ v ≫ b =
      (pullback.snd a (pullback.fst g t) ≫ pullback.snd g t) ≫ t := by
    rw [hv.w, pullback.condition_assoc, Category.assoc, pullback.condition]
  let vT : pullback a (pullback.fst g t) ⟶ pullback b t :=
    pullback.lift (pullback.fst a (pullback.fst g t) ≫ v)
      (pullback.snd a (pullback.fst g t) ≫ pullback.snd g t) (by simpa using hcond)
  refine ⟨pullback b t, pullback.snd b t, vT, P.pullback_snd b t hb, ?_, ?_⟩
  · have houter : IsPullback (vT ≫ pullback.fst b t) (pullback.snd a (pullback.fst g t)) b
        (pullback.snd g t ≫ t) := by
      have := (IsPullback.of_hasPullback a (pullback.fst g t)).paste_horiz hv
      simp only [vT, pullback.lift_fst]
      rwa [← pullback.condition]
    exact houter.of_right (by simp [vT]) (IsPullback.of_hasPullback b t)
  · apply pullback.hom_ext
    · have h₁ : (D.baseChange t).act ≫ pullback.fst a (pullback.fst g t) =
          DescentDatum.baseChangeAux g a t ≫ D.act := pullback.lift_fst _ _ _
      simp only [Category.assoc, vT, pullback.lift_fst, reassoc_of% h₁, hact,
        DescentDatum.baseChangeAux_fst_assoc]
    · simp [vT, DescentDatum.baseChange]

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.4.10, uniqueness of descent data: if `g` is radicial, an étale `S'`-scheme carries at
most one descent datum relative to `g`. Indeed `X' ×_S S' ⟶ X'` is radicial, so its section
`x' ↦ (x', a(x'))` is surjective, and both actions restrict to the identity along it. -/
theorem DescentDatum.act_eq_of_universallyInjective [UniversallyInjective g] [Etale a]
    (D₁ D₂ : DescentDatum g a) : D₁.act = D₂.act := by
  set s := pullback.lift (f := a ≫ g) (g := g) (𝟙 X') a (by simp)
  have : UniversallyInjective (pullback.fst (a ≫ g) g) := MorphismProperty.pullback_fst _ _ ‹_›
  have : Surjective s := ⟨fun e ↦ ⟨pullback.fst (a ≫ g) g e, (pullback.fst (a ≫ g) g).injective
    (by rw [← Scheme.Hom.comp_apply, pullback.lift_fst]; simp)⟩⟩
  refine hom_ext_of_surjective s a (by rw [D₁.act_comp, D₂.act_comp]) ?_
  rw [D₁.unit, D₂.unit]

namespace DescentDatum

variable (g a) in
/-- The "diagonal" section `x' ↦ (x', a(x'))` of `X' ×_S S' ⟶ X'`. -/
noncomputable abbrev diag : X' ⟶ pullback (a ≫ g) g :=
  pullback.lift (f := a ≫ g) (g := g) (𝟙 X') a (by simp)

set_option backward.isDefEq.respectTransparency.types false in
lemma surjective_of_universallyInjective [UniversallyInjective g] {T : Scheme.{u}}
    (k : T ⟶ S) {s : T ⟶ pullback k g} (hs : s ≫ pullback.fst k g = 𝟙 _) :
    Surjective s := by
  have : UniversallyInjective (pullback.fst k g) := MorphismProperty.pullback_fst _ _ ‹_›
  exact ⟨fun e ↦ ⟨pullback.fst k g e, (pullback.fst k g).injective
    (by rw [← Scheme.Hom.comp_apply, hs]; simp)⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- If `g` is radicial, the diagonal section `X' ⟶ X' ×_S S'` is radicial and universally
submersive: it is a surjective closed immersion. -/
lemma diag_universallyInjective_universallySubmersive [UniversallyInjective g] :
    UniversallyInjective (diag g a) ∧ UniversallySubmersive (diag g a) := by
  have hs : diag g a ≫ pullback.fst (a ≫ g) g = 𝟙 X' := pullback.lift_fst _ _ _
  have : IsSplitMono (diag g a) := .mk' ⟨_, hs⟩
  have : UniversallyInjective (pullback.fst (a ≫ g) g) := MorphismProperty.pullback_fst _ _ ‹_›
  have : IsSeparated (pullback.fst (a ≫ g) g) :=
    isSeparated_of_injective _ (pullback.fst (a ≫ g) g).injective
  have := isClosedImmersion_of_section _ hs
  have : Surjective (diag g a) := surjective_of_universallyInjective (a ≫ g) hs
  exact ⟨inferInstance, inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- If `g` is radicial and `a` is étale, a morphism `X' ×_S S' ⟶ X'` over the second projection
which restricts to the identity along the diagonal section is a descent datum: associativity
is automatic. -/
noncomputable def ofAct [UniversallyInjective g] [Etale a] (act : pullback (a ≫ g) g ⟶ X')
    (hact : act ≫ a = pullback.snd (a ≫ g) g) (hunit : diag g a ≫ act = 𝟙 X') :
    DescentDatum g a where
  act := act
  act_comp := hact
  unit := hunit
  assoc := by
    let k : pullback (a ≫ g) g ⟶ pullback (pullback.snd (a ≫ g) g ≫ g) g :=
      pullback.lift (𝟙 _) (pullback.snd (a ≫ g) g) (by simp)
    have hk : Surjective k :=
      surjective_of_universallyInjective (pullback.snd (a ≫ g) g ≫ g) (pullback.lift_fst _ _ _)
    refine hom_ext_of_surjective k a (by simp [hact]) ?_
    have h₁ : k ≫ pullback.lift (f := a ≫ g) (g := g)
        (pullback.fst (pullback.snd (a ≫ g) g ≫ g) g ≫ act)
        (pullback.snd (pullback.snd (a ≫ g) g ≫ g) g) (by simp [reassoc_of% hact]) =
        act ≫ diag g a := by
      apply pullback.hom_ext <;> simp [k, hact]
    have h₂ : k ≫ pullback.lift (f := a ≫ g) (g := g)
        (pullback.fst (pullback.snd (a ≫ g) g ≫ g) g ≫ pullback.fst (a ≫ g) g)
        (pullback.snd (pullback.snd (a ≫ g) g ≫ g) g) (by simp) = 𝟙 _ := by
      apply pullback.hom_ext <;> simp [k]
    rw [reassoc_of% h₁, reassoc_of% h₂, hunit, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
lemma existsUnique_act [UniversallyInjective g] [Etale a] :
    ∃! act : pullback (a ≫ g) g ⟶ X',
      act ≫ a = pullback.snd (a ≫ g) g ∧ diag g a ≫ act = 𝟙 X' :=
  have := (diag_universallyInjective_universallySubmersive (g := g) (a := a)).1
  have := (diag_universallyInjective_universallySubmersive (g := g) (a := a)).2
  have hφ : 𝟙 X' ≫ a = diag g a ≫ pullback.snd (a ≫ g) g := by simp
  existsUnique_hom_of_kernelPair (diag g a) (pullback.snd (a ≫ g) g) a (𝟙 X') hφ
    (kernelPair_condition_of_universallyInjective _ _ a _ hφ)

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.4.10, proof: if `g` is radicial, every étale `S'`-scheme carries a descent datum relative
to `g` (it is unique by `DescentDatum.act_eq_of_universallyInjective`). The action is the
unique `S'`-morphism `X' ×_S S' ⟶ X'` restricting to the identity along the diagonal section,
which exists by the full faithfulness IX.4.10 along that section. -/
noncomputable def ofUniversallyInjective [UniversallyInjective g] [Etale a] :
    DescentDatum g a :=
  let act := (existsUnique_act (g := g) (a := a)).exists.choose
  have hact : act ≫ a = pullback.snd (a ≫ g) g :=
    (existsUnique_act (g := g) (a := a)).exists.choose_spec.1
  have hunit : diag g a ≫ act = 𝟙 X' := (existsUnique_act (g := g) (a := a)).exists.choose_spec.2
  ofAct act hact hunit

end DescentDatum

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.4.10, proof: if `g` is radicial and every descent datum on an étale `S'`-scheme is
effective, base change of étale schemes along `g` is essentially surjective. -/
theorem essSurj_pullback_etale_of_isEffective [UniversallyInjective g]
    (H : ∀ ⦃X' : Scheme.{u}⦄ (a : X' ⟶ S') [Etale a] (D : DescentDatum g a),
      D.IsEffective @Etale) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).EssSurj where
  mem_essImage A := by
    obtain ⟨X, b, v, hb, hv, -⟩ := H A.hom (.ofUniversallyInjective (g := g) (a := A.hom))
    refine ⟨MorphismProperty.Over.mk ⊤ b hb, ⟨MorphismProperty.Over.isoMk hv.isoPullback.symm ?_⟩⟩
    exact hv.isoPullback_inv_snd

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.4.10, structure of the proof: for `g` radicial and universally submersive, base change of
étale schemes is an equivalence as soon as every descent datum on an étale `S'`-scheme is
effective (which SGA deduces from IX.4.7). -/
theorem isEquivalence_pullback_etale_of_isEffective [UniversallyInjective g]
    [UniversallySubmersive g]
    (H : ∀ ⦃X' : Scheme.{u}⦄ (a : X' ⟶ S') [Etale a] (D : DescentDatum g a),
      D.IsEffective @Etale) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).IsEquivalence :=
  have := essSurj_pullback_etale_of_isEffective H
  have := (fullyFaithfulPullbackEtale g).full
  have := (fullyFaithfulPullbackEtale g).faithful
  { }

/-- Effectiveness for open subschemes: along a universally submersive `g`, every descent datum
on an open subscheme `U'` of `S'` is effective, the descended object being an open subscheme of
`S` (namely `g(U')`). This is a special case of IX.4.1 and IX.4.7–IX.4.9, valid for any
universally submersive `g`. -/
theorem DescentDatum.isEffective_of_opens [UniversallySubmersive g] (U' : S'.Opens)
    (D : DescentDatum g U'.ι) : D.IsEffective @IsOpenImmersion := by
  -- `U'` is saturated for the equivalence relation defined by `g`
  have key (w : ↥(pullback g g)) (hw : pullback.fst g g w ∈ U') : pullback.snd g g w ∈ U' := by
    obtain ⟨u, hu⟩ : pullback.fst g g w ∈ Set.range U'.ι := by rwa [Scheme.Opens.range_ι]
    obtain ⟨e, he₁, he₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := U'.ι ≫ g) (g := g)
      u (pullback.snd g g w) (by
        rw [Scheme.Hom.comp_apply, hu, ← Scheme.Hom.comp_apply, pullback.condition,
          Scheme.Hom.comp_apply])
    have : pullback.snd g g w ∈ Set.range U'.ι :=
      ⟨D.act e, by rw [← Scheme.Hom.comp_apply, D.act_comp, he₂]⟩
    simpa using this
  have hsat : pullback.fst g g ⁻¹ᵁ U' = pullback.snd g g ⁻¹ᵁ U' := by
    refine le_antisymm (fun w hw ↦ key w hw) (fun w hw ↦ ?_)
    have := key ((pullbackSymmetry g g).hom w) (by
      rwa [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst])
    rwa [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_snd] at this
  obtain ⟨U, hU, -⟩ := exists_unique_opens_preimage_eq g U' hsat
  subst hU
  refine ⟨U, U.ι, g ∣_ U, inferInstance, isPullback_morphismRestrict g U, ?_⟩
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    reassoc_of% D.act_comp, pullback_fst_comp_comp]

variable (g) in
/-- VI / IX.4: `g` is an *effective descent morphism* for the fibred category of schemes whose
structure morphism satisfies `P`: it is a descent morphism (IX.3.3) and every descent datum
on a `P`-scheme over `S'` is effective. -/
def IsEffectiveDescentMorphism (P : MorphismProperty Scheme.{u}) : Prop :=
  IsDescentMorphism P g ∧
    ∀ ⦃X' : Scheme.{u}⦄ (a : X' ⟶ S') (D : DescentDatum g a), P a → D.IsEffective P

lemma IsDescentMorphism.of_le {P Q : MorphismProperty Scheme.{u}} (hPQ : P ≤ Q)
    (h : IsDescentMorphism Q g) : IsDescentMorphism P g :=
  fun _ _ p q hp hq ↦ h p q (hPQ _ hp) (hPQ _ hq)

/-- IX.3.3 for any subcategory of étale schemes: a universally submersive morphism is a descent
morphism for it. -/
lemma isDescentMorphism_of_le_etale {P : MorphismProperty Scheme.{u}} (hP : P ≤ @Etale)
    [UniversallySubmersive g] : IsDescentMorphism P g :=
  (isDescentMorphism_etale g).of_le hP

/-- IX.4.1, proof: when `P` descends along `g`, a descent datum on a `P`-scheme is effective for
`P` as soon as it is effective in the fibred category of all arrows ("it suffices to make sure
of the effectiveness … for the fibred category of arrows of `Sch`"). -/
lemma DescentDatum.IsEffective.of_top {P Q : MorphismProperty Scheme.{u}} [P.DescendsAlong Q]
    (hg : Q g) (D : DescentDatum g a) (h : D.IsEffective ⊤) (ha : P a) : D.IsEffective P := by
  obtain ⟨X, b, v, -, hv, hact⟩ := h
  exact ⟨X, b, v, of_isPullback_of_descendsAlong hv.flip hg ha, hv, hact⟩

/-! ### The fibred categories of §4 -/

/-- The fibred category of IX.4.1 and IX.4.7–IX.4.9: étale, separated, of finite type (finite
type means locally of finite type, which étale morphisms are, and quasi-compact). -/
def etaleSeparatedFiniteType : MorphismProperty Scheme.{u} :=
  @Etale ⊓ @IsSeparated ⊓ @QuasiCompact

/-- Étale morphisms of finite presentation (IX.4.4–IX.4.6). -/
def etaleFinitePresentation : MorphismProperty Scheme.{u} :=
  @Etale ⊓ @QuasiCompact ⊓ @QuasiSeparated

set_option backward.isDefEq.respectTransparency.types false in
instance : etaleSeparatedFiniteType.{u}.IsStableUnderBaseChange := by
  unfold etaleSeparatedFiniteType
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance : etaleFinitePresentation.{u}.IsStableUnderBaseChange := by
  unfold etaleFinitePresentation
  infer_instance

lemma etaleSeparatedFiniteType_le_etale : etaleSeparatedFiniteType.{u} ≤ @Etale :=
  fun _ _ _ h ↦ h.1.1

lemma etaleCovering_le_etale : etaleCovering.{u} ≤ @Etale :=
  fun _ _ _ h ↦ h.2

/-- IX.4.1, part of the proof: an `S`-scheme is étale, separated and of finite type as soon as
its base change along a faithfully flat quasi-compact morphism is. -/
instance etaleSeparatedFiniteType_descendsAlong :
    etaleSeparatedFiniteType.{u}.DescendsAlong
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  have h₁ : MorphismProperty.DescendsAlong @Etale (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    inferInstance
  have h₂ : MorphismProperty.DescendsAlong @IsSeparated (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    DescendsAlong.of_le (Q := @UniversallySubmersive) fun _ _ f ⟨⟨h₁, h₂⟩, h₃⟩ ↦
      (inferInstance : UniversallySubmersive f)
  have h₃ : MorphismProperty.DescendsAlong @QuasiCompact (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    have := quasiCompact_descendsAlong.{u}
    DescendsAlong.of_le (Q := @Surjective ⊓ @QuasiCompact) fun _ _ _ ⟨⟨h₁, _⟩, h₃⟩ ↦ ⟨h₁, h₃⟩
  exact ⟨fun h hf hfst ↦ ⟨⟨h₁.of_isPullback h hf hfst.1.1, h₂.of_isPullback h hf hfst.1.2⟩,
    h₃.of_isPullback h hf hfst.2⟩⟩

/-! ### IX.4.1 -/

/-- IX.4.1, descent half: a faithfully flat quasi-compact morphism is a descent morphism for
étale, separated schemes of finite type. -/
theorem isDescentMorphism_of_flat [Flat g] [QuasiCompact g] [Surjective g] :
    IsDescentMorphism etaleSeparatedFiniteType g :=
  isDescentMorphism_of_le_etale etaleSeparatedFiniteType_le_etale

/-- IX.4.1, reduction in the proof: along a faithfully flat quasi-compact `g`, a descent datum on
an étale separated `S'`-scheme of finite type is effective as soon as it is effective in the
fibred category of all schemes. -/
theorem DescentDatum.isEffective_of_flat [Flat g] [QuasiCompact g] [Surjective g]
    (D : DescentDatum g a) (ha : etaleSeparatedFiniteType a) (h : D.IsEffective ⊤) :
    D.IsEffective etaleSeparatedFiniteType := by
  obtain ⟨X, b, v, -, hv, hact⟩ := h
  exact ⟨X, b, v, etaleSeparatedFiniteType_descendsAlong.of_isPullback hv.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ ha, hv, hact⟩

/-! ### IX.4.2–IX.4.6: reductions -/

/-- The morphism `Spec 𝒪̂_{S,x} ⟶ S` from the spectrum of the completed local ring. -/
noncomputable def fromSpecCompletedStalk (S : Scheme.{u}) (x : S) :
    Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk x))
      (S.presheaf.stalk x))) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk x)
    (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk x)) (S.presheaf.stalk x)))) ≫
    S.fromSpecStalk x

/-- IX.4.6 (statement only, as in SGA): under the hypotheses of IX.4.4, with `S` locally noetherian
and `X'` separated over `S'`, a descent datum is effective iff it is effective after base change to
every spectrum of a complete noetherian local ring with algebraically closed residue field.

Proved in `SGA.SGA1.ExposeIX.StrictlyLocalDescent` with *separably* closed residue fields
(`DescentDatum.isEffective_iff_forall_isSepClosed`, which suffices for étale descent), and in this
form when the residue fields of `S` are perfect (`DescentDatum.isEffective_iff_forall_isAlgClosed`).
The general case needs flat local extensions of complete local rings realizing purely inseparable
residue field extensions (EGA 0_III 10.3.1). -/
def IsEffectiveIffStrictlyLocalStatement : Prop :=
  ∀ ⦃S' S X' : Scheme.{u}⦄ (g : S' ⟶ S) [UniversallySubmersive g]
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g] [IsLocallyNoetherian S]
    (a : X' ⟶ S') [IsSeparated a] (D : DescentDatum g a), etaleFinitePresentation a →
      (D.IsEffective etaleFinitePresentation ↔
        ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
          [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
          [IsAlgClosed (IsLocalRing.ResidueField R)] (t : Spec (.of R) ⟶ S),
          (D.baseChange t).IsEffective etaleFinitePresentation)

/-! ### IX.4.7–IX.4.9 and IX.4.12: effective descent morphisms -/

/-- IX.4.7, descent half: a finite surjective morphism is a descent morphism for étale schemes
(it is universally closed and surjective, hence universally submersive). -/
theorem isDescentMorphism_of_isFinite [IsFinite g] [Surjective g] :
    IsDescentMorphism etaleSeparatedFiniteType g :=
  isDescentMorphism_of_le_etale etaleSeparatedFiniteType_le_etale

/-- IX.4.9 (statement only): over a locally noetherian `S`, a surjective universally open
morphism of finite type is an effective descent morphism for étale, separated schemes of
finite type. Proved in `SGA.SGA1.ExposeIX.UniversallyOpenDescent`
(`effectiveDescentOfUniversallyOpen`) from the existence of quasi-sections of universally open
morphisms (`QuasiSectionStatement`, EGA IV 14.5.4), which is the one step of SGA's proof not
formalized. -/
def EffectiveDescentOfUniversallyOpenStatement : Prop :=
  ∀ ⦃S' S : Scheme.{u}⦄ (g : S' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType g]
    [QuasiCompact g] [Surjective g] [UniversallyOpen g],
    IsEffectiveDescentMorphism g etaleSeparatedFiniteType.{u}

/-- IX.4.9, descent half: a surjective universally open morphism is a descent morphism for étale
schemes. (For IX.4.8, where `g` is assumed universally submersive, use
`isDescentMorphism_of_le_etale`.) -/
theorem isDescentMorphism_of_universallyOpen [UniversallyOpen g] [Surjective g] :
    IsDescentMorphism etaleSeparatedFiniteType g :=
  isDescentMorphism_of_le_etale etaleSeparatedFiniteType_le_etale

/-- IX.4.9, last step of the proof ("the statement is trivial"): a morphism with a section is an
effective descent morphism for any class of étale morphisms stable under base change. (Such a
morphism is universally submersive, so IX.3.3 gives the descent half.) -/
theorem isEffectiveDescentMorphism_of_section {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] (hP : P ≤ @Etale) {σ : S ⟶ S'} (hσ : σ ≫ g = 𝟙 S) :
    IsEffectiveDescentMorphism g P :=
  have := UniversallySubmersive.of_section g hσ
  ⟨isDescentMorphism_of_le_etale hP, fun _ _ D ha ↦ D.isEffective_of_section hσ P ha⟩

/-- IX.4.12 (statement): a proper surjective morphism of finite presentation is an effective
descent morphism for étale coverings. Proved over a locally noetherian base in
`SGA.SGA1.ExposeIX.ProperEffectiveDescent` (`isEffectiveDescentMorphism_of_isProper`); the
general case needs the reduction to a noetherian base (EGA IV 8). -/
def EffectiveDescentOfProperStatement : Prop :=
  ∀ ⦃S' S : Scheme.{u}⦄ (g : S' ⟶ S) [IsProper g] [Surjective g]
    [LocallyOfFinitePresentation g], IsEffectiveDescentMorphism g etaleCovering.{u}

/-- IX.4.12, descent half: a proper surjective morphism is a descent morphism for étale
coverings (IX.2.2 and IX.3.3). -/
theorem isDescentMorphism_of_isProper [IsProper g] [Surjective g] :
    IsDescentMorphism etaleCovering g :=
  isDescentMorphism_of_le_etale etaleCovering_le_etale

/-! ### IX.4.10 and IX.4.11: topological invariance of the étale site -/

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.4.10, essential surjectivity for open subschemes: along a radicial universally submersive
`g` (a universal homeomorphism), every open subscheme `U'` of `S'` is the base change of an open
subscheme of `S`, namely of its image. -/
theorem mem_essImage_pullback_etale_of_opens [UniversallyInjective g] [UniversallySubmersive g]
    (U' : S'.Opens) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).essImage
      (MorphismProperty.Over.mk ⊤ U'.ι inferInstance) := by
  have hsat : g ⁻¹' (g '' U') = U' := Set.preimage_image_eq _ g.injective
  let U : S.Opens := ⟨g '' U', by
    rw [← (Scheme.Hom.isQuotientMap g).isOpen_preimage, hsat]
    exact U'.isOpen⟩
  have hU : g ⁻¹ᵁ U = U' := SetLike.coe_injective hsat
  let e : pullback U.ι g ≅ U' := pullbackSymmetry U.ι g ≪≫ pullbackRestrictIsoRestrict g U ≪≫
    S'.isoOfEq hU
  refine ⟨MorphismProperty.Over.mk ⊤ U.ι inferInstance,
    ⟨MorphismProperty.Over.isoMk e ?_⟩⟩
  change e.hom ≫ U'.ι = pullback.snd U.ι g
  simp only [e, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
    pullbackRestrictIsoRestrict_hom_ι, pullbackSymmetry_hom_comp_fst]

end SGA.SGA1.ExposeIX
