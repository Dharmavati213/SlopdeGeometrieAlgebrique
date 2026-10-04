/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier
import SGA.Foundations.Etale.TorsorPullback
import SGA.Foundations.Etale.TorsorPushforward
import SGA.Foundations.Etale.TorsorTwist
import SGA.Foundations.EtaleStalkBaseChange
import SGA.Foundations.EtaleStalkProper
import SGA.Foundations.EtaleStalkTorsor
import SGA.SGA1.ExposeXIII.EtaleRestriction

/-!
# SGA 1, Exposé XIII, §1: cohomological properness

Let `f : X ⟶ Y` be a morphism of `S`-schemes. A sheaf of sets `F` on the étale site of `X` is
*cohomologically proper relative to `S`* in dimension `≤ -1` (resp. `≤ 0`) if for every
`S`-scheme `S'`, with `Y' = Y ×_S S'` and `X' = X ×_Y Y'`, the base change morphism
`g^* f_* F ⟶ f'_* h^* F` is injective (resp. bijective) (XIII 1.1, 1.2). This file makes
these definitions with the base change morphism `Scheme.etaleBaseChangeMap` of
`SGA.Foundations.Etale.BaseChange`, and proves the formal properties of §1 for sheaves of
sets: independence of the base (`of_comp_base`), locality on `Y` for the étale topology and
stability under base change (1.5 c)), composition and cancellation (1.6), exact diagrams
(1.13 1)). It proves XIII 1.4 in dimension `≤ -1` (the injectivity half of the proper base
change theorem) for every universally closed `f`
(`isCohomologicallyProperLENegOne_of_universallyClosed`, from
`AlgebraicGeometry.Scheme.mono_etaleBaseChangeMap_of_universallyClosed`), and with it 1.8 and 1.9
in dimension `≤ -1` unconditionally (`IsCohomologicallyProperLENegOne.comp_of_universallyClosed`,
`isCohomologicallyProperLENegOne_pushforward_iff_of_isIntegralHom`). In dimension `≤ 0`, 1.8 and
1.9 are deduced from the proper and integral base change theorems (SGA 4 XII 5.1, VIII 5.6),
which are recorded as statements (`ProperBaseChangeStatement`, `IntegralBaseChangeStatement`).
For `f` finite, the base change theorem (SGA 4 VIII 5.6 for finite morphisms) is proved in
`SGA.Foundations.EtaleStalkBaseChange`, and 1.9 holds unconditionally
(`isCohomologicallyProperLEZero_pushforward_iff_of_isFinite`). The local triviality of torsors
along integral morphisms (SGA 4 VIII 5.8) is proved in `SGA.Foundations.EtaleStalkTorsor`
(`isLocallyTrivialAlong_of_isIntegralHom`).

SGA defines cohomological properness for stacks (1.1) and for sheaves of groups through their
stacks of torsors (1.3). Inverse images of stacks (stackification) are not available; for sheaves
of groups we use the characterization (ii) of XIII 1.3.1 as the definition
(`IsCohomologicallyProperLENegOneGroup`, `IsCohomologicallyProperLEZeroGroup`: the twisted groups
`^P F₁` are cohomologically proper as sheaves of sets, and in dimension `≤ 0` the base change
morphism `a₁` on `R¹` is injective, stated on stalks with the inverse images of torsors of
`SGA.Foundations.Etale.TorsorPullback`). We prove 1.5 a) (a sheaf of groups which is
cohomologically proper is so as a sheaf of sets), 1.4 in dimension `≤ -1` for sheaves of groups
(`isCohomologicallyProperLENegOneGroup_of_universallyClosed`), 1.7 in dimension `≤ -1`
(`IsCohomologicallyProperLENegOneGroup.pushforward`, through `^Q(f_* F) ≅ f_*(^P F)` of
`SGA.Foundations.Etale.TorsorPushforward`) and the groups part of 1.9 in dimension `≤ -1`
(`isCohomologicallyProperLENegOneGroup_pushforward_iff_of_isIntegralHom`, which uses SGA 4 VIII
5.8). Not formalized: 1.7 and 1.9 in dimension `≤ 0` (these need the compatibility of `Q ↦ P`
with base change), dimension `≤ 1` for sheaves of groups, 1.13 2)–3) (quotient sheaves `Q/F`),
and 1.10–1.17 about exact diagrams of stacks and specialization maps, except 1.13 1).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry
open Scheme (etalePullback etalePushforward etaleAdjunction etalePullbackComp etalePushforwardComp
  etaleBaseChangeMap etaleBaseChangeMap_comp_app etaleBaseChangeMap_comp_horiz_app
  isIso_etaleBaseChangeMap_of_etale isIso_of_forall_isIso_etalePullback
  mono_of_forall_mono_etalePullback)

-- See the comment in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA1.ExposeXIII

variable {S X Y Z : Scheme.{u}}

section Definitions

variable (s : Y ⟶ S) (f : X ⟶ Y) (F : Sheaf X.smallEtaleTopology (Type u))

/-- XIII 1.2: a sheaf of sets `F` on `X` is cohomologically proper for `f : X ⟶ Y` relative to
`S` (with `s : Y ⟶ S`) in dimension `≤ -1` if for every `t : S' ⟶ S` and all cartesian squares
`Y' = Y ×_S S'`, `X' = X ×_Y Y'` (1.0.1), the base change morphism `g^* f_* F ⟶ f'_* h^* F` is a
monomorphism. (SGA defines this as the cohomological properness of the associated stack in
discrete categories in dimension `≤ 0`, and notes that it amounts to this condition.) -/
def IsCohomologicallyProperLENegOne : Prop :=
  ∀ ⦃S' Y' X' : Scheme.{u}⦄ (t : S' ⟶ S) (s' : Y' ⟶ S') (g : Y' ⟶ Y) (h : X' ⟶ X)
    (f' : X' ⟶ Y'), IsPullback g s' s t → ∀ (hX : IsPullback h f' f g),
      Mono ((etaleBaseChangeMap hX.w).app F)

/-- XIII 1.2: a sheaf of sets `F` on `X` is cohomologically proper for `f : X ⟶ Y` relative to
`S` in dimension `≤ 0` if for every `S`-scheme `S'` the base change morphism
`g^* f_* F ⟶ f'_* h^* F` is an isomorphism, i.e. the formation of `f_* F` commutes with every
change of base `S' ⟶ S`. -/
def IsCohomologicallyProperLEZero : Prop :=
  ∀ ⦃S' Y' X' : Scheme.{u}⦄ (t : S' ⟶ S) (s' : Y' ⟶ S') (g : Y' ⟶ Y) (h : X' ⟶ X)
    (f' : X' ⟶ Y'), IsPullback g s' s t → ∀ (hX : IsPullback h f' f g),
      IsIso ((etaleBaseChangeMap hX.w).app F)

variable {s f F}

lemma IsCohomologicallyProperLEZero.leNegOne (hF : IsCohomologicallyProperLEZero s f F) :
    IsCohomologicallyProperLENegOne s f F := by
  intro S' Y' X' t s' g h f' hY hX
  have := hF t s' g h f' hY hX
  infer_instance

/-- A cartesian square over `S₀` which is the base change of `S ⟶ S₀` factors through a
cartesian square over `S`. -/
lemma exists_isPullback_of_comp {S₀ S₀' Y' : Scheme.{u}} (s₀ : S ⟶ S₀) (t₀ : S₀' ⟶ S₀)
    (s' : Y' ⟶ S₀') (g : Y' ⟶ Y) (hY : IsPullback g s' (s ≫ s₀) t₀) :
    ∃ (S' : Scheme.{u}) (t : S' ⟶ S) (s'' : Y' ⟶ S'), IsPullback g s'' s t := by
  refine ⟨pullback s₀ t₀, pullback.fst _ _, pullback.lift (g ≫ s) s' (by simpa using hY.w), ?_⟩
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback s₀ t₀)
  simpa using hY

/-- Cohomological properness relative to `S` implies cohomological properness relative to any
`S₀` over which `S` lies. In particular properness relative to `Y` (the case `S = Y`, called
simply "cohomologically proper" in XIII 1.1) is the strongest form. -/
lemma IsCohomologicallyProperLENegOne.of_comp_base {S₀ : Scheme.{u}} (s₀ : S ⟶ S₀)
    (hF : IsCohomologicallyProperLENegOne s f F) :
    IsCohomologicallyProperLENegOne (s ≫ s₀) f F := by
  intro S₀' Y' X' t₀ s' g h f' hY hX
  obtain ⟨S', t, s'', hY'⟩ := exists_isPullback_of_comp s₀ t₀ s' g hY
  exact hF t s'' g h f' hY' hX

lemma IsCohomologicallyProperLEZero.of_comp_base {S₀ : Scheme.{u}} (s₀ : S ⟶ S₀)
    (hF : IsCohomologicallyProperLEZero s f F) :
    IsCohomologicallyProperLEZero (s ≫ s₀) f F := by
  intro S₀' Y' X' t₀ s' g h f' hY hX
  obtain ⟨S', t, s'', hY'⟩ := exists_isPullback_of_comp s₀ t₀ s' g hY
  exact hF t s'' g h f' hY' hX

lemma IsCohomologicallyProperLENegOne.of_id (hF : IsCohomologicallyProperLENegOne (𝟙 Y) f F)
    (s : Y ⟶ S) : IsCohomologicallyProperLENegOne s f F := by
  simpa using hF.of_comp_base s

lemma IsCohomologicallyProperLEZero.of_id (hF : IsCohomologicallyProperLEZero (𝟙 Y) f F)
    (s : Y ⟶ S) : IsCohomologicallyProperLEZero s f F := by
  simpa using hF.of_comp_base s

end Definitions

section Locality

/-! ### XIII 1.5 c): cohomological properness is local on `Y` -/

lemma isIso_baseChangeMap_congr {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {h₁ h₂ : X' ⟶ X} {g₁ g₂ : Y' ⟶ Y} (hh : h₁ = h₂) (hg : g₁ = g₂)
    (w₁ : h₁ ≫ f = f' ≫ g₁) (w₂ : h₂ ≫ f = f' ≫ g₂) (F : Sheaf X.smallEtaleTopology (Type u)) :
    IsIso ((etaleBaseChangeMap w₁).app F) ↔ IsIso ((etaleBaseChangeMap w₂).app F) := by
  subst hh hg
  rfl

lemma mono_baseChangeMap_congr {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {h₁ h₂ : X' ⟶ X} {g₁ g₂ : Y' ⟶ Y} (hh : h₁ = h₂) (hg : g₁ = g₂)
    (w₁ : h₁ ≫ f = f' ≫ g₁) (w₂ : h₂ ≫ f = f' ≫ g₂) (F : Sheaf X.smallEtaleTopology (Type u)) :
    Mono ((etaleBaseChangeMap w₁).app F) ↔ Mono ((etaleBaseChangeMap w₂).app F) := by
  subst hh hg
  rfl

section Cancel

variable {C : Type*} [Category* C] {P Q R T U : C} (a : P ⟶ Q) (i : Q ⟶ R) (j : R ⟶ T)
  (b : T ⟶ U) [IsIso a] [IsIso j] [IsIso b]

lemma isIso_comp_four_iff : IsIso (a ≫ i ≫ j ≫ b) ↔ IsIso i := by
  refine ⟨fun H ↦ ?_, fun _ ↦ inferInstance⟩
  have : IsIso ((a ≫ i ≫ j) ≫ b) := by simpa only [Category.assoc] using H
  have : IsIso (a ≫ i ≫ j) := IsIso.of_isIso_comp_right _ b
  have : IsIso (i ≫ j) := IsIso.of_isIso_comp_left a _
  exact IsIso.of_isIso_comp_right i j

lemma mono_comp_four_iff : Mono (a ≫ i ≫ j ≫ b) ↔ Mono i := by
  refine ⟨fun H ↦ ?_, fun _ ↦ inferInstance⟩
  have : Mono ((a ≫ i) ≫ j ≫ b) := by simpa only [Category.assoc] using H
  have : Mono (a ≫ i) := mono_of_mono _ (j ≫ b)
  have : Mono (inv a ≫ a ≫ i) := mono_comp _ _
  simpa using this

omit [IsIso j] in
lemma isIso_comp_four_iff' {j' : Q ⟶ R} [IsIso j'] {i' : R ⟶ T} :
    IsIso (a ≫ j' ≫ i' ≫ b) ↔ IsIso i' := by
  refine ⟨fun H ↦ ?_, fun _ ↦ inferInstance⟩
  have : IsIso ((a ≫ j') ≫ i' ≫ b) := by simpa only [Category.assoc] using H
  have : IsIso (i' ≫ b) := IsIso.of_isIso_comp_left (a ≫ j') _
  exact IsIso.of_isIso_comp_right i' b

omit [IsIso j] in
lemma mono_comp_four_iff' {j' : Q ⟶ R} [IsIso j'] {i' : R ⟶ T} :
    Mono (a ≫ j' ≫ i' ≫ b) ↔ Mono i' := by
  refine ⟨fun H ↦ ?_, fun _ ↦ inferInstance⟩
  have : Mono (inv (a ≫ j') ≫ (a ≫ j') ≫ i' ≫ b) := by
    have : Mono ((a ≫ j') ≫ i' ≫ b) := by simpa only [Category.assoc] using H
    exact mono_comp _ _
  have : Mono (i' ≫ b) := by simpa using this
  exact mono_of_mono i' b

end Cancel

section Paste

variable {X' Y' X'' Y'' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}
  {k : Y'' ⟶ Y'} {m : X'' ⟶ X'} {f'' : X'' ⟶ Y''}

/-- Pasting a cartesian square along an étale `k` on the side of `Y'`: the base change morphism
of the composite square is an isomorphism iff `k^*` of that of the first square is. -/
lemma isIso_baseChangeMap_comp_etale_iff [Etale k] (hm : IsPullback m f'' f' k)
    (w₁ : h ≫ f = f' ≫ g) (w : (m ≫ h) ≫ f = f'' ≫ k ≫ g)
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    IsIso ((etaleBaseChangeMap w).app F) ↔
      IsIso ((etalePullback k).map ((etaleBaseChangeMap w₁).app F)) := by
  rw [etaleBaseChangeMap_comp_horiz_app w₁ hm.w w]
  have := isIso_etaleBaseChangeMap_of_etale k hm ((etalePullback h).obj F)
  exact isIso_comp_four_iff _ _ _ _

lemma mono_baseChangeMap_comp_etale_iff [Etale k] (hm : IsPullback m f'' f' k)
    (w₁ : h ≫ f = f' ≫ g) (w : (m ≫ h) ≫ f = f'' ≫ k ≫ g)
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    Mono ((etaleBaseChangeMap w).app F) ↔
      Mono ((etalePullback k).map ((etaleBaseChangeMap w₁).app F)) := by
  rw [etaleBaseChangeMap_comp_horiz_app w₁ hm.w w]
  have := isIso_etaleBaseChangeMap_of_etale k hm ((etalePullback h).obj F)
  exact mono_comp_four_iff _ _ _ _

/-- Pasting along an étale `g` on the side of `Y`: the base change morphism of the composite
square is an isomorphism iff that of the second square (for the inverse image of `F`) is. -/
lemma isIso_baseChangeMap_etale_comp_iff [Etale g] (hX : IsPullback h f' f g)
    (w₂ : m ≫ f' = f'' ≫ k) (w : (m ≫ h) ≫ f = f'' ≫ k ≫ g)
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    IsIso ((etaleBaseChangeMap w).app F) ↔
      IsIso ((etaleBaseChangeMap w₂).app ((etalePullback h).obj F)) := by
  rw [etaleBaseChangeMap_comp_horiz_app hX.w w₂ w]
  have := isIso_etaleBaseChangeMap_of_etale g hX F
  exact isIso_comp_four_iff' _ _

lemma mono_baseChangeMap_etale_comp_iff [Etale g] (hX : IsPullback h f' f g)
    (w₂ : m ≫ f' = f'' ≫ k) (w : (m ≫ h) ≫ f = f'' ≫ k ≫ g)
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    Mono ((etaleBaseChangeMap w).app F) ↔
      Mono ((etaleBaseChangeMap w₂).app ((etalePullback h).obj F)) := by
  rw [etaleBaseChangeMap_comp_horiz_app hX.w w₂ w]
  have := isIso_etaleBaseChangeMap_of_etale g hX F
  exact mono_comp_four_iff' _ _

end Paste

section Local

variable {s : Y ⟶ S} {f : X ⟶ Y} {F : Sheaf X.smallEtaleTopology (Type u)}
  {ι : Type*} {V : ι → Scheme.{u}} (e : ∀ i, V i ⟶ Y) [∀ i, Etale (e i)]

/-- XIII 1.5 c), first paragraph, dimension `≤ 0` for sheaves of sets: cohomological
properness is local on `Y` for the étale topology. For a jointly surjective family of étale
morphisms `e i : V i ⟶ Y`, `(F, f)` is cohomologically proper relative to `S` if and only if
each `(F|X ×_Y V i, X ×_Y V i ⟶ V i)` is. -/
theorem isCohomologicallyProperLEZero_iff_of_etale_cover (he : ∀ y : Y, ∃ i v, e i v = y) :
    IsCohomologicallyProperLEZero s f F ↔ ∀ i, IsCohomologicallyProperLEZero (e i ≫ s)
      (pullback.snd f (e i)) ((etalePullback (pullback.fst f (e i))).obj F) := by
  have hXi (i) := IsPullback.of_hasPullback f (e i)
  constructor
  · intro H i S' Y₁' X₁' t s₁' g₁ h₁' f₁' hY₁ hX₁
    have hY : IsPullback (pullback.fst s t) (pullback.snd s t) s t :=
      IsPullback.of_hasPullback s t
    let k : Y₁' ⟶ pullback s t := pullback.lift (g₁ ≫ e i) s₁' (by rw [Category.assoc, hY₁.w])
    have hkg : k ≫ pullback.fst s t = g₁ ≫ e i := pullback.lift_fst _ _ _
    have hks : k ≫ pullback.snd s t = s₁' := pullback.lift_snd _ _ _
    have hk : IsPullback g₁ k (e i) (pullback.fst s t) :=
      IsPullback.of_bot (by rw [hks]; exact hY₁) hkg.symm hY
    have : Etale k := MorphismProperty.of_isPullback hk inferInstance
    have hX := IsPullback.of_hasPullback f (pullback.fst s t)
    have hout : IsPullback (h₁' ≫ pullback.fst f (e i)) f₁' f (g₁ ≫ e i) :=
      hX₁.paste_horiz (hXi i)
    let m : X₁' ⟶ pullback f (pullback.fst s t) := hX.lift (h₁' ≫ pullback.fst f (e i))
      (f₁' ≫ k) (by rw [hout.w, Category.assoc, hkg])
    have hm₁ : m ≫ pullback.fst f (pullback.fst s t) = h₁' ≫ pullback.fst f (e i) :=
      hX.lift_fst _ _ _
    have hm₂ : m ≫ pullback.snd f (pullback.fst s t) = f₁' ≫ k := hX.lift_snd _ _ _
    have hm : IsPullback m f₁' (pullback.snd f (pullback.fst s t)) k :=
      IsPullback.of_right (by rw [hm₁, hkg]; exact hout) hm₂ hX
    have h₁ : IsIso ((etaleBaseChangeMap (hm.paste_horiz hX).w).app F) := by
      rw [isIso_baseChangeMap_comp_etale_iff hm hX.w]
      have := H t _ _ _ _ hY hX
      infer_instance
    rw [isIso_baseChangeMap_congr hm₁ hkg _ hout.w] at h₁
    exact (isIso_baseChangeMap_etale_comp_iff (hXi i) hX₁.w hout.w F).1 h₁
  · intro H S' Y' X' t s' g h f' hY hX
    have hk (i) := IsPullback.of_hasPullback (e i) g
    have : ∀ i, Etale (pullback.snd (e i) g) :=
      fun i ↦ MorphismProperty.of_isPullback (hk i) inferInstance
    apply isIso_of_forall_isIso_etalePullback (fun i ↦ pullback.snd (e i) g)
    · intro y
      obtain ⟨i, v, hv⟩ := he (g y)
      obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback v y hv
      exact ⟨i, z, hz⟩
    intro i
    have hm := IsPullback.of_hasPullback f' (pullback.snd (e i) g)
    rw [← isIso_baseChangeMap_comp_etale_iff hm hX.w (hm.paste_horiz hX).w F]
    have hout := hm.paste_horiz hX
    have hkg : pullback.snd (e i) g ≫ g = pullback.fst (e i) g ≫ e i := (hk i).w.symm
    let h' : pullback f' (pullback.snd (e i) g) ⟶ pullback f (e i) :=
      (hXi i).lift (pullback.fst _ _ ≫ h) (pullback.snd _ _ ≫ pullback.fst (e i) g)
        (by rw [hout.w, Category.assoc, hkg])
    have hh₁ : h' ≫ pullback.fst f (e i) = pullback.fst f' (pullback.snd (e i) g) ≫ h :=
      (hXi i).lift_fst _ _ _
    have hh₂ : h' ≫ pullback.snd f (e i) =
        pullback.snd f' (pullback.snd (e i) g) ≫ pullback.fst (e i) g :=
      (hXi i).lift_snd _ _ _
    have hX' : IsPullback h' (pullback.snd f' (pullback.snd (e i) g)) (pullback.snd f (e i))
        (pullback.fst (e i) g) :=
      IsPullback.of_right (by rw [hh₁, ← hkg]; exact hout) hh₂ (hXi i)
    rw [isIso_baseChangeMap_congr hh₁.symm hkg hout.w (hX'.paste_horiz (hXi i)).w,
      isIso_baseChangeMap_etale_comp_iff (hXi i) hX'.w]
    exact H i t _ _ _ _ ((hk i).paste_vert hY) hX'

/-- XIII 1.5 c), first paragraph, dimension `≤ -1` for sheaves of sets: cohomological
properness is local on `Y` for the étale topology. For a jointly surjective family of étale
morphisms `e i : V i ⟶ Y`, `(F, f)` is cohomologically proper relative to `S` if and only if
each `(F|X ×_Y V i, X ×_Y V i ⟶ V i)` is. -/
theorem isCohomologicallyProperLENegOne_iff_of_etale_cover (he : ∀ y : Y, ∃ i v, e i v = y) :
    IsCohomologicallyProperLENegOne s f F ↔ ∀ i, IsCohomologicallyProperLENegOne (e i ≫ s)
      (pullback.snd f (e i)) ((etalePullback (pullback.fst f (e i))).obj F) := by
  have hXi (i) := IsPullback.of_hasPullback f (e i)
  constructor
  · intro H i S' Y₁' X₁' t s₁' g₁ h₁' f₁' hY₁ hX₁
    have hY : IsPullback (pullback.fst s t) (pullback.snd s t) s t :=
      IsPullback.of_hasPullback s t
    let k : Y₁' ⟶ pullback s t := pullback.lift (g₁ ≫ e i) s₁' (by rw [Category.assoc, hY₁.w])
    have hkg : k ≫ pullback.fst s t = g₁ ≫ e i := pullback.lift_fst _ _ _
    have hks : k ≫ pullback.snd s t = s₁' := pullback.lift_snd _ _ _
    have hk : IsPullback g₁ k (e i) (pullback.fst s t) :=
      IsPullback.of_bot (by rw [hks]; exact hY₁) hkg.symm hY
    have : Etale k := MorphismProperty.of_isPullback hk inferInstance
    have hX := IsPullback.of_hasPullback f (pullback.fst s t)
    have hout : IsPullback (h₁' ≫ pullback.fst f (e i)) f₁' f (g₁ ≫ e i) :=
      hX₁.paste_horiz (hXi i)
    let m : X₁' ⟶ pullback f (pullback.fst s t) := hX.lift (h₁' ≫ pullback.fst f (e i))
      (f₁' ≫ k) (by rw [hout.w, Category.assoc, hkg])
    have hm₁ : m ≫ pullback.fst f (pullback.fst s t) = h₁' ≫ pullback.fst f (e i) :=
      hX.lift_fst _ _ _
    have hm₂ : m ≫ pullback.snd f (pullback.fst s t) = f₁' ≫ k := hX.lift_snd _ _ _
    have hm : IsPullback m f₁' (pullback.snd f (pullback.fst s t)) k :=
      IsPullback.of_right (by rw [hm₁, hkg]; exact hout) hm₂ hX
    have h₁ : Mono ((etaleBaseChangeMap (hm.paste_horiz hX).w).app F) := by
      rw [mono_baseChangeMap_comp_etale_iff hm hX.w]
      have := H t _ _ _ _ hY hX
      infer_instance
    rw [mono_baseChangeMap_congr hm₁ hkg _ hout.w] at h₁
    exact (mono_baseChangeMap_etale_comp_iff (hXi i) hX₁.w hout.w F).1 h₁
  · intro H S' Y' X' t s' g h f' hY hX
    have hk (i) := IsPullback.of_hasPullback (e i) g
    have : ∀ i, Etale (pullback.snd (e i) g) :=
      fun i ↦ MorphismProperty.of_isPullback (hk i) inferInstance
    apply mono_of_forall_mono_etalePullback (fun i ↦ pullback.snd (e i) g)
    · intro y
      obtain ⟨i, v, hv⟩ := he (g y)
      obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback v y hv
      exact ⟨i, z, hz⟩
    intro i
    have hm := IsPullback.of_hasPullback f' (pullback.snd (e i) g)
    rw [← mono_baseChangeMap_comp_etale_iff hm hX.w (hm.paste_horiz hX).w F]
    have hout := hm.paste_horiz hX
    have hkg : pullback.snd (e i) g ≫ g = pullback.fst (e i) g ≫ e i := (hk i).w.symm
    let h' : pullback f' (pullback.snd (e i) g) ⟶ pullback f (e i) :=
      (hXi i).lift (pullback.fst _ _ ≫ h) (pullback.snd _ _ ≫ pullback.fst (e i) g)
        (by rw [hout.w, Category.assoc, hkg])
    have hh₁ : h' ≫ pullback.fst f (e i) = pullback.fst f' (pullback.snd (e i) g) ≫ h :=
      (hXi i).lift_fst _ _ _
    have hh₂ : h' ≫ pullback.snd f (e i) =
        pullback.snd f' (pullback.snd (e i) g) ≫ pullback.fst (e i) g :=
      (hXi i).lift_snd _ _ _
    have hX' : IsPullback h' (pullback.snd f' (pullback.snd (e i) g)) (pullback.snd f (e i))
        (pullback.fst (e i) g) :=
      IsPullback.of_right (by rw [hh₁, ← hkg]; exact hout) hh₂ (hXi i)
    rw [mono_baseChangeMap_congr hh₁.symm hkg hout.w (hX'.paste_horiz (hXi i)).w,
      mono_baseChangeMap_etale_comp_iff (hXi i) hX'.w]
    exact H i t _ _ _ _ ((hk i).paste_vert hY) hX'

end Local

end Locality

section Composition

/-! ### XIII 1.6: composition -/

variable {sZ : Z ⟶ S} {f : X ⟶ Y} {g : Y ⟶ Z} {F : Sheaf X.smallEtaleTopology (Type u)}

/-- The diagram (XIII 1.6.1): a cartesian square for `f ≫ g` along `m : Z' ⟶ Z` factors
through `Y' = Y ×_Z Z'` into two cartesian squares. -/
lemma exists_isPullback_factor {X' Z' : Scheme.{u}} {m : Z' ⟶ Z} {h : X' ⟶ X}
    {f'' : X' ⟶ Z'} (hX : IsPullback h f'' (f ≫ g) m) :
    ∃ (f' : X' ⟶ pullback g m), IsPullback h f' f (pullback.fst g m) ∧
      f' ≫ pullback.snd g m = f'' := by
  refine ⟨pullback.lift (h ≫ f) f'' (by simpa using hX.w), ?_, by simp⟩
  exact IsPullback.of_bot (by simpa using hX) (by simp) (IsPullback.of_hasPullback g m)

/-- XIII 1.6 1), dimension `≤ -1` for sheaves of sets: if `(F, f)` and `(f_* F, g)` are
cohomologically proper relative to `S`, so is `(F, f ≫ g)`. -/
theorem IsCohomologicallyProperLENegOne.comp (hf : IsCohomologicallyProperLENegOne (g ≫ sZ) f F)
    (hg : IsCohomologicallyProperLENegOne sZ g ((etalePushforward f).obj F)) :
    IsCohomologicallyProperLENegOne sZ (f ≫ g) F := by
  intro S' Z' X' t s' m h f'' hZ hX
  obtain ⟨f', h₁, rfl⟩ := exists_isPullback_factor hX
  have hY := IsPullback.of_hasPullback g m
  have := hf t _ _ h f' (hY.paste_vert hZ) h₁
  have := hg t s' m _ _ hZ hY
  rw [etaleBaseChangeMap_comp_app h₁.w hY.w hX.w]
  infer_instance

/-- XIII 1.6 1), dimension `≤ 0` for sheaves of sets. -/
theorem IsCohomologicallyProperLEZero.comp (hf : IsCohomologicallyProperLEZero (g ≫ sZ) f F)
    (hg : IsCohomologicallyProperLEZero sZ g ((etalePushforward f).obj F)) :
    IsCohomologicallyProperLEZero sZ (f ≫ g) F := by
  intro S' Z' X' t s' m h f'' hZ hX
  obtain ⟨f', h₁, rfl⟩ := exists_isPullback_factor hX
  have hY := IsPullback.of_hasPullback g m
  have := hf t _ _ h f' (hY.paste_vert hZ) h₁
  have := hg t s' m _ _ hZ hY
  rw [etaleBaseChangeMap_comp_app h₁.w hY.w hX.w]
  infer_instance

/-- XIII 1.6 2), dimension `≤ -1` for sheaves of sets: if `(F, f ≫ g)` is cohomologically proper
relative to `S`, so is `(f_* F, g)`. (For stacks in discrete categories the extra hypothesis of
1.6 2) on `(Φ, f)` in dimension `≤ -1` is automatic.) -/
theorem IsCohomologicallyProperLENegOne.of_comp
    (hfg : IsCohomologicallyProperLENegOne sZ (f ≫ g) F) :
    IsCohomologicallyProperLENegOne sZ g ((etalePushforward f).obj F) := by
  intro S' Z' Y' t s' m k g' hZ hY
  have h₁ := IsPullback.of_hasPullback f k
  have H := hfg t s' m _ _ hZ (h₁.paste_vert hY)
  rw [etaleBaseChangeMap_comp_app h₁.w hY.w (h₁.paste_vert hY).w] at H
  set a := (etalePullback m).map ((etalePushforwardComp f g).hom.app F)
  set i := (etaleBaseChangeMap hY.w).app ((etalePushforward f).obj F)
  set j := (etalePushforward g').map ((etaleBaseChangeMap h₁.w).app F)
  set b := (etalePushforwardComp (pullback.snd f k) g').inv.app
    ((etalePullback (pullback.fst f k)).obj F)
  have : Mono ((a ≫ i) ≫ j ≫ b) := by rwa [Category.assoc]
  have : Mono (a ≫ i) := mono_of_mono _ (j ≫ b)
  have : Mono (inv a ≫ a ≫ i) := mono_comp _ _
  simpa using this

/-- XIII 1.6 2), dimension `≤ 0` for sheaves of sets: if `(F, f ≫ g)` is cohomologically proper
relative to `S` in dimension `≤ 0` and `(F, f)` in dimension `≤ -1`, then `(f_* F, g)` is
cohomologically proper relative to `S` in dimension `≤ 0`. -/
theorem IsCohomologicallyProperLEZero.of_comp
    (hfg : IsCohomologicallyProperLEZero sZ (f ≫ g) F)
    (hf : IsCohomologicallyProperLENegOne (g ≫ sZ) f F) :
    IsCohomologicallyProperLEZero sZ g ((etalePushforward f).obj F) := by
  intro S' Z' Y' t s' m k g' hZ hY
  have h₁ := IsPullback.of_hasPullback f k
  have H := hfg t s' m _ _ hZ (h₁.paste_vert hY)
  have := hf t _ _ _ _ (hY.paste_vert hZ) h₁
  rw [etaleBaseChangeMap_comp_app h₁.w hY.w (h₁.paste_vert hY).w] at H
  set a := (etalePullback m).map ((etalePushforwardComp f g).hom.app F)
  set i := (etaleBaseChangeMap hY.w).app ((etalePushforward f).obj F)
  set j := (etalePushforward g').map ((etaleBaseChangeMap h₁.w).app F)
  set b := (etalePushforwardComp (pullback.snd f k) g').inv.app
    ((etalePullback (pullback.fst f k)).obj F)
  have : IsIso (i ≫ j) := by
    have : IsIso ((a ≫ i ≫ j) ≫ b) := by simpa using H
    have : IsIso (a ≫ i ≫ j) := IsIso.of_isIso_comp_right _ b
    exact IsIso.of_isIso_comp_left a _
  have : IsSplitEpi j := ⟨⟨{ section_ := inv (i ≫ j) ≫ i, id := by simp }⟩⟩
  have : IsIso j := isIso_of_mono_of_isSplitEpi j
  exact IsIso.of_isIso_comp_right i j

end Composition

section BaseChange

/-! ### XIII 1.5 c): stability under base change -/

variable {s : Y ⟶ S} {f : X ⟶ Y} {F : Sheaf X.smallEtaleTopology (Type u)}

/-- XIII 1.5 c), second paragraph, for sheaves of sets: if `(F, f)` is cohomologically proper
relative to `S` in dimension `≤ 0`, then for every `S`-scheme `S'` the inverse image `h^* F` is
cohomologically proper for `f' : X' ⟶ Y'` relative to `S'` in dimension `≤ 0`. (SGA gives an
example showing that this fails in dimension `≤ -1`.) -/
theorem IsCohomologicallyProperLEZero.baseChange (hF : IsCohomologicallyProperLEZero s f F)
    {S' Y' X' : Scheme.{u}} {t : S' ⟶ S} {s' : Y' ⟶ S'} {g : Y' ⟶ Y} {h : X' ⟶ X}
    {f' : X' ⟶ Y'} (hY : IsPullback g s' s t) (hX : IsPullback h f' f g) :
    IsCohomologicallyProperLEZero s' f' ((etalePullback h).obj F) := by
  intro S'' Y'' X'' t₂ s'' g₂ h₂ f'' hY₂ hX₂
  have H := hF (t₂ ≫ t) s'' (g₂ ≫ g) (h₂ ≫ h) f'' (hY₂.paste_horiz hY) (hX₂.paste_horiz hX)
  have := hF t s' g h f' hY hX
  rw [etaleBaseChangeMap_comp_horiz_app hX.w hX₂.w (hX₂.paste_horiz hX).w] at H
  set a := (etalePullbackComp g₂ g).inv.app ((etalePushforward f).obj F)
  set i := (etalePullback g₂).map ((etaleBaseChangeMap hX.w).app F)
  set j := (etaleBaseChangeMap hX₂.w).app ((etalePullback h).obj F)
  set b := (etalePushforward f'').map ((etalePullbackComp h₂ h).hom.app F)
  have : IsIso ((a ≫ i ≫ j) ≫ b) := by simpa using H
  have : IsIso (a ≫ i ≫ j) := IsIso.of_isIso_comp_right _ b
  have : IsIso (i ≫ j) := IsIso.of_isIso_comp_left a _
  exact IsIso.of_isIso_comp_left i j

end BaseChange

section ProperAndIntegral

/-! ### XIII 1.4, 1.8, 1.9: proper and integral morphisms -/

/-- XIII 1.4 (statement only for an arbitrary base), case of sheaves of sets: for a proper morphism
`f : X ⟶ Y`, every sheaf of sets `F` on `X` is cohomologically proper for `f` in dimension `≤ 0`
(relative to `Y`). This is the proper base change theorem for `f_*` (SGA 4 XII 5.1, Giraud VII
2.2.2); only sections of étale sheaves are involved, no higher cohomology. Proved cases: the
injectivity half (dimension `≤ -1`) for every universally closed `f`
(`isCohomologicallyProperLENegOne_of_universallyClosed`), and the whole statement for every sheaf
of sets when `Y` is locally noetherian
(`isCohomologicallyProperLEZero_of_isProper_of_isLocallyNoetherian`, in
`SGA.SGA1.ExposeXIII.ProperBaseChangeNoetherian`, from Gabber's theorem). Open: an arbitrary `Y`,
which needs the reduction to a noetherian base (EGA IV 8 and constructible sheaves). -/
def ProperBaseChangeStatement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [IsProper f] (F : Sheaf X.smallEtaleTopology (Type u)),
    IsCohomologicallyProperLEZero (𝟙 Y) f F

/-- The base change theorem for integral morphisms (SGA 4 VIII 5.6), used in the proof of
XIII 1.9 (statement only): for `f` integral, the formation of `f_* F` commutes with every
change of base. Proved cases: `f` finite (`isCohomologicallyProperLEZero_of_isFinite`), and the
injectivity half (dimension `≤ -1`) for every integral `f`
(`isCohomologicallyProperLENegOne_of_universallyClosed`). The limit theorems used by SGA are
proved in degree `0`, in the generality needed, in `SGA.Foundations.Limits.EtaleSectionsGluing`:
the sections of the inverse image of a sheaf over a cofiltered limit come from a finite level
(SGA 4 VII 5.7, surjectivity, `AlgebraicGeometry.Scheme.exists_toLimitSections_eq`), and the
stalks of direct images are the sections over the strict localizations (SGA 4 VIII 5.2,
`AlgebraicGeometry.Scheme.pushforwardStalkStrictLocalizationStatement`). With them and the criterion
`AlgebraicGeometry.Scheme.isIso_etaleBaseChangeMap_of_forall_bijective_of_quasiSeparated`, the
main missing input is Gabber's theorem for `B` integral over a strictly henselian local ring `A`:
the restriction of sections from `Spec B` to `Spec (B ⧸ 𝔪_A B)` is bijective (`(B, 𝔪_A B)` is a
henselian pair). -/
def IntegralBaseChangeStatement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [IsIntegralHom f] (F : Sheaf X.smallEtaleTopology (Type u)),
    IsCohomologicallyProperLEZero (𝟙 Y) f F

section UniversallyClosed

variable (f : X ⟶ Y) [UniversallyClosed f] (F : Sheaf X.smallEtaleTopology (Type u))

/-- XIII 1.4 in dimension `≤ -1`, for sheaves of sets: for a universally closed (for instance
proper) morphism `f : X ⟶ Y`, every sheaf of sets `F` on `X` is cohomologically proper for `f` in
dimension `≤ -1`, i.e. the base change morphism `g^* f_* F ⟶ f'_* h^* F` is injective for every
base change `Y' ⟶ Y`. (SGA 1 states 1.4 for `f` proper and in dimension `≤ 0`; this is its
injectivity half, which holds for every universally closed `f` and every `Y`.) -/
theorem isCohomologicallyProperLENegOne_of_universallyClosed :
    IsCohomologicallyProperLENegOne (𝟙 Y) f F :=
  fun _ _ _ _ _ _ _ _ _ hX ↦ Scheme.mono_etaleBaseChangeMap_of_universallyClosed hX F

/-- XIII 1.4 in dimension `≤ -1`, for sheaves of sets, relative to any base `S`
(`isCohomologicallyProperLENegOne_of_universallyClosed`). -/
theorem isCohomologicallyProperLENegOne_of_universallyClosed' (s : Y ⟶ S) :
    IsCohomologicallyProperLENegOne s f F :=
  (isCohomologicallyProperLENegOne_of_universallyClosed f F).of_id s

end UniversallyClosed

variable {sZ : Z ⟶ S} {f : X ⟶ Y} {g : Y ⟶ Z} {F : Sheaf X.smallEtaleTopology (Type u)}

/-- XIII 1.8 for sheaves of sets, dimension `≤ -1`, without assuming the proper base change
theorem: if `(F, f)` is cohomologically proper relative to `S` in dimension `≤ -1` and `g` is
proper (more generally, universally closed), then `(F, f ≫ g)` is cohomologically proper relative
to `S` in dimension `≤ -1`. (SGA 1 states 1.8 for an ind-finite stack `Φ` and a coherent `f`, in
dimensions `≤ -1`, `≤ 0`, `≤ 1`; this is the case of a sheaf of sets in dimension `≤ -1`, where
neither the finiteness of `Φ` nor the coherence of `f` is needed.) -/
theorem IsCohomologicallyProperLENegOne.comp_of_universallyClosed [UniversallyClosed g]
    (hf : IsCohomologicallyProperLENegOne (g ≫ sZ) f F) :
    IsCohomologicallyProperLENegOne sZ (f ≫ g) F :=
  hf.comp (isCohomologicallyProperLENegOne_of_universallyClosed' g _ sZ)

/-- XIII 1.8 for sheaves of sets, dimension `≤ -1`, in the form SGA deduces it from 1.6 1) and
the proper base change theorem 1.4. The hypothesis `ProperBaseChangeStatement` is not used: this
is `IsCohomologicallyProperLENegOne.comp_of_universallyClosed`, which supersedes it. -/
theorem IsCohomologicallyProperLENegOne.comp_of_isProper (_hPBC : ProperBaseChangeStatement.{u})
    [IsProper g] (hf : IsCohomologicallyProperLENegOne (g ≫ sZ) f F) :
    IsCohomologicallyProperLENegOne sZ (f ≫ g) F :=
  hf.comp_of_universallyClosed

/-- XIII 1.8 for sheaves of sets, dimension `≤ 0`, deduced from 1.6 1) and the proper base change
theorem 1.4: if `(F, f)` is cohomologically proper relative to `S` in dimension `≤ 0` and `g` is
proper, then `(F, f ≫ g)` is cohomologically proper relative to `S` in dimension `≤ 0`.
(`IsCohomologicallyProperLEZero.comp_of_isProper_of_isLocallyNoetherian` proves it without the
hypothesis when the target of `g` is locally noetherian.) -/
theorem IsCohomologicallyProperLEZero.comp_of_isProper (hPBC : ProperBaseChangeStatement.{u})
    [IsProper g] (hf : IsCohomologicallyProperLEZero (g ≫ sZ) f F) :
    IsCohomologicallyProperLEZero sZ (f ≫ g) F :=
  hf.comp ((hPBC g _).of_id sZ)

/-- XIII 1.6 2) for sheaves of sets, dimension `≤ 0`, when `f` is universally closed: if
`(F, f ≫ g)` is cohomologically proper relative to `S` in dimension `≤ 0`, so is `(f_* F, g)`.
(The hypothesis of 1.6 2) that `(F, f)` be cohomologically proper in dimension `≤ -1` holds by
`isCohomologicallyProperLENegOne_of_universallyClosed`.) -/
theorem IsCohomologicallyProperLEZero.of_comp_of_universallyClosed [UniversallyClosed f]
    (hfg : IsCohomologicallyProperLEZero sZ (f ≫ g) F) :
    IsCohomologicallyProperLEZero sZ g ((etalePushforward f).obj F) :=
  hfg.of_comp (isCohomologicallyProperLENegOne_of_universallyClosed' f F _)

/-- XIII 1.9 for sheaves of sets, dimension `≤ -1`, unconditionally: for `f` integral,
`(f_* F, g)` is cohomologically proper relative to `S` in dimension `≤ -1` if and only if
`(F, f ≫ g)` is. (SGA deduces 1.9 from the integral base change theorem SGA 4 VIII 5.6; in
dimension `≤ -1` only its injectivity half is used, which holds for every universally closed `f`,
`isCohomologicallyProperLENegOne_of_universallyClosed`.) -/
theorem isCohomologicallyProperLENegOne_pushforward_iff_of_isIntegralHom [IsIntegralHom f] :
    IsCohomologicallyProperLENegOne sZ g ((etalePushforward f).obj F) ↔
      IsCohomologicallyProperLENegOne sZ (f ≫ g) F :=
  ⟨fun h ↦ (isCohomologicallyProperLENegOne_of_universallyClosed' f F _).comp h,
    fun h ↦ h.of_comp⟩

/-- XIII 1.9 for sheaves of sets, dimension `≤ -1`, in the form SGA deduces it from 1.6 and the
base change theorem for integral morphisms. The hypothesis `IntegralBaseChangeStatement` is not
used: this is `isCohomologicallyProperLENegOne_pushforward_iff_of_isIntegralHom`, which supersedes
it. -/
theorem isCohomologicallyProperLENegOne_pushforward_iff (_hInt : IntegralBaseChangeStatement.{u})
    [IsIntegralHom f] :
    IsCohomologicallyProperLENegOne sZ g ((etalePushforward f).obj F) ↔
      IsCohomologicallyProperLENegOne sZ (f ≫ g) F :=
  isCohomologicallyProperLENegOne_pushforward_iff_of_isIntegralHom

/-- XIII 1.9 for sheaves of sets, dimension `≤ 0`, deduced from 1.6 and the base change theorem
for integral morphisms: for `f` integral, `(f_* F, g)` is cohomologically proper relative to `S`
if and only if `(F, f ≫ g)` is. -/
theorem isCohomologicallyProperLEZero_pushforward_iff (hInt : IntegralBaseChangeStatement.{u})
    [IsIntegralHom f] :
    IsCohomologicallyProperLEZero sZ g ((etalePushforward f).obj F) ↔
      IsCohomologicallyProperLEZero sZ (f ≫ g) F :=
  ⟨fun h ↦ ((hInt f F).of_id _).comp h, fun h ↦ h.of_comp ((hInt f F).of_id _).leNegOne⟩

variable (f F) in
/-- SGA 4 VIII 5.6 for finite morphisms (the finite case of `IntegralBaseChangeStatement`): for
`f` finite, the formation of `f_* F` commutes with every change of base
(`AlgebraicGeometry.Scheme.isIso_etaleBaseChangeMap_of_isFinite`). -/
theorem isCohomologicallyProperLEZero_of_isFinite [IsFinite f] :
    IsCohomologicallyProperLEZero (𝟙 Y) f F := by
  intro _ _ _ _ _ _ _ _ _ hX
  exact Scheme.isIso_etaleBaseChangeMap_of_isFinite hX F

/-- XIII 1.9 for sheaves of sets and `f` finite, dimension `≤ -1`: `(f_* F, g)` is
cohomologically proper relative to `S` if and only if `(F, f ≫ g)` is. This is the finite case of
`isCohomologicallyProperLENegOne_pushforward_iff_of_isIntegralHom`, which supersedes it. -/
theorem isCohomologicallyProperLENegOne_pushforward_iff_of_isFinite [IsFinite f] :
    IsCohomologicallyProperLENegOne sZ g ((etalePushforward f).obj F) ↔
      IsCohomologicallyProperLENegOne sZ (f ≫ g) F :=
  isCohomologicallyProperLENegOne_pushforward_iff_of_isIntegralHom

/-- XIII 1.9 for sheaves of sets and `f` finite, dimension `≤ 0`, unconditionally. (SGA 1 states
this for `f` integral; see `isCohomologicallyProperLEZero_pushforward_iff`.) -/
theorem isCohomologicallyProperLEZero_pushforward_iff_of_isFinite [IsFinite f] :
    IsCohomologicallyProperLEZero sZ g ((etalePushforward f).obj F) ↔
      IsCohomologicallyProperLEZero sZ (f ≫ g) F :=
  ⟨fun h ↦ ((isCohomologicallyProperLEZero_of_isFinite f F).of_id _).comp h,
    fun h ↦ h.of_comp ((isCohomologicallyProperLEZero_of_isFinite f F).of_id _).leNegOne⟩

end ProperAndIntegral

section Equalizers

/-! ### XIII 1.13 1): exact diagrams of sheaves of sets -/

/-- A morphism between two limit forks which is an isomorphism on the middle objects and a
monomorphism on the last objects is an isomorphism on the limits. -/
lemma isIso_of_fork_map {C : Type*} [Category* C] {G₁ H₁ G₂ H₂ : C} {a₁ b₁ : G₁ ⟶ H₁}
    {a₂ b₂ : G₂ ⟶ H₂} {c₁ : Fork a₁ b₁} {c₂ : Fork a₂ b₂} (hc₁ : IsLimit c₁) (hc₂ : IsLimit c₂)
    (φG : G₁ ⟶ G₂) (φH : H₁ ⟶ H₂) [IsIso φG] [Mono φH] (ha : a₁ ≫ φH = φG ≫ a₂)
    (hb : b₁ ≫ φH = φG ≫ b₂) (φ : c₁.pt ⟶ c₂.pt) (hφ : φ ≫ c₂.ι = c₁.ι ≫ φG) : IsIso φ := by
  let ψ : c₂.pt ⟶ c₁.pt := Fork.IsLimit.lift hc₁ (c₂.ι ≫ inv φG) (by
    rw [← cancel_mono φH]
    simp only [Category.assoc, ha, hb, IsIso.inv_hom_id_assoc, c₂.condition])
  have hψ : ψ ≫ c₁.ι = c₂.ι ≫ inv φG := Fork.IsLimit.lift_ι hc₁
  refine ⟨ψ, Fork.IsLimit.hom_ext hc₁ ?_, Fork.IsLimit.hom_ext hc₂ ?_⟩
  · rw [Category.assoc, hψ, reassoc_of% hφ, IsIso.hom_inv_id, Category.comp_id,
      Category.id_comp]
  · rw [Category.assoc, hφ, reassoc_of% hψ, IsIso.inv_hom_id, Category.comp_id,
      Category.id_comp]

variable {s : Y ⟶ S} {f : X ⟶ Y} {G H : Sheaf X.smallEtaleTopology (Type u)}

/-- XIII 1.13 1): let `F ⟶ G ⇉ H` be an exact diagram of sheaves of sets on `X` (that is, `F` is
the equalizer). If `(G, f)` is cohomologically proper relative to `S` in dimension `≤ 0` and
`(H, f)` in dimension `≤ -1`, then `(F, f)` is cohomologically proper relative to `S` in
dimension `≤ 0`. -/
theorem IsCohomologicallyProperLEZero.of_isLimit_fork {a b : G ⟶ H} {c : Fork a b}
    (hc : IsLimit c) (hG : IsCohomologicallyProperLEZero s f G)
    (hH : IsCohomologicallyProperLENegOne s f H) : IsCohomologicallyProperLEZero s f c.pt := by
  intro S' Y' X' t s' g h f' hY hX
  have := hG t s' g h f' hY hX
  have := hH t s' g h f' hY hX
  let bc := etaleBaseChangeMap hX.w
  have hc' : IsLimit (Fork.ofι c.ι c.condition) := hc.ofIsoLimit (Fork.isoForkOfι c)
  have := (etaleAdjunction f).rightAdjoint_preservesLimits
  have := (etaleAdjunction f').rightAdjoint_preservesLimits
  have h₁ := isLimitForkMapOfIsLimit (etalePushforward f ⋙ etalePullback g) c.condition hc'
  have h₂ := isLimitForkMapOfIsLimit (etalePullback h ⋙ etalePushforward f') c.condition hc'
  exact isIso_of_fork_map h₁ h₂ (bc.app G) (bc.app H) (bc.naturality a) (bc.naturality b)
    (bc.app c.pt) (bc.naturality c.ι).symm

end Equalizers

section Iso

variable {s : Y ⟶ S} {f : X ⟶ Y} {F F' : Sheaf X.smallEtaleTopology (Type u)}

lemma etaleBaseChangeMap_app_eq_of_iso {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {h : X' ⟶ X}
    {f' : X' ⟶ Y'} (w : h ≫ f = f' ≫ g) (e : F ≅ F') :
    (etaleBaseChangeMap w).app F' = (etalePullback g).map ((etalePushforward f).map e.inv) ≫
      (etaleBaseChangeMap w).app F ≫ (etalePushforward f').map ((etalePullback h).map e.hom) := by
  have H := (etaleBaseChangeMap w).natTrans.naturality e.hom
  simp only [Functor.comp_map] at H
  rw [← H, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, e.inv_hom_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Cohomological properness in dimension `≤ -1` only depends on the isomorphism class of the
sheaf. -/
lemma IsCohomologicallyProperLENegOne.of_iso (e : F ≅ F')
    (hF : IsCohomologicallyProperLENegOne s f F) : IsCohomologicallyProperLENegOne s f F' := by
  intro S' Y' X' t s' g h f' hY hX
  have := hF t s' g h f' hY hX
  rw [etaleBaseChangeMap_app_eq_of_iso hX.w e]
  infer_instance

/-- Cohomological properness in dimension `≤ 0` only depends on the isomorphism class of the
sheaf. -/
lemma IsCohomologicallyProperLEZero.of_iso (e : F ≅ F')
    (hF : IsCohomologicallyProperLEZero s f F) : IsCohomologicallyProperLEZero s f F' := by
  intro S' Y' X' t s' g h f' hY hX
  have := hF t s' g h f' hY hX
  rw [etaleBaseChangeMap_app_eq_of_iso hX.w e]
  infer_instance

end Iso

section Groups

/-! ### XIII 1.3, 1.5 a), 1.7: sheaves of groups -/

variable (s : Y ⟶ S) (f : X ⟶ Y) (G : X.Etaleᵒᵖ ⥤ GrpCat.{u})

/-- The restriction `F|X₁` of a sheaf of groups on `X` to an étale `X₁ ⟶ X`. -/
noncomputable abbrev restrictGroup {X₁ : Scheme.{u}} (e : X₁ ⟶ X) [Etale e] :
    X₁.Etaleᵒᵖ ⥤ GrpCat.{u} :=
  (Scheme.Etale.map e).op ⋙ G

variable {G} in
lemma isSheaf_restrictGroup (hG : Presieve.IsSheaf X.smallEtaleTopology (G ⋙ forget GrpCat))
    {X₁ : Scheme.{u}} (e : X₁ ⟶ X) [Etale e] :
    Presieve.IsSheaf X₁.smallEtaleTopology (restrictGroup G e ⋙ forget GrpCat) :=
  (Scheme.Etale.map e).op_comp_isSheaf_of_isSheaf_type _ hG

/-- Two torsors on `X₁` are locally isomorphic over `Y₁` at a point `y` of `Y₁` (for
`π : X₁ ⟶ Y₁`): `y` has an étale neighbourhood `V` such that they become isomorphic on
`X₁ ×_{Y₁} V`. Equivalently, their classes have the same image in the stalk of `R¹π_*` at a
geometric point over `y`. -/
def IsLocallyIsoOverAt {X₁ Y₁ : Scheme.{u}} (π : X₁ ⟶ Y₁) {H : X₁.Etaleᵒᵖ ⥤ GrpCat.{u}}
    (P Q : Torsor X₁.smallEtaleTopology H) (y : Y₁) : Prop :=
  ∃ (V : Scheme.{u}) (v : V ⟶ Y₁) (_ : Etale v), y ∈ Set.range v ∧
    Nonempty (Scheme.etaleRestrictTorsor (pullback.fst π v) P ≅
      Scheme.etaleRestrictTorsor (pullback.fst π v) Q)

/-- Two torsors on `X₁` are locally isomorphic over `Y₁` (for `π : X₁ ⟶ Y₁`) if they are so at
every point of `Y₁` (`IsLocallyIsoOverAt`), i.e. their classes have the same image in
`Γ(Y₁, R¹π_*)`. -/
def IsLocallyIsoOver {X₁ Y₁ : Scheme.{u}} (π : X₁ ⟶ Y₁) {H : X₁.Etaleᵒᵖ ⥤ GrpCat.{u}}
    (P Q : Torsor X₁.smallEtaleTopology H) : Prop :=
  ∀ y : Y₁, IsLocallyIsoOverAt π P Q y

/-- XIII 1.3 for a sheaf of groups `F`, dimension `≤ -1`, in the form (ii) of XIII 1.3.1: for every
étale `Y₁ ⟶ Y`, with `X₁ = X ×_Y Y₁`, and every torsor `P` on `X₁` under `F₁ = F|X₁`, the
twisted group `^P F₁` is cohomologically proper for `f₁ : X₁ ⟶ Y₁` relative to `S` in dimension
`≤ -1`, as a sheaf of sets. (SGA defines this notion through the stack of `F`-torsors and proves
the equivalence with (ii) in 1.3.1; inverse images of stacks are not formalized. We use the base
change morphism of the sheaf of sets `^P F₁`, whose target `f'₁_* h₁^*(^P F₁)` is isomorphic to
the `f'₁_*(^{P'} F'₁)` of SGA.) The fibre product `X₁` is any cartesian square over `Y₁ ⟶ Y`. -/
def IsCohomologicallyProperLENegOneGroup : Prop :=
  ∀ ⦃Y₁ X₁ : Scheme.{u}⦄ (e : Y₁ ⟶ Y) [Etale e] (e' : X₁ ⟶ X) [Etale e'] (f₁ : X₁ ⟶ Y₁),
    IsPullback e' f₁ f e → ∀ P : Torsor X₁.smallEtaleTopology (restrictGroup G e'),
      IsCohomologicallyProperLENegOne (e ≫ s) f₁ (Torsor.twistSheaf P)

/-- XIII 1.3 for a sheaf of groups `F`, dimension `≤ 0`, in the form (ii) of XIII 1.3.1: for every
étale `Y₁ ⟶ Y`, with `X₁ = X ×_Y Y₁`, and every torsor `P` on `X₁` under `F₁`, `^P F₁` is
cohomologically proper for `f₁` relative to `S` in dimension `≤ 0` as a sheaf of sets, and the base
change morphism `a₁ : g^*(R¹f_* F) ⟶ R¹f'_* F'` is injective.

The injectivity of `a₁` is stated on stalks. Let `S'` be an `S`-scheme, `Y' = Y ×_S S'`, `Y₁`
étale over `Y`, `Y'₁ = Y₁ ×_Y Y'` with projection `g₁ : Y'₁ ⟶ Y₁`, and `X'₁ = X₁ ×_{Y₁} Y'₁`.
Let `P`, `Q` be `F₁`-torsors on `X₁` and `y'` a point of `Y'₁`. If the inverse images of `P` and
`Q` on `X'₁` are locally isomorphic over `Y'₁` at `y'`, then `P` and `Q` are locally isomorphic
over `Y₁` at `g₁ y'` (`IsLocallyIsoOverAt`). At a geometric point of `Y'` over the image of `y'`,
the stalk of `g^*(R¹f_* F)` is the stalk of `R¹f_* F` at the image point of `Y`, whose elements
are represented by such torsors `P` for the étale neighbourhoods `Y₁` of that point; so this is
the injectivity of `a₁` on every stalk. Only the points `g₁ y'` are concerned: `a₁` says nothing
about the points of `Y₁` outside the image of `Y'₁`. (The proof of XIII 1.3.1 writes "`P` and `Q`
are locally isomorphic over `Y₁`", which must be read near the image of `Y'₁`: taken over all of
`Y₁`, the condition would fail for every proper `f` with `R¹f_* F` non-trivial, already for
`Y' = ∅`.) -/
def IsCohomologicallyProperLEZeroGroup
    (hG : Presieve.IsSheaf X.smallEtaleTopology (G ⋙ forget GrpCat)) : Prop :=
  (∀ ⦃Y₁ X₁ : Scheme.{u}⦄ (e : Y₁ ⟶ Y) [Etale e] (e' : X₁ ⟶ X) [Etale e'] (f₁ : X₁ ⟶ Y₁),
    IsPullback e' f₁ f e → ∀ P : Torsor X₁.smallEtaleTopology (restrictGroup G e'),
      IsCohomologicallyProperLEZero (e ≫ s) f₁ (Torsor.twistSheaf P)) ∧
  ∀ ⦃S' Y' : Scheme.{u}⦄ (t : S' ⟶ S) (s' : Y' ⟶ S') (g : Y' ⟶ Y), IsPullback g s' s t →
    ∀ ⦃Y₁ X₁ Y'₁ X'₁ : Scheme.{u}⦄ (e : Y₁ ⟶ Y) [Etale e] (e' : X₁ ⟶ X) [Etale e']
      (f₁ : X₁ ⟶ Y₁), IsPullback e' f₁ f e → ∀ (eY' : Y'₁ ⟶ Y') (g₁ : Y'₁ ⟶ Y₁),
      IsPullback g₁ eY' e g → ∀ (h₁ : X'₁ ⟶ X₁) (f'₁ : X'₁ ⟶ Y'₁),
      IsPullback h₁ f'₁ f₁ g₁ →
      ∀ (P Q : Torsor X₁.smallEtaleTopology (restrictGroup G e')) (y' : Y'₁),
        IsLocallyIsoOverAt f'₁ (Scheme.etalePullbackTorsor h₁ (isSheaf_restrictGroup hG e') P)
          (Scheme.etalePullbackTorsor h₁ (isSheaf_restrictGroup hG e') Q) y' →
        IsLocallyIsoOverAt f₁ P Q (g₁ y')

variable {s f G} (hG : Presieve.IsSheaf X.smallEtaleTopology (G ⋙ forget GrpCat))

/-- The underlying sheaf of sets of a sheaf of groups. -/
abbrev groupSheaf : Sheaf X.smallEtaleTopology (Type u) :=
  ⟨G ⋙ forget GrpCat, (isSheaf_iff_isSheaf_of_type _ _).2 hG⟩

/-- The twist of the restriction of `F` to `X ×_Y Y` by the trivial torsor is the inverse image of
`F`, as a sheaf of sets. -/
noncomputable def twistSheafTrivialIsoPullback :
    Torsor.twistSheaf (Torsor.trivial _ (restrictGroup G (pullback.fst f (𝟙 Y)))
      (isSheaf_restrictGroup hG (pullback.fst f (𝟙 Y)))) ≅
        (etalePullback (pullback.fst f (𝟙 Y))).obj (groupSheaf hG) :=
  Torsor.twistSheafTrivialIso _ ≪≫
    (ObjectProperty.isoMk _ (Iso.refl _) :
      (⟨restrictGroup G (pullback.fst f (𝟙 Y)) ⋙ forget GrpCat, _⟩ : Sheaf _ (Type u)) ≅
        (Scheme.etaleRestrict (pullback.fst f (𝟙 Y))).obj (groupSheaf hG)) ≪≫
    (Scheme.etalePullbackIsoRestrict (pullback.fst f (𝟙 Y))).symm.app _

/-- XIII 1.5 a), dimension `≤ -1`: if a sheaf of groups `F` is cohomologically proper for `f`
relative to `S` in dimension `≤ -1`, so is its underlying sheaf of sets. (SGA also gives an example
showing that the converse fails.) -/
theorem IsCohomologicallyProperLENegOneGroup.isCohomologicallyProperLENegOne
    (h : IsCohomologicallyProperLENegOneGroup s f G) :
    IsCohomologicallyProperLENegOne s f (groupSheaf hG) := by
  have H := (h (𝟙 Y) (pullback.fst f (𝟙 Y)) (pullback.snd f (𝟙 Y)) (.of_hasPullback f (𝟙 Y))
    (Torsor.trivial _ _ (isSheaf_restrictGroup hG (pullback.fst f (𝟙 Y))))).of_iso
    (twistSheafTrivialIsoPullback hG)
  exact (isCohomologicallyProperLENegOne_iff_of_etale_cover (fun _ : Unit ↦ 𝟙 Y)
    (fun y ↦ ⟨(), y, rfl⟩)).2 fun _ ↦ H

/-- XIII 1.5 a), dimension `≤ 0`: if a sheaf of groups `F` is cohomologically proper for `f`
relative to `S` in dimension `≤ 0`, so is its underlying sheaf of sets. -/
theorem IsCohomologicallyProperLEZeroGroup.isCohomologicallyProperLEZero
    (h : IsCohomologicallyProperLEZeroGroup s f G hG) :
    IsCohomologicallyProperLEZero s f (groupSheaf hG) := by
  have H := (h.1 (𝟙 Y) (pullback.fst f (𝟙 Y)) (pullback.snd f (𝟙 Y)) (.of_hasPullback f (𝟙 Y))
    (Torsor.trivial _ _ (isSheaf_restrictGroup hG (pullback.fst f (𝟙 Y))))).of_iso
    (twistSheafTrivialIsoPullback hG)
  exact (isCohomologicallyProperLEZero_iff_of_etale_cover (fun _ : Unit ↦ 𝟙 Y)
    (fun y ↦ ⟨(), y, rfl⟩)).2 fun _ ↦ H

/-- XIII 1.3: cohomological properness in dimension `≤ 0` implies dimension `≤ -1`, for sheaves of
groups. -/
theorem IsCohomologicallyProperLEZeroGroup.leNegOne
    (h : IsCohomologicallyProperLEZeroGroup s f G hG) :
    IsCohomologicallyProperLENegOneGroup s f G :=
  fun _ _ e _ e' _ f₁ hsq P ↦ (h.1 e e' f₁ hsq P).leNegOne

/-- The direct image `f_* F` of a sheaf of groups: `(f_* F)(V) = F(X ×_Y V)`. -/
noncomputable abbrev pushforwardGroup (f : X ⟶ Y) (G : X.Etaleᵒᵖ ⥤ GrpCat.{u}) :
    Y.Etaleᵒᵖ ⥤ GrpCat.{u} :=
  (Scheme.Etale.pullback f).op ⋙ G

/-- XIII 1.7, dimension `≤ -1`: if a sheaf of groups `F` on `X` is cohomologically proper for
`f ≫ g` relative to `S` in dimension `≤ -1`, then `f_* F` is cohomologically proper for `g` relative
to `S` in dimension `≤ -1`. For a torsor `Q` under `(f_* F)|Y₁`, the twisted group `^Q(f_* F)` is
the direct image of `^P F` for the torsor `P` under `F` deduced from `Q` by extension of the
structure group (`Scheme.exists_twistSheaf_iso_etalePushforward`); conclude by 1.6 2). -/
theorem IsCohomologicallyProperLENegOneGroup.pushforward {sZ : Z ⟶ S} {g : Y ⟶ Z}
    (hG : Presieve.IsSheaf X.smallEtaleTopology (G ⋙ forget GrpCat))
    (h : IsCohomologicallyProperLENegOneGroup sZ (f ≫ g) G) :
    IsCohomologicallyProperLENegOneGroup sZ g (pushforwardGroup f G) := by
  intro Z₁ Y₁ e _ eY _ g₁ hY Q
  have hsq : IsPullback (pullback.fst f eY) (pullback.snd f eY) f eY := .of_hasPullback f eY
  have hX : IsPullback (pullback.fst f eY) (pullback.snd f eY ≫ g₁) (f ≫ g) e :=
    hsq.paste_vert hY
  obtain ⟨R, ⟨i⟩⟩ := Scheme.exists_twistSheaf_iso_etalePushforward hsq G hG Q
  have H := h e (pullback.fst f eY) (pullback.snd f eY ≫ g₁) hX R
  exact (H.of_comp).of_iso i.symm

/-- SGA 4 VIII 5.8, used in the proof of XIII 1.9: for an integral morphism `f : X ⟶ Y`,
every torsor under a sheaf of groups on `X` is locally trivial over `Y` (i.e. `R¹f_* F` is
trivial) (`AlgebraicGeometry.Scheme.isLocallyTrivialAlong_etalePullback_of_isIntegralHom`). -/
theorem isLocallyTrivialAlong_of_isIntegralHom [IsIntegralHom f]
    (P : Torsor X.smallEtaleTopology G) :
    P.IsLocallyTrivialAlong Y.smallEtaleTopology (Scheme.Etale.pullback f) :=
  Scheme.isLocallyTrivialAlong_etalePullback_of_isIntegralHom f P

/-- SGA 4 VIII 5.8, used in the proof of XIII 1.9: for an integral morphism `f : X ⟶ Y`, every
torsor under a sheaf of groups on `X` is locally trivial over `Y`
(`isLocallyTrivialAlong_of_isIntegralHom`). -/
theorem IntegralTorsorLocallyTrivialStatement :
    ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [IsIntegralHom f] (G : X.Etaleᵒᵖ ⥤ GrpCat.{u})
      (P : Torsor X.smallEtaleTopology G),
      P.IsLocallyTrivialAlong Y.smallEtaleTopology (Scheme.Etale.pullback f) :=
  fun _ _ f _ _ P ↦ isLocallyTrivialAlong_of_isIntegralHom (f := f) P

/-- XIII 1.4 in dimension `≤ -1`, for sheaves of groups: for a universally closed (for instance
proper) morphism `f`, every sheaf of groups on `X` is cohomologically proper for `f` relative to
any `S` in dimension `≤ -1`. (SGA 1 states 1.4 for `f` proper, in dimension `≤ 0` for all sheaves
of groups; this is the dimension `≤ -1` part. The twisted groups `^P F₁` live on base changes
`f₁` of `f`, which are again universally closed.) -/
theorem isCohomologicallyProperLENegOneGroup_of_universallyClosed (s : Y ⟶ S) (f : X ⟶ Y)
    [UniversallyClosed f] (G : X.Etaleᵒᵖ ⥤ GrpCat.{u}) :
    IsCohomologicallyProperLENegOneGroup s f G := by
  intro Y₁ X₁ e _ e' _ f₁ hsq P
  have : UniversallyClosed f₁ := MorphismProperty.of_isPullback hsq inferInstance
  exact isCohomologicallyProperLENegOne_of_universallyClosed' f₁ _ (e ≫ s)

/-- XIII 1.9 for sheaves of groups, dimension `≤ -1`, unconditionally: for `f` integral,
`(f_* F, g)` is cohomologically proper relative to `S` in dimension `≤ -1` if and only if
`(F, f ≫ g)` is. The direct implication uses the local triviality over `Y` of torsors on `X`
(SGA 4 VIII 5.8, `isLocallyTrivialAlong_of_isIntegralHom`) and, in place of the integral base
change theorem SGA 4 VIII 5.6 used by SGA, its injectivity half
`isCohomologicallyProperLENegOne_of_universallyClosed`; the converse is 1.7. -/
theorem isCohomologicallyProperLENegOneGroup_pushforward_iff_of_isIntegralHom {sZ : Z ⟶ S}
    {g : Y ⟶ Z} [IsIntegralHom f]
    (hG : Presieve.IsSheaf X.smallEtaleTopology (G ⋙ forget GrpCat)) :
    IsCohomologicallyProperLENegOneGroup sZ g (pushforwardGroup f G) ↔
      IsCohomologicallyProperLENegOneGroup sZ (f ≫ g) G := by
  refine ⟨fun h ↦ ?_, IsCohomologicallyProperLENegOneGroup.pushforward hG⟩
  intro Z₁ X₁ e _ eX _ h₁ hX P
  obtain ⟨f₁, hsq, hf₁⟩ := exists_isPullback_factor hX
  have hY := IsPullback.of_hasPullback g e
  have : IsIntegralHom f₁ := MorphismProperty.of_isPullback hsq ‹_›
  have hP := isLocallyTrivialAlong_of_isIntegralHom (f := f₁) P
  let Q := P.pushforward (Scheme.Etale.pullback f₁) (Scheme.pushforwardRestrictIso hsq G) hP
  have H := (h e (pullback.fst g e) (pullback.snd g e) hY Q).of_iso
    (Torsor.twistPushforwardIso _ _ P hP).symm
  rw [← hf₁]
  exact (isCohomologicallyProperLENegOne_of_universallyClosed' f₁ _ _).comp H

/-- XIII 1.9 for sheaves of groups, dimension `≤ -1`, in the form SGA deduces it from the base
change theorem for integral morphisms (SGA 4 VIII 5.6) and SGA 4 VIII 5.8. The hypothesis
`IntegralBaseChangeStatement` is not used: this is
`isCohomologicallyProperLENegOneGroup_pushforward_iff_of_isIntegralHom`, which supersedes it. -/
theorem isCohomologicallyProperLENegOneGroup_pushforward_iff {sZ : Z ⟶ S} {g : Y ⟶ Z}
    (_hInt : IntegralBaseChangeStatement.{u})
    [IsIntegralHom f] (hG : Presieve.IsSheaf X.smallEtaleTopology (G ⋙ forget GrpCat)) :
    IsCohomologicallyProperLENegOneGroup sZ g (pushforwardGroup f G) ↔
      IsCohomologicallyProperLENegOneGroup sZ (f ≫ g) G :=
  isCohomologicallyProperLENegOneGroup_pushforward_iff_of_isIntegralHom hG

/-- SGA 4 VIII 5.8 for finite morphisms: torsors on `X` are locally trivial over `Y` for `f`
finite (`AlgebraicGeometry.Scheme.isLocallyTrivialAlong_etalePullback_of_isFinite`). -/
theorem isLocallyTrivialAlong_of_isFinite [IsFinite f] (P : Torsor X.smallEtaleTopology G) :
    P.IsLocallyTrivialAlong Y.smallEtaleTopology (Scheme.Etale.pullback f) :=
  Scheme.isLocallyTrivialAlong_etalePullback_of_isFinite f P

/-- XIII 1.9 for sheaves of groups and `f` finite, dimension `≤ -1`: `(f_* F, g)` is
cohomologically proper relative to `S` if and only if `(F, f ≫ g)` is. This is the finite case of
`isCohomologicallyProperLENegOneGroup_pushforward_iff_of_isIntegralHom`, which supersedes it. -/
theorem isCohomologicallyProperLENegOneGroup_pushforward_iff_of_isFinite {sZ : Z ⟶ S}
    {g : Y ⟶ Z} [IsFinite f] (hG : Presieve.IsSheaf X.smallEtaleTopology (G ⋙ forget GrpCat)) :
    IsCohomologicallyProperLENegOneGroup sZ g (pushforwardGroup f G) ↔
      IsCohomologicallyProperLENegOneGroup sZ (f ≫ g) G :=
  isCohomologicallyProperLENegOneGroup_pushforward_iff_of_isIntegralHom hG

end Groups

end SGA.SGA1.ExposeXIII
