/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import SGA.Foundations.Etale.ConstantScheme
import SGA.Foundations.Etale.Restriction
import SGA.Foundations.StrictLocalizationFunctorial

/-!
# Local acyclicity

Let `f : X ⟶ S` be a morphism of schemes, `x̄` a geometric point of `X`, and
`φ : X̃ = Spec 𝒪^{sh}_{X,x̄} ⟶ S̃ = Spec 𝒪^{sh}_{S,f(x̄)}` the induced morphism of strict
localizations (`AlgebraicGeometry.Scheme.Hom.strictLocalizationMap`). For a geometric point `t̄` of
`S̃`, the fibre `X̃ ×_{S̃} t̄` is the *Milnor fibre* (variety of vanishing cycles) of `f` at `x̄`
over `t̄` (SGA 4 XV 1.7). The morphism `f` is *locally acyclic* for a property `P` of schemes if
`P` holds for all Milnor fibres, and *universally* so if every base change of `f` is
(SGA 4 XV 1.11):

* `Scheme.Hom.IsLocallyAcyclicFor P f`, `Scheme.Hom.IsUniversallyLocallyAcyclicFor P f`.

The geometric points `t̄ : Spec K ⟶ S̃` are taken *algebraic* (`Scheme.Hom.IsAlgebraicPoint`:
`K` is algebraic over the residue field of the image of `t̄`; all such `t̄` are quantified over).
This is the convention of SGA 4 XV (Stacks 0GJP drops it); with arbitrary separably closed `K` the
condition would contain an invariance of `P` under extension of separably closed fields.

For `P` "connected and nonempty" (`ConnectedSpace`; this is `H⁰(Z, C) = C` for every set `C`,
i.e. `Z` is *`0`-acyclic* in the sense of SGA 4 XV 1.3, by
`Scheme.connectedSpace_iff_bijective_constantSchemeSection`) we get *locally `0`-acyclic* morphisms
(`Scheme.Hom.IsLocallyZeroAcyclic`, `Scheme.Hom.IsUniversallyLocallyZeroAcyclic`). The
non-abelian degree `1` (`1`-asphericity for a set of primes `L`) uses the fundamental group and is
defined in `SGA.SGA1.ExposeXIII.LocalAcyclicity`.

We also record the *base change form* of universal `0`-acyclicity of Stacks, Section 59.87: for
every base change `f' : X' ⟶ S'` of `f` and every morphism `g : T ⟶ S'`, with
`h : Y = X' ×_{S'} T ⟶ X'` and `e : Y ⟶ T`, the base change morphism `f'^* g_* F ⟶ h_* e^* F` is
an isomorphism for every étale sheaf of sets `F` on `T`
(`Scheme.Hom.IsUniversallyZeroAcyclicBaseChange`). No hypothesis is put on `g`, as in Stacks 0EYS
(Lemma 59.87.2: "Consider a cartesian diagram of schemes where `f` is flat and locally of finite
presentation with geometrically reduced fibres. Then `f⁻¹ g_* F = h_* e⁻¹ F` for any sheaf `F` on
`T_étale`."). The proof of SGA 1 XIII.3.3 only uses the case of `g` étale of finite presentation
(applied to stacks of torsors). The comparison with the Milnor-fibre form goes through the
description of the stalks of `g_* F` by strict localizations (SGA 4 VIII 5.2) and the limit
theorem SGA 4 VII 5.7, which need `g` quasi-compact and quasi-separated and are not used here;
without that hypothesis on `g` the base change form may be strictly stronger than the Milnor-fibre
form.

## Main results

* `Scheme.connectedSpace_iff_bijective_constantSchemeSection`: `Z` is `0`-acyclic (every section
  of the constant sheaf with value `C`, i.e. of the constant scheme `∐_{c ∈ C} Z`, is constant
  with a unique value) if and only if it is nonempty and connected.
* `Scheme.Hom.isUniversallyLocallyAcyclicFor_of_etale`: étale morphisms are universally locally
  acyclic for every property `P` (closed under isomorphisms) of the spectra of separably closed
  fields: their Milnor fibres are the geometric points `t̄` themselves, since the morphism of
  strict localizations is an isomorphism (`Scheme.Hom.isIso_strictLocalizationMap`).
* `Scheme.Hom.isUniversallyLocallyZeroAcyclic_of_etale`.
* `Scheme.Hom.isUniversallyZeroAcyclicBaseChange_of_etale`: étale base change.
* Local acyclicity is local on the source for the étale topology:
  `Scheme.Hom.IsLocallyAcyclicFor.comp_etale`, `Scheme.Hom.IsLocallyAcyclicFor.of_comp_etale`
  (for `e` étale surjective) and their universal versions; the Milnor fibre of `e ≫ f` at `x̄` is
  that of `f` at `e ∘ x̄` (`Scheme.Hom.milnorFibreCompEtaleIso`).

## References

* [SGA 4, Exposé XV, 1][sga4]
* [Stacks Project, Section 59.87 (Tag 0EYQ), Lemmas 0EZX, 0EYS, 0EZY][stacks]
-/

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme

section ZeroAcyclic

/-! ### `0`-acyclic schemes are the nonempty connected ones -/

variable (Z : Scheme.{u})

/-- The section `e` of the constant `Z`-scheme `∐_{e ∈ E} Z`. The constant étale sheaf with value
`E` is represented by `∐_{e ∈ E} Z` (`AlgebraicGeometry.Scheme.constantSheafIsoYoneda`), so its
global sections are the sections of `∐_{e ∈ E} Z ⟶ Z`, and these are the ones coming from `E`. -/
noncomputable def constantSchemeSection (E : Type u) (e : E) :
    {s : Z ⟶ constantScheme Z E // s ≫ constantSchemeHom Z E = 𝟙 Z} :=
  ⟨constantSchemeι Z E e, constantSchemeι_hom Z E e⟩

/-- SGA 4 XV 1.3 in degree `0`: a scheme `Z` is `0`-acyclic, i.e. `H⁰(Z, C) = C` for every set
`C` (every section of the constant scheme `∐_{c ∈ C} Z` is one of the canonical ones, uniquely),
if and only if `Z` is nonempty and connected. -/
theorem connectedSpace_iff_bijective_constantSchemeSection :
    ConnectedSpace Z ↔ ∀ E : Type u, Function.Bijective (constantSchemeSection Z E) := by
  constructor
  · intro _ E
    obtain ⟨z⟩ := (inferInstance : Nonempty Z)
    refine ⟨fun e e' h ↦ ?_, fun ⟨s, hs⟩ ↦ ?_⟩
    · by_contra hne
      have := isEmpty_of_comp_constantSchemeι_eq Z E (𝟙 Z) hne
        (by simpa [constantSchemeSection] using congrArg Subtype.val h)
      exact this.false z
    obtain ⟨e, x, hx⟩ := constantSchemeι_surjective Z E (s z)
    have hdisj (a b : E) (y y' : Z) (h : constantSchemeι Z E a y = constantSchemeι Z E b y') :
        a = b := by
      by_contra hab
      have := (disjoint_opensRange_sigmaι (fun _ : E ↦ Z) a b hab).le_bot
        (show constantSchemeι Z E a y ∈ (Sigma.ι (fun _ : E ↦ Z) a).opensRange ⊓
          (Sigma.ι (fun _ : E ↦ Z) b).opensRange from ⟨⟨y, rfl⟩, ⟨y', h.symm⟩⟩)
      exact this
    let V : Set Z := s ⁻¹' Set.range (constantSchemeι Z E e)
    have hVo : IsOpen V := (constantSchemeι Z E e).isOpenEmbedding.isOpen_range.preimage
      s.continuous
    have hVc : IsClosed V := by
      have : Vᶜ = s ⁻¹' ⋃ (e' : E) (_ : e' ≠ e), Set.range (constantSchemeι Z E e') := by
        ext y
        simp only [V, Set.mem_compl_iff, Set.mem_preimage, Set.mem_iUnion, Set.mem_range]
        constructor
        · intro hy
          obtain ⟨e', y', hy'⟩ := constantSchemeι_surjective Z E (s y)
          exact ⟨e', fun h ↦ hy ⟨y', h ▸ hy'⟩, y', hy'⟩
        · rintro ⟨e', he', y', hy'⟩ ⟨y'', hy''⟩
          exact he' (hdisj e' e y' y'' (hy'.trans hy''.symm))
      rw [← isOpen_compl_iff, this]
      exact (isOpen_iUnion fun e' ↦ isOpen_iUnion fun _ ↦
        (constantSchemeι Z E e').isOpenEmbedding.isOpen_range).preimage s.continuous
    have hV : V = Set.univ :=
      (isClopen_iff.mp ⟨hVc, hVo⟩).resolve_left (Set.nonempty_iff_ne_empty.mp ⟨z, x, hx⟩)
    have hrange : Set.range s ⊆ Set.range (constantSchemeι Z E e) := by
      rintro _ ⟨y, rfl⟩
      exact (show y ∈ V from hV ▸ trivial)
    let g := IsOpenImmersion.lift (constantSchemeι Z E e) s hrange
    have hg : g ≫ constantSchemeι Z E e = s := IsOpenImmersion.lift_fac _ _ _
    have hg1 : g = 𝟙 Z := by
      have : g ≫ constantSchemeι Z E e ≫ constantSchemeHom Z E = g := by
        rw [constantSchemeι_hom, Category.comp_id]
      rw [← this, ← Category.assoc, hg, hs]
    refine ⟨e, Subtype.ext ?_⟩
    change constantSchemeι Z E e = s
    rw [← hg, hg1, Category.id_comp]
  · intro h
    have hne : Nonempty Z := by
      by_contra hZ
      rw [not_nonempty_iff] at hZ
      obtain ⟨e, -⟩ := (h PEmpty).2
        ⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _⟩
      exact e.elim
    refine @ConnectedSpace.mk _ _ (preconnectedSpace_iff_clopen.mpr fun U hU ↦ ?_) hne
    let W : Bool → Z.Opens := fun b ↦ if b then ⟨U, hU.isOpen⟩ else ⟨Uᶜ, hU.isClosed.isOpen_compl⟩
    have hW : TopologicalSpace.IsOpenCover W := by
      refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun z _ ↦ ?_)
      rw [TopologicalSpace.Opens.mem_iSup]
      by_cases hz : z ∈ U
      · exact ⟨true, by simpa [W] using hz⟩
      · exact ⟨false, by simpa [W] using hz⟩
    let 𝒰 := Z.openCoverOfIsOpenCover W hW
    let E := ULift.{u} Bool
    let f : ∀ b, 𝒰.X b ⟶ constantScheme Z E := fun b ↦ (W b).ι ≫ constantSchemeι Z E ⟨b⟩
    have hf : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ f a = pullback.snd _ _ ≫ f b := by
      intro (a : Bool) (b : Bool)
      by_cases hab : a = b
      · subst hab
        change pullback.fst (𝒰.f a) (𝒰.f a) ≫ 𝒰.f a ≫ _ = pullback.snd _ _ ≫ 𝒰.f a ≫ _
        rw [pullback.condition_assoc]
      · have : IsEmpty ↥(pullback (𝒰.f a) (𝒰.f b) : Scheme.{u}) := by
          refine ⟨fun y ↦ ?_⟩
          have hy := congrArg (fun g ↦ g y) (pullback.condition (f := 𝒰.f a) (g := 𝒰.f b))
          simp only [Scheme.Hom.comp_apply] at hy
          change (W a).ι _ = (W b).ι _ at hy
          have ha : (W a).ι (pullback.fst (𝒰.f a) (𝒰.f b) y) ∈ (W a : Set Z) := by
            rw [← Scheme.Opens.range_ι]
            exact ⟨_, rfl⟩
          have hb : (W b).ι (pullback.snd (𝒰.f a) (𝒰.f b) y) ∈ (W b : Set Z) := by
            rw [← Scheme.Opens.range_ι]
            exact ⟨_, rfl⟩
          rw [hy] at ha
          cases a <;> cases b <;> simp_all [W]
        exact isInitialOfIsEmpty.hom_ext _ _
    have hgl (b : 𝒰.I₀) : 𝒰.f b ≫ 𝒰.glueMorphisms f hf = f b :=
      Scheme.Cover.ι_glueMorphisms 𝒰 f hf b
    have hs : 𝒰.glueMorphisms f hf ≫ constantSchemeHom Z E = 𝟙 Z := by
      refine 𝒰.hom_ext _ _ fun b ↦ ?_
      rw [Category.comp_id, ← Category.assoc, hgl]
      change ((W b).ι ≫ constantSchemeι Z E ⟨b⟩) ≫ _ = (W b).ι
      rw [Category.assoc, constantSchemeι_hom, Category.comp_id]
    obtain ⟨⟨e⟩, he⟩ := (h E).2 ⟨𝒰.glueMorphisms f hf, hs⟩
    have he' : constantSchemeι Z E ⟨e⟩ = 𝒰.glueMorphisms f hf := congrArg Subtype.val he
    have hb (b : Bool) :
        (W b).ι ≫ constantSchemeι Z E ⟨e⟩ = (W b).ι ≫ constantSchemeι Z E ⟨b⟩ := by
      rw [he']
      exact hgl b
    cases e
    · left
      have : IsEmpty (W true) := isEmpty_of_comp_constantSchemeι_eq Z E (W true).ι
        (fun h ↦ absurd (congrArg ULift.down h) (by decide)) (hb true)
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hz ↦ this.false ⟨z, hz⟩
    · right
      have : IsEmpty (W false) := isEmpty_of_comp_constantSchemeι_eq Z E (W false).ι
        (fun h ↦ absurd (congrArg ULift.down h) (by decide)) (hb false)
      ext z
      simp only [Set.mem_univ, iff_true]
      by_contra hz
      exact this.false ⟨z, hz⟩

end ZeroAcyclic

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- A geometric point `t̄ : Spec K ⟶ T` is *algebraic* if `K` is algebraic over the residue field
`κ(t)` of its image `t` (e.g. `K` an algebraic or separable closure of `κ(t)`). -/
def IsAlgebraicPoint {T : Scheme.{u}} {K : Type u} [Field K] (t : Spec (.of K) ⟶ T) : Prop :=
  t.residueFieldEmbedding.hom.IsIntegral

/-- SGA 4 XV 1.11 (Milnor-fibre form): `f : X ⟶ S` is *locally acyclic for* a property `P` of
schemes if for every geometric point `x̄ : Spec Ω ⟶ X` (`Ω` separably closed) and every algebraic
geometric point `t̄ : Spec K ⟶ S̃` of the strict localization `S̃ = Spec 𝒪^{sh}_{S,f(x̄)}`
(`K` separably closed), the Milnor fibre `X̃ ×_{S̃} t̄`, with `X̃ = Spec 𝒪^{sh}_{X,x̄}`, satisfies
`P`. -/
def IsLocallyAcyclicFor (P : ObjectProperty Scheme.{u}) (f : X ⟶ S) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) (K : Type u) [Field K]
    [IsSepClosed K] (t : Spec (.of K) ⟶ Spec (x ≫ f).strictLocalization), t.IsAlgebraicPoint →
    P (pullback (f.strictLocalizationMap x) t)

/-- SGA 4 XV 1.11: `f` is *universally locally acyclic for* `P` if every base change of `f` is
locally acyclic for `P`. -/
def IsUniversallyLocallyAcyclicFor (P : ObjectProperty Scheme.{u}) (f : X ⟶ S) : Prop :=
  ∀ ⦃S' X' : Scheme.{u}⦄ (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S'),
    IsPullback g' f' f g → f'.IsLocallyAcyclicFor P

/-- SGA 4 XV 1.3, 1.11: `f` is *locally `0`-acyclic* if its Milnor fibres are `0`-acyclic, i.e.
nonempty and connected (`H⁰(Z, C) = C` for every set `C`;
`Scheme.connectedSpace_iff_bijective_constantSchemeSection`). -/
abbrev IsLocallyZeroAcyclic (f : X ⟶ S) : Prop :=
  f.IsLocallyAcyclicFor (ConnectedSpace ·)

/-- SGA 4 XV 1.11: `f` is *universally locally `0`-acyclic* if every base change of `f` is
locally `0`-acyclic. -/
abbrev IsUniversallyLocallyZeroAcyclic (f : X ⟶ S) : Prop :=
  f.IsUniversallyLocallyAcyclicFor (ConnectedSpace ·)

/-- Base change form of universal local `0`-acyclicity (the conclusion of Stacks 0EZX, 0EYS,
0EZY): for every base change `f' : X' ⟶ S'` of `f`, every `g : T ⟶ S'` and every étale sheaf of
sets `F` on `T`, with `Y = X' ×_{S'} T`, `h : Y ⟶ X'` and `e : Y ⟶ T`, the base change morphism
`f'^* g_* F ⟶ h_* e^* F` is an isomorphism.

There is no hypothesis on `g`, as in Stacks 0EYS. The proof of SGA 1 XIII.3.3 only needs `g`
étale of finite presentation. Without a quasi-compactness and quasi-separatedness hypothesis on
`g`, this form may be strictly stronger than the Milnor-fibre form
`Scheme.Hom.IsUniversallyLocallyZeroAcyclic` (their comparison goes through SGA 4 VIII 5.2 and
VII 5.7, which need `g` qcqs). -/
def IsUniversallyZeroAcyclicBaseChange (f : X ⟶ S) : Prop :=
  ∀ ⦃S' X' : Scheme.{u}⦄ (s : S' ⟶ S) (s' : X' ⟶ X) (f' : X' ⟶ S'), IsPullback s' f' f s →
    ∀ ⦃T Y : Scheme.{u}⦄ (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (hsq : IsPullback h e f' g)
      (F : Sheaf T.smallEtaleTopology (Type u)),
      IsIso ((etaleBaseChangeMap hsq.flip.w).app F)

section Basic

variable {P : ObjectProperty Scheme.{u}} {f : X ⟶ S}

lemma IsUniversallyLocallyAcyclicFor.isLocallyAcyclicFor
    (h : f.IsUniversallyLocallyAcyclicFor P) : f.IsLocallyAcyclicFor P :=
  h (𝟙 S) (𝟙 X) f (IsPullback.of_horiz_isIso ⟨by simp⟩)

lemma IsUniversallyLocallyAcyclicFor.of_isPullback {S' X' : Scheme.{u}} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (h : f.IsUniversallyLocallyAcyclicFor P)
    (hsq : IsPullback g' f' f g) : f'.IsUniversallyLocallyAcyclicFor P :=
  fun _ _ g₁ g₁' f₁ hsq₁ ↦ h (g₁ ≫ g) (g₁' ≫ g') f₁ (hsq₁.paste_horiz hsq)

lemma IsLocallyAcyclicFor.of_le {Q : ObjectProperty Scheme.{u}} (hPQ : P ≤ Q)
    (h : f.IsLocallyAcyclicFor P) : f.IsLocallyAcyclicFor Q :=
  fun Ω _ _ x K _ _ t ht ↦ hPQ _ (h Ω x K t ht)

lemma IsUniversallyLocallyAcyclicFor.of_le {Q : ObjectProperty Scheme.{u}} (hPQ : P ≤ Q)
    (h : f.IsUniversallyLocallyAcyclicFor P) : f.IsUniversallyLocallyAcyclicFor Q :=
  fun _ _ g g' f' hsq ↦ (h g g' f' hsq).of_le hPQ

end Basic

section Etale

variable (P : ObjectProperty Scheme.{u}) [P.IsClosedUnderIsomorphisms] (f : X ⟶ S)

/-- An étale morphism is locally acyclic for every property `P` (closed under isomorphisms) of the
spectra of separably closed fields: since `f` induces an isomorphism of strict localizations, the
Milnor fibre over `t̄ : Spec K ⟶ S̃` is `Spec K`. -/
theorem isLocallyAcyclicFor_of_etale [Etale f]
    (hP : ∀ (K : Type u) [Field K] [IsSepClosed K], P (Spec (.of K))) :
    f.IsLocallyAcyclicFor P := by
  intro Ω _ _ x K _ _ t _
  exact P.prop_of_iso (asIso (pullback.snd (f.strictLocalizationMap x) t)).symm (hP K)

/-- SGA 4 XV 1.11 for étale morphisms: an étale morphism is universally locally acyclic for every
property `P` (closed under isomorphisms) of the spectra of separably closed fields. -/
theorem isUniversallyLocallyAcyclicFor_of_etale [Etale f]
    (hP : ∀ (K : Type u) [Field K] [IsSepClosed K], P (Spec (.of K))) :
    f.IsUniversallyLocallyAcyclicFor P := fun _ _ g _ f' hsq ↦
  have : Etale f' := MorphismProperty.of_isPullback hsq ‹_›
  f'.isLocallyAcyclicFor_of_etale P hP

/-- An étale morphism is universally locally `0`-acyclic. -/
theorem isUniversallyLocallyZeroAcyclic_of_etale [Etale f] :
    f.IsUniversallyLocallyZeroAcyclic :=
  f.isUniversallyLocallyAcyclicFor_of_etale _ fun _ _ _ ↦ inferInstance

/-- Étale morphisms satisfy the base change form of universal `0`-acyclicity: this is the étale
base change theorem `AlgebraicGeometry.Scheme.isIso_etaleBaseChangeMap_of_etale`, applied to the
base changes of `f`, which are étale. -/
theorem isUniversallyZeroAcyclicBaseChange_of_etale [Etale f] :
    f.IsUniversallyZeroAcyclicBaseChange := by
  intro _ _ s _ f' hsq _ _ g h e hsq' F
  have : Etale f' := MorphismProperty.of_isPullback hsq ‹_›
  exact isIso_etaleBaseChangeMap_of_etale f' hsq'.flip F

end Etale

section EtaleLocal

/-! ### Local acyclicity is local on the source for the étale topology -/

variable {P : ObjectProperty Scheme.{u}} [P.IsClosedUnderIsomorphisms] {f : X ⟶ S}
  {X' : Scheme.{u}} (e : X' ⟶ X) [Etale e]

omit [P.IsClosedUnderIsomorphisms] [Etale e] in
lemma isAlgebraicPoint_comp_strictLocalizationIsoOfEq {Ω K : Type u} [Field Ω] [Field K]
    {ξ₁ ξ₂ : Spec (.of Ω) ⟶ S} (h : ξ₁ = ξ₂) {t : Spec (.of K) ⟶ Spec ξ₁.strictLocalization}
    (ht : t.IsAlgebraicPoint) : (t ≫ (strictLocalizationIsoOfEq h).hom).IsAlgebraicPoint := by
  subst h
  simpa [strictLocalizationIsoOfEq] using ht

omit [P.IsClosedUnderIsomorphisms] in
/-- For `e` étale, the Milnor fibre of `e ≫ f` at `x̄` is the Milnor fibre of `f` at `e ∘ x̄`,
since `e` induces an isomorphism of strict localizations. -/
def milnorFibreCompEtaleIso {Ω K : Type u} [Field Ω] [Field K]
    (x : Spec (.of Ω) ⟶ X') (t : Spec (.of K) ⟶ Spec (x ≫ e ≫ f).strictLocalization) :
    pullback ((e ≫ f).strictLocalizationMap x) t ≅
      pullback (f.strictLocalizationMap (x ≫ e))
        (t ≫ (strictLocalizationIsoOfEq (Category.assoc x e f)).inv) :=
  pullback.congrHom (strictLocalizationMap_comp f e x) rfl ≪≫
    asIso (pullback.map _ _ _ _ (e.strictLocalizationMap x) (𝟙 _)
      (strictLocalizationIsoOfEq (Category.assoc x e f)).inv (by simp) (by simp))

/-- Local acyclicity is inherited by `e ≫ f` for `e` étale. -/
theorem IsLocallyAcyclicFor.comp_etale (h : f.IsLocallyAcyclicFor P) :
    (e ≫ f).IsLocallyAcyclicFor P := by
  intro Ω _ _ x K _ _ t ht
  refine P.prop_of_iso (milnorFibreCompEtaleIso e x t).symm (h Ω (x ≫ e) K _ ?_)
  exact isAlgebraicPoint_comp_strictLocalizationIsoOfEq (Category.assoc x e f).symm ht

/-- Local acyclicity is local on the source for the étale topology: if `e` is étale and
surjective and `e ≫ f` is locally acyclic for `P`, so is `f`. -/
theorem IsLocallyAcyclicFor.of_comp_etale [Surjective e] (h : (e ≫ f).IsLocallyAcyclicFor P) :
    f.IsLocallyAcyclicFor P := by
  intro Ω _ _ x K _ _ t ht
  obtain ⟨x₀, hx₀⟩ := e.surjective (x default)
  obtain ⟨x', hx', -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed e x x₀ hx₀
  subst hx'
  have := P.prop_of_iso (milnorFibreCompEtaleIso e x' (t ≫
    (strictLocalizationIsoOfEq (Category.assoc x' e f)).hom))
    (h Ω x' K _ (isAlgebraicPoint_comp_strictLocalizationIsoOfEq _ ht))
  simpa using this

/-- Universal local acyclicity is inherited by `e ≫ f` for `e` étale. -/
theorem IsUniversallyLocallyAcyclicFor.comp_etale (h : f.IsUniversallyLocallyAcyclicFor P) :
    (e ≫ f).IsUniversallyLocallyAcyclicFor P := by
  intro S' X'' g g' f' hsq
  let e' : X'' ⟶ pullback f g := pullback.lift (g' ≫ e) f' (by simpa using hsq.w)
  have he' : IsPullback g' e' e (pullback.fst f g) :=
    IsPullback.of_bot (by rw [pullback.lift_snd]; exact hsq) (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback f g)
  have : Etale e' := MorphismProperty.of_isPullback he' ‹_›
  have hf' : f' = e' ≫ pullback.snd f g := (pullback.lift_snd _ _ _).symm
  rw [hf']
  exact (h g _ _ (IsPullback.of_hasPullback f g)).comp_etale e'

/-- Universal local acyclicity is local on the source for the étale topology. -/
theorem IsUniversallyLocallyAcyclicFor.of_comp_etale [Surjective e]
    (h : (e ≫ f).IsUniversallyLocallyAcyclicFor P) : f.IsUniversallyLocallyAcyclicFor P := by
  intro S' Y g g' f' hsq
  have hsq' : IsPullback (pullback.fst e g') (pullback.snd e g' ≫ f') (e ≫ f) g :=
    (IsPullback.of_hasPullback e g').paste_vert hsq
  have := h g _ _ hsq'
  exact IsLocallyAcyclicFor.of_comp_etale (pullback.snd e g') this

end EtaleLocal

end AlgebraicGeometry.Scheme.Hom
