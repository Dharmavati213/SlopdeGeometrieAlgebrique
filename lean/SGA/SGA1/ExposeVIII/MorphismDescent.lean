/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import SGA.Foundations.Ample
import SGA.Foundations.Projective.AmpleDescent
import SGA.SGA1.ExposeVIII.TopologicalDescent

/-!
# SGA 1, Exposé VIII, §5: descent of morphisms of preschemes

* VIII.5.1 a): a surjective morphism `g` with `𝒪_S ⟶ g_* 𝒪_{S'}` injective is an epimorphism of
  schemes; without surjectivity, it is an epimorphism for morphisms into separated schemes (the
  remark in the proof). Part b) (the effective epimorphism criterion in ringed spaces) is not
  formalized; its application VIII.5.3 is in mathlib.
* VIII.5.2: a faithfully flat quasi-compact morphism is a descent morphism for morphisms of
  schemes (`existsUnique_hom_of_fpqc`).
* VIII.5.3: it is a universal effective epimorphism (mathlib).
* VIII.5.4: isomorphisms descend (mathlib).
* VIII.5.5: closed immersions, open immersions (mathlib) and quasi-compact immersions descend.
* VIII.5.6: affine morphisms descend. SGA proves this with VIII.2.1; here we use the flat base
  change of global sections (mathlib's `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`):
  the base change of `X ⟶ Spec Γ(X, 𝒪_X)` is `X' ⟶ Spec Γ(X', 𝒪_{X'})`
  (`isPullback_toSpecΓ_of_flat`), and isomorphisms descend.
* VIII.5.7: integral, finite, and finite locally free morphisms descend.
* VIII.5.9: quasi-affine morphisms (`AlgebraicGeometry.IsQuasiAffineHom`, in
  `SGA.Foundations.QuasiAffine`) descend. SGA deduces this from VIII.5.8; we argue as for
  VIII.5.6, with open immersions instead of isomorphisms: over affine bases, the base change of
  `X ⟶ Spec Γ(X, 𝒪_X)` is `X' ⟶ Spec Γ(X', 𝒪_{X'})`.
* VIII.5.8, for "ample" (`isRelativelyAmpleDescentStatement`), with line bundles and relative
  ampleness from `SGA.Foundations.Ample`. The implication "`L` relatively ample ⇒ `L'` relatively
  ample" holds for any base change (`isRelativelyAmple_pullback_of_isRelativelyAmple`, EGA II
  4.6.13 (iii)). For the descent direction we reduce to affine bases
  (`isRelativelyAmple_of_isRelativelyAmple_pullback`); there, instead of SGA's `Proj` of
  `⊕ f_*(Lⁿ)`, we use that `L` is ample iff the non-vanishing loci `X_s` of the sections of its
  positive powers cover `X` and are quasi-affine (EGA II 4.5.2): the covering descends by flat
  base change of sections, and quasi-affineness by VIII.5.9 (`isAmple_of_isAmple_pullback`).
  The part on very ample sheaves is not recorded. SGA's remark that
  quasi-affine means "`𝒪_X` relatively ample" is `Scheme.LineBundle.isRelativelyAmple_trivial_iff`.
  The remark VIII.5.10 (Hironaka's example) is not formalized.

Faithfully flat quasi-compact is written `@Surjective ⊓ @Flat ⊓ @QuasiCompact`, as in mathlib.
-/

universe u

namespace SGA.SGA1.ExposeVIII

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MorphismProperty Topology

section Epi

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.5.1 a): a surjective morphism `g : S' ⟶ S` such that `𝒪_S ⟶ g_* 𝒪_{S'}` is injective
is an epimorphism in the category of schemes. -/
theorem epi_of_surjective_of_injective_app {S S' : Scheme.{u}} (g : S' ⟶ S) [Surjective g]
    (hg : ∀ U : S.Opens, Function.Injective (g.app U)) : Epi g := by
  constructor
  intro Z f₁ f₂ e
  have hbase : f₁.base = f₂.base := by
    ext s
    obtain ⟨s', rfl⟩ := g.surjective s
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  refine Scheme.Hom.ext hbase fun U ↦ ?_
  ext x
  apply hg (f₂ ⁻¹ᵁ U)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 1
  rw [Category.assoc, Scheme.Hom.naturality, ← Category.assoc, ← Scheme.Hom.comp_app,
    ← Scheme.Hom.comp_app, Scheme.Hom.congr_app e U]
  simp only [Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj, Scheme.Hom.comp_app,
    eqToHom_op, Category.assoc, eqToHom_unop, CommRingCat.hom_comp]
  rw [← CommRingCat.hom_comp, ← Functor.map_comp, Subsingleton.elim (_ ≫ _) (𝟙 _),
    CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.5.1, remark in the proof of a): if `𝒪_S ⟶ g_* 𝒪_{S'}` is injective (in mathlib's terms,
`g` is scheme-theoretically dominant), but `g` is not necessarily surjective, two morphisms from
`S` to a separated scheme that agree after composition with `g` are equal: the closed
subscheme where they agree contains `g`, so its ideal is zero. -/
theorem eq_of_isSchemeTheoreticallyDominant {S S' Z : Scheme.{u}} (g : S' ⟶ S)
    [IsSchemeTheoreticallyDominant g] [Z.IsSeparated] {f₁ f₂ : S ⟶ Z} (e : g ≫ f₁ = g ≫ f₂) :
    f₁ = f₂ := by
  have : IsClosedImmersion (equalizer.ι f₁ f₂) :=
    MorphismProperty.of_isPullback (isPullback_equalizer_prod f₁ f₂).flip inferInstance
  have : IsIso (equalizer.ι f₁ f₂) := by
    rw [IsClosedImmersion.isIso_iff_ker_eq_bot, eq_bot_iff]
    calc (equalizer.ι f₁ f₂).ker ≤ (equalizer.lift g e ≫ equalizer.ι f₁ f₂).ker :=
          Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [equalizer.lift_ι]; exact g.ker_eq_bot
  exact eq_of_epi_equalizer

/-- VIII.5.1 a), for flat morphisms: a faithfully flat morphism is an epimorphism of schemes
(mathlib's `Flat.epi_of_flat_of_surjective`). -/
theorem epi_of_flat_of_surjective {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g] [Surjective g] :
    Epi g :=
  Flat.epi_of_flat_of_surjective g

end Epi

section EffectiveEpi

variable {S S' X Y : Scheme.{u}} (g : S' ⟶ S) [Surjective g] [Flat g] [QuasiCompact g]

/-- VIII.5.3: a faithfully flat quasi-compact morphism is an effective epimorphism (mathlib). -/
theorem effectiveEpi_of_fpqc : EffectiveEpi g := inferInstance

/-- VIII.5.3: a faithfully flat quasi-compact morphism is a universal effective epimorphism:
all its base changes are effective epimorphisms. -/
theorem effectiveEpi_pullback_fst_of_fpqc {T : Scheme.{u}} (t : T ⟶ S) :
    EffectiveEpi (pullback.fst t g) := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.5.2: a faithfully flat quasi-compact morphism `g : S' ⟶ S` is a descent morphism for
morphisms of schemes. For `S`-schemes `X` and `Y`, with `X' = X ×_S S'`, an `S`-morphism
`u : X' ⟶ Y` (the same as an `S'`-morphism `X' ⟶ Y ×_S S'`) whose two pullbacks to
`X'' = X' ×_X X'` agree comes from a unique `S`-morphism `X ⟶ Y`. This is the exactness of
`Hom_S(X, Y) → Hom_{S'}(X', Y') ⇉ Hom_{S''}(X'', Y'')`. -/
theorem existsUnique_hom_of_fpqc (x : X ⟶ S) (y : Y ⟶ S) (u : pullback x g ⟶ Y)
    (hu : u ≫ y = pullback.fst x g ≫ x)
    (h : pullback.fst (pullback.fst x g) (pullback.fst x g) ≫ u =
      pullback.snd (pullback.fst x g) (pullback.fst x g) ≫ u) :
    ∃! v : X ⟶ Y, v ≫ y = x ∧ pullback.fst x g ≫ v = u := by
  have H : ∀ {T : Scheme.{u}} (a b : T ⟶ pullback x g),
      a ≫ pullback.fst x g = b ≫ pullback.fst x g → a ≫ u = b ≫ u := fun a b e ↦ by
    rw [← pullback.lift_fst a b e, Category.assoc, h, pullback.lift_snd_assoc]
  have hfac := EffectiveEpi.fac (pullback.fst x g) u H
  refine ⟨EffectiveEpi.desc _ u H, ⟨?_, hfac⟩, fun v hv ↦ EffectiveEpi.uniq _ u H v hv.2⟩
  rw [← cancel_epi (pullback.fst x g), reassoc_of% hfac, hu]

end EffectiveEpi

section Flat

/-- Flatness of ring maps codescends along faithfully flat ring maps. -/
theorem flat_codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.Flat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.flat_algebraMap_iff] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact Module.Flat.of_flat_tensorProduct R T S

/-- VIII.5.7 (flatness, a part of "finite and locally free"): flat morphisms descend along
faithfully flat quasi-compact morphisms. -/
instance flat_descendsAlong_fpqc : DescendsAlong @Flat (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat flat_codescendsAlong_faithfullyFlat

end Flat

section Affine

set_option backward.isDefEq.respectTransparency.types false in
lemma appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (e) : f.appLE ⊤ ⊤ e = f.appTop := by
  simp [Scheme.Hom.appLE]

variable {T B Y : Scheme.{u}} [IsAffine T] [IsAffine B] (h : T ⟶ B) (g : Y ⟶ B)

set_option backward.isDefEq.respectTransparency.types false in
/-- Flat base change of global sections: for `h : T ⟶ B` flat between affine schemes and `Y`
quasi-compact and quasi-separated over `B`, `Γ(Y ×_B T) = Γ(Y) ⊗_{Γ(B)} Γ(T)`. -/
theorem isPushout_appTop_of_flat [Flat h] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsPushout g.appTop h.appTop (pullback.snd h g).appTop (pullback.fst h g).appTop := by
  have H : IsPullback (pullback.snd h g) (pullback.fst h g) g h :=
    (IsPullback.of_hasPullback h g).flip
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H (US := ⊤) (UT := ⊤)
    (UX := ⊤) (UY := ⊤) (by simp) (by simp) (by simp) (isAffineOpen_top B) (isAffineOpen_top T)
    isCompact_univ isQuasiSeparated_univ
  rw [isIso_pushoutSection_iff] at hiso
  simpa only [appLE_top_top] using hiso

set_option backward.isDefEq.respectTransparency.types false in
/-- The flat base change of the canonical morphism `Y ⟶ Spec Γ(Y, 𝒪_Y)`: for `h : T ⟶ B` flat
between affine schemes and `Y` quasi-compact and quasi-separated over `B`, the square with
`Y ×_B T ⟶ Spec Γ(Y ×_B T)` and `Y ⟶ Spec Γ(Y)` is cartesian. -/
theorem isPullback_toSpecΓ_of_flat [Flat h] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsPullback (pullback.snd h g) (pullback h g).toSpecΓ Y.toSpecΓ
      (Spec.map (pullback.snd h g).appTop) := by
  have H : IsPullback (pullback.snd h g) (pullback.fst h g) g h :=
    (IsPullback.of_hasPullback h g).flip
  refine IsPullback.of_bot ?_ (Scheme.toSpecΓ_naturality _)
    (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_appTop_of_flat h g))
  rw [← Scheme.toSpecΓ_naturality, ← Scheme.toSpecΓ_naturality]
  exact H.paste_vert (IsPullback.of_vert_isIso ⟨Scheme.toSpecΓ_naturality h⟩)

set_option backward.isDefEq.respectTransparency.types false in
/-- In the situation of `isPullback_toSpecΓ_of_flat`, if `h` is faithfully flat, so is
`Spec Γ(Y ×_B T) ⟶ Spec Γ(Y)`. -/
theorem fpqc_SpecMap_appTop [Flat h] [Surjective h] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (pullback.snd h g).appTop) := by
  have hh : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) h :=
    ⟨⟨‹_›, ‹_›⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback
    (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_appTop_of_flat h g)).flip
    ((arrow_mk_iso_iff (P := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}))
      (arrowIsoSpecΓOfIsAffine h)).mp hh)

set_option backward.isDefEq.respectTransparency.types false in
/-- Quasi-compactness and quasi-separatedness of `Y` descend along `Y ×_B T ⟶ Y` when `h` is
faithfully flat and `Y ×_B T` is quasi-compact and separated. -/
lemma compactSpace_quasiSeparatedSpace_of_pullback [Flat h] [Surjective h]
    [CompactSpace ↥(pullback h g)] [(pullback h g).IsSeparated] :
    CompactSpace Y ∧ QuasiSeparatedSpace Y := by
  refine ⟨⟨by simpa [Set.range_eq_univ.mpr (pullback.snd h g).surjective] using
    isCompact_range (pullback.snd h g).continuous⟩, ?_⟩
  have : IsSeparated (pullback.fst h g ≫ terminal.from T) := by
    rw [terminal.comp_from]; infer_instance
  have : IsSeparated (pullback.fst h g) := .of_comp _ (terminal.from T)
  have : QuasiSeparated g := of_pullback_fst_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := h) ⟨⟨‹_›, ‹_›⟩, inferInstance⟩
    (inferInstanceAs (QuasiSeparated (pullback.fst h g)))
  exact (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).mp this

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.5.6 over affine bases: if `h : T ⟶ B` is a faithfully flat morphism of affine schemes
and `Y ×_B T` is affine, then `Y` is affine. -/
theorem isAffine_of_isAffine_pullback [Flat h] [Surjective h] [IsAffine (pullback h g)] :
    IsAffine Y := by
  obtain ⟨_, _⟩ := compactSpace_quasiSeparatedSpace_of_pullback h g
  have : IsIso Y.toSpecΓ := of_isPullback_of_descendsAlong (P := isomorphisms Scheme)
    (isPullback_toSpecΓ_of_flat h g).flip (fpqc_SpecMap_appTop h g)
    (inferInstanceAs (IsIso (pullback h g).toSpecΓ))
  exact ⟨this⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.5.6: affine morphisms descend along faithfully flat quasi-compact morphisms. -/
instance isAffineHom_descendsAlong_fpqc :
    DescendsAlong @IsAffineHom (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R S Y φ g hφ hfst
  have : Surjective (Spec.map φ) := hφ.1
  have : Flat (Spec.map φ) := hφ.2
  have : IsAffine (pullback (Spec.map φ) g) := isAffine_of_isAffineHom (pullback.fst _ g)
  have := isAffine_of_isAffine_pullback (Spec.map φ) g
  exact isAffineHom_of_isAffine g

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.5.9 over affine bases: if `h : T ⟶ B` is a faithfully flat morphism of affine schemes
and `Y ×_B T` is quasi-affine, then `Y` is quasi-affine. -/
theorem isQuasiAffine_of_isQuasiAffine_pullback [Flat h] [Surjective h]
    [(pullback h g).IsQuasiAffine] : Y.IsQuasiAffine := by
  obtain ⟨_, _⟩ := compactSpace_quasiSeparatedSpace_of_pullback h g
  have : IsOpenImmersion Y.toSpecΓ := of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (isPullback_toSpecΓ_of_flat h g).flip (fpqc_SpecMap_appTop h g)
    (inferInstanceAs (IsOpenImmersion (pullback h g).toSpecΓ))
  exact ⟨⟩

set_option backward.isDefEq.respectTransparency false in
/-- VIII.5.9: quasi-affine morphisms descend along faithfully flat quasi-compact morphisms. -/
instance isQuasiAffineHom_descendsAlong_fpqc :
    DescendsAlong @IsQuasiAffineHom (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R S Y φ g hφ hfst
  have : Surjective (Spec.map φ) := hφ.1
  have : Flat (Spec.map φ) := hφ.2
  have : (pullback (Spec.map φ) g).IsQuasiAffine :=
    isQuasiAffine_of_isQuasiAffineHom (pullback.fst _ g)
  have := isQuasiAffine_of_isQuasiAffine_pullback (Spec.map φ) g
  exact (isQuasiAffineHom_iff_isQuasiAffine g).mpr this

set_option backward.isDefEq.respectTransparency false in
/-- VIII.5.9: for a faithfully flat quasi-compact change of base `g : S' ⟶ S` and an `S`-morphism
`f`, `f` is quasi-affine iff `f' : X ×_S S' ⟶ Y ×_S S'` is. -/
theorem isQuasiAffineHom_pullback_map_iff {X Y S S' : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ S)
    (g : S' ⟶ S) [Surjective g] [Flat g] [QuasiCompact g] :
    IsQuasiAffineHom (pullback.map (f ≫ p) g p g f (𝟙 S') (𝟙 S) (by simp) (by simp)) ↔
      IsQuasiAffineHom f :=
  pullback_map_iff_of_descendsAlong (P := @IsQuasiAffineHom)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) f p ⟨⟨‹_›, ‹_›⟩, ‹_›⟩

/-- VIII.5.8, for "ample" (proved in `isRelativelyAmpleDescentStatement`): let `g : Y' ⟶ Y` be
faithfully flat and quasi-compact, `f : X ⟶ Y` quasi-compact, and `L` a line bundle on `X`. Then
`L` is ample relative to `f` iff its inverse image on `X' = X ×_Y Y'` is ample relative to
`f' : X' ⟶ Y'`. (As in the rest of this file, SGA's situation over a base `S` reduces to `S = Y`.)
The part on very ample sheaves is not recorded. -/
def IsRelativelyAmpleDescentStatement : Prop :=
  ∀ ⦃X Y Y' : Scheme.{u}⦄ (f : X ⟶ Y) (g : Y' ⟶ Y) [Surjective g] [Flat g] [QuasiCompact g]
    [QuasiCompact f] (L : X.LineBundle),
    (L.pullback (pullback.fst f g)).IsRelativelyAmple (pullback.snd f g) ↔ L.IsRelativelyAmple f

/-- VIII.5.8, the implication `⇐` of `IsRelativelyAmpleDescentStatement`, which holds for an
arbitrary base change `g : Y' ⟶ Y` (EGA II 4.6.13 (iii)): if `L` is ample relative to `f`, its
inverse image on `X ×_Y Y'` is ample relative to `f' : X ×_Y Y' ⟶ Y'`. -/
theorem isRelativelyAmple_pullback_of_isRelativelyAmple {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) {L : X.LineBundle} (hL : L.IsRelativelyAmple f) :
    (L.pullback (pullback.fst f g)).IsRelativelyAmple (pullback.snd f g) :=
  hL.of_isPullback (IsPullback.of_hasPullback f g)

end Affine

section FlatBaseChange

variable {P X T B : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ T} {f : X ⟶ B} {h : T ⟶ B}

set_option backward.isDefEq.respectTransparency false in
/-- Flat base change of global sections, for any cartesian square: if `h : T ⟶ B` is a flat
morphism of affine schemes and `X` is quasi-compact and quasi-separated, then
`Γ(X ×_B T) = Γ(X) ⊗_{Γ(B)} Γ(T)`. -/
theorem isPushout_appTop_of_isPullback_of_flat (H : IsPullback fst snd f h) [IsAffine T]
    [IsAffine B] [Flat h] [CompactSpace X] [QuasiSeparatedSpace X] :
    IsPushout f.appTop h.appTop fst.appTop snd.appTop := by
  let e := H.flip.isoPullback
  refine (isPushout_appTop_of_flat h f).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Scheme.Γ.mapIso e.op) (by simp) (by simp) ?_ ?_
  · change _ ≫ e.hom.appTop = 𝟙 _ ≫ fst.appTop
    rw [← Scheme.Hom.comp_appTop, IsPullback.isoPullback_hom_snd, Category.id_comp]
  · change _ ≫ e.hom.appTop = 𝟙 _ ≫ snd.appTop
    rw [← Scheme.Hom.comp_appTop, IsPullback.isoPullback_hom_fst, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The flat base change of `X ⟶ Spec Γ(X, 𝒪_X)`, for any cartesian square as in
`isPushout_appTop_of_isPullback_of_flat`. -/
theorem isPullback_toSpecΓ_of_isPullback_of_flat (H : IsPullback fst snd f h) [IsAffine T]
    [IsAffine B] [Flat h] [CompactSpace X] [QuasiSeparatedSpace X] :
    IsPullback fst P.toSpecΓ X.toSpecΓ (Spec.map fst.appTop) := by
  refine IsPullback.of_bot ?_ (Scheme.toSpecΓ_naturality _)
    (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_appTop_of_isPullback_of_flat H))
  rw [← Scheme.toSpecΓ_naturality, ← Scheme.toSpecΓ_naturality]
  exact H.paste_vert (IsPullback.of_vert_isIso ⟨Scheme.toSpecΓ_naturality h⟩)

end FlatBaseChange

section Finite

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.5.7 (integral): integral morphisms descend along faithfully flat quasi-compact
morphisms, being the universally closed affine morphisms. -/
instance isIntegralHom_descendsAlong_fpqc :
    DescendsAlong @IsIntegralHom (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [IsIntegralHom.eq_universallyClosed_inf_isAffineHom]
  exact DescendsAlong.inf

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.5.7 (finite): finite morphisms descend along faithfully flat quasi-compact morphisms,
being the integral morphisms locally of finite type. -/
instance isFinite_descendsAlong_fpqc :
    DescendsAlong @IsFinite (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [IsFinite.eq_inf]
  exact DescendsAlong.inf

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.5.7 (finite and locally free): finite locally free morphisms (finite, flat and of
finite presentation) descend along faithfully flat quasi-compact morphisms. -/
instance isFinite_flat_finitePresentation_descendsAlong_fpqc :
    DescendsAlong (@IsFinite ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  inferInstance

end Finite

section Immersion

set_option backward.isDefEq.respectTransparency.types false in
/-- Monomorphisms descend along faithfully flat quasi-compact morphisms: a morphism is a
monomorphism iff its diagonal is an isomorphism. -/
instance monomorphisms_descendsAlong_fpqc :
    DescendsAlong (monomorphisms Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : monomorphisms Scheme.{u} = (isomorphisms Scheme.{u}).diagonal := by
    ext X Y f
    exact (pullback.isIso_diagonal_iff f).symm
  rw [this]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.5.5 (closed immersions): closed immersions descend along faithfully flat quasi-compact
morphisms, being the finite monomorphisms. -/
instance isClosedImmersion_descendsAlong_fpqc :
    DescendsAlong @IsClosedImmersion (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [IsClosedImmersion.eq_isFinite_inf_mono]
  exact DescendsAlong.inf

/-- VIII.5.5 (open immersions): mathlib's
`descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`. -/
instance isOpenImmersion_descendsAlong_fpqc :
    DescendsAlong @IsOpenImmersion (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  inferInstance

/-- VIII.5.4: isomorphisms descend along faithfully flat quasi-compact morphisms (mathlib). -/
instance isomorphisms_descendsAlong_fpqc :
    DescendsAlong (isomorphisms Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.5.5 (quasi-compact immersions): quasi-compact immersions descend along faithfully flat
quasi-compact morphisms. As in SGA: the image is locally closed by VIII.4.5, and over the open
set in which it is closed the morphism is a closed immersion after base change. -/
instance isImmersion_inf_quasiCompact_descendsAlong_fpqc :
    DescendsAlong (@IsImmersion ⊓ @QuasiCompact) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    have : Surjective f := hf.1.1
    have : Flat f := hf.1.2
    have : QuasiCompact f := hf.2
    have : IsImmersion fst := hfst.1
    have : QuasiCompact fst := hfst.2
    have hg : QuasiCompact g := of_isPullback_of_descendsAlong h hf hfst.2
    refine ⟨?_, hg⟩
    have hrange : Set.range fst = f ⁻¹' Set.range g := by
      simpa using Scheme.image_preimage_eq_of_isPullback h.flip Set.univ
    have hlc : IsLocallyClosed (Set.range g) :=
      (isLocallyClosed_preimage_iff f g).mp (hrange ▸ fst.isLocallyClosed_range)
    let U : Z.Opens := ⟨coborder (Set.range g), hlc.isOpen_coborder⟩
    let g₁ : Y ⟶ U := IsOpenImmersion.lift U.ι g (by simpa [U] using subset_coborder)
    have hg₁ : g₁ ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
    let fst₁ : A ⟶ f ⁻¹ᵁ U := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι fst (by
      rw [Scheme.Opens.range_ι, hrange]
      exact Set.preimage_mono (subset_coborder (s := Set.range g)))
    have hfst₁ : fst₁ ≫ (f ⁻¹ᵁ U).ι = fst := IsOpenImmersion.lift_fac _ _ _
    have sq : IsPullback fst₁ snd (f ∣_ U) g₁ := by
      refine IsPullback.of_right (by rw [hfst₁, hg₁]; exact h) ?_
        (isPullback_morphismRestrict f U).flip
      rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι, hg₁,
        reassoc_of% hfst₁, h.w]
    have hfU : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (f ∣_ U) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip hf
    have : IsImmersion fst₁ := by
      have : IsImmersion (fst₁ ≫ (f ⁻¹ᵁ U).ι) := hfst₁ ▸ hfst.1
      exact IsImmersion.of_comp fst₁ (f ⁻¹ᵁ U).ι
    have hclosed : IsClosed (Set.range g₁) := by
      have : Set.range g₁ = U.ι ⁻¹' Set.range g := by
        rw [← hg₁, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
          Set.preimage_image_eq _ U.ι.isOpenEmbedding.injective]
      rw [this]
      exact isClosed_preimage_val_coborder
    have : IsClosedImmersion fst₁ := by
      refine .of_isPreimmersion _ ?_
      have : Set.range fst₁ = (f ∣_ U) ⁻¹' Set.range g₁ := by
        simpa using Scheme.image_preimage_eq_of_isPullback sq.flip Set.univ
      rw [this]
      exact hclosed.preimage (f ∣_ U).continuous
    have : IsClosedImmersion g₁ := of_isPullback_of_descendsAlong sq hfU this
    rw [← hg₁]
    infer_instance

end Immersion

section Ample

open Scheme.LineBundle

variable {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {fst : X' ⟶ X} {snd : X' ⟶ Y'}

set_option backward.isDefEq.respectTransparency false in
/-- VIII.5.8 over affine bases (EGA IV 2.7.2): let `g : Y' ⟶ Y` be a faithfully flat morphism of
affine schemes and `X' = X ×_Y Y'`. If the inverse image on `X'` of a line bundle `L` on `X` is
ample, then `L` is ample. By flat base change the non-vanishing loci of the sections of the
powers of `L` cover `X`, their inverse images are the non-vanishing loci of sections of the
powers of the inverse image, hence quasi-affine, and quasi-affineness descends (VIII.5.9). -/
theorem isAmple_of_isAmple_pullback (H : IsPullback fst snd f g) [IsAffine Y] [IsAffine Y']
    [Flat g] [Surjective g] {L : X.LineBundle} (hL : (L.pullback fst).IsAmple) : L.IsAmple := by
  have := hL.1
  have := hL.quasiSeparatedSpace
  have hg : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) g :=
    ⟨⟨‹_›, ‹_›⟩, inferInstance⟩
  have hfst : Surjective fst := MorphismProperty.of_isPullback H.flip inferInstance
  have : CompactSpace X :=
    ⟨by simpa [Set.range_eq_univ.mpr fst.surjective] using isCompact_range fst.continuous⟩
  have : QuasiSeparatedSpace X := by
    have : QuasiSeparated snd := (quasiSeparated_iff_quasiSeparatedSpace snd).mpr ‹_›
    have : QuasiSeparated f := of_isPullback_of_descendsAlong H.flip hg this
    exact (quasiSeparated_iff_quasiSeparatedSpace f).mp this
  have hcov := exists_isSection_mem_famLocus_of_isPullback (L := L) H fun x' ↦ by
    obtain ⟨n, hn, t, hx, -⟩ := hL.2 x'
    exact ⟨n, hn, t.toFam, t.isSection_toFam, by rwa [sections.famLocus_toFam]⟩
  refine isAmple_of_isQuasiAffine_secLocus (R := Γ(X, ⊤)) (fun x ↦ ?_) fun d s hs hd ↦ ?_
  · obtain ⟨d, hd, s, hs, hx⟩ := hcov x
    refine ⟨⟨⟨d, L.ofIsSection s hs⟩, hd, ofIsSection_mem s hs⟩, ?_⟩
    simpa only [secLocus, coeFam_ofIsSection] using hx
  -- the inverse image of `X_s` is the non-vanishing locus of a section of a power of `L'`
  set W := L.secLocus Γ(X, ⊤) s
  have hs' := (isSection_coeFam hs).famPullback fst fst.preimage_top.ge
  have hW : fst ⁻¹ᵁ W = (L.pullback fst).secLocus Γ(X', ⊤)
      ((L.pullback fst).ofIsSection
        (L.famPullback fst fst.preimage_top.ge (L.coeFam _ s)) hs') := by
    simp only [W, secLocus, coeFam_ofIsSection, famLocus_famPullback, top_inf_eq]
  have hqa := hL.isQuasiAffine_secLocus (ofIsSection_mem (R := Γ(X', ⊤)) _ hs') hd
  rw [← hW] at hqa
  have hsnd' : IsQuasiAffineHom ((fst ⁻¹ᵁ W).ι ≫ snd) :=
    (isQuasiAffineHom_iff_isQuasiAffine _).mpr hqa
  have sq : IsPullback (fst ∣_ W) ((fst ⁻¹ᵁ W).ι ≫ snd) (W.ι ≫ f) g :=
    (isPullback_morphismRestrict fst W).paste_vert H
  have : IsQuasiAffineHom (W.ι ≫ f) := of_isPullback_of_descendsAlong sq.flip hg hsnd'
  exact (isQuasiAffineHom_iff_isQuasiAffine _).mp this

set_option backward.isDefEq.respectTransparency false in
/-- VIII.5.8 (EGA IV 2.7.2), the implication `⇒` of `IsRelativelyAmpleDescentStatement`: for
`g : Y' ⟶ Y` faithfully flat and quasi-compact and `f` quasi-compact, if the inverse image of `L`
on `X ×_Y Y'` is ample relative to `f'`, then `L` is ample relative to `f`. We reduce to affine
bases: over an affine open `V` of `Y`, the finite disjoint union `V'` of affine opens covering
`g⁻¹(V)` is affine and faithfully flat over `V`. -/
theorem isRelativelyAmple_of_isRelativelyAmple_pullback {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) [Surjective g] [Flat g] [QuasiCompact g] [QuasiCompact f] {L : X.LineBundle}
    (hL : (L.pullback (pullback.fst f g)).IsRelativelyAmple (pullback.snd f g)) :
    L.IsRelativelyAmple f := by
  refine isRelativelyAmple_of_iSup_eq_top f (fun V : Y.affineOpens ↦ V.1) (fun V ↦ V.2)
    (iSup_affineOpens_eq_top Y) fun V ↦ ?_
  obtain ⟨V, hV⟩ := V
  -- a finite affine open cover of `g⁻¹ V`
  obtain ⟨S, hS, hSV⟩ :=
    isCompact_iff_finite_and_eq_biUnion_affineOpens.mp (g.isCompact_preimage hV.isCompact)
  have := hS.to_subtype
  let W (i : S) : Y'.Opens := i.1.1
  have hWV (i : S) : W i ≤ g ⁻¹ᵁ V := by
    rw [hSV]
    exact le_iSup₂ (f := fun (j : Y'.affineOpens) (_ : j ∈ S) ↦ (j : Y'.Opens)) i.1 i.2
  have : ∀ i, IsAffine (W i) := fun i ↦ i.1.2
  let a (i : S) : (W i).toScheme ⟶ V.toScheme := g.resLE V (W i) (hWV i)
  let gV : ∐ (fun i ↦ (W i).toScheme) ⟶ V.toScheme := Sigma.desc a
  let h : ∐ (fun i ↦ (W i).toScheme) ⟶ Y' := Sigma.desc fun i ↦ (W i).ι
  have hgh : gV ≫ V.ι = h ≫ g := Sigma.hom_ext _ _ fun i ↦ by
    simp only [gV, h, a, Sigma.ι_desc_assoc, Scheme.Hom.resLE_comp_ι]
  have : IsAffine V := hV
  have : Flat gV := IsZariskiLocalAtSource.sigmaDesc fun i ↦
    IsZariskiLocalAtSource.resLE (P := @Flat) _ inferInstance
  have : Surjective gV := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨y', hy'⟩ := g.surjective y.1
    have hy'V : y' ∈ g ⁻¹ᵁ V := by rw [Scheme.Hom.mem_preimage, hy']; exact y.2
    rw [hSV] at hy'V
    obtain ⟨i, hi, hy'i⟩ : ∃ i ∈ S, y' ∈ (i : Y'.Opens) := by simpa using hy'V
    refine ⟨Sigma.ι (fun i ↦ (W i).toScheme) ⟨i, hi⟩ ⟨y', hy'i⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
    apply Subtype.ext
    rw [← Scheme.Opens.ι_apply, ← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.comp_apply]
    exact hy'
  -- the base change to `V'` of `f'` is the base change to `V'` of `f⁻¹ V ⟶ V`
  have P0 := IsPullback.of_hasPullback (f ∣_ V) gV
  let k : pullback (f ∣_ V) gV ⟶ pullback f g :=
    pullback.lift (pullback.fst (f ∣_ V) gV ≫ (f ⁻¹ᵁ V).ι) (pullback.snd (f ∣_ V) gV ≫ h) (by
      rw [Category.assoc, ← morphismRestrict_ι, pullback.condition_assoc, hgh, Category.assoc])
  have outer : IsPullback (pullback.fst (f ∣_ V) gV ≫ (f ⁻¹ᵁ V).ι) (pullback.snd (f ∣_ V) gV) f
      (gV ≫ V.ι) := P0.paste_horiz (isPullback_morphismRestrict f V).flip
  have sq : IsPullback k (pullback.snd (f ∣_ V) gV) (pullback.snd f g) h :=
    IsPullback.of_right (by rw [pullback.lift_fst, ← hgh]; exact outer) (pullback.lift_snd ..)
      (IsPullback.of_hasPullback f g)
  have hZ := (hL.of_isPullback sq).isAmple
  rw [← Scheme.LineBundle.pullback_comp, pullback.lift_fst,
    Scheme.LineBundle.pullback_comp] at hZ
  exact isAmple_of_isAmple_pullback P0 hZ

/-- VIII.5.8 (EGA IV 2.7.2): relative ampleness descends along faithfully flat quasi-compact
morphisms. -/
theorem isRelativelyAmpleDescentStatement : IsRelativelyAmpleDescentStatement.{u} :=
  fun _ _ _ f g _ _ _ _ _ ↦ ⟨isRelativelyAmple_of_isRelativelyAmple_pullback f g,
    isRelativelyAmple_pullback_of_isRelativelyAmple f g⟩

end Ample

end SGA.SGA1.ExposeVIII
