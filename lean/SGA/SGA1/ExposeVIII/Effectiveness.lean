/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Projective.LineBundleIso
import SGA.Foundations.Projective.NormLineBundle
import SGA.Foundations.Projective.QuasiProjective
import SGA.SGA1.ExposeVIII.AffineSchemeDescent
import SGA.SGA1.ExposeVIII.FiniteDescent

/-!
# SGA 1, Exposé VIII, §7: effectiveness criteria for a descent datum

At the start of §7, SGA describes a descent datum on an `S'`-scheme `X'` relative to
`g : S' ⟶ S` as an equivalence pair `q₁, q₂ : X'' ⇉ X'` lying over the pair
`p₁, p₂ : S'' = S' ×_S S' ⇉ S'`, such that both squares are cartesian; a solution of the descent
problem is a cartesian square `X' ⟶ X` over `S' ⟶ S` with `h ∘ q₁ = h ∘ q₂`. We take this as the
definition (`DescentDatum`, `DescentDatum.IsEffective`). That `(q₁, q₂)` is an equivalence pair
is expressed on `T`-valued points; the pair is automatically jointly monic because of the
cartesian squares.

* `ofScheme`: the descent datum defined by an `S`-scheme, which is effective.
* VIII.7.1: for `g` faithfully flat and quasi-compact, a descent datum is effective iff the
  equivalence relation `(q₁, q₂)` has a quotient `X' ⟶ Q` that is faithfully flat and
  quasi-compact with `X''` as fibered square.
* VIII.7.2: the induced descent datum on a stable open subset (`restrict`); a descent datum is
  effective iff the induced ones on a covering by stable open subsets are. Sufficiency glues the
  descended schemes of all stable open subsets with effective induced datum, a locally directed
  diagram of open immersions (`effDiagram`), with mathlib's colimits of such diagrams.
* VIII.7.3: the descent datum relative to `g⁻¹(V) ⟶ V` induced over an open subset `V` of `S`
  (`restrictBase`), and the reduction of effectiveness to an open covering of `S`.
* VIII.2.1 in the form of VIII.7 (`isEffective_of_isAffineHom`): from the case of an affine base
  (`SGA.SGA1.ExposeVIII.AffineSchemeDescent`) by VIII.7.3.
* VIII.7.4, VIII.7.5 (radicial `g`), VIII.7.6 (finite locally free `g`) and VIII.7.9 (quasi-affine
  `X'`) are proved. For VIII.7.9 the base is reduced to affine `S` and `S'` (VIII.7.3 and an fppf
  covering of `S'`, `isEffective_of_isEffective_pullbackBase`); then `Γ(X')` descends by VIII.1.6
  (`isPushout_eqLocus_of_descent`) and `X'` is a saturated open subset of `Spec Γ(X')`.
  VIII.7.6 is proved by the variant through VIII.7.9 indicated after SGA's proof, without norms.
* VIII.7.7 is proved (`effectiveOfQuasiProjectiveStatement`): the effectiveness
  (`isEffective_of_isQuasiProjective`) follows from VIII.7.6 and EGA II 4.5.4 (a finite subset of
  a scheme with an ample line bundle lies in an affine open,
  `SGA.Foundations.Projective.AmpleFinite`); the descended scheme is quasi-projective by
  EGA II 6.6.4, the norm of a relatively ample line bundle along the finite locally free
  `X' ⟶ X` being relatively ample (`SGA.Foundations.Projective.NormLineBundle`).
* VIII.7.8 (descent of schemes with a relatively ample line bundle endowed with a descent datum,
  `LineBundleDatum`) is stated here as `EffectiveOfRelativelyAmpleStatement`, isomorphisms of
  line bundles being `Scheme.LineBundle.Iso`; its special case `L' = 𝒪_{X'}` is VIII.7.9. It is
  proved in `SGA.SGA1.ExposeVIII.AmpleEffectiveness` (effectiveness) and
  `SGA.SGA1.ExposeVIII.LineBundleDescent` (descent of the line bundle,
  `effectiveOfRelativelyAmpleStatement`). The counterexamples VIII.7.10 are not formalized.
-/

universe u

namespace SGA.SGA1.ExposeVIII

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MorphismProperty

/-- If `j : U ⟶ X'` and `ι : V ⟶ X` are open immersions and `h : X' ⟶ X` maps `U` into `V` with
`h⁻¹(V) = U`, the square is cartesian. -/
lemma isPullback_of_preimage_range_eq {U X' V X : Scheme.{u}} (j : U ⟶ X') [IsOpenImmersion j]
    (k : U ⟶ V) (h : X' ⟶ X) (ι : V ⟶ X) [IsOpenImmersion ι] (w : j ≫ h = k ≫ ι)
    (hr : h ⁻¹' Set.range ι ⊆ Set.range j) : IsPullback j k h ι := by
  have H (s : PullbackCone h ι) : Set.range s.fst ⊆ Set.range j := by
    rintro _ ⟨t, rfl⟩
    refine hr ?_
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, s.condition, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w
    (fun s ↦ IsOpenImmersion.lift j s.fst (H s)) (fun s ↦ IsOpenImmersion.lift_fac _ _ _)
    (fun s ↦ ?_) (fun s m h₁ _ ↦ ?_))
  · rw [← cancel_mono ι, Category.assoc, ← w, IsOpenImmersion.lift_fac_assoc, s.condition]
  · rw [← cancel_mono j, h₁, IsOpenImmersion.lift_fac]

section PullbackRestrict

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (V : S.Opens)

/-- The fibered square of `g⁻¹(V) ⟶ V` is the open subscheme of `S' ×_S S'` lying over `V`. -/
noncomputable def pullbackRestrictι : pullback (g ∣_ V) (g ∣_ V) ⟶ pullback g g :=
  pullback.map _ _ _ _ (g ⁻¹ᵁ V).ι (g ⁻¹ᵁ V).ι V.ι (morphismRestrict_ι g V)
    (morphismRestrict_ι g V)

instance : IsOpenImmersion (pullbackRestrictι g V) := by
  unfold pullbackRestrictι; infer_instance

@[reassoc (attr := simp)]
lemma pullbackRestrictι_fst :
    pullbackRestrictι g V ≫ pullback.fst g g = pullback.fst _ _ ≫ (g ⁻¹ᵁ V).ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullbackRestrictι_snd :
    pullbackRestrictι g V ≫ pullback.snd g g = pullback.snd _ _ ≫ (g ⁻¹ᵁ V).ι :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma isPullback_pullbackRestrictι_fst :
    IsPullback (pullbackRestrictι g V) (pullback.fst _ _) (pullback.fst g g) (g ⁻¹ᵁ V).ι := by
  refine isPullback_of_preimage_range_eq _ _ _ _ (pullbackRestrictι_fst g V) fun z hz ↦ ?_
  rw [Set.mem_preimage, Scheme.Opens.range_ι] at hz
  rw [pullbackRestrictι, Scheme.Pullback.range_map, Scheme.Opens.range_ι]
  refine ⟨hz, ?_⟩
  change g (pullback.snd g g z) ∈ V
  rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  exact hz

set_option backward.isDefEq.respectTransparency false in
lemma isPullback_pullbackRestrictι_snd :
    IsPullback (pullbackRestrictι g V) (pullback.snd _ _) (pullback.snd g g) (g ⁻¹ᵁ V).ι := by
  refine isPullback_of_preimage_range_eq _ _ _ _ (pullbackRestrictι_snd g V) fun z hz ↦ ?_
  rw [Set.mem_preimage, Scheme.Opens.range_ι] at hz
  rw [pullbackRestrictι, Scheme.Pullback.range_map, Scheme.Opens.range_ι]
  refine ⟨?_, hz⟩
  change g (pullback.fst g g z) ∈ V
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  exact hz

end PullbackRestrict

variable {S S' : Scheme.{u}} {g : S' ⟶ S}

/-- VIII.7: a descent datum on an `S'`-scheme `X'` relative to `g : S' ⟶ S`, given as an
equivalence pair `q₁, q₂ : X'' ⇉ X'` over `p₁, p₂ : S' ×_S S' ⇉ S'` such that the two squares
`q_i, p_i` are cartesian. -/
structure DescentDatum (g : S' ⟶ S) where
  /-- The scheme `X'` over `S'`. -/
  X' : Scheme.{u}
  /-- The structure morphism `X' ⟶ S'`. -/
  a : X' ⟶ S'
  /-- The scheme `X''` over `S'' = S' ×_S S'`. -/
  X'' : Scheme.{u}
  /-- The structure morphism `X'' ⟶ S''`. -/
  b : X'' ⟶ pullback g g
  /-- The first map of the equivalence pair. -/
  q₁ : X'' ⟶ X'
  /-- The second map of the equivalence pair. -/
  q₂ : X'' ⟶ X'
  isPullback₁ : IsPullback q₁ b a (pullback.fst g g)
  isPullback₂ : IsPullback q₂ b a (pullback.snd g g)
  refl : ∀ ⦃T : Scheme.{u}⦄ (x : T ⟶ X'), ∃ r : T ⟶ X'', r ≫ q₁ = x ∧ r ≫ q₂ = x
  symm : ∀ ⦃T : Scheme.{u}⦄ (r : T ⟶ X''), ∃ r' : T ⟶ X'', r' ≫ q₁ = r ≫ q₂ ∧ r' ≫ q₂ = r ≫ q₁
  trans : ∀ ⦃T : Scheme.{u}⦄ (r r' : T ⟶ X''), r ≫ q₂ = r' ≫ q₁ →
    ∃ r'' : T ⟶ X'', r'' ≫ q₁ = r ≫ q₁ ∧ r'' ≫ q₂ = r' ≫ q₂

namespace DescentDatum

variable (D : DescentDatum g)

/-- VIII.7: a descent datum is effective if it comes from an `S`-scheme: there is a cartesian
square `X' ⟶ X` over `S' ⟶ S` whose top arrow `h` satisfies `h ∘ q₁ = h ∘ q₂`. -/
def IsEffective : Prop :=
  ∃ (X : Scheme.{u}) (f : X ⟶ S) (h : D.X' ⟶ X), IsPullback h D.a f g ∧ D.q₁ ≫ h = D.q₂ ≫ h

/-- VIII.7: an open (or any) subset `U'` of `X'` is stable under the descent datum if its two
inverse images in `X''` agree. -/
def IsStable (U' : Set D.X') : Prop := D.q₁ ⁻¹' U' = D.q₂ ⁻¹' U'

/-- VIII.7.5: the class `R(x') = q₂(q₁⁻¹(x'))` of a point for the set-theoretic equivalence
relation defined by the descent datum. -/
def orbit (x : D.X') : Set D.X' := D.q₂ '' (D.q₁ ⁻¹' {x})

set_option backward.isDefEq.respectTransparency.types false in
/-- If `h : X' ⟶ X` solves the descent problem, `X''` is the fibered square of `X'` over `X`. -/
theorem isPullback_q₁_q₂ {X : Scheme.{u}} {f : X ⟶ S} {h : D.X' ⟶ X}
    (hX : IsPullback h D.a f g) (hq : D.q₁ ≫ h = D.q₂ ≫ h) : IsPullback D.q₁ D.q₂ h h := by
  refine IsPullback.of_isLimit' ⟨hq⟩ (PullbackCone.IsLimit.mk hq
    (fun s ↦ D.isPullback₁.lift s.fst (pullback.lift (s.fst ≫ D.a) (s.snd ≫ D.a) ?_) ?_)
    (fun s ↦ D.isPullback₁.lift_fst _ _ _) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  · rw [Category.assoc, Category.assoc, ← hX.w, reassoc_of% s.condition]
  · exact (pullback.lift_fst _ _ _).symm
  · apply hX.hom_ext
    · rw [Category.assoc, ← hq, D.isPullback₁.lift_fst_assoc, s.condition]
    · rw [Category.assoc, D.isPullback₂.w, D.isPullback₁.lift_snd_assoc, pullback.lift_snd]
  · apply D.isPullback₁.hom_ext
    · simp [h₁]
    · apply pullback.hom_ext
      · rw [Category.assoc, ← D.isPullback₁.w, reassoc_of% h₁, Category.assoc,
          D.isPullback₁.lift_snd_assoc, pullback.lift_fst]
      · rw [Category.assoc, ← D.isPullback₂.w, reassoc_of% h₂, Category.assoc,
          D.isPullback₁.lift_snd_assoc, pullback.lift_snd]

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.7.1: let `g` be faithfully flat and quasi-compact. A descent datum relative to `g` is
effective iff the equivalence relation `(q₁, q₂)` is effective (it has a quotient `X' ⟶ Q` whose
fibered square is `X''`) with a faithfully flat quasi-compact quotient morphism. -/
theorem isEffective_iff [Surjective g] [Flat g] [QuasiCompact g] :
    D.IsEffective ↔ ∃ (Q : Scheme.{u}) (h : D.X' ⟶ Q), IsPullback D.q₁ D.q₂ h h ∧
      Surjective h ∧ Flat h ∧ QuasiCompact h := by
  constructor
  · rintro ⟨X, f, h, hX, hq⟩
    have hh : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) h :=
      MorphismProperty.of_isPullback hX.flip ⟨⟨‹_›, ‹_›⟩, ‹_›⟩
    exact ⟨X, h, D.isPullback_q₁_q₂ hX hq, hh.1.1, hh.1.2, hh.2⟩
  · rintro ⟨Q, h, hQ, _, _, _⟩
    have H : ∀ {T : Scheme.{u}} (u v : T ⟶ D.X'), u ≫ h = v ≫ h →
        u ≫ D.a ≫ g = v ≫ D.a ≫ g := fun u v e ↦ by
      obtain ⟨r, rfl, rfl⟩ : ∃ r, r ≫ D.q₁ = u ∧ r ≫ D.q₂ = v :=
        ⟨_, hQ.lift_fst _ _ e, hQ.lift_snd _ _ e⟩
      rw [Category.assoc, Category.assoc, D.isPullback₁.w_assoc, D.isPullback₂.w_assoc,
        pullback.condition]
    let f : Q ⟶ S := EffectiveEpi.desc h (D.a ≫ g) H
    have hf : h ≫ f = D.a ≫ g := EffectiveEpi.fac h (D.a ≫ g) H
    refine ⟨Q, f, h, ?_, hQ.w⟩
    -- The comparison map `c : X' ⟶ Q ×_S S'` becomes an isomorphism after base change along `h`.
    let c : D.X' ⟶ pullback f g := pullback.lift h D.a hf
    -- `X''` is `X' ×_Q (Q ×_S S')`, via `q₂` and `q₁ ≫ c`.
    have sq₁ : IsPullback (D.q₁ ≫ c) D.q₂ (pullback.fst f g) h := by
      refine IsPullback.of_right (h₁₂ := pullback.snd f g) ?_
        (by rw [Category.assoc, pullback.lift_fst, hQ.w]) (IsPullback.of_hasPullback f g).flip
      rw [Category.assoc, pullback.lift_snd, D.isPullback₁.w, hf]
      exact D.isPullback₂.flip.paste_horiz (IsPullback.of_hasPullback g g)
    -- and it is also `X' ×_{Q ×_S S'} (Q ×_S S') ×_Q X'`, via `q₁` and `c`.
    have sq₂ : IsPullback sq₁.isoPullback.hom D.q₁ (pullback.fst (pullback.fst f g) h) c := by
      refine IsPullback.of_right (h₁₂ := pullback.snd (pullback.fst f g) h) ?_ (by simp)
        (IsPullback.of_hasPullback (pullback.fst f g) h).flip
      rw [IsPullback.isoPullback_hom_snd, pullback.lift_fst]
      exact hQ.flip
    have : IsIso c := of_isPullback_of_descendsAlong (P := isomorphisms Scheme)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq₂
      (MorphismProperty.pullback_fst _ _ ⟨⟨‹_›, ‹_›⟩, ‹_›⟩)
      (inferInstanceAs (IsIso sq₁.isoPullback.hom))
    exact IsPullback.of_iso_pullback ⟨hf⟩ (asIso c) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)

section Restrict

variable {U' : D.X'.Opens} (hU : D.IsStable U')

include hU in
lemma preimage_q₁_eq_preimage_q₂ : D.q₁ ⁻¹ᵁ U' = D.q₂ ⁻¹ᵁ U' :=
  TopologicalSpace.Opens.ext hU

/-- A morphism `T ⟶ X''` whose composite with `q₁` lands in `U'` factors through `q₁⁻¹(U')`. -/
private noncomputable def liftPreimage {T : Scheme.{u}} (r : T ⟶ D.X'') (x : T ⟶ U')
    (hr : r ≫ D.q₁ = x ≫ U'.ι) : T ⟶ D.q₁ ⁻¹ᵁ U' :=
  IsOpenImmersion.lift (D.q₁ ⁻¹ᵁ U').ι r (by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (r ≫ D.q₁) t ∈ U'
    rw [hr, Scheme.Hom.comp_apply]
    exact (x t).2)

private lemma liftPreimage_ι {T : Scheme.{u}} (r : T ⟶ D.X'') (x : T ⟶ U')
    (hr : r ≫ D.q₁ = x ≫ U'.ι) : D.liftPreimage r x hr ≫ (D.q₁ ⁻¹ᵁ U').ι = r :=
  IsOpenImmersion.lift_fac _ _ _

/-- The second projection of the descent datum induced on a stable open subset. -/
noncomputable def restrictQ₂ : (D.q₁ ⁻¹ᵁ U').toScheme ⟶ U' :=
  (D.X''.isoOfEq (D.preimage_q₁_eq_preimage_q₂ hU)).hom ≫ D.q₂ ∣_ U'

lemma restrictQ₂_ι : D.restrictQ₂ hU ≫ U'.ι = (D.q₁ ⁻¹ᵁ U').ι ≫ D.q₂ := by
  simp [restrictQ₂, morphismRestrict_ι]

/-- A morphism `T ⟶ X''` whose composite with `q₂` lands in `U'` factors through `q₁⁻¹(U')`. -/
private noncomputable def liftPreimage₂ {T : Scheme.{u}} (r : T ⟶ D.X'') (x : T ⟶ U')
    (hr : r ≫ D.q₂ = x ≫ U'.ι) : T ⟶ D.q₁ ⁻¹ᵁ U' :=
  IsOpenImmersion.lift (D.q₁ ⁻¹ᵁ U').ι r (by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι, D.preimage_q₁_eq_preimage_q₂ hU]
    change (r ≫ D.q₂) t ∈ U'
    rw [hr, Scheme.Hom.comp_apply]
    exact (x t).2)

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.7: the descent datum induced on an open subset `U'` of `X'` stable under the descent
datum. -/
noncomputable abbrev restrict : DescentDatum g where
  X' := U'
  a := U'.ι ≫ D.a
  X'' := D.q₁ ⁻¹ᵁ U'
  b := (D.q₁ ⁻¹ᵁ U').ι ≫ D.b
  q₁ := D.q₁ ∣_ U'
  q₂ := D.restrictQ₂ hU
  isPullback₁ := (isPullback_morphismRestrict D.q₁ U').paste_vert D.isPullback₁
  isPullback₂ := by
    refine IsPullback.paste_vert ?_ D.isPullback₂
    have := (IsPullback.of_horiz_isIso (fst := (D.X''.isoOfEq
      (D.preimage_q₁_eq_preimage_q₂ hU)).hom) (g := 𝟙 D.X'')
      ⟨by rw [Scheme.isoOfEq_hom_ι, Category.comp_id]⟩).paste_horiz
      (isPullback_morphismRestrict D.q₂ U')
    simpa [restrictQ₂] using this
  refl T x := by
    obtain ⟨r, h₁, h₂⟩ := D.refl (x ≫ U'.ι)
    refine ⟨D.liftPreimage r x h₁, ?_, ?_⟩ <;> rw [← cancel_mono U'.ι, Category.assoc]
    · rw [morphismRestrict_ι, reassoc_of% D.liftPreimage_ι r x h₁, h₁]
    · rw [D.restrictQ₂_ι hU, reassoc_of% D.liftPreimage_ι r x h₁, h₂]
  symm T r := by
    obtain ⟨r', h₁, h₂⟩ := D.symm (r ≫ (D.q₁ ⁻¹ᵁ U').ι)
    have e₁ : r' ≫ D.q₁ = (r ≫ D.restrictQ₂ hU) ≫ U'.ι := by
      rw [h₁]
      simp only [Category.assoc, D.restrictQ₂_ι hU]
    refine ⟨D.liftPreimage r' _ e₁, ?_, ?_⟩ <;> rw [← cancel_mono U'.ι, Category.assoc]
    · rw [morphismRestrict_ι, reassoc_of% D.liftPreimage_ι r' _ e₁, e₁]
    · rw [D.restrictQ₂_ι hU, reassoc_of% D.liftPreimage_ι r' _ e₁, h₂, Category.assoc,
        Category.assoc, morphismRestrict_ι]
  trans T r r' e := by
    have e' : (r ≫ (D.q₁ ⁻¹ᵁ U').ι) ≫ D.q₂ = (r' ≫ (D.q₁ ⁻¹ᵁ U').ι) ≫ D.q₁ := by
      simp only [Category.assoc, ← D.restrictQ₂_ι hU, ← morphismRestrict_ι]
      rw [← Category.assoc, ← Category.assoc, e]
    obtain ⟨r'', h₁, h₂⟩ := D.trans _ _ e'
    have e₁ : r'' ≫ D.q₁ = (r ≫ D.q₁ ∣_ U') ≫ U'.ι := by
      rw [h₁]
      simp only [Category.assoc, morphismRestrict_ι]
    refine ⟨D.liftPreimage r'' _ e₁, ?_, ?_⟩ <;> rw [← cancel_mono U'.ι, Category.assoc]
    · rw [morphismRestrict_ι, reassoc_of% D.liftPreimage_ι r'' _ e₁, e₁]
    · rw [D.restrictQ₂_ι hU, reassoc_of% D.liftPreimage_ι r'' _ e₁, h₂, Category.assoc,
        Category.assoc, D.restrictQ₂_ι hU]

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.7.2, necessity: for `g` faithfully flat and quasi-compact, if a descent datum is
effective, so is the descent datum it induces on a stable open subset. -/
theorem isEffective_restrict [Surjective g] [Flat g] [QuasiCompact g] (hD : D.IsEffective) :
    (D.restrict hU).IsEffective := by
  obtain ⟨X, f, h, hX, hq⟩ := hD
  have hh : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) h :=
    MorphismProperty.of_isPullback hX.flip ⟨⟨‹_›, ‹_›⟩, ‹_›⟩
  have : Surjective h := hh.1.1
  have : Flat h := hh.1.2
  have : QuasiCompact h := hh.2
  have hQ := D.isPullback_q₁_q₂ hX hq
  -- `U'` is the inverse image of the open subset `h(U')` of `X`.
  have hpre : h ⁻¹' (h '' U') = U' := by
    refine subset_antisymm (fun x ⟨u, hu, e⟩ ↦ ?_) (Set.subset_preimage_image _ _)
    obtain ⟨r, hr₁, hr₂⟩ := Scheme.exists_preimage_of_isPullback hQ u x e
    have : r ∈ D.q₁ ⁻¹' U' := by rw [Set.mem_preimage, hr₁]; exact hu
    rw [hU] at this
    rwa [Set.mem_preimage, hr₂] at this
  let V : X.Opens := ⟨h '' U', (isOpen_preimage_iff h).mp (by rw [hpre]; exact U'.isOpen)⟩
  have hV : h ⁻¹ᵁ V = U' := TopologicalSpace.Opens.ext hpre
  let hV' := (D.X'.isoOfEq hV).inv ≫ h ∣_ V
  have hV'ι : hV' ≫ V.ι = U'.ι ≫ h := by simp [hV', morphismRestrict_ι]
  refine ⟨V, V.ι ≫ f, hV', ?_, ?_⟩
  · refine IsPullback.paste_vert ?_ hX
    have := (IsPullback.of_horiz_isIso (fst := (D.X'.isoOfEq hV).inv) (g := 𝟙 D.X')
      ⟨by rw [Scheme.isoOfEq_inv_ι, Category.comp_id]⟩).paste_horiz
      (isPullback_morphismRestrict h V)
    rw [Category.id_comp] at this
    exact this
  · change (D.q₁ ∣_ U') ≫ hV' = D.restrictQ₂ hU ≫ hV'
    rw [← cancel_mono V.ι]
    simp only [Category.assoc, hV'ι]
    rw [← Category.assoc (D.q₁ ∣_ U'), morphismRestrict_ι, ← Category.assoc (D.restrictQ₂ hU),
      D.restrictQ₂_ι hU, Category.assoc, Category.assoc, hq]

end Restrict

/-- A solution of the descent problem posed by a descent datum: the data whose existence is
`IsEffective`. -/
structure Solution where
  /-- The descended `S`-scheme. -/
  X : Scheme.{u}
  /-- Its structure morphism. -/
  f : X ⟶ S
  /-- The morphism `X' ⟶ X`. -/
  h : D.X' ⟶ X
  isPullback : IsPullback h D.a f g
  q₁_h : D.q₁ ≫ h = D.q₂ ≫ h

lemma isEffective_iff_nonempty_solution : D.IsEffective ↔ Nonempty D.Solution :=
  ⟨fun ⟨X, f, h, hX, hq⟩ ↦ ⟨⟨X, f, h, hX, hq⟩⟩, fun ⟨s⟩ ↦ ⟨s.X, s.f, s.h, s.isPullback, s.q₁_h⟩⟩

namespace Solution

variable {D} [Surjective g] [Flat g] [QuasiCompact g]

set_option backward.isDefEq.respectTransparency false in
lemma fpqc_h (s : D.Solution) : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty _) s.h :=
  MorphismProperty.of_isPullback s.isPullback.flip ⟨⟨‹_›, ‹_›⟩, ‹_›⟩

instance (s : D.Solution) : Surjective s.h := s.fpqc_h.1.1
instance (s : D.Solution) : Flat s.h := s.fpqc_h.1.2
instance (s : D.Solution) : QuasiCompact s.h := s.fpqc_h.2

variable {D₁ D₂ : DescentDatum g} (s₁ : D₁.Solution) (s₂ : D₂.Solution) (φ : D₁.X' ⟶ D₂.X')
  (φ'' : D₁.X'' ⟶ D₂.X'') (h₁ : φ'' ≫ D₂.q₁ = D₁.q₁ ≫ φ) (h₂ : φ'' ≫ D₂.q₂ = D₁.q₂ ≫ φ)

omit [Surjective g] [Flat g] [QuasiCompact g] in
include h₁ h₂ in
lemma desc_aux {T : Scheme.{u}} (a b : T ⟶ D₁.X') (e : a ≫ s₁.h = b ≫ s₁.h) :
    a ≫ φ ≫ s₂.h = b ≫ φ ≫ s₂.h := by
  have hQ := D₁.isPullback_q₁_q₂ s₁.isPullback s₁.q₁_h
  calc a ≫ φ ≫ s₂.h = hQ.lift a b e ≫ D₁.q₁ ≫ φ ≫ s₂.h := by rw [hQ.lift_fst_assoc]
    _ = hQ.lift a b e ≫ φ'' ≫ D₂.q₁ ≫ s₂.h := by rw [reassoc_of% h₁]
    _ = hQ.lift a b e ≫ φ'' ≫ D₂.q₂ ≫ s₂.h := by rw [s₂.q₁_h]
    _ = b ≫ φ ≫ s₂.h := by rw [reassoc_of% h₂, hQ.lift_snd_assoc]

/-- A morphism of descent data between the `X'` of two solutions descends to the solutions. -/
noncomputable def desc : s₁.X ⟶ s₂.X :=
  EffectiveEpi.desc s₁.h (φ ≫ s₂.h) fun a b e ↦ s₁.desc_aux s₂ φ φ'' h₁ h₂ a b e

@[reassoc (attr := simp)]
lemma h_desc : s₁.h ≫ s₁.desc s₂ φ φ'' h₁ h₂ = φ ≫ s₂.h :=
  EffectiveEpi.fac _ _ _

end Solution

section RestrictLE

variable {W W₁ W₂ : D.X'.Opens} (hW : D.IsStable W) (hW₁ : D.IsStable W₁) (hW₂ : D.IsStable W₂)
  (hle : W₁ ≤ W₂)

lemma q₁_ι_apply (r : (D.q₁ ⁻¹ᵁ W).toScheme) : D.q₁ ((D.q₁ ⁻¹ᵁ W).ι r) = W.ι ((D.q₁ ∣_ W) r) := by
  rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]

lemma q₂_ι_apply (r : (D.q₁ ⁻¹ᵁ W).toScheme) :
    D.q₂ ((D.q₁ ⁻¹ᵁ W).ι r) = W.ι (D.restrictQ₂ hW r) := by
  rw [← Scheme.Hom.comp_apply, ← D.restrictQ₂_ι hW, Scheme.Hom.comp_apply]

include hle in
lemma preimage_q₁_le : D.q₁ ⁻¹ᵁ W₁ ≤ D.q₁ ⁻¹ᵁ W₂ := fun _ hx ↦ hle hx

@[reassoc]
lemma homOfLE_q₁ : D.X''.homOfLE (D.preimage_q₁_le hle) ≫ D.q₁ ∣_ W₂ =
    D.q₁ ∣_ W₁ ≫ D.X'.homOfLE hle := by
  rw [← cancel_mono W₂.ι]
  simp [morphismRestrict_ι]

@[reassoc]
lemma homOfLE_restrictQ₂ : D.X''.homOfLE (D.preimage_q₁_le hle) ≫ D.restrictQ₂ hW₂ =
    D.restrictQ₂ hW₁ ≫ D.X'.homOfLE hle := by
  rw [← cancel_mono W₂.ι]
  simp [restrictQ₂_ι]

variable [Surjective g] [Flat g] [QuasiCompact g]

omit [Surjective g] [Flat g] [QuasiCompact g] in
set_option backward.isDefEq.respectTransparency false in
/-- The points of `W` identified in a solution of the descent problem on `W` are related by the
descent datum, so they lie in the same stable subsets of `X'`. -/
lemma Solution.mem_of_h_eq (s : (D.restrict hW).Solution) {T : Set D.X'} (hT : D.IsStable T)
    {x y : W} (e : s.h x = s.h y) (hx : W.ι x ∈ T) : W.ι y ∈ T := by
  obtain ⟨r, hr₁, hr₂⟩ := Scheme.exists_preimage_of_isPullback
    ((D.restrict hW).isPullback_q₁_q₂ s.isPullback s.q₁_h) x y e
  have : (D.q₁ ⁻¹ᵁ W).ι r ∈ D.q₁ ⁻¹' T := by
    rw [Set.mem_preimage, q₁_ι_apply]
    exact hr₁ ▸ hx
  rw [hT, Set.mem_preimage, D.q₂_ι_apply hW] at this
  exact hr₂ ▸ this

set_option backward.isDefEq.respectTransparency false in
/-- If the descent datum induced on a stable open `W₂` is effective, so is the one induced on a
stable open `W₁ ⊆ W₂`. -/
theorem isEffective_restrict_of_le (hle : W₁ ≤ W₂) (H : (D.restrict hW₂).IsEffective) :
    (D.restrict hW₁).IsEffective := by
  obtain ⟨s⟩ := ((D.restrict hW₂).isEffective_iff_nonempty_solution).mp H
  let i := D.X'.homOfLE hle
  have hsat : s.h ⁻¹' (s.h '' Set.range i) ⊆ Set.range i := by
    rintro x ⟨_, ⟨u, rfl⟩, e⟩
    have : W₂.ι x ∈ (W₁ : Set D.X') :=
      Solution.mem_of_h_eq D hW₂ s hW₁ e (by
        rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
        exact u.2)
    refine ⟨⟨_, this⟩, W₂.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    rfl
  have hopen : IsOpen (s.h '' Set.range i) := by
    rw [← isOpen_preimage_iff s.h, subset_antisymm hsat (Set.subset_preimage_image _ _)]
    exact i.isOpenEmbedding.isOpen_range
  let V : s.X.Opens := ⟨_, hopen⟩
  have hrange : Set.range (i ≫ s.h) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rfl
  let k : (W₁ : Scheme) ⟶ V := IsOpenImmersion.lift V.ι (i ≫ s.h) hrange
  have hk : k ≫ V.ι = i ≫ s.h := IsOpenImmersion.lift_fac _ _ _
  have sq : IsPullback i k s.h V.ι :=
    isPullback_of_preimage_range_eq i k s.h V.ι hk.symm (by rw [Scheme.Opens.range_ι]; exact hsat)
  refine ⟨V, V.ι ≫ s.f, k, ?_, ?_⟩
  · have := sq.flip.paste_vert s.isPullback
    change IsPullback k (W₁.ι ≫ D.a) (V.ι ≫ s.f) g
    rwa [← D.X'.homOfLE_ι hle, Category.assoc]
  · change (D.q₁ ∣_ W₁) ≫ k = D.restrictQ₂ hW₁ ≫ k
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, hk, ← D.homOfLE_q₁_assoc hle,
      ← D.homOfLE_restrictQ₂_assoc hW₁ hW₂ hle]
    exact congrArg _ s.q₁_h

end RestrictLE

section Gluing

/-- (Implementation) The stable open subsets of `X'` on which the induced descent datum is
effective, ordered by inclusion. -/
abbrev EffOpens : Type u := {W : D.X'.Opens // ∃ hW : D.IsStable W, (D.restrict hW).IsEffective}

namespace EffOpens

variable {D} [Surjective g] [Flat g] [QuasiCompact g]

omit [Surjective g] [Flat g] [QuasiCompact g] in
lemma isStable (W : D.EffOpens) : D.IsStable W.1 := W.2.fst

/-- A chosen solution of the descent problem on `W`. -/
noncomputable def sol (W : D.EffOpens) : (D.restrict W.isStable).Solution :=
  Classical.choice (((D.restrict _).isEffective_iff_nonempty_solution).mp W.2.snd)

set_option backward.isDefEq.respectTransparency false in
/-- The morphism between the descended schemes induced by an inclusion `W₁ ⊆ W₂`. -/
noncomputable def transition {W₁ W₂ : D.EffOpens} (hle : W₁ ≤ W₂) : W₁.sol.X ⟶ W₂.sol.X :=
  W₁.sol.desc W₂.sol (D.X'.homOfLE hle) (D.X''.homOfLE (D.preimage_q₁_le hle))
    (D.homOfLE_q₁ hle) (D.homOfLE_restrictQ₂ W₁.isStable W₂.isStable hle)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma h_transition {W₁ W₂ : D.EffOpens} (hle : W₁ ≤ W₂) :
    W₁.sol.h ≫ transition hle = D.X'.homOfLE hle ≫ W₂.sol.h :=
  Solution.h_desc ..

set_option backward.isDefEq.respectTransparency false in
lemma transition_id (W : D.EffOpens) : transition (le_refl W) = 𝟙 _ := by
  rw [← cancel_epi W.sol.h, h_transition, Scheme.homOfLE_rfl, Category.id_comp,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
lemma transition_comp {W₁ W₂ W₃ : D.EffOpens} (h₁₂ : W₁ ≤ W₂) (h₂₃ : W₂ ≤ W₃) :
    transition h₁₂ ≫ transition h₂₃ = transition (h₁₂.trans h₂₃) := by
  rw [← cancel_epi W₁.sol.h, h_transition_assoc, h_transition, h_transition,
    Scheme.homOfLE_homOfLE_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma transition_f {W₁ W₂ : D.EffOpens} (hle : W₁ ≤ W₂) :
    transition hle ≫ W₂.sol.f = W₁.sol.f := by
  rw [← cancel_epi W₁.sol.h, h_transition_assoc, W₂.sol.isPullback.w, W₁.sol.isPullback.w]
  change D.X'.homOfLE hle ≫ (W₂.1.ι ≫ D.a) ≫ g = (W₁.1.ι ≫ D.a) ≫ g
  simp only [Category.assoc, Scheme.homOfLE_ι_assoc]

set_option backward.isDefEq.respectTransparency false in
lemma isPullback_transition {W₁ W₂ : D.EffOpens} (hle : W₁ ≤ W₂) :
    IsPullback (D.X'.homOfLE hle) W₁.sol.h W₂.sol.h (transition hle) := by
  refine (IsPullback.of_bot ?_ (h_transition hle) W₂.sol.isPullback).flip
  have := W₁.sol.isPullback
  change IsPullback W₁.sol.h (W₁.1.ι ≫ D.a) W₁.sol.f g at this
  change IsPullback W₁.sol.h (D.X'.homOfLE hle ≫ W₂.1.ι ≫ D.a) (transition hle ≫ W₂.sol.f) g
  rwa [Scheme.homOfLE_ι_assoc, transition_f]

set_option backward.isDefEq.respectTransparency false in
instance {W₁ W₂ : D.EffOpens} (hle : W₁ ≤ W₂) : IsOpenImmersion (transition hle) :=
  of_isPullback_of_descendsAlong (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_transition hle) W₂.sol.fpqc_h
    (inferInstanceAs (IsOpenImmersion (D.X'.homOfLE hle)))

end EffOpens

variable [Surjective g] [Flat g] [QuasiCompact g]

/-- (Implementation) The diagram of the descended schemes of the `W ∈ EffOpens`. -/
noncomputable def effDiagram : D.EffOpens ⥤ Scheme.{u} where
  obj W := W.sol.X
  map φ := EffOpens.transition (leOfHom φ)
  map_id W := EffOpens.transition_id W
  map_comp _ _ := (EffOpens.transition_comp _ _).symm

instance {W₁ W₂ : D.EffOpens} (φ : W₁ ⟶ W₂) : IsOpenImmersion (D.effDiagram.map φ) :=
  inferInstanceAs (IsOpenImmersion (EffOpens.transition _))

omit [Surjective g] [Flat g] [QuasiCompact g] in
lemma isStable_inter {T₁ T₂ : Set D.X'} (h₁ : D.IsStable T₁) (h₂ : D.IsStable T₂) :
    D.IsStable (T₁ ∩ T₂) := by
  change D.q₁ ⁻¹' (T₁ ∩ T₂) = D.q₂ ⁻¹' (T₁ ∩ T₂)
  rw [Set.preimage_inter, Set.preimage_inter, h₁, h₂]

/-- (Implementation) The intersection of two members of `EffOpens`. -/
def EffOpens.inf (W₁ W₂ : D.EffOpens) : D.EffOpens :=
  ⟨W₁.1 ⊓ W₂.1, D.isStable_inter W₁.isStable W₂.isStable,
    D.isEffective_restrict_of_le _ W₁.isStable inf_le_left W₁.2.snd⟩

lemma EffOpens.inf_le_left (W₁ W₂ : D.EffOpens) : EffOpens.inf D W₁ W₂ ≤ W₁ :=
  show W₁.1 ⊓ W₂.1 ≤ W₁.1 from _root_.inf_le_left

lemma EffOpens.inf_le_right (W₁ W₂ : D.EffOpens) : EffOpens.inf D W₁ W₂ ≤ W₂ :=
  show W₁.1 ⊓ W₂.1 ≤ W₂.1 from _root_.inf_le_right

set_option backward.isDefEq.respectTransparency false in
instance : (D.effDiagram ⋙ Scheme.forget).IsLocallyDirected where
  cond {W₁ W₂ W₃} f₁ f₂ x₁ x₂ e := by
    change EffOpens.transition (leOfHom f₁) x₁ = EffOpens.transition (leOfHom f₂) x₂ at e
    obtain ⟨w₁, rfl⟩ : ∃ w : (W₁.1 : Scheme), W₁.sol.h w = x₁ := W₁.sol.h.surjective x₁
    obtain ⟨w₂, rfl⟩ : ∃ w : (W₂.1 : Scheme), W₂.sol.h w = x₂ := W₂.sol.h.surjective x₂
    rw [← Scheme.Hom.comp_apply, EffOpens.h_transition, ← Scheme.Hom.comp_apply,
      EffOpens.h_transition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e
    have hw : W₁.1.ι w₁ ∈ W₂.1 := by
      have := Solution.mem_of_h_eq D W₃.isStable W₃.sol W₂.isStable e.symm (by
        rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
        exact w₂.2)
      rwa [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι] at this
    have hw₁ : W₁.1.ι w₁ ∈ W₁.1 := w₁.2
    let W₄ := EffOpens.inf D W₁ W₂
    have h₄₁ : W₄ ≤ W₁ := EffOpens.inf_le_left D W₁ W₂
    have h₄₂ : W₄ ≤ W₂ := EffOpens.inf_le_right D W₁ W₂
    refine ⟨W₄, homOfLE h₄₁, homOfLE h₄₂, W₄.sol.h ⟨W₁.1.ι w₁, hw₁, hw⟩, ?_, ?_⟩
    · change EffOpens.transition h₄₁ _ = _
      rw [← Scheme.Hom.comp_apply, EffOpens.h_transition, Scheme.Hom.comp_apply]
      congr 1
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · change EffOpens.transition h₄₂ _ = _
      apply (EffOpens.transition (leOfHom f₂)).isOpenEmbedding.injective
      have key : W₄.sol.h ≫ EffOpens.transition h₄₂ ≫ EffOpens.transition (leOfHom f₂) =
          D.X'.homOfLE (h₄₂.trans (leOfHom f₂)) ≫ W₃.sol.h := by
        rw [EffOpens.transition_comp, EffOpens.h_transition]
      have k₁ := congr(($key) ⟨W₁.1.ι w₁, hw₁, hw⟩)
      have k₂ := congr($(EffOpens.h_transition (leOfHom f₂)) w₂)
      simp only [Scheme.Hom.comp_apply] at k₁ k₂
      refine k₁.trans (Eq.trans ((congrArg W₃.sol.h ?_).trans e) k₂.symm)
      apply W₃.1.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
      rfl

/-- (Implementation) The scheme obtained by gluing the descended schemes. -/
noncomputable abbrev glued : Scheme.{u} := colimit D.effDiagram

/-- (Implementation) The structure morphism of the glued scheme. -/
noncomputable def gluedTo : D.glued ⟶ S :=
  colimit.desc D.effDiagram ⟨S, { app W := W.sol.f, naturality _ _ φ :=
    (EffOpens.transition_f (leOfHom φ)).trans (Category.comp_id _).symm }⟩

@[reassoc (attr := simp)]
lemma ι_gluedTo (W : D.EffOpens) : colimit.ι D.effDiagram W ≫ D.gluedTo = W.sol.f :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma homOfLE_h_ι {W₁ W₂ : D.EffOpens} (hle : W₁ ≤ W₂) :
    D.X'.homOfLE hle ≫ W₂.sol.h ≫ colimit.ι D.effDiagram W₂ =
      W₁.sol.h ≫ colimit.ι D.effDiagram W₁ := by
  rw [← EffOpens.h_transition_assoc]
  exact congrArg (W₁.sol.h ≫ ·) (colimit.w D.effDiagram (homOfLE hle))

variable (hcov : ⨆ W : D.EffOpens, W.1 = ⊤)

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) The morphism from `X'` to the glued scheme. -/
noncomputable def toGlued : D.X' ⟶ D.glued :=
  (D.X'.openCoverOfIsOpenCover (fun W : D.EffOpens ↦ W.1) hcov).glueMorphisms
    (fun W ↦ W.sol.h ≫ colimit.ι D.effDiagram W) fun W₁ W₂ ↦ by
      let W₄ := EffOpens.inf D W₁ W₂
      have hr : Set.range (pullback.fst W₁.1.ι W₂.1.ι ≫ W₁.1.ι) ⊆ Set.range W₄.1.ι := by
        rintro _ ⟨p, rfl⟩
        rw [Scheme.Opens.range_ι]
        refine ⟨?_, ?_⟩
        · rw [Scheme.Hom.comp_apply]
          exact (pullback.fst W₁.1.ι W₂.1.ι p).2
        · rw [pullback.condition, Scheme.Hom.comp_apply]
          exact (pullback.snd W₁.1.ι W₂.1.ι p).2
      let m := IsOpenImmersion.lift W₄.1.ι _ hr
      have hm : m ≫ W₄.1.ι = pullback.fst W₁.1.ι W₂.1.ι ≫ W₁.1.ι := IsOpenImmersion.lift_fac _ _ _
      have hm₁ : m ≫ D.X'.homOfLE (EffOpens.inf_le_left D W₁ W₂) = pullback.fst _ _ := by
        rw [← cancel_mono W₁.1.ι, Category.assoc, Scheme.homOfLE_ι, hm]
      have hm₂ : m ≫ D.X'.homOfLE (EffOpens.inf_le_right D W₁ W₂) = pullback.snd _ _ := by
        rw [← cancel_mono W₂.1.ι, Category.assoc, Scheme.homOfLE_ι, hm, pullback.condition]
      change pullback.fst W₁.1.ι W₂.1.ι ≫ _ = pullback.snd W₁.1.ι W₂.1.ι ≫ _
      rw [← hm₁, ← hm₂, Category.assoc, Category.assoc, homOfLE_h_ι, homOfLE_h_ι]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma ι_toGlued (W : D.EffOpens) :
    W.1.ι ≫ D.toGlued hcov = W.sol.h ≫ colimit.ι D.effDiagram W :=
  Scheme.Cover.ι_glueMorphisms (D.X'.openCoverOfIsOpenCover (fun W : D.EffOpens ↦ W.1) hcov) _ _ W

set_option backward.isDefEq.respectTransparency false in
lemma preimage_range_ι_subset (W : D.EffOpens) :
    D.toGlued hcov ⁻¹' Set.range (colimit.ι D.effDiagram W) ⊆ Set.range W.1.ι := by
  rintro x ⟨y, hy⟩
  obtain ⟨W₀, hx₀⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
  have hx := congr($(D.ι_toGlued hcov W₀) ⟨x, hx₀⟩)
  simp only [Scheme.Hom.comp_apply] at hx
  obtain ⟨W₁, f₀, f, z, hz₀, rfl⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff D.effDiagram).mp (hy.trans hx).symm
  obtain ⟨w₁, rfl⟩ : ∃ w : (W₁.1 : Scheme), W₁.sol.h w = z := W₁.sol.h.surjective z
  change EffOpens.transition (leOfHom f₀) (W₁.sol.h w₁) = _ at hz₀
  rw [← Scheme.Hom.comp_apply, EffOpens.h_transition, Scheme.Hom.comp_apply] at hz₀
  have := Solution.mem_of_h_eq D W₀.isStable W₀.sol W₁.isStable hz₀ (by
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact w₁.2)
  rw [Scheme.Opens.range_ι]
  exact leOfHom f this

set_option backward.isDefEq.respectTransparency false in
lemma isPullback_ι_toGlued (W : D.EffOpens) :
    IsPullback W.1.ι W.sol.h (D.toGlued hcov) (colimit.ι D.effDiagram W) :=
  isPullback_of_preimage_range_eq _ _ _ _ (D.ι_toGlued hcov W) (D.preimage_range_ι_subset hcov W)

include hcov in
set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.2, sufficiency: for `g` faithfully flat and quasi-compact, a descent datum is
effective as soon as `X'` is covered by stable open subsets on which the induced descent datum is
effective. The descended scheme is obtained by gluing the descended schemes of these open
subsets (and of their intersections) along open immersions. -/
theorem isEffective_of_iSup_eq_top : D.IsEffective := by
  refine ⟨D.glued, D.gluedTo, D.toGlued hcov, ?_, ?_⟩
  · refine Scheme.isPullback_of_openCover _ _ _ _
      (Scheme.IsLocallyDirected.openCover D.effDiagram) fun (W : D.EffOpens) ↦ ?_
    have sq := D.isPullback_ι_toGlued hcov W
    refine IsPullback.of_iso W.sol.isPullback sq.isoPullback (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ (by simp)
    · exact (Category.comp_id _).trans sq.isoPullback_hom_snd.symm
    · change (W.1.ι ≫ D.a) ≫ 𝟙 _ = sq.isoPullback.hom ≫ pullback.fst _ _ ≫ D.a
      rw [Category.comp_id, ← Category.assoc, sq.isoPullback_hom_fst]
    · exact (D.ι_gluedTo W).symm.trans (Category.id_comp _).symm
  · refine Scheme.Cover.hom_ext (D.X''.openCoverOfIsOpenCover (fun W : D.EffOpens ↦ D.q₁ ⁻¹ᵁ W.1)
      ?_) _ _ fun (W : D.EffOpens) ↦ ?_
    · change ⨆ W : D.EffOpens, D.q₁ ⁻¹ᵁ W.1 = ⊤
      rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
    · change (D.q₁ ⁻¹ᵁ W.1).ι ≫ D.q₁ ≫ D.toGlued hcov =
        (D.q₁ ⁻¹ᵁ W.1).ι ≫ D.q₂ ≫ D.toGlued hcov
      rw [← morphismRestrict_ι_assoc, ← reassoc_of% (D.restrictQ₂_ι W.isStable), ι_toGlued]
      exact congrArg (· ≫ colimit.ι D.effDiagram W) W.sol.q₁_h

end Gluing

section OpenCover

variable [Surjective g] [Flat g] [QuasiCompact g]

/-- VIII.7.2: for `g` faithfully flat and quasi-compact and a covering of `X'` by open subsets
stable under a descent datum, the descent datum is effective iff the induced descent data on the
members of the covering are. -/
theorem isEffective_iff_forall_isEffective_restrict {ι : Type*} (U : ι → D.X'.Opens)
    (hU : ∀ i, D.IsStable (U i)) (hU' : iSup U = ⊤) :
    D.IsEffective ↔ ∀ i, (D.restrict (hU i)).IsEffective := by
  refine ⟨fun h i ↦ D.isEffective_restrict (hU i) h, fun h ↦ D.isEffective_of_iSup_eq_top ?_⟩
  refine top_le_iff.mp fun x _ ↦ ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU'.ge (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U i, hU i, h i⟩, hi⟩

end OpenCover

set_option backward.isDefEq.respectTransparency.types false in
/-- For an open subset `V` of `S`, the inverse image of `V` in `X'` is stable under the descent
datum. -/
theorem isStable_preimage (V : S.Opens) : D.IsStable ((D.a ≫ g) ⁻¹' V) := by
  change (D.q₁ ≫ D.a ≫ g) ⁻¹' V = (D.q₂ ≫ D.a ≫ g) ⁻¹' V
  rw [D.isPullback₁.w_assoc, D.isPullback₂.w_assoc, pullback.condition]

section RestrictBase

variable (V : S.Opens)

lemma isStable_preimage_preimage : D.IsStable (D.a ⁻¹ᵁ g ⁻¹ᵁ V) := D.isStable_preimage V

set_option backward.isDefEq.respectTransparency false in
lemma restrictBase_aux :
    (D.q₁ ∣_ (D.a ⁻¹ᵁ g ⁻¹ᵁ V) ≫ D.a ∣_ (g ⁻¹ᵁ V)) ≫ g ∣_ V =
      (D.restrictQ₂ (D.isStable_preimage_preimage V) ≫ D.a ∣_ (g ⁻¹ᵁ V)) ≫ g ∣_ V := by
  rw [← cancel_mono V.ι]
  simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc]
  rw [reassoc_of% (D.restrictQ₂_ι (D.isStable_preimage_preimage V)), D.isPullback₁.w_assoc,
    D.isPullback₂.w_assoc, pullback.condition]

set_option backward.isDefEq.respectTransparency false in
lemma restrictBase_b_ι :
    pullback.lift _ _ (D.restrictBase_aux V) ≫ pullbackRestrictι g V =
      (D.q₁ ⁻¹ᵁ (D.a ⁻¹ᵁ g ⁻¹ᵁ V)).ι ≫ D.b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackRestrictι_fst, pullback.lift_fst_assoc,
      morphismRestrict_ι, morphismRestrict_ι_assoc]
    rw [D.isPullback₁.w]
  · simp only [Category.assoc, pullbackRestrictι_snd, pullback.lift_snd_assoc,
      morphismRestrict_ι]
    rw [reassoc_of% (D.restrictQ₂_ι (D.isStable_preimage_preimage V)), D.isPullback₂.w]

set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.3: for an open subset `V` of `S`, the descent datum relative to `g⁻¹(V) ⟶ V` induced
by `D` on the inverse image `X'_V` of `V` in `X'`. -/
noncomputable abbrev restrictBase : DescentDatum (g ∣_ V) where
  X' := D.a ⁻¹ᵁ g ⁻¹ᵁ V
  a := D.a ∣_ (g ⁻¹ᵁ V)
  X'' := D.q₁ ⁻¹ᵁ (D.a ⁻¹ᵁ g ⁻¹ᵁ V)
  b := pullback.lift _ _ (D.restrictBase_aux V)
  q₁ := D.q₁ ∣_ (D.a ⁻¹ᵁ g ⁻¹ᵁ V)
  q₂ := D.restrictQ₂ (D.isStable_preimage_preimage V)
  isPullback₁ := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (isPullback_pullbackRestrictι_fst g V).flip
    rw [D.restrictBase_b_ι, morphismRestrict_ι]
    exact (D.restrict (D.isStable_preimage_preimage V)).isPullback₁
  isPullback₂ := by
    refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm
      (isPullback_pullbackRestrictι_snd g V).flip
    rw [D.restrictBase_b_ι, morphismRestrict_ι]
    exact (D.restrict (D.isStable_preimage_preimage V)).isPullback₂
  refl := (D.restrict (D.isStable_preimage_preimage V)).refl
  symm := (D.restrict (D.isStable_preimage_preimage V)).symm
  trans := (D.restrict (D.isStable_preimage_preimage V)).trans

omit D in
set_option backward.isDefEq.respectTransparency false in
lemma isPullback_comp_ι_iff {W X : Scheme.{u}} (h : W ⟶ X) (aV : W ⟶ g ⁻¹ᵁ V) (fV : X ⟶ V) :
    IsPullback h (aV ≫ (g ⁻¹ᵁ V).ι) (fV ≫ V.ι) g ↔ IsPullback h aV fV (g ∣_ V) := by
  refine ⟨fun H ↦ IsPullback.of_bot H ?_ (isPullback_morphismRestrict g V), fun H ↦ ?_⟩
  · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, H.w,
      Category.assoc]
  · exact H.paste_vert (isPullback_morphismRestrict g V)

set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.3: the descent datum induced on `X'_V` is effective relative to `g` iff it is
effective relative to `g⁻¹(V) ⟶ V`. -/
theorem isEffective_restrict_iff_isEffective_restrictBase [Surjective g] :
    (D.restrict (D.isStable_preimage_preimage V)).IsEffective ↔
      (D.restrictBase V).IsEffective := by
  constructor
  · rintro ⟨X, f, h, hX, hq⟩
    have : Surjective h := MorphismProperty.of_isPullback hX.flip ‹_›
    have hf : Set.range f ⊆ Set.range V.ι := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨w, rfl⟩ := h.surjective x
      rw [Scheme.Opens.range_ι, ← Scheme.Hom.comp_apply, hX.w]
      exact w.2
    refine ⟨X, IsOpenImmersion.lift V.ι f hf, h, (isPullback_comp_ι_iff V _ _ _).mp ?_, hq⟩
    rwa [IsOpenImmersion.lift_fac, morphismRestrict_ι]
  · rintro ⟨X, f, h, hX, hq⟩
    refine ⟨X, f ≫ V.ι, h, ?_, hq⟩
    have := (isPullback_comp_ι_iff V _ _ _).mpr hX
    rwa [morphismRestrict_ι] at this

end RestrictBase

/-- VIII.7.3: for `g` faithfully flat and quasi-compact and an open covering `(Sᵢ)` of `S`, a
descent datum is effective iff, for every `i`, the descent datum it induces on the inverse image
`X'ᵢ` of `Sᵢ`, relative to `gᵢ : S'ᵢ = g⁻¹(Sᵢ) ⟶ Sᵢ`, is effective. -/
theorem isEffective_iff_forall_isEffective_restrictBase [Surjective g] [Flat g]
    [QuasiCompact g] {ι : Type*} (V : ι → S.Opens) (hV : iSup V = ⊤) :
    D.IsEffective ↔ ∀ i, (D.restrictBase (V i)).IsEffective := by
  rw [D.isEffective_iff_forall_isEffective_restrict (fun i ↦ D.a ⁻¹ᵁ g ⁻¹ᵁ V i)
    (fun i ↦ D.isStable_preimage_preimage (V i))]
  · exact forall_congr' fun i ↦ D.isEffective_restrict_iff_isEffective_restrictBase (V i)
  · rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, hV, Scheme.Hom.preimage_top,
      Scheme.Hom.preimage_top]

/-- VIII.7.3, with the induced descent data taken relative to `g`: for `g` faithfully flat and
quasi-compact and an open covering `(Sᵢ)` of `S`, a descent datum is effective iff the descent
data it induces on the inverse images `X'ᵢ` of the `Sᵢ` are. -/
theorem isEffective_iff_of_iSup_eq_top [Surjective g] [Flat g] [QuasiCompact g] {ι : Type*}
    (V : ι → S.Opens) (hV : iSup V = ⊤) :
    D.IsEffective ↔ ∀ i, (D.restrict (D.isStable_preimage_preimage (V i))).IsEffective :=
  (D.isEffective_iff_forall_isEffective_restrictBase V hV).trans
    (forall_congr' fun i ↦ (D.isEffective_restrict_iff_isEffective_restrictBase (V i)).symm)

set_option backward.isDefEq.respectTransparency false in
/-- VIII.2.1, in the form of VIII.7: a faithfully flat quasi-compact morphism `g : S' ⟶ S` is an
effective descent morphism for affine morphisms, i.e. every descent datum on an `X'` affine over
`S'` is effective. For affine `S` this is `exists_isPullback_of_isAffineHom_of_isAffine`
(`SGA.SGA1.ExposeVIII.AffineSchemeDescent`); the general case follows by VIII.7.3. -/
theorem isEffective_of_isAffineHom [Surjective g] [Flat g] [QuasiCompact g] [IsAffineHom D.a] :
    D.IsEffective := by
  refine (D.isEffective_iff_forall_isEffective_restrictBase (fun V : S.affineOpens ↦ V.1)
    (iSup_affineOpens_eq_top S)).mpr fun V ↦ ?_
  have : IsAffine V.1 := V.2
  have : IsAffineHom (D.restrictBase V.1).a := IsZariskiLocalAtTarget.restrict ‹_› _
  have : Flat (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : Surjective (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : QuasiCompact (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  let E := D.restrictBase V.1
  exact exists_isPullback_of_isAffineHom_of_isAffine _ E.a E.b E.q₁ E.q₂ E.isPullback₁
    E.isPullback₂ E.refl E.trans

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.7.4, necessity: if `S` and `S'` are affine and the descent datum is effective, `X'` is
covered by affine open subsets stable under the descent datum (the inverse images of the affine
open subsets of the descended scheme). -/
theorem exists_isAffineOpen_isStable_of_isEffective [IsAffine S] [IsAffine S']
    (hD : D.IsEffective) (x : D.X') :
    ∃ U : D.X'.Opens, x ∈ U ∧ IsAffineOpen U ∧ D.IsStable U := by
  obtain ⟨X, f, h, hX, hq⟩ := hD
  have : IsAffineHom h := MorphismProperty.of_isPullback hX.flip inferInstance
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (h x)) isOpen_univ
  refine ⟨h ⁻¹ᵁ V, hxV, hV.preimage h, ?_⟩
  change (D.q₁ ≫ h) ⁻¹' V = (D.q₂ ≫ h) ⁻¹' V
  rw [hq]

/-- By reflexivity, `q₁` and `q₂` have a common section `X' ⟶ X''`. -/
lemma exists_section_q₁_q₂ : ∃ e : D.X' ⟶ D.X'', ∀ x, D.q₁ (e x) = x ∧ D.q₂ (e x) = x := by
  obtain ⟨e, he₁, he₂⟩ := D.refl (𝟙 D.X')
  refine ⟨e, fun x ↦ ⟨?_, ?_⟩⟩
  · simpa using congrArg (fun φ : D.X' ⟶ D.X' ↦ φ x) he₁
  · simpa using congrArg (fun φ : D.X' ⟶ D.X' ↦ φ x) he₂

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.7.5, the key step: if `g` is radicial, then `q₁` and `q₂` agree on points, so every
class `R(x')` is a point and every subset of `X'` is stable under the descent datum. -/
theorem q₁_apply_eq_q₂_apply [UniversallyInjective g] (r : D.X'') : D.q₁ r = D.q₂ r := by
  have : UniversallyInjective D.q₁ := MorphismProperty.of_isPullback D.isPullback₁.flip
    (MorphismProperty.pullback_fst (P := @UniversallyInjective) g g ‹_›)
  obtain ⟨e, he⟩ := D.exists_section_q₁_q₂
  have : r = e (D.q₁ r) := D.q₁.injective (he _).1.symm
  rw [this, (he _).1, (he _).2]

/-- VIII.7.5: if `g` is radicial, every subset of `X'` is stable under the descent datum. -/
theorem isStable_of_universallyInjective [UniversallyInjective g] (U' : Set D.X') :
    D.IsStable U' := by
  ext r
  simp [D.q₁_apply_eq_q₂_apply r]

/-- VIII.7.5: if `g` is radicial, the class `R(x')` of every point is `{x'}`. -/
theorem orbit_eq_singleton [UniversallyInjective g] (x : D.X') : D.orbit x = {x} := by
  ext y
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨r, hr, rfl⟩
    rw [← D.q₁_apply_eq_q₂_apply r]
    exact hr
  · obtain ⟨e, he⟩ := D.exists_section_q₁_q₂
    rw [Set.mem_singleton_iff] at hy
    exact ⟨e x, (he x).1, hy ▸ (he x).2⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.7.6, remark in the proof: for `g` finite, the class `R(x')` of every point is finite. -/
theorem orbit_finite [IsFinite g] (x : D.X') : (D.orbit x).Finite := by
  have : IsFinite D.q₁ := MorphismProperty.of_isPullback D.isPullback₁.flip
    (MorphismProperty.pullback_fst (P := @IsFinite) g g ‹_›)
  exact (D.q₁.finite_preimage_singleton x).image _

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.7.6, necessity: if `g` is finite and the descent datum is effective, the class `R(x')`
of every point is contained in an affine open subset of `X'`. -/
theorem exists_isAffineOpen_orbit_subset_of_isEffective [IsFinite g] (hD : D.IsEffective)
    (x : D.X') : ∃ U : D.X'.Opens, IsAffineOpen U ∧ D.orbit x ⊆ U := by
  obtain ⟨X, f, h, hX, hq⟩ := hD
  have : IsAffineHom h := MorphismProperty.of_isPullback hX.flip inferInstance
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (h x)) isOpen_univ
  refine ⟨h ⁻¹ᵁ V, hV.preimage h, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  change h (D.q₂ r) ∈ V
  rw [← Scheme.Hom.comp_apply, ← hq, Scheme.Hom.comp_apply, show D.q₁ r = x from hr]
  exact hxV

/-- VIII.2.1, restated for `DescentDatum`: a faithfully flat quasi-compact morphism is an
effective descent morphism for affine morphisms. Proved by `isEffectiveOfIsAffineHomStatement`. -/
def IsEffectiveOfIsAffineHomStatement : Prop :=
  ∀ ⦃S S' : Scheme.{u}⦄ (g : S' ⟶ S) [Surjective g] [Flat g] [QuasiCompact g]
    (D : DescentDatum g), IsAffineHom D.a → D.IsEffective

/-- VIII.2.1, restated for `DescentDatum` (see `isEffective_of_isAffineHom`). -/
theorem isEffectiveOfIsAffineHomStatement : IsEffectiveOfIsAffineHomStatement.{u} :=
  fun _ _ _ _ _ _ D _ ↦ D.isEffective_of_isAffineHom

/-- VIII.7.4, sufficiency: for `S`, `S'` affine and `g` faithfully flat, a descent datum is
effective if `X'` is covered by affine open subsets stable under it. As in SGA, this follows from
VIII.7.2 and VIII.2.1. -/
theorem isEffective_of_forall_exists_isAffineOpen_isStable [IsAffine S] [IsAffine S']
    [Surjective g] [Flat g]
    (H : ∀ x : D.X', ∃ U : D.X'.Opens, x ∈ U ∧ IsAffineOpen U ∧ D.IsStable U) :
    D.IsEffective := by
  have : IsAffineHom g := isAffineHom_of_isAffine g
  choose U hxU hUa hUs using H
  refine (D.isEffective_iff_forall_isEffective_restrict U hUs ?_).mpr fun x ↦ ?_
  · exact top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩
  · have : IsAffine (D.restrict (hUs x)).X' := hUa x
    have : IsAffineHom (D.restrict (hUs x)).a := isAffineHom_of_isAffine _
    exact (D.restrict (hUs x)).isEffective_of_isAffineHom

/-- VIII.7.4: for `S`, `S'` affine and `g` faithfully flat, a descent datum is effective iff `X'`
is covered by affine open subsets stable under it. -/
theorem isEffective_iff_forall_exists_isAffineOpen_isStable [IsAffine S] [IsAffine S']
    [Surjective g] [Flat g] :
    D.IsEffective ↔ ∀ x : D.X', ∃ U : D.X'.Opens, x ∈ U ∧ IsAffineOpen U ∧ D.IsStable U :=
  ⟨D.exists_isAffineOpen_isStable_of_isEffective,
    D.isEffective_of_forall_exists_isAffineOpen_isStable⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.7.5 over an affine base: if `S` is affine and `g : S' ⟶ S` is faithfully flat,
quasi-compact and radicial, every descent datum relative to `g` is effective. As in SGA: every
open subset of `X'` is stable, `S'` is separated, so the affine open subsets of `X'` are affine
over `S'`, and one concludes by VIII.2.1 and VIII.7.2. -/
theorem isEffective_of_universallyInjective_of_isAffine [IsAffine S] [Surjective g] [Flat g]
    [QuasiCompact g] [UniversallyInjective g] : D.IsEffective := by
  have : IsSeparated g := isSeparated_of_injective g g.injective
  have : IsSeparated (terminal.from S') := by
    rw [← terminal.comp_from g]
    infer_instance
  have H : ∀ x : D.X', ∃ U : D.X'.Opens, x ∈ U ∧ IsAffineOpen U := fun x ↦ by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      D.X'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hxV, hV⟩
  choose U hxU hUa using H
  refine (D.isEffective_iff_forall_isEffective_restrict U
    (fun x ↦ D.isStable_of_universallyInjective _) ?_).mpr fun x ↦ ?_
  · exact top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩
  · let D' := D.restrict (D.isStable_of_universallyInjective (U x))
    have : IsAffine D'.X' := hUa x
    have : IsAffineHom (D'.a ≫ terminal.from S') := by
      rw [terminal.comp_from]
      infer_instance
    have : IsAffineHom D'.a := IsAffineHom.of_comp _ (terminal.from S')
    exact D'.isEffective_of_isAffineHom

set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.5: a faithfully flat, quasi-compact and radicial morphism `g` is an effective descent
morphism: every descent datum relative to `g` is effective. As in SGA, VIII.7.3 reduces this to
an affine base (`isEffective_of_universallyInjective_of_isAffine`). -/
theorem isEffective_of_universallyInjective [Surjective g] [Flat g] [QuasiCompact g]
    [UniversallyInjective g] : D.IsEffective := by
  refine (D.isEffective_iff_forall_isEffective_restrictBase (fun V : S.affineOpens ↦ V.1)
    (iSup_affineOpens_eq_top S)).mpr fun V ↦ ?_
  have : IsAffine V.1 := V.2
  have : Flat (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : Surjective (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : QuasiCompact (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : UniversallyInjective (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  exact (D.restrictBase V.1).isEffective_of_universallyInjective_of_isAffine

set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.9 for `S` and `S'` affine and `X'` quasi-affine. -/
theorem isEffective_of_isQuasiAffine_of_isAffine [IsAffine S] [IsAffine S'] [Flat g]
    [Surjective g] [D.X'.IsQuasiAffine] : D.IsEffective := by
  have hg : g.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp ⟨‹_›, ‹_›⟩
  have hP := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback g g)
  have : QuasiCompact D.a := (quasiCompact_iff_compactSpace D.a).mpr inferInstance
  have : IsQuasiAffineHom D.a := isQuasiAffineHom_of_isQuasiAffine D.a
  have : IsQuasiAffineHom D.b := MorphismProperty.of_isPullback D.isPullback₁ ‹_›
  have : D.X''.IsQuasiAffine := isQuasiAffine_of_isQuasiAffineHom D.b
  have hR₁ := isPushout_appTop_of_isPullback_of_flat D.isPullback₁
  have hR₂ := isPushout_appTop_of_isPullback_of_flat D.isPullback₂
  obtain ⟨r, hr₁, hr₂⟩ := D.refl (𝟙 D.X')
  have hδ₁ : D.q₁.appTop ≫ r.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hr₁]; rfl
  have hδ₂ : D.q₂.appTop ≫ r.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hr₂]; rfl
  obtain ⟨r'', hr''₁, hr''₂⟩ :=
    D.trans (pullback.fst D.q₂ D.q₁) (pullback.snd D.q₂ D.q₁) pullback.condition
  have hT : IsPullback (pullback.fst D.q₂ D.q₁) (pullback.snd D.q₂ D.q₁ ≫ D.b) (D.q₂ ≫ D.a)
      (pullback.fst g g) := (IsPullback.of_hasPullback D.q₂ D.q₁).paste_vert D.isPullback₁
  have hT' := isPushout_appTop_of_isPullback_of_flat hT
  simp only [Scheme.Hom.comp_appTop] at hT'
  have hQ : IsPushout D.q₂.appTop D.q₁.appTop (pullback.fst D.q₂ D.q₁).appTop
      (pullback.snd D.q₂ D.q₁).appTop := by
    refine hT'.of_left ?_ hR₁
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, pullback.condition]
  have hτ₁ : D.q₁.appTop ≫ r''.appTop = D.q₁.appTop ≫ (pullback.fst D.q₂ D.q₁).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hr''₁]
  have hτ₂ : D.q₂.appTop ≫ r''.appTop = D.q₂.appTop ≫ (pullback.snd D.q₂ D.q₁).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hr''₂]
  have hpush := isPushout_eqLocus_of_descent g.appTop hg D.a.appTop _ _ hP D.b.appTop
    D.q₁.appTop D.q₂.appTop hR₁.w hR₂ r.appTop hδ₁ hδ₂ _ _ hQ r''.appTop hτ₁ hτ₂
  -- the descended ring `C₀ = {x | q₁^* x = q₂^* x}` and `ι : C₀ ⟶ C = Γ(X')`
  set ι : CommRingCat.of (D.q₁.appTop.hom.eqLocus D.q₂.appTop.hom) ⟶ Γ(D.X', ⊤) :=
    CommRingCat.ofHom (D.q₁.appTop.hom.eqLocus D.q₂.appTop.hom).subtype with hι
  set ι₀ := CommRingCat.ofHom ((g.appTop ≫ D.a.appTop).hom.codRestrict _
    (comp_mem_eqLocus _ _ _ _ _ _ _ hP hR₁.w hR₂)) with hι₀
  have hιq : ι ≫ D.q₁.appTop = ι ≫ D.q₂.appTop := by
    ext x
    exact x.2
  -- `Spec C` is the base change of `Spec C₀` and its fibered square is `Spec Γ(X'')`
  have hker : IsPushout ι ι D.q₁.appTop D.q₂.appTop := by
    refine (IsPushout.of_left ?_ hιq.symm hpush.flip).flip
    rw [← hpush.w, hR₁.w]
    exact hP.flip.paste_horiz hR₂
  have hK := isPullback_SpecMap_of_isPushout _ _ _ _ hker
  have sqS := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  have hψ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (Spec.map ι) :=
    MorphismProperty.of_isPullback sqS ((arrow_mk_iso_iff
      (P := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}))
      (arrowIsoSpecΓOfIsAffine g)).mp ⟨⟨‹_›, ‹_›⟩, inferInstance⟩)
  have : Surjective (Spec.map ι) := hψ.1.1
  have : Flat (Spec.map ι) := hψ.1.2
  have : QuasiCompact (Spec.map ι) := hψ.2
  have hX''₁ := isPullback_toSpecΓ_of_isPullback_of_flat D.isPullback₁
  -- `X'` is saturated for the equivalence relation defined by `Spec C ⟶ Spec C₀`
  have hsat : Spec.map ι ⁻¹' (Spec.map ι '' Set.range D.X'.toSpecΓ) ⊆
      Set.range D.X'.toSpecΓ := by
    rintro z ⟨_, ⟨x, rfl⟩, e⟩
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.exists_preimage_of_isPullback hK _ z e
    obtain ⟨p, hp₁, hp₂⟩ := Scheme.exists_preimage_of_isPullback hX''₁ x w hw₁.symm
    refine ⟨D.q₂ p, ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.toSpecΓ_naturality, Scheme.Hom.comp_apply, hp₂, hw₂]
  have hopen : IsOpen (Spec.map ι '' Set.range D.X'.toSpecΓ) := by
    rw [← isOpen_preimage_iff (Spec.map ι),
      subset_antisymm hsat (Set.subset_preimage_image _ _)]
    exact D.X'.toSpecΓ.isOpenEmbedding.isOpen_range
  let V : (Spec (CommRingCat.of (D.q₁.appTop.hom.eqLocus D.q₂.appTop.hom))).Opens := ⟨_, hopen⟩
  have hrange : Set.range (D.X'.toSpecΓ ≫ Spec.map ι) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rfl
  let k : D.X' ⟶ V := IsOpenImmersion.lift V.ι _ hrange
  have hk : k ≫ V.ι = D.X'.toSpecΓ ≫ Spec.map ι := IsOpenImmersion.lift_fac _ _ _
  have sq₁ : IsPullback D.X'.toSpecΓ k (Spec.map ι) V.ι :=
    isPullback_of_preimage_range_eq _ _ _ _ hk.symm (by rw [Scheme.Opens.range_ι]; exact hsat)
  have sq₂ : IsPullback (Spec.map ι) (Spec.map D.a.appTop ≫ S'.isoSpec.inv)
      (Spec.map ι₀ ≫ S.isoSpec.inv) g :=
    sqS.flip.of_iso (Iso.refl _) (Iso.refl _) S'.isoSpec.symm S.isoSpec.symm (by simp)
      (by simp) (by simp) (by simp [Scheme.isoSpec_inv_naturality])
  refine ⟨V, V.ι ≫ Spec.map ι₀ ≫ S.isoSpec.inv, k, ?_, ?_⟩
  · have := sq₁.flip.paste_vert sq₂
    rwa [← Category.assoc D.X'.toSpecΓ, ← Scheme.toSpecΓ_naturality, Category.assoc,
      ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id] at this
  · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, hk, Scheme.toSpecΓ_naturality_assoc,
      Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp, ← Spec.map_comp, hιq]

section PullbackBase

variable {S₁ : Scheme.{u}} (π : S₁ ⟶ S')

/-- The morphism `S₁ ×_S S₁ ⟶ S' ×_S S'` induced by `π : S₁ ⟶ S'`. -/
noncomputable abbrev pullbackBaseπ'' : pullback (π ≫ g) (π ≫ g) ⟶ pullback g g :=
  pullback.map _ _ g g π π (𝟙 S) (by simp) (by simp)

lemma pullbackBaseπ''_fst :
    pullbackBaseπ'' π ≫ pullback.fst g g = pullback.fst (π ≫ g) (π ≫ g) ≫ π :=
  pullback.lift_fst _ _ _

lemma pullbackBaseπ''_snd :
    pullbackBaseπ'' π ≫ pullback.snd g g = pullback.snd (π ≫ g) (π ≫ g) ≫ π :=
  pullback.lift_snd _ _ _

/-- The first projection of the pulled back descent datum. -/
noncomputable abbrev pullbackBaseQ₁ : pullback D.b (pullbackBaseπ'' π) ⟶ pullback D.a π :=
  pullback.lift (pullback.fst D.b _ ≫ D.q₁) (pullback.snd D.b _ ≫ pullback.fst (π ≫ g) (π ≫ g))
    (by rw [Category.assoc, Category.assoc, D.isPullback₁.w, pullback.condition_assoc,
      pullbackBaseπ''_fst])

/-- The second projection of the pulled back descent datum. -/
noncomputable abbrev pullbackBaseQ₂ : pullback D.b (pullbackBaseπ'' π) ⟶ pullback D.a π :=
  pullback.lift (pullback.fst D.b _ ≫ D.q₂) (pullback.snd D.b _ ≫ pullback.snd (π ≫ g) (π ≫ g))
    (by rw [Category.assoc, Category.assoc, D.isPullback₂.w, pullback.condition_assoc,
      pullbackBaseπ''_snd])

set_option backward.isDefEq.respectTransparency false in
/-- The descent datum relative to `π ≫ g` obtained by pulling back `D` along `π : S₁ ⟶ S'`: it
lives on `X' ×_{S'} S₁`. -/
noncomputable def pullbackBase : DescentDatum (π ≫ g) where
  X' := pullback D.a π
  a := pullback.snd D.a π
  X'' := pullback D.b (pullbackBaseπ'' π)
  b := pullback.snd D.b (pullbackBaseπ'' π)
  q₁ := D.pullbackBaseQ₁ π
  q₂ := D.pullbackBaseQ₂ π
  isPullback₁ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback D.a π)
    rw [pullback.lift_fst, ← pullbackBaseπ''_fst]
    exact (IsPullback.of_hasPullback D.b _).paste_horiz D.isPullback₁
  isPullback₂ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback D.a π)
    rw [pullback.lift_fst, ← pullbackBaseπ''_snd]
    exact (IsPullback.of_hasPullback D.b _).paste_horiz D.isPullback₂
  refl T x := by
    obtain ⟨r', hr'₁, hr'₂⟩ := D.refl (x ≫ pullback.fst D.a π)
    let σ : T ⟶ pullback (π ≫ g) (π ≫ g) :=
      pullback.lift (x ≫ pullback.snd D.a π) (x ≫ pullback.snd D.a π) rfl
    have hσ : r' ≫ D.b = σ ≫ pullbackBaseπ'' π := by
      apply pullback.hom_ext
      · rw [Category.assoc, ← D.isPullback₁.w, reassoc_of% hr'₁, Category.assoc,
          pullbackBaseπ''_fst, pullback.lift_fst_assoc, Category.assoc, pullback.condition]
      · rw [Category.assoc, ← D.isPullback₂.w, reassoc_of% hr'₂, Category.assoc,
          pullbackBaseπ''_snd, pullback.lift_snd_assoc, Category.assoc, pullback.condition]
    refine ⟨pullback.lift r' σ hσ, ?_, ?_⟩ <;> apply pullback.hom_ext <;> simp [σ, hr'₁, hr'₂]
  symm T r := by
    obtain ⟨ρ, hρ₁, hρ₂⟩ := D.symm (r ≫ pullback.fst D.b _)
    let σ : T ⟶ pullback (π ≫ g) (π ≫ g) :=
      pullback.lift (r ≫ pullback.snd D.b _ ≫ pullback.snd (π ≫ g) (π ≫ g))
        (r ≫ pullback.snd D.b _ ≫ pullback.fst (π ≫ g) (π ≫ g))
        (by simp only [Category.assoc]; rw [pullback.condition])
    have hσ : ρ ≫ D.b = σ ≫ pullbackBaseπ'' π := by
      apply pullback.hom_ext
      · rw [Category.assoc, ← D.isPullback₁.w, reassoc_of% hρ₁, Category.assoc,
          D.isPullback₂.w, pullback.condition_assoc, pullbackBaseπ''_snd,
          pullbackBaseπ''_fst, pullback.lift_fst_assoc]
        simp only [Category.assoc]
      · rw [Category.assoc, ← D.isPullback₂.w, reassoc_of% hρ₂, Category.assoc,
          D.isPullback₁.w, pullback.condition_assoc, pullbackBaseπ''_fst,
          pullbackBaseπ''_snd, pullback.lift_snd_assoc]
        simp only [Category.assoc]
    refine ⟨pullback.lift ρ σ hσ, ?_, ?_⟩ <;> apply pullback.hom_ext <;> simp [σ, hρ₁, hρ₂]
  trans T r r' hrr := by
    have hρ : (r ≫ pullback.fst D.b _) ≫ D.q₂ = (r' ≫ pullback.fst D.b _) ≫ D.q₁ := by
      simpa using congr($hrr ≫ pullback.fst D.a π)
    obtain ⟨ρ'', hρ₁, hρ₂⟩ := D.trans _ _ hρ
    have hmid : r ≫ pullback.snd D.b _ ≫ pullback.snd (π ≫ g) (π ≫ g) =
        r' ≫ pullback.snd D.b _ ≫ pullback.fst (π ≫ g) (π ≫ g) := by
      simpa using congr($hrr ≫ pullback.snd D.a π)
    let σ : T ⟶ pullback (π ≫ g) (π ≫ g) :=
      pullback.lift (r ≫ pullback.snd D.b _ ≫ pullback.fst (π ≫ g) (π ≫ g))
        (r' ≫ pullback.snd D.b _ ≫ pullback.snd (π ≫ g) (π ≫ g)) (by
          simp only [Category.assoc]
          rw [pullback.condition, reassoc_of% hmid, pullback.condition])
    have hσ : ρ'' ≫ D.b = σ ≫ pullbackBaseπ'' π := by
      apply pullback.hom_ext
      · rw [Category.assoc, ← D.isPullback₁.w, reassoc_of% hρ₁, Category.assoc,
          D.isPullback₁.w, pullback.condition_assoc, pullbackBaseπ''_fst,
          pullback.lift_fst_assoc]
        simp only [Category.assoc]
      · rw [Category.assoc, ← D.isPullback₂.w, reassoc_of% hρ₂, Category.assoc,
          D.isPullback₂.w, pullback.condition_assoc, pullbackBaseπ''_snd,
          pullback.lift_snd_assoc]
        simp only [Category.assoc]
    refine ⟨pullback.lift ρ'' σ hσ, ?_, ?_⟩ <;> apply pullback.hom_ext <;> simp [σ, hρ₁, hρ₂]

set_option backward.isDefEq.respectTransparency false in
/-- If the descent datum pulled back along a surjective flat morphism `π : S₁ ⟶ S'` locally of
finite presentation is effective (relative to `π ≫ g`), then `D` is effective. The argument is
the one of `exists_isPullback_of_isAffineHom_of_isAffine`. -/
theorem isEffective_of_isEffective_pullbackBase [Surjective π] [Flat π]
    [LocallyOfFinitePresentation π] (H : (D.pullbackBase π).IsEffective) : D.IsEffective := by
  obtain ⟨X, f, h₁X, hpb, hq⟩ := H
  change IsPullback h₁X (pullback.snd D.a π) f (π ≫ g) at hpb
  change D.pullbackBaseQ₁ π ≫ h₁X = D.pullbackBaseQ₂ π ≫ h₁X at hq
  have hX₁ : IsPullback (pullback.fst D.a π) (pullback.snd D.a π) D.a π :=
    IsPullback.of_hasPullback D.a π
  -- `h₁X` factors through the fppf covering `X' ×_{S'} S₁ ⟶ X'`
  have hdesc : ∀ {T : Scheme.{u}} (u v : T ⟶ pullback D.a π),
      u ≫ pullback.fst D.a π = v ≫ pullback.fst D.a π → u ≫ h₁X = v ≫ h₁X := by
    intro T u v huv
    obtain ⟨r, hr₁, hr₂⟩ := D.refl (u ≫ pullback.fst D.a π)
    let σ : T ⟶ pullback (π ≫ g) (π ≫ g) :=
      pullback.lift (u ≫ pullback.snd D.a π) (v ≫ pullback.snd D.a π) (by
        simp only [Category.assoc]
        rw [← hX₁.w_assoc, reassoc_of% huv, hX₁.w_assoc])
    have hσ : r ≫ D.b = σ ≫ pullbackBaseπ'' π := by
      apply pullback.hom_ext
      · rw [Category.assoc, ← D.isPullback₁.w, reassoc_of% hr₁, Category.assoc,
          pullbackBaseπ''_fst, pullback.lift_fst_assoc, Category.assoc, hX₁.w]
      · rw [Category.assoc, ← D.isPullback₂.w, reassoc_of% hr₂, Category.assoc,
          pullbackBaseπ''_snd, pullback.lift_snd_assoc, Category.assoc, reassoc_of% huv, hX₁.w]
    have hw₁ : pullback.lift r σ hσ ≫ D.pullbackBaseQ₁ π = u := by
      apply pullback.hom_ext <;> simp [σ, hr₁]
    have hw₂ : pullback.lift r σ hσ ≫ D.pullbackBaseQ₂ π = v := by
      apply pullback.hom_ext <;> simp [σ, hr₂, huv]
    rw [← hw₁, ← hw₂, Category.assoc, Category.assoc, hq]
  let h : D.X' ⟶ X := EffectiveEpi.desc (pullback.fst D.a π) h₁X hdesc
  have hfac : pullback.fst D.a π ≫ h = h₁X := EffectiveEpi.fac _ _ _
  have w : h ≫ f = D.a ≫ g := by
    rw [← cancel_epi (pullback.fst D.a π), reassoc_of% hfac, hpb.w, hX₁.w_assoc]
  refine ⟨X, f, h, ?_, ?_⟩
  · -- the comparison map `X' ⟶ X ×_S S'` is an isomorphism, since it is one after the fppf
    -- base change `S₁ ⟶ S'`
    let c : D.X' ⟶ pullback f g := pullback.lift h D.a w
    have hY₁ : IsPullback (pullback.fst (pullback.snd f g) π ≫ pullback.fst f g)
        (pullback.snd (pullback.snd f g) π) f (π ≫ g) :=
      (IsPullback.of_hasPullback (pullback.snd f g) π).paste_horiz (IsPullback.of_hasPullback f g)
    let c₁ : pullback D.a π ⟶ pullback (pullback.snd f g) π :=
      pullback.lift (pullback.fst D.a π ≫ c) (pullback.snd D.a π) (by
        rw [Category.assoc, pullback.lift_snd, hX₁.w])
    have hc₁ : c₁ = (hpb.isoIsPullback _ _ hY₁).hom := by
      apply hY₁.hom_ext
      · rw [IsPullback.isoIsPullback_hom_fst, pullback.lift_fst_assoc, Category.assoc,
          pullback.lift_fst, hfac]
      · rw [IsPullback.isoIsPullback_hom_snd, pullback.lift_snd]
    have hsq : IsPullback c₁ (pullback.fst D.a π) (pullback.fst (pullback.snd f g) π) c := by
      refine IsPullback.of_right (h₁₂ := pullback.snd (pullback.snd f g) π)
        (h₂₂ := pullback.snd f g) ?_ (pullback.lift_fst _ _ _)
        (IsPullback.of_hasPullback (pullback.snd f g) π).flip
      rw [pullback.lift_snd, pullback.lift_snd]
      exact hX₁.flip
    have : IsIso c := by
      apply MorphismProperty.of_isPullback_of_descendsAlong (P := isomorphisms Scheme.{u})
        (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hsq
      · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      · rw [hc₁]
        exact (isomorphisms Scheme).of_isIso _
    exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
  · -- `h ∘ q₁ = h ∘ q₂`, checked after the fppf base change `X₁'' ⟶ X''`
    have : Surjective (pullbackBaseπ'' (g := g) π) :=
      MorphismProperty.pullbackMap (P := @Surjective) ‹_› ‹_› rfl rfl
    have : Flat (pullbackBaseπ'' (g := g) π) :=
      MorphismProperty.pullbackMap (P := @Flat) ‹Flat π› ‹Flat π› rfl rfl
    have : LocallyOfFinitePresentation (pullbackBaseπ'' (g := g) π) :=
      MorphismProperty.pullbackMap (P := @LocallyOfFinitePresentation)
        ‹LocallyOfFinitePresentation π› ‹LocallyOfFinitePresentation π› rfl rfl
    have hq₁ : D.pullbackBaseQ₁ π ≫ pullback.fst D.a π = pullback.fst D.b _ ≫ D.q₁ :=
      pullback.lift_fst _ _ _
    have hq₂ : D.pullbackBaseQ₂ π ≫ pullback.fst D.a π = pullback.fst D.b _ ≫ D.q₂ :=
      pullback.lift_fst _ _ _
    rw [← cancel_epi (pullback.fst D.b (pullbackBaseπ'' π)), ← reassoc_of% hq₁,
      ← reassoc_of% hq₂, hfac, hq]

end PullbackBase

set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.9 over an affine base: if `S` is affine and `X'` is quasi-affine over `S'`, every
descent datum on `X'` relative to a faithfully flat quasi-compact `g` is effective. One replaces
`S'` by an affine `S₁` covering it (`isEffective_of_isEffective_pullbackBase`) and applies
`isEffective_of_isQuasiAffine_of_isAffine`. -/
theorem isEffective_of_isQuasiAffineHom_of_isAffine [IsAffine S] [Surjective g] [Flat g]
    [QuasiCompact g] [IsQuasiAffineHom D.a] : D.IsEffective := by
  have : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace g
  obtain ⟨S₁, π, hπs, hπ, hS₁⟩ := S'.exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  have : Flat π := IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ π hπ
  have : ContainsIdentities @LocallyOfFinitePresentation := ⟨fun _ ↦ inferInstance⟩
  have : LocallyOfFinitePresentation π :=
    IsLocalIso.le_of_isZariskiLocalAtSource @LocallyOfFinitePresentation _ _ π hπ
  have : Surjective π := hπs
  refine D.isEffective_of_isEffective_pullbackBase π ?_
  have : IsAffine S₁ := hS₁
  have : IsQuasiAffineHom (D.pullbackBase π).a :=
    inferInstanceAs (IsQuasiAffineHom (pullback.snd D.a π))
  have : (D.pullbackBase π).X'.IsQuasiAffine :=
    isQuasiAffine_of_isQuasiAffineHom (D.pullbackBase π).a
  exact (D.pullbackBase π).isEffective_of_isQuasiAffine_of_isAffine

set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.9: for `g : S' ⟶ S` faithfully flat and quasi-compact, every descent datum on an `X'`
quasi-affine over `S'` is effective. SGA deduces this from VIII.7.8; here VIII.7.3 reduces it to
an affine base (`isEffective_of_isQuasiAffineHom_of_isAffine`). -/
theorem isEffective_of_isQuasiAffineHom [Surjective g] [Flat g] [QuasiCompact g]
    [IsQuasiAffineHom D.a] : D.IsEffective := by
  refine (D.isEffective_iff_forall_isEffective_restrictBase (fun V : S.affineOpens ↦ V.1)
    (iSup_affineOpens_eq_top S)).mpr fun V ↦ ?_
  have : IsAffine V.1 := V.2
  have : Flat (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : Surjective (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : QuasiCompact (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsQuasiAffineHom (D.restrictBase V.1).a := IsZariskiLocalAtTarget.restrict ‹_› _
  exact (D.restrictBase V.1).isEffective_of_isQuasiAffineHom_of_isAffine

set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.9: for `g : S' ⟶ S` faithfully flat and quasi-compact, every descent datum on an `X'`
quasi-affine over `S'` is effective, and the descended scheme is quasi-affine over `S`
(VIII.5.9). -/
theorem exists_isPullback_isQuasiAffineHom [Surjective g] [Flat g] [QuasiCompact g]
    [IsQuasiAffineHom D.a] :
    ∃ (X : Scheme.{u}) (f : X ⟶ S) (h : D.X' ⟶ X),
      IsPullback h D.a f g ∧ D.q₁ ≫ h = D.q₂ ≫ h ∧ IsQuasiAffineHom f := by
  obtain ⟨X, f, h, hX, hq⟩ := D.isEffective_of_isQuasiAffineHom
  exact ⟨X, f, h, hX, hq, of_isPullback_of_descendsAlong (P := @IsQuasiAffineHom)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hX.flip ⟨⟨‹_›, ‹_›⟩, ‹_›⟩ ‹_›⟩

section Saturation

/-- The saturation `R(T) = q₂(q₁⁻¹(T))` of a subset `T` of `X'` for the set-theoretic equivalence
relation defined by the descent datum. -/
def saturation (T : Set D.X') : Set D.X' := D.q₂ '' (D.q₁ ⁻¹' T)

lemma orbit_eq_saturation (x : D.X') : D.orbit x = D.saturation {x} := rfl

/-- Symmetry of the set-theoretic equivalence relation defined by the descent datum. -/
lemma exists_q₁_q₂_swap (r : D.X'') : ∃ r', D.q₁ r' = D.q₂ r ∧ D.q₂ r' = D.q₁ r := by
  obtain ⟨σ, hσ₁, hσ₂⟩ := D.symm (𝟙 D.X'')
  refine ⟨σ r, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hσ₁, Category.id_comp]
  · rw [← Scheme.Hom.comp_apply, hσ₂, Category.id_comp]

/-- Transitivity of the set-theoretic equivalence relation defined by the descent datum. -/
lemma exists_q₁_q₂_trans {r r' : D.X''} (h : D.q₂ r = D.q₁ r') :
    ∃ r'', D.q₁ r'' = D.q₁ r ∧ D.q₂ r'' = D.q₂ r' := by
  obtain ⟨μ, hμ₁, hμ₂⟩ :=
    D.trans (pullback.fst D.q₂ D.q₁) (pullback.snd D.q₂ D.q₁) pullback.condition
  obtain ⟨p, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback r r' h
  refine ⟨μ p, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hμ₁, Scheme.Hom.comp_apply]
  · rw [← Scheme.Hom.comp_apply, hμ₂, Scheme.Hom.comp_apply]

lemma subset_saturation (T : Set D.X') : T ⊆ D.saturation T := fun x hx ↦ by
  obtain ⟨e, he⟩ := D.exists_section_q₁_q₂
  exact ⟨e x, by rw [Set.mem_preimage, (he x).1]; exact hx, (he x).2⟩

lemma saturation_mono {T₁ T₂ : Set D.X'} (h : T₁ ⊆ T₂) : D.saturation T₁ ⊆ D.saturation T₂ :=
  Set.image_mono (Set.preimage_mono h)

lemma saturation_saturation (T : Set D.X') : D.saturation (D.saturation T) = D.saturation T := by
  refine subset_antisymm ?_ (D.subset_saturation _)
  rintro _ ⟨r', ⟨r, hr, e⟩, rfl⟩
  obtain ⟨r'', h₁, h₂⟩ := D.exists_q₁_q₂_trans e
  exact ⟨r'', by rw [Set.mem_preimage, h₁]; exact hr, h₂⟩

/-- The saturation of a subset is stable under the descent datum. -/
lemma isStable_saturation (T : Set D.X') : D.IsStable (D.saturation T) := by
  ext r
  constructor
  · intro hr
    rw [Set.mem_preimage, ← D.saturation_saturation]
    exact ⟨r, hr, rfl⟩
  · intro hr
    obtain ⟨r', h₁, h₂⟩ := D.exists_q₁_q₂_swap r
    rw [Set.mem_preimage, ← D.saturation_saturation, ← h₂]
    refine ⟨r', ?_, rfl⟩
    rw [Set.mem_preimage, h₁]
    exact hr

/-- The complement `X' - R(X' - U)` of the saturation of the complement of `U` is saturated. -/
lemma saturation_compl_saturation_compl (U : Set D.X') :
    D.saturation (D.saturation Uᶜ)ᶜ ⊆ (D.saturation Uᶜ)ᶜ := by
  rintro _ ⟨r, hr, rfl⟩ ⟨r', hr', e⟩
  apply hr
  obtain ⟨r₁, h₁, h₂⟩ := D.exists_q₁_q₂_swap r
  obtain ⟨r'', h₃, h₄⟩ := D.exists_q₁_q₂_trans (r := r') (r' := r₁) (by rw [e, h₁])
  exact ⟨r'', by rw [Set.mem_preimage, h₃]; exact hr', by rw [h₄, h₂]⟩

end Saturation

set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.6 over an affine base, in the form used by its proof: let `S` be affine and `g`
finite, locally free and surjective. If every class `R(x')` is contained in a quasi-affine open
subset `U` of `X'`, the descent datum is effective. As in SGA (the variant through VIII.7.9 given
after the proof, which avoids norms): `U' = X' - R(X' - U)` is a saturated open subset contained
in `U` and containing `R(x')`; the saturation `W` of a quasi-compact open neighbourhood of `R(x')`
in `U'` is then a saturated quasi-compact open subset of `U`, hence quasi-affine, and one concludes
by VIII.7.9 and VIII.7.2. -/
theorem isEffective_of_forall_orbit_subset_isQuasiAffine [IsAffine S] [IsFinite g] [Flat g]
    [LocallyOfFinitePresentation g] [Surjective g]
    (H : ∀ x : D.X', ∃ U : D.X'.Opens, (U : Scheme).IsQuasiAffine ∧ D.orbit x ⊆ U) :
    D.IsEffective := by
  have : IsAffine S' := isAffine_of_isAffineHom g
  have : IsFinite D.q₁ := MorphismProperty.of_isPullback D.isPullback₁.flip
    (MorphismProperty.pullback_fst (P := @IsFinite) g g ‹_›)
  have : IsFinite D.q₂ := MorphismProperty.of_isPullback D.isPullback₂.flip
    (MorphismProperty.pullback_snd (P := @IsFinite) g g ‹_›)
  have : Flat D.q₂ := MorphismProperty.of_isPullback D.isPullback₂.flip
    (MorphismProperty.pullback_snd (P := @Flat) g g ‹_›)
  have : LocallyOfFinitePresentation D.q₂ := MorphismProperty.of_isPullback D.isPullback₂.flip
    (MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) g g ‹_›)
  have hW : ∀ x : D.X', ∃ W : D.X'.Opens, x ∈ W ∧ ∃ hW : D.IsStable W,
      (D.restrict hW).IsEffective := by
    intro x
    obtain ⟨U, hU, hxU⟩ := H x
    -- the saturated open subset `U' = X' - R(X' - U)`
    set U' : Set D.X' := (D.saturation (U : Set D.X')ᶜ)ᶜ
    have hU'open : IsOpen U' := (D.q₂.isClosedMap _
      (U.isOpen.isClosed_compl.preimage D.q₁.continuous)).isOpen_compl
    have hU'U : U' ⊆ U := fun y hy ↦ by
      by_contra h
      exact hy (D.subset_saturation _ h)
    have hxU' : x ∈ U' := by
      rintro ⟨r, hr, e⟩
      obtain ⟨r₁, h₁, h₂⟩ := D.exists_q₁_q₂_swap r
      exact hr (hxU ⟨r₁, by rw [Set.mem_preimage, h₁, e]; rfl, h₂⟩)
    have horb : D.orbit x ⊆ U' := (D.saturation_mono (Set.singleton_subset_iff.mpr hxU')).trans
      (D.saturation_compl_saturation_compl _)
    -- a quasi-compact open neighbourhood `U''` of `R(x)` in `U'`
    have : Finite (D.orbit x) := (D.orbit_finite x).to_subtype
    have hex : ∀ y : D.orbit x, ∃ V : D.X'.Opens, IsAffineOpen V ∧ y.1 ∈ V ∧
        (V : Set D.X') ⊆ U' := fun y ↦ by
      obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
        D.X'.isBasis_affineOpens.exists_subset_of_mem_open (horb y.2) hU'open
      exact ⟨V, hV, hyV, hVU⟩
    choose A hA hyA hAU' using hex
    let U'' : D.X'.Opens := ⨆ y : D.orbit x, A y
    have hU''c : IsCompact (U'' : Set D.X') := by
      rw [TopologicalSpace.Opens.coe_iSup]
      exact isCompact_iUnion fun y ↦ (hA y).isCompact
    have hU''U' : (U'' : Set D.X') ⊆ U' := by
      rw [TopologicalSpace.Opens.coe_iSup]
      exact Set.iUnion_subset hAU'
    have horbU'' : D.orbit x ⊆ U'' := fun y hy ↦
      TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyA ⟨y, hy⟩⟩
    -- its saturation `W`
    let W : D.X'.Opens :=
      ⟨D.saturation U'', D.q₂.isOpenMap _ (U''.isOpen.preimage D.q₁.continuous)⟩
    have hWc : IsCompact (W : Set D.X') :=
      (D.q₁.isCompact_preimage (U := U'') hU''c).image D.q₂.continuous
    have hWU : W ≤ U := fun y hy ↦ hU'U ((D.saturation_mono hU''U').trans
      (D.saturation_compl_saturation_compl _) hy)
    have hxW : x ∈ W := D.subset_saturation _ (horbU'' (D.subset_saturation {x} rfl))
    have hWs : D.IsStable W := D.isStable_saturation _
    have : CompactSpace W := isCompact_iff_compactSpace.mp hWc
    have : (W : Scheme).IsQuasiAffine := .of_isImmersion (D.X'.homOfLE hWU)
    have : QuasiCompact (D.restrict hWs).a := (quasiCompact_iff_compactSpace _).mpr ‹_›
    have : IsQuasiAffineHom (D.restrict hWs).a := isQuasiAffineHom_of_isQuasiAffine _
    exact ⟨W, hxW, hWs, (D.restrict hWs).isEffective_of_isQuasiAffineHom⟩
  choose W hxW hWs hWe using hW
  refine (D.isEffective_iff_forall_isEffective_restrict W hWs ?_).mpr hWe
  exact top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩

set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.6: let `g : S' ⟶ S` be finite, locally free and surjective. A descent datum relative
to `g` is effective iff, for every `x' ∈ X'`, the class `R(x') = q₂(q₁⁻¹(x'))` is contained in an
affine open subset of `X'`. Sufficiency is reduced by VIII.7.3 to an affine base
(`isEffective_of_forall_orbit_subset_isQuasiAffine`), using that a finite subset of an open
subset of an affine scheme has a quasi-compact, hence quasi-affine, open neighbourhood. -/
theorem isEffective_iff_forall_exists_isAffineOpen_orbit_subset [IsFinite g] [Flat g]
    [LocallyOfFinitePresentation g] [Surjective g] :
    D.IsEffective ↔ ∀ x : D.X', ∃ U : D.X'.Opens, IsAffineOpen U ∧ D.orbit x ⊆ U := by
  refine ⟨D.exists_isAffineOpen_orbit_subset_of_isEffective, fun H ↦ ?_⟩
  refine (D.isEffective_iff_forall_isEffective_restrictBase (fun V : S.affineOpens ↦ V.1)
    (iSup_affineOpens_eq_top S)).mpr fun V ↦ ?_
  have : IsAffine V.1 := V.2
  have : IsFinite (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : Flat (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : LocallyOfFinitePresentation (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : Surjective (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  set W : D.X'.Opens := D.a ⁻¹ᵁ g ⁻¹ᵁ V.1
  have hWs : D.IsStable W := D.isStable_preimage_preimage V.1
  refine (D.restrictBase V.1).isEffective_of_forall_orbit_subset_isQuasiAffine fun x ↦ ?_
  obtain ⟨U, hU, hxU⟩ := H (W.ι x)
  have horbW : D.orbit (W.ι x) ⊆ W := by
    rintro _ ⟨r, hr, rfl⟩
    have : r ∈ D.q₁ ⁻¹' (W : Set D.X') := by
      rw [Set.mem_preimage, Set.mem_singleton_iff.mp hr]
      exact x.2
    rw [hWs] at this
    exact this
  have : Finite (D.orbit (W.ι x)) := (D.orbit_finite _).to_subtype
  have hex : ∀ y : D.orbit (W.ι x), ∃ A : D.X'.Opens, IsAffineOpen A ∧ y.1 ∈ A ∧ A ≤ U ⊓ W :=
    fun y ↦ by
      obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAUW⟩ := D.X'.isBasis_affineOpens.exists_subset_of_mem_open
        (show y.1 ∈ ((U ⊓ W : D.X'.Opens) : Set D.X') from ⟨hxU y.2, horbW y.2⟩) (U ⊓ W).isOpen
      exact ⟨A, hA, hyA, hAUW⟩
  choose A hA hyA hAUW using hex
  let O : D.X'.Opens := ⨆ y, A y
  have hOc : IsCompact (O : Set D.X') := by
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun y ↦ (hA y).isCompact
  have hOUW : O ≤ U ⊓ W := iSup_le hAUW
  have horbO : D.orbit (W.ι x) ⊆ O := fun y hy ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyA ⟨y, hy⟩⟩
  refine ⟨W.ι ⁻¹ᵁ O, ?_, ?_⟩
  · have : CompactSpace O := isCompact_iff_compactSpace.mp hOc
    have : IsAffine U := hU
    have : (O : Scheme).IsQuasiAffine := .of_isImmersion (D.X'.homOfLE (hOUW.trans inf_le_left))
    have hr : Set.range ((W.ι ⁻¹ᵁ O).ι ≫ W.ι) = Set.range O.ι := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
        Scheme.Opens.range_ι, Scheme.Hom.coe_preimage, Set.image_preimage_eq_inter_range,
        Scheme.Opens.range_ι, Set.inter_eq_left]
      exact fun y hy ↦ (hOUW hy).2
    exact .of_isIso (IsOpenImmersion.isoOfRangeEq _ O.ι hr).hom
  · rintro _ ⟨r, hr, rfl⟩
    change W.ι (D.restrictQ₂ hWs r) ∈ O
    rw [← D.q₂_ι_apply]
    refine horbO ⟨_, ?_, rfl⟩
    rw [Set.mem_preimage, D.q₁_ι_apply, Set.mem_singleton_iff.mp hr]
    rfl

/-- VIII.7.7: a finite, locally free and surjective `g : S' ⟶ S` is an effective descent
morphism for quasi-projective schemes: every descent datum on an `X'` quasi-projective over `S'`
is effective, and the descended `S`-scheme is quasi-projective over `S`. Proved by
`effectiveOfQuasiProjectiveStatement`. -/
def EffectiveOfQuasiProjectiveStatement : Prop :=
  ∀ ⦃S S' : Scheme.{u}⦄ (g : S' ⟶ S) [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    [Surjective g] (D : DescentDatum g), IsQuasiProjective D.a →
      ∃ (X : Scheme.{u}) (f : X ⟶ S) (h : D.X' ⟶ X),
        IsPullback h D.a f g ∧ D.q₁ ≫ h = D.q₂ ≫ h ∧ IsQuasiProjective f

set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.7, effectiveness: for `g : S' ⟶ S` finite, locally free and surjective, a descent
datum on an `S'`-scheme `X'` quasi-projective over `S'` is effective. As in SGA, by VIII.7.6 it
suffices that every class `R(x')` is contained in an affine open subset of `X'`; `R(x')` is finite
and lies over one point of `S`, hence in the inverse image of an affine open subset `V` of `S`,
over which `X'` has an ample line bundle, and a finite subset of a scheme with an ample line
bundle is contained in an affine open subset (EGA II 4.5.4). The quasi-projectivity of the
descended scheme is `effectiveOfQuasiProjectiveStatement`. -/
theorem isEffective_of_isQuasiProjective [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    [Surjective g] (hD : IsQuasiProjective D.a) : D.IsEffective := by
  rw [D.isEffective_iff_forall_exists_isAffineOpen_orbit_subset]
  intro x
  obtain ⟨L, hL⟩ := hD.exists_isRelativelyAmple
  obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show g (D.a x) ∈ (⊤ : S.Opens) from trivial)
  have hV' : IsAffineOpen (g ⁻¹ᵁ V) := hV.preimage g
  set W := D.a ⁻¹ᵁ g ⁻¹ᵁ V
  have hLW : (L.pullback W.ι).IsAmple := hL.2 _ hV'
  have key : D.q₂ ≫ D.a ≫ g = D.q₁ ≫ D.a ≫ g := by
    rw [← Category.assoc, D.isPullback₂.w, ← Category.assoc, D.isPullback₁.w, Category.assoc,
      Category.assoc, pullback.condition]
  have horb : D.orbit x ⊆ W := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hr
    change g (D.a (D.q₂ r)) ∈ V
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, hr]
    exact hxV
  classical
  let F : Finset W := (D.orbit_finite x).toFinset.attach.image fun y ↦
    (⟨y.1, horb ((D.orbit_finite x).mem_toFinset.mp y.2)⟩ : W)
  obtain ⟨U, hU, hFU⟩ := hLW.exists_isAffineOpen_of_finite F
  refine ⟨W.ι ''ᵁ U, W.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hU, fun y hy ↦ ?_⟩
  have := hFU ⟨y, horb hy⟩ (Finset.mem_image.mpr
    ⟨⟨y, (D.orbit_finite x).mem_toFinset.mpr hy⟩, Finset.mem_attach _ _, rfl⟩)
  exact (Scheme.Hom.apply_mem_image_iff W.ι).mpr this

set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.7: a finite, locally free and surjective `g : S' ⟶ S` is an effective descent
morphism for quasi-projective schemes. The descent datum is effective by
`isEffective_of_isQuasiProjective`; if `X' ⟶ X` over `S' ⟶ S` solves it, `X' ⟶ X` is finite,
locally free and surjective (a base change of `g`), `X ⟶ S` is of finite type and
quasi-separated by descent (VIII.3.3, VIII.3.6), and `X' ⟶ S' ⟶ S` is quasi-projective, so
`X ⟶ S` is quasi-projective by EGA II 6.6.4 (the norm along `X' ⟶ X` of a relatively ample
line bundle is relatively ample). -/
theorem effectiveOfQuasiProjectiveStatement :
    EffectiveOfQuasiProjectiveStatement.{u} := by
  intro S S' g _ _ _ _ D hD
  obtain ⟨X, f, h, hpb, hq⟩ := D.isEffective_of_isQuasiProjective hD
  refine ⟨X, f, h, hpb, hq, ?_⟩
  have : IsQuasiProjective D.a := hD
  have : IsFinite h := MorphismProperty.of_isPullback hpb.flip ‹IsFinite g›
  have : Flat h := MorphismProperty.of_isPullback hpb.flip ‹Flat g›
  have : LocallyOfFinitePresentation h := MorphismProperty.of_isPullback hpb.flip ‹_›
  have : Surjective h := MorphismProperty.of_isPullback hpb.flip ‹Surjective g›
  have hg : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) g :=
    ⟨⟨‹_›, ‹_›⟩, inferInstance⟩
  have : LocallyOfFiniteType f :=
    DescendsAlong.of_isPullback (P := @LocallyOfFiniteType) hpb.flip hg inferInstance
  have : QuasiCompact f :=
    DescendsAlong.of_isPullback (P := @QuasiCompact) hpb.flip hg inferInstance
  have : QuasiSeparated f :=
    DescendsAlong.of_isPullback (P := @QuasiSeparated) hpb.flip hg inferInstance
  have : IsQuasiProjective (h ≫ f) := by
    rw [hpb.w]
    exact IsQuasiProjective.comp_isFinite D.a g
  exact IsQuasiProjective.of_isFinite_comp h f

section LineBundleDatum

variable (L' : D.X'.LineBundle)

/-- The open subset of `T` on which the transitivity condition of a descent datum on a line bundle
compares the components `φᵢₖ`, `φⱼₖ`, `φᵢⱼ`, pulled back along `r''`, `r'`, `r`. -/
def cocycleOpen {T : Scheme.{u}} (r r' : T ⟶ D.X'') (i j k : L'.ι) : T.Opens :=
  (r ≫ D.q₁) ⁻¹ᵁ L'.U i ⊓ (r ≫ D.q₂) ⁻¹ᵁ L'.U j ⊓ (r' ≫ D.q₂) ⁻¹ᵁ L'.U k

variable {L'} in
lemma cocycleOpen_le₁ {T : Scheme.{u}} {r r' r'' : T ⟶ D.X''} {i j k : L'.ι}
    (h₁ : r'' ≫ D.q₁ = r ≫ D.q₁) (h₂ : r'' ≫ D.q₂ = r' ≫ D.q₂) :
    D.cocycleOpen L' r r' i j k ≤ r'' ⁻¹ᵁ (D.q₁ ⁻¹ᵁ L'.U i ⊓ D.q₂ ⁻¹ᵁ L'.U k) := by
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h₁, h₂]
  exact le_inf (inf_le_left.trans inf_le_left) inf_le_right

variable {L'} in
lemma cocycleOpen_le₂ {T : Scheme.{u}} {r r' : T ⟶ D.X''} {i j k : L'.ι}
    (hr : r ≫ D.q₂ = r' ≫ D.q₁) :
    D.cocycleOpen L' r r' i j k ≤ r' ⁻¹ᵁ (D.q₁ ⁻¹ᵁ L'.U j ⊓ D.q₂ ⁻¹ᵁ L'.U k) := by
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ← hr]
  exact le_inf (inf_le_left.trans inf_le_right) inf_le_right

variable {L'} in
lemma cocycleOpen_le₃ {T : Scheme.{u}} {r r' : T ⟶ D.X''} {i j k : L'.ι} :
    D.cocycleOpen L' r r' i j k ≤ r ⁻¹ᵁ (D.q₁ ⁻¹ᵁ L'.U i ⊓ D.q₂ ⁻¹ᵁ L'.U j) := by
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
  exact inf_le_left

/-- VIII.7.8: a descent datum on a line bundle `L'` on `X'`, relative to the descent datum `D`: an
isomorphism `φ : q₁*L' ≅ q₂*L'` on `X''` satisfying the transitivity condition, stated on
`T`-valued points: if `r, r', r'' : T ⟶ X''` satisfy `q₂ r = q₁ r'`, `q₁ r'' = q₁ r` and
`q₂ r'' = q₂ r'`, then `r''*φ = r'*φ ∘ r*φ`, i.e. `φᵢₖ = φⱼₖ φᵢⱼ` after pulling back. -/
structure LineBundleDatum where
  /-- The isomorphism `q₁*L' ≅ q₂*L'`. -/
  iso : (L'.pullback D.q₁).Iso (L'.pullback D.q₂)
  cocycle ⦃T : Scheme.{u}⦄ (r r' r'' : T ⟶ D.X'') (hr : r ≫ D.q₂ = r' ≫ D.q₁)
    (h₁ : r'' ≫ D.q₁ = r ≫ D.q₁) (h₂ : r'' ≫ D.q₂ = r' ≫ D.q₂) (i j k : L'.ι) :
    r''.appLE _ _ (D.cocycleOpen_le₁ h₁ h₂) (iso.φ i k).1 =
      r'.appLE _ _ (D.cocycleOpen_le₂ (i := i) hr)
          (iso.φ j k).1 *
        r.appLE _ _ (D.cocycleOpen_le₃ (k := k))
          (iso.φ i j).1

variable {L'} {X : Scheme.{u}} {h : D.X' ⟶ X} (hq : D.q₁ ≫ h = D.q₂ ≫ h) {L : X.LineBundle}

/-- The open subset of `X''` on which the compatibility of `ψ : h*L ≅ L'` with a descent datum on
`L'` compares components. -/
def compatOpen (h : D.X' ⟶ X) (L : X.LineBundle) (α : L.ι) (i k : L'.ι) : D.X''.Opens :=
  (D.q₁ ≫ h) ⁻¹ᵁ L.U α ⊓ D.q₁ ⁻¹ᵁ L'.U i ⊓ D.q₂ ⁻¹ᵁ L'.U k

lemma compatOpen_le₁ {α : L.ι} {i k : L'.ι} :
    D.compatOpen h L α i k ≤ D.q₁ ⁻¹ᵁ (h ⁻¹ᵁ L.U α ⊓ L'.U i) := by
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage]
  exact inf_le_left

include hq in
lemma compatOpen_le₂ {α : L.ι} {i k : L'.ι} :
    D.compatOpen h L α i k ≤ D.q₂ ⁻¹ᵁ (h ⁻¹ᵁ L.U α ⊓ L'.U k) := by
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← hq]
  exact le_inf (inf_le_left.trans inf_le_left) inf_le_right

lemma compatOpen_le₃ {α : L.ι} {i k : L'.ι} :
    D.compatOpen h L α i k ≤ D.q₁ ⁻¹ᵁ L'.U i ⊓ D.q₂ ⁻¹ᵁ L'.U k :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right

variable {D} in
/-- VIII.7.8: an isomorphism `ψ : h*L ≅ L'` is compatible with a descent datum `E` on `L'`
relative to `D`: `E ∘ q₁*ψ = q₂*ψ`, i.e. `ψ_{αk} = φᵢₖ ψ_{αi}` on `X''` after pulling back. -/
def LineBundleDatum.IsCompatible (E : D.LineBundleDatum L') (ψ : (L.pullback h).Iso L') :
    Prop :=
  ∀ (α : L.ι) (i k : L'.ι),
    D.q₂.appLE _ _ (D.compatOpen_le₂ hq (i := i))
        (ψ.φ α k).1 =
      D.X''.presheaf.map (homOfLE (D.compatOpen_le₃ (h := h) (α := α))).op
          (E.iso.φ i k).1 *
        D.q₁.appLE _ _ (D.compatOpen_le₁ (k := k))
          (ψ.φ α i).1

end LineBundleDatum

/-- VIII.7.8: a faithfully flat quasi-compact `g : S' ⟶ S` is an effective descent morphism for
schemes endowed with a relatively ample line bundle. For a descent datum `D` on `X' ⟶ S'` and a
line bundle `L'` on `X'` ample relative to `S'` with a descent datum `E` relative to `D`, `D` is
effective, and `L'` descends: there is a line bundle `L` on the descended `S`-scheme `X`, ample
relative to `S`, with an isomorphism `h*L ≅ L'` compatible with `E`. The case `L' = 𝒪_{X'}` is
VIII.7.9 (`isEffective_of_isQuasiAffineHom`). Proved in
`SGA.SGA1.ExposeVIII.effectiveOfRelativelyAmpleStatement`, by descending the graded ring
`⊕ₙ Γ(X', L'^{⊗n})` over affine bases (VIII.1) as in SGA. -/
def EffectiveOfRelativelyAmpleStatement : Prop :=
  ∀ ⦃S S' : Scheme.{u}⦄ (g : S' ⟶ S) [Surjective g] [Flat g] [QuasiCompact g]
    (D : DescentDatum g) (L' : D.X'.LineBundle) (E : D.LineBundleDatum L'),
    L'.IsRelativelyAmple D.a →
      ∃ (X : Scheme.{u}) (f : X ⟶ S) (h : D.X' ⟶ X) (hq : D.q₁ ≫ h = D.q₂ ≫ h),
        IsPullback h D.a f g ∧ ∃ (L : X.LineBundle) (ψ : (L.pullback h).Iso L'),
          E.IsCompatible hq ψ ∧ L.IsRelativelyAmple f

section OfScheme

variable (g) {X : Scheme.{u}} (x : X ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- The descent datum on `X ×_S S'` defined by an `S`-scheme `X`: here
`X'' = X ×_S S''`, and `q₁, q₂` are induced by the two projections `S'' ⇉ S'`. -/
noncomputable def ofScheme : DescentDatum g where
  X' := pullback x g
  a := pullback.snd x g
  X'' := pullback x (pullback.fst g g ≫ g)
  b := pullback.snd x (pullback.fst g g ≫ g)
  q₁ := pullback.map _ _ _ _ (𝟙 X) (pullback.fst g g) (𝟙 S) (by simp) (by simp)
  q₂ := pullback.map _ _ _ _ (𝟙 X) (pullback.snd g g) (𝟙 S) (by simp)
    (by simp [pullback.condition])
  isPullback₁ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback x g)
    rw [pullback.lift_fst, Category.comp_id]
    exact IsPullback.of_hasPullback _ _
  isPullback₂ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback x g)
    rw [pullback.lift_fst, Category.comp_id, ← pullback.condition]
    exact IsPullback.of_hasPullback _ _
  refl T y := by
    refine ⟨pullback.lift (y ≫ pullback.fst x g) (y ≫ pullback.snd x g ≫ pullback.diagonal g)
      (by simp [pullback.condition]), ?_, ?_⟩ <;> apply pullback.hom_ext <;> simp
  symm T r := by
    refine ⟨pullback.lift (r ≫ pullback.fst _ _)
      (r ≫ pullback.snd _ _ ≫ (pullbackSymmetry g g).hom) ?_, ?_, ?_⟩
    · simp [pullback.condition]
    all_goals apply pullback.hom_ext <;> simp
  trans T r r' e := by
    have e₁ := congr($e ≫ pullback.fst x g)
    have e₂ := congr($e ≫ pullback.snd x g)
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at e₁ e₂
    refine ⟨pullback.lift (r ≫ pullback.fst _ _) (pullback.lift
      (r ≫ pullback.snd _ _ ≫ pullback.fst g g) (r' ≫ pullback.snd _ _ ≫ pullback.snd g g) ?_)
      ?_, ?_, ?_⟩
    · have hc : pullback.fst g g ≫ g = pullback.snd g g ≫ g := pullback.condition
      simp only [Category.assoc]
      calc r ≫ pullback.snd _ _ ≫ pullback.fst g g ≫ g
          = r ≫ pullback.snd _ _ ≫ pullback.snd g g ≫ g :=
            congrArg (fun k ↦ r ≫ pullback.snd x (pullback.fst g g ≫ g) ≫ k) hc
        _ = r' ≫ pullback.snd _ _ ≫ pullback.fst g g ≫ g := by
            simpa only [Category.assoc] using congrArg (· ≫ g) e₂
        _ = r' ≫ pullback.snd _ _ ≫ pullback.snd g g ≫ g :=
            congrArg (fun k ↦ r' ≫ pullback.snd x (pullback.fst g g ≫ g) ≫ k) hc
    · rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc,
        pullback.condition (f := x)]
      simp only [Category.assoc]
    · apply pullback.hom_ext <;> simp
    · apply pullback.hom_ext <;> simp [e₁]

set_option backward.isDefEq.respectTransparency false in
/-- The descent datum defined by an `S`-scheme is effective. -/
theorem isEffective_ofScheme : (ofScheme g x).IsEffective :=
  ⟨X, x, pullback.fst x g, IsPullback.of_hasPullback x g, by simp [ofScheme]⟩

end OfScheme

end DescentDatum

end SGA.SGA1.ExposeVIII
