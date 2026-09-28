/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import SGA.SGA1.ExposeIX.Submersive
import SGA.SGA1.ExposeIX.Unramified

/-!
# SGA 1, Exposé IX, §§1 and 3: sections of étale morphisms and descent of morphisms

§1 recalls facts on étale morphisms. We use mathlib's `Etale` (flat, unramified, locally of
finite presentation, no noetherian hypotheses), as SGA asks after IX.1.1; its agreement with
the definition of IX.1.1 (locally a base change of an étale morphism of noetherian affine
schemes) is not formalized. The central facts for what follows are IX.1.5 and IX.1.6: a
section of an étale morphism is an open immersion, so `S`-morphisms into an étale `S`-scheme
are determined by the underlying open subsets of their graphs. IX.1.9 is proved in the affine
case; IX.1.8 is proved in `SGA.SGA1.ExposeIX.CompleteLocal`; IX.1.10 is recorded as a
statement.

§3 deduces that morphisms into étale schemes descend along universally submersive morphisms:

* IX.3.1: base change along a surjective morphism is injective on morphisms into an
  unramified scheme (`hom_ext_of_surjective`, `pullback_map_injective`);
* IX.3.2 / IX.3.3: along a universally submersive morphism `g : S' ⟶ S`, the diagram
  `Hom_S(X, Y) → Hom_{S'}(X', Y') ⇉ Hom_{S''}(X'', Y'')` is exact for `Y` étale
  (`existsUnique_hom_of_universallySubmersive`); it is stated in the equivalent form
  "an `S`-morphism `X ×_S S' ⟶ Y` equalizing the two projections from
  `X'' = X' ×_X X'` factors uniquely through `X'`";
* IX.3.4: connectedness and full faithfulness along universally submersive morphisms with
  geometrically connected fibres;
* the full faithfulness half of IX.1.7 and IX.4.10: base change along a radicial universally
  submersive morphism (for instance a surjective closed immersion, or a finite radicial
  surjective morphism) is fully faithful on étale schemes. Essential surjectivity is IX.1.7 in
  `SGA.SGA1.ExposeIX.NilImmersion` and IX.4.10 in `SGA.SGA1.ExposeIX.FiniteEffectiveDescent`.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

/-! ### §1: recollections -/

section Recollections

variable {X Y S : Scheme.{u}}

/-- IX.1.2: an étale morphism (mathlib's `Etale`, used for IX.1.1) is flat, unramified and
locally of finite presentation, and conversely. -/
theorem etale_iff_flat_formallyUnramified_locallyOfFinitePresentation (f : X ⟶ Y) :
    Etale f ↔ Flat f ∧ FormallyUnramified f ∧ LocallyOfFinitePresentation f :=
  Etale.iff_flat_and_formallyUnramified

/-- IX.1.3: étale morphisms are stable under base change. -/
theorem etale_isStableUnderBaseChange : IsStableUnderBaseChange @Etale :=
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.1.4, sufficiency (I.5.1): an étale radicial morphism is an open immersion. Its diagonal
is an open immersion (unramified) and surjective (radicial), hence an isomorphism, so the
morphism is a flat monomorphism of finite presentation. -/
theorem isOpenImmersion_of_etale_of_universallyInjective (f : X ⟶ Y) [Etale f]
    [UniversallyInjective f] : IsOpenImmersion f := by
  have : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr
      ⟨inferInstance, (UniversallyInjective.iff_diagonal f).mp inferInstance⟩
  have : Mono f := (pullback.isIso_diagonal_iff f).mp inferInstance
  exact IsOpenImmersion.of_flat_of_mono f

/-- IX.1.4 (I.5.1): a morphism is an open immersion if and only if it is étale and radicial
(radicial = `UniversallyInjective`). -/
theorem isOpenImmersion_iff_etale_and_universallyInjective (f : X ⟶ Y) :
    IsOpenImmersion f ↔ Etale f ∧ UniversallyInjective f :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩,
    fun ⟨_, _⟩ ↦ isOpenImmersion_of_etale_of_universallyInjective f⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A section of a separated morphism is a closed immersion (I.5.3). -/
theorem isClosedImmersion_of_section (f : X ⟶ S) [IsSeparated f] {s : S ⟶ X}
    (hs : s ≫ f = 𝟙 S) : IsClosedImmersion s := by
  have : IsIso (s ≫ f) := hs.symm ▸ inferInstance
  have : IsClosedImmersion (s ≫ f) := inferInstance
  exact IsClosedImmersion.of_comp s f

/-- A section of an unramified morphism is an open immersion (no separatedness needed). -/
theorem isOpenImmersion_of_section (f : X ⟶ S) [FormallyUnramified f] [LocallyOfFiniteType f]
    {s : S ⟶ X} (hs : s ≫ f = 𝟙 S) : IsOpenImmersion s := by
  have : Etale (s ≫ f) := hs.symm ▸ (inferInstance : Etale (𝟙 S))
  have := Etale.of_comp s f
  have : IsSplitMono s := .mk' ⟨f, hs⟩
  exact isOpenImmersion_of_etale_of_universallyInjective s

/-- An étale radicial surjective morphism is an isomorphism. -/
theorem isIso_of_etale_of_universallyInjective_of_surjective (f : X ⟶ Y) [Etale f]
    [UniversallyInjective f] [Surjective f] : IsIso f := by
  have := isOpenImmersion_of_etale_of_universallyInjective f
  exact (isIso_iff_isOpenImmersion_and_surjective f).mpr ⟨inferInstance, inferInstance⟩

lemma isIso_ι_comp_of_section (f : X ⟶ S) {s : S ⟶ X} (hs : s ≫ f = 𝟙 S)
    [IsOpenImmersion s] : IsIso (s.opensRange.ι ≫ f) := by
  let e := IsOpenImmersion.isoOfRangeEq s s.opensRange.ι (by simp)
  have : s.opensRange.ι ≫ f = e.inv := by
    rw [← cancel_epi e.hom, e.hom_inv_id, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, hs]
  rw [this]
  infer_instance

variable (f : X ⟶ S) [Etale f]

/-- IX.1.5: for `X` étale over `S`, sections of `X` over `S` correspond bijectively to open
subsets `Γ` of `X` such that `Γ ⟶ S` is radicial and surjective, via `s ↦ s(S)`. -/
noncomputable def sectionsEquivOpens :
    {s : S ⟶ X // s ≫ f = 𝟙 S} ≃
      {U : X.Opens // UniversallyInjective (U.ι ≫ f) ∧ Surjective (U.ι ≫ f)} where
  toFun s :=
    have := isOpenImmersion_of_section f s.2
    have := isIso_ι_comp_of_section f s.2
    ⟨s.1.opensRange, inferInstance, inferInstance⟩
  invFun U :=
    have := U.2.1
    have := U.2.2
    have := isIso_of_etale_of_universallyInjective_of_surjective (U.1.ι ≫ f)
    ⟨inv (U.1.ι ≫ f) ≫ U.1.ι, by simp⟩
  left_inv s := by
    have := isOpenImmersion_of_section f s.2
    have := isIso_ι_comp_of_section f s.2
    ext1
    let e := IsOpenImmersion.isoOfRangeEq s.1 s.1.opensRange.ι (by simp)
    have : inv (s.1.opensRange.ι ≫ f) = e.hom :=
      IsIso.inv_eq_of_inv_hom_id (by rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, s.2])
    simp only [this, e, IsOpenImmersion.isoOfRangeEq_hom_fac]
  right_inv U := by
    have := U.2.1
    have := U.2.2
    have := isIso_of_etale_of_universallyInjective_of_surjective (U.1.ι ≫ f)
    ext1
    simp [Scheme.Hom.opensRange_comp_of_isIso]

/-- IX.1.5, remark: if moreover `X` is separated over `S`, the image of a section is open and
closed. -/
theorem isClopen_range_of_section [IsSeparated f] {s : S ⟶ X} (hs : s ≫ f = 𝟙 S) :
    IsClopen (Set.range s) :=
  have := isOpenImmersion_of_section f hs
  have := isClosedImmersion_of_section f hs
  ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpen_range⟩

@[simp]
lemma sectionsEquivOpens_apply_coe (s : {s : S ⟶ X // s ≫ f = 𝟙 S}) :
    ((sectionsEquivOpens f s).1 : Set X) = Set.range s.1 := rfl

variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)

/-- `S`-morphisms `X ⟶ Y` are the sections of `X ×_S Y ⟶ X` (graph morphisms). -/
noncomputable def homEquivSections :
    {φ : X ⟶ Y // φ ≫ q = p} ≃ {s : X ⟶ pullback p q // s ≫ pullback.fst p q = 𝟙 X} where
  toFun φ := ⟨pullback.lift (𝟙 X) φ.1 (by simp [φ.2]), pullback.lift_fst _ _ _⟩
  invFun s := ⟨s.1 ≫ pullback.snd p q, by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, s.2, Category.id_comp]⟩
  left_inv φ := Subtype.ext (pullback.lift_snd _ _ _)
  right_inv s := by
    ext1
    apply pullback.hom_ext
    · rw [pullback.lift_fst, s.2]
    · rw [pullback.lift_snd]

/-- IX.1.6: for `Y` étale over `S`, `S`-morphisms `X ⟶ Y` correspond bijectively to open
subsets `Γ` of `X ×_S Y` such that `pr₁ : Γ ⟶ X` is radicial and surjective, via
`φ ↦` the underlying set of the graph of `φ`. -/
noncomputable def homEquivOpens [Etale q] :
    {φ : X ⟶ Y // φ ≫ q = p} ≃
      {U : (pullback p q).Opens //
        UniversallyInjective (U.ι ≫ pullback.fst p q) ∧ Surjective (U.ι ≫ pullback.fst p q)} :=
  (homEquivSections p q).trans (sectionsEquivOpens (pullback.fst p q))

lemma homEquivOpens_apply_coe [Etale q] (φ : {φ : X ⟶ Y // φ ≫ q = p}) :
    ((homEquivOpens p q φ).1 : Set ↥(pullback p q)) =
      Set.range (pullback.lift (𝟙 X) φ.1 (by simp [φ.2])) := rfl

/-- Étale coverings, i.e. finite étale morphisms. -/
def etaleCovering : MorphismProperty Scheme.{u} :=
  @IsFinite ⊓ @Etale

set_option backward.isDefEq.respectTransparency.types false in
instance : etaleCovering.{u}.IsStableUnderBaseChange := by
  unfold etaleCovering
  infer_instance

/-- IX.1.9, necessity (affine form): a finite étale algebra is locally free of finite type with
étale fibres. -/
theorem projective_and_etale_fiber_of_finite_etale (R B : Type u) [CommRing R] [CommRing B]
    [Algebra R B] [Module.Finite R B] [Algebra.Etale R B] :
    Module.Projective R B ∧
      ∀ (p : Ideal R) [p.IsPrime], Algebra.Etale p.ResidueField (p.Fiber B) := by
  have : Module.FinitePresentation R B := .of_finite_of_finitePresentation R B
  exact ⟨Module.Flat.projective_of_finitePresentation, fun _ _ ↦ inferInstance⟩

/-- IX.1.9 (affine form): an `R`-algebra `B` is finite étale iff it is a finitely generated
projective (= locally free of finite type) `R`-module whose fibres `κ(p) ⊗_R B` are étale,
i.e. finite products of finite separable extensions of `κ(p)`. (The global form over a
scheme `S`, with `𝒜` a quasi-coherent algebra, follows by working on affine opens.) -/
theorem finite_etale_iff (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    (Module.Finite R B ∧ Algebra.Etale R B) ↔
      (Module.Finite R B ∧ Module.Projective R B ∧
        ∀ (p : Ideal R) [p.IsPrime], Algebra.Etale p.ResidueField (p.Fiber B)) := by
  refine ⟨fun ⟨_, _⟩ ↦ ⟨inferInstance, projective_and_etale_fiber_of_finite_etale R B⟩,
    fun ⟨_, _, h⟩ ↦ ⟨inferInstance, etale_of_projective_of_etale_fiber h⟩⟩

/-- IX.1.10 (statement): for `X` proper over the spectrum `S` of a complete noetherian local ring,
restriction to the closed fibre `X₀` is an equivalence between étale coverings of `X` and of
`X₀`. In `SGA.SGA1.ExposeIX.EtaleCoveringsClosedFibre` this is proved for `X` projective over `S`
(`etaleCoveringsOfClosedFibre_of_isClosedImmersion`, from Grothendieck's existence theorem in the
foundations), the full faithfulness is proved for every proper `X` (`full_pullback_closedFibre`,
`faithful_pullback_closedFibre`), and the statement is reduced to the essential surjectivity along
the first thickening (`etaleCoveringsOfClosedFibreStatement_of_essSurj`). -/
def EtaleCoveringsOfClosedFibreStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsProper f],
    (MorphismProperty.Over.pullback etaleCovering ⊤
      (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))).IsEquivalence

end Recollections

/-! ### Descent of surjectivity and radiciality along surjective morphisms -/

/-- Surjectivity descends along surjective morphisms. -/
instance surjective_descendsAlong_surjective : DescendsAlong @Surjective @Surjective where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨x, rfl⟩ := f.surjective z
    obtain ⟨a, rfl⟩ := fst.surjective x
    exact ⟨snd a, by rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]⟩

/-- VIII.3.1 (used in IX.3): being radicial descends along surjective morphisms. -/
instance universallyInjective_descendsAlong_surjective :
    DescendsAlong @UniversallyInjective @Surjective := by
  rw [universallyInjective_eq_diagonal]
  exact instDescendsAlongDiagonalOfRespectsIsoOfIsStableUnderBaseChange _ _

/-! ### §3: descent of morphisms of étale schemes -/

section Descent

variable {X Y S : Scheme.{u}}

/-- If the diagonal of `q : Y ⟶ S` is an open immersion (e.g. `q` unramified), two
`S`-morphisms `u v : T ⟶ Y` are equal as soon as `(u, v) : T ⟶ Y ×_S Y` lands set-theoretically
in the diagonal. -/
lemma eq_of_range_lift_subset {T : Scheme.{u}} (q : Y ⟶ S) [IsOpenImmersion (pullback.diagonal q)]
    {u v : T ⟶ Y} (h : u ≫ q = v ≫ q)
    (hr : Set.range (pullback.lift u v h) ⊆ Set.range (pullback.diagonal q)) : u = v := by
  have hk := IsOpenImmersion.lift_fac (pullback.diagonal q) (pullback.lift u v h) hr
  have h₁ := congrArg (· ≫ pullback.fst q q) hk
  have h₂ := congrArg (· ≫ pullback.snd q q) hk
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    pullback.lift_fst, pullback.lift_snd] at h₁ h₂
  rw [← h₁, h₂]

/-- IX.3.1, key step: a surjective morphism `k : T' ⟶ T` is an epimorphism with respect to
`S`-morphisms into an unramified `S`-scheme. -/
theorem hom_ext_of_surjective {T' T : Scheme.{u}} (k : T' ⟶ T) [Surjective k] (q : Y ⟶ S)
    [FormallyUnramified q] [LocallyOfFiniteType q] {u v : T ⟶ Y} (h : u ≫ q = v ≫ q)
    (hk : k ≫ u = k ≫ v) : u = v := by
  apply eq_of_range_lift_subset q h
  rintro _ ⟨t, rfl⟩
  obtain ⟨t', rfl⟩ := k.surjective t
  have : k ≫ pullback.lift u v h = k ≫ u ≫ pullback.diagonal q := by
    apply pullback.hom_ext <;> simp [hk]
  refine ⟨u (k t'), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, this]

/-- IX.3.1: let `g : S' ⟶ S` be surjective and `Y` unramified over `S`. Two `S`-morphisms
`X ⟶ Y` with the same base change `X ×_S S' ⟶ Y ×_S S'` are equal. -/
theorem pullback_map_injective {S' : Scheme.{u}} (g : S' ⟶ S) [Surjective g] {p : X ⟶ S}
    (q : Y ⟶ S)
    [FormallyUnramified q] [LocallyOfFiniteType q] {φ₁ φ₂ : X ⟶ Y} (h₁ : φ₁ ≫ q = p)
    (h₂ : φ₂ ≫ q = p)
    (h : pullback.map p g q g φ₁ (𝟙 _) (𝟙 S) (by simp [h₁]) (by simp) =
      pullback.map p g q g φ₂ (𝟙 _) (𝟙 S) (by simp [h₂]) (by simp)) :
    φ₁ = φ₂ := by
  refine hom_ext_of_surjective (pullback.fst p g) q (h₁.trans h₂.symm) ?_
  have := congrArg (· ≫ pullback.fst q g) h
  simpa using this

section Core

variable {X' X Y : Scheme.{u}} (h : X' ⟶ X) (q : Y ⟶ X) (φ' : X' ⟶ Y)

/-- The locus of `Y ×_X X'` where the first projection agrees with `φ' ∘ pr₂`; it is the
underlying set of the graph of `φ'`. -/
noncomputable def graphLocus [IsOpenImmersion (pullback.diagonal q)] (hφ : φ' ≫ q = h) :
    (pullback q h).Opens :=
  pullback.lift (pullback.fst q h) (pullback.snd q h ≫ φ')
    (by rw [pullback.condition, Category.assoc, hφ]) ⁻¹ᵁ (pullback.diagonal q).opensRange

variable {h q φ'}

lemma eq_of_range_subset_graphLocus [IsOpenImmersion (pullback.diagonal q)] (hφ : φ' ≫ q = h)
    {T : Scheme.{u}} (t : T ⟶ pullback q h) (ht : Set.range t ⊆ graphLocus h q φ' hφ) :
    t ≫ pullback.fst q h = t ≫ pullback.snd q h ≫ φ' := by
  refine eq_of_range_lift_subset (u := t ≫ pullback.fst q h) (v := t ≫ pullback.snd q h ≫ φ') q
    (by simp only [Category.assoc, pullback.condition, hφ]) ?_
  rintro _ ⟨x, rfl⟩
  have : pullback.lift (f := q) (g := q) (t ≫ pullback.fst q h) (t ≫ pullback.snd q h ≫ φ')
      (by simp only [Category.assoc, pullback.condition, hφ]) = t ≫ pullback.lift (pullback.fst q h)
        (pullback.snd q h ≫ φ') (by rw [pullback.condition, Category.assoc, hφ]) := by
    apply pullback.hom_ext <;> simp
  rw [this, Scheme.Hom.comp_apply]
  exact ht ⟨x, rfl⟩

lemma preimage_graphLocus_eq [IsOpenImmersion (pullback.diagonal q)] (hφ : φ' ≫ q = h)
    (hker : pullback.fst h h ≫ φ' = pullback.snd h h ≫ φ') :
    pullback.fst (pullback.fst q h) (pullback.fst q h) ⁻¹ᵁ graphLocus h q φ' hφ =
      pullback.snd (pullback.fst q h) (pullback.fst q h) ⁻¹ᵁ graphLocus h q φ' hφ := by
  set a := pullback.fst q h
  set b := pullback.snd q h
  set P₁ := pullback.fst a a
  set P₂ := pullback.snd a a
  let m : pullback a a ⟶ pullback h h := pullback.lift (P₁ ≫ b) (P₂ ≫ b) (by
    simp only [Category.assoc, b, ← pullback.condition, P₁, P₂, a]
    rw [← Category.assoc, pullback.condition, Category.assoc])
  have hm : P₁ ≫ b ≫ φ' = P₂ ≫ b ≫ φ' := by
    have := congrArg (m ≫ ·) hker
    simpa [m] using this
  have : P₁ ≫ pullback.lift a (b ≫ φ') (by rw [pullback.condition, Category.assoc, hφ]) =
      P₂ ≫ pullback.lift a (b ≫ φ') (by rw [pullback.condition, Category.assoc, hφ]) := by
    apply pullback.hom_ext
    · simp [P₁, P₂, pullback.condition]
    · simpa using hm
  simp only [graphLocus, ← Scheme.Hom.comp_preimage, a, b, P₁, P₂] at this ⊢
  rw [this]

variable (h q φ')

/-- IX.3.2, core case (`X` over itself): let `h : X' ⟶ X` be universally submersive and
`q : Y ⟶ X` étale. A morphism `φ' : X' ⟶ Y` over `X` whose two composites with the
projections `X' ×_X X' ⇉ X'` agree is `h ≫ σ` for a unique section `σ` of `q`. -/
theorem existsUnique_section_of_universallySubmersive [UniversallySubmersive h] [Etale q]
    (hφ : φ' ≫ q = h) (hker : pullback.fst h h ≫ φ' = pullback.snd h h ≫ φ') :
    ∃! σ : X ⟶ Y, σ ≫ q = 𝟙 X ∧ h ≫ σ = φ' := by
  set a := pullback.fst q h
  set b := pullback.snd q h
  set L := graphLocus h q φ' hφ
  -- the graph locus is the preimage of an open subset `U` of `Y`
  obtain ⟨U, hU, -⟩ := exists_unique_opens_preimage_eq a L (preimage_graphLocus_eq hφ hker)
  have hU' : graphLocus h q φ' hφ = a ⁻¹ᵁ U := hU.symm
  -- the graph of `φ'` lies in `L`, so `φ'` lands in `U`
  let σ' : X' ⟶ pullback q h := pullback.lift φ' (𝟙 X') (by simp [hφ])
  have hσ'L : Set.range σ' ⊆ L := by
    rintro _ ⟨x, rfl⟩
    have : σ' ≫ pullback.lift a (b ≫ φ') (by rw [pullback.condition, Category.assoc, hφ]) =
        φ' ≫ pullback.diagonal q := by
      apply pullback.hom_ext <;> simp [σ', a, b]
    change pullback.lift a (b ≫ φ') _ (σ' x) ∈ (pullback.diagonal q).opensRange
    rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hφU : Set.range φ' ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : σ' x ∈ a ⁻¹ᵁ U := hU ▸ hσ'L ⟨x, rfl⟩
    simpa [← Scheme.Hom.comp_apply, σ', a] using this
  -- `U ⟶ X` is surjective
  have : Surjective (U.ι ≫ q) := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨x', rfl⟩ := h.surjective x
    obtain ⟨y, hy⟩ := hφU ⟨x', rfl⟩
    exact ⟨y, by rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, hφ]⟩
  -- `U ⟶ X` is radicial, since its base change `a⁻¹(U) ⟶ X'` is a monomorphism
  have : Mono ((a ⁻¹ᵁ U).ι ≫ b) := by
    constructor
    intro T t₁ t₂ ht
    have key (t : T ⟶ a ⁻¹ᵁ U) : t ≫ (a ⁻¹ᵁ U).ι ≫ a = t ≫ (a ⁻¹ᵁ U).ι ≫ b ≫ φ' := by
      have := eq_of_range_subset_graphLocus hφ (t ≫ (a ⁻¹ᵁ U).ι) (by
        rw [hU', coe_comp_eq_comp, Set.range_comp]
        exact (Set.image_subset_range _ _).trans (by simp))
      simpa using this
    rw [← cancel_mono (a ⁻¹ᵁ U).ι]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, key, key]
      simp only [← Category.assoc] at ht ⊢
      rw [ht]
    · simpa using ht
  have hpb : IsPullback (a ∣_ U) ((a ⁻¹ᵁ U).ι ≫ b) (U.ι ≫ q) h :=
    (isPullback_morphismRestrict a U).paste_vert (IsPullback.of_hasPullback q h)
  have : UniversallyInjective (U.ι ≫ q) :=
    of_isPullback_of_descendsAlong (P := @UniversallyInjective) (Q := @Surjective) hpb.flip
      inferInstance inferInstance
  have := isIso_of_etale_of_universallyInjective_of_surjective (U.ι ≫ q)
  -- the section
  have e : U.ι ≫ q ≫ inv (U.ι ≫ q) ≫ U.ι = U.ι := by
    rw [← Category.assoc, IsIso.hom_inv_id_assoc]
  have hfac := IsOpenImmersion.lift_fac U.ι φ' hφU
  have hσ₀ : h ≫ inv (U.ι ≫ q) ≫ U.ι = φ' := by
    rw [← hφ, ← hfac, Category.assoc, Category.assoc, e]
  refine ⟨inv (U.ι ≫ q) ≫ U.ι, ⟨by simp, hσ₀⟩, fun σ hσ ↦ ?_⟩
  exact hom_ext_of_surjective h q (by rw [hσ.1]; simp) (hσ.2.trans hσ₀.symm)

end Core

variable {S' X' : Scheme.{u}}

/-- IX.3.2, kernel-pair form: let `h : X' ⟶ X` be universally submersive, `p : X ⟶ S`, and
`q : Y ⟶ S` étale. An `S`-morphism `φ' : X' ⟶ Y` whose two composites with the projections
`X' ×_X X' ⇉ X'` agree factors uniquely as `h ≫ φ` with `φ` an `S`-morphism. -/
theorem existsUnique_hom_of_kernelPair (h : X' ⟶ X) [UniversallySubmersive h] (p : X ⟶ S)
    (q : Y ⟶ S) [Etale q] (φ' : X' ⟶ Y) (hφ : φ' ≫ q = h ≫ p)
    (hker : pullback.fst h h ≫ φ' = pullback.snd h h ≫ φ') :
    ∃! φ : X ⟶ Y, φ ≫ q = p ∧ h ≫ φ = φ' := by
  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, -⟩ := existsUnique_section_of_universallySubmersive h
    (pullback.snd q p) (pullback.lift φ' h hφ) (by simp) (by
      apply pullback.hom_ext
      · simpa using hker
      · simpa using pullback.condition)
  refine ⟨σ ≫ pullback.fst q p, ⟨?_, ?_⟩, fun φ hφ' ↦ ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hσ₁, Category.id_comp]
  · rw [← Category.assoc, hσ₂, pullback.lift_fst]
  · refine hom_ext_of_surjective h q ?_ ?_
    · rw [hφ'.1, Category.assoc, pullback.condition, ← Category.assoc, hσ₁, Category.id_comp]
    · rw [hφ'.2, ← Category.assoc, hσ₂, pullback.lift_fst]

/-- IX.3.2: let `g : S' ⟶ S` be universally submersive, `X` an `S`-scheme and `Y` an étale
`S`-scheme; write `X' = X ×_S S'`. The diagram
`Hom_S(X, Y) → Hom_{S'}(X', Y') ⇉ Hom_{S''}(X'', Y'')` is exact.

Here an `S'`-morphism `X' ⟶ Y' = Y ×_S S'` is the same as an `S`-morphism `φ' : X' ⟶ Y`, and
since `X'' = X ×_S S'' = X' ×_X X'`, the two induced `S''`-morphisms `X'' ⟶ Y''` agree iff the
two composites `X' ×_X X' ⇉ X' ⟶ Y` agree. So the statement says: such a `φ'` is the base change
of a unique `S`-morphism `φ : X ⟶ Y`. -/
theorem existsUnique_hom_of_universallySubmersive (g : S' ⟶ S) [UniversallySubmersive g]
    (p : X ⟶ S) (q : Y ⟶ S) [Etale q] (φ' : pullback p g ⟶ Y)
    (hφ : φ' ≫ q = pullback.fst p g ≫ p)
    (hker : pullback.fst (pullback.fst p g) (pullback.fst p g) ≫ φ' =
      pullback.snd (pullback.fst p g) (pullback.fst p g) ≫ φ') :
    ∃! φ : X ⟶ Y, φ ≫ q = p ∧ pullback.fst p g ≫ φ = φ' :=
  existsUnique_hom_of_kernelPair _ p q φ' hφ hker

end Descent

/-- VI / IX.3.3: `g : S' ⟶ S` is a *descent morphism* for the fibred category of `S`-schemes
whose structure morphism satisfies `P`: for `X`, `Y` in this category, with `X' = X ×_S S'`,
the diagram `Hom_S(X, Y) → Hom_{S'}(X', Y') ⇉ Hom_{S''}(X'', Y'')` is exact, written in the
kernel-pair form explained at `existsUnique_hom_of_universallySubmersive`. Equivalently, the
functor from `P`-schemes over `S` to `P`-schemes over `S'` with descent data is fully
faithful. -/
def IsDescentMorphism (P : MorphismProperty Scheme.{u}) {S' S : Scheme.{u}} (g : S' ⟶ S) :
    Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (p : X ⟶ S) (q : Y ⟶ S), P p → P q →
    ∀ φ' : pullback p g ⟶ Y, φ' ≫ q = pullback.fst p g ≫ p →
      pullback.fst (pullback.fst p g) (pullback.fst p g) ≫ φ' =
        pullback.snd (pullback.fst p g) (pullback.fst p g) ≫ φ' →
      ∃! φ : X ⟶ Y, φ ≫ q = p ∧ pullback.fst p g ≫ φ = φ'

/-- IX.3.3: a universally submersive morphism is a descent morphism for the fibred category of
étale schemes. (IX.3.2 gives more: `X` may be arbitrary.) -/
theorem isDescentMorphism_etale {S' S : Scheme.{u}} (g : S' ⟶ S) [UniversallySubmersive g] :
    IsDescentMorphism @Etale g := by
  intro X Y p q _ hq φ' hφ hker
  have : Etale q := hq
  exact existsUnique_hom_of_universallySubmersive g p q φ' hφ hker

/-! ### Base change functors on étale schemes -/

section Functor

variable {S' S : Scheme.{u}} (g : S' ⟶ S)

/-- For a radicial `h`, the kernel-pair condition of IX.3.2 is automatic: the diagonal of `h`
is surjective, so IX.3.1 applies. -/
lemma kernelPair_condition_of_universallyInjective {X' X Y S : Scheme.{u}} (h : X' ⟶ X)
    [UniversallyInjective h] (p : X ⟶ S) (q : Y ⟶ S) [FormallyUnramified q]
    [LocallyOfFiniteType q] (φ' : X' ⟶ Y) (hφ : φ' ≫ q = h ≫ p) :
    pullback.fst h h ≫ φ' = pullback.snd h h ≫ φ' := by
  have : Surjective (pullback.diagonal h) := (UniversallyInjective.iff_diagonal h).mp ‹_›
  refine hom_ext_of_surjective (pullback.diagonal h) q ?_ (by simp)
  simp only [Category.assoc, hφ, pullback.condition_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.4.10 (full faithfulness) and IX.1.7 (full faithfulness): along a radicial universally
submersive morphism `g : S' ⟶ S`, every `S`-morphism `X ×_S S' ⟶ Y` into an étale `Y` comes
from a unique `S`-morphism `X ⟶ Y`. -/
theorem existsUnique_hom_of_universallyInjective [UniversallyInjective g]
    [UniversallySubmersive g] {X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) [Etale q]
    (φ' : pullback p g ⟶ Y) (hφ : φ' ≫ q = pullback.fst p g ≫ p) :
    ∃! φ : X ⟶ Y, φ ≫ q = p ∧ pullback.fst p g ≫ φ = φ' :=
  have : UniversallyInjective (pullback.fst p g) := MorphismProperty.pullback_fst _ _ ‹_›
  existsUnique_hom_of_universallySubmersive g p q φ' hφ
    (kernelPair_condition_of_universallyInjective _ p q φ' hφ)

variable (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]

/-- IX.3.1, functorial form: if every `P`-morphism is unramified, base change of `P`-schemes
along a surjective morphism is faithful. -/
lemma faithful_overPullback_of_surjective [Surjective g]
    (hP : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), P f → FormallyUnramified f ∧ LocallyOfFiniteType f) :
    (MorphismProperty.Over.pullback P ⊤ g).Faithful where
  map_injective {A B} φ₁ φ₂ h := by
    have := (hP _ B.prop).1
    have := (hP _ B.prop).2
    ext1
    refine hom_ext_of_surjective (pullback.fst A.hom g) B.hom
      (by rw [MorphismProperty.Over.w, MorphismProperty.Over.w]) ?_
    have := congrArg (fun k ↦ k.left ≫ pullback.fst B.hom g) h
    simp only [MorphismProperty.Over.pullback_map_left] at this
    exact (pullback.lift_fst _ _ _).symm.trans (this.trans (pullback.lift_fst _ _ _))

/-- A criterion for the base change functor on `P`-schemes to be full: every `S`-morphism
`X ×_S S' ⟶ Y` between `P`-schemes comes from an `S`-morphism `X ⟶ Y`. -/
lemma full_overPullback_of_exists
    (H : ∀ ⦃X Y : Scheme.{u}⦄ (p : X ⟶ S) (q : Y ⟶ S), P p → P q →
      ∀ φ' : pullback p g ⟶ Y, φ' ≫ q = pullback.fst p g ≫ p →
        ∃ φ : X ⟶ Y, φ ≫ q = p ∧ pullback.fst p g ≫ φ = φ') :
    (MorphismProperty.Over.pullback P ⊤ g).Full where
  map_surjective {A B} ψ := by
    let ψ' : pullback A.hom g ⟶ pullback B.hom g := ψ.left
    have hψ : ψ' ≫ pullback.snd B.hom g = pullback.snd A.hom g := Over.w ψ
    obtain ⟨φ, hφ₁, hφ₂⟩ := H A.hom B.hom A.prop B.prop (ψ' ≫ pullback.fst B.hom g) (by
      rw [Category.assoc, pullback.condition (f := B.hom), reassoc_of% hψ,
        pullback.condition (f := A.hom)])
    refine ⟨MorphismProperty.Over.homMk φ hφ₁, ?_⟩
    ext1
    rw [MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hφ₂
    · exact (pullback.lift_snd _ _ _).trans hψ.symm

/-- IX.4.10 and IX.1.7, full faithfulness: if every `P`-morphism is étale, base change of
`P`-schemes along a radicial universally submersive morphism is fully faithful. -/
noncomputable def fullyFaithfulOverPullbackOfUniversallyInjective [UniversallyInjective g]
    [UniversallySubmersive g] (hP : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), P f → Etale f) :
    (MorphismProperty.Over.pullback P ⊤ g).FullyFaithful :=
  have := faithful_overPullback_of_surjective g P fun _ _ f hf ↦
    have := hP f hf; ⟨inferInstance, inferInstance⟩
  have := full_overPullback_of_exists g P fun _ _ p q _ hq φ' hφ ↦
    have := hP q hq
    (existsUnique_hom_of_universallyInjective g p q φ' hφ).exists
  .ofFullyFaithful _

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.3.1: base change of étale schemes along a surjective morphism is faithful. -/
instance faithful_pullback_etale [Surjective g] :
    (MorphismProperty.Over.pullback @Etale ⊤ g).Faithful :=
  faithful_overPullback_of_surjective g @Etale fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.4.10 and IX.1.7, full faithfulness: base change of étale schemes along a radicial
universally submersive morphism is fully faithful. -/
noncomputable def fullyFaithfulPullbackEtale [UniversallyInjective g]
    [UniversallySubmersive g] : (MorphismProperty.Over.pullback @Etale ⊤ g).FullyFaithful :=
  fullyFaithfulOverPullbackOfUniversallyInjective g @Etale fun _ _ _ h ↦ h

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.1.7, full faithfulness: let `S₀ ⟶ S` be a closed immersion defined by a nil ideal, i.e.
a surjective closed immersion. Base change `X ↦ X ×_S S₀` from étale `S`-schemes to étale
`S₀`-schemes is fully faithful. -/
noncomputable def fullyFaithfulPullbackEtaleOfIsClosedImmersion {S₀ : Scheme.{u}}
    (i : S₀ ⟶ S) [IsClosedImmersion i] [Surjective i] :
    (MorphismProperty.Over.pullback @Etale ⊤ i).FullyFaithful :=
  fullyFaithfulPullbackEtale i

end Functor

/-! ### IX.3.4: morphisms with geometrically connected fibres -/

section Connected

variable {X Y Z : Scheme.{u}}

/-- IX.3.4: if `f : X ⟶ S` is submersive with connected fibres and `S` is connected, then `X` is
connected. -/
theorem connectedSpace_of_submersive (f : X ⟶ Y) [Submersive f] [GeometricallyConnected f]
    [ConnectedSpace Y] : ConnectedSpace X := by
  have := (Scheme.Hom.isQuotientMap f).isCoinducing.isConnected_preimage_of_isClosed
    f.isConnected_preimage_singleton isClosed_univ isConnected_univ
  simpa [connectedSpace_iff_univ] using this

/-- IX.3.4, proof: a composite `f ≫ g` of morphisms with geometrically connected fibres has
geometrically connected fibres when `f` is universally submersive. -/
theorem geometricallyConnected_comp (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyConnected f]
    [UniversallySubmersive f] [GeometricallyConnected g] : GeometricallyConnected (f ≫ g) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  rw [← (pullbackRightPullbackFstIso g x f).hom.homeomorph.connectedSpace_iff]
  have : ConnectedSpace ↥(pullback g x) :=
    GeometricallyConnected.geometrically_connectedSpace x _ _ (.of_hasPullback g x)
  exact connectedSpace_of_submersive (pullback.snd f (pullback.fst g x))

variable {S' S : Scheme.{u}} (g : S' ⟶ S)

/-- IX.3.4, first assertion: if `g : S' ⟶ S` is universally submersive with geometrically
connected fibres and `S` is connected, then `S'` is connected. -/
theorem connectedSpace_of_universallySubmersive [UniversallySubmersive g]
    [GeometricallyConnected g] [ConnectedSpace S] : ConnectedSpace S' :=
  connectedSpace_of_submersive g

/-- IX.3.4, key step: along a universally submersive `g` with geometrically connected fibres,
every `S`-morphism `φ' : X ×_S S' ⟶ Y` into an étale `Y` satisfies the kernel-pair condition
of IX.3.2. The coincidence locus in `X'' = X' ×_X X'` of the two composites is open, closed in
each fibre of `X'' ⟶ X` (fibres of étale morphisms are discrete) and meets every fibre, which is
connected. -/
theorem kernelPair_condition_of_geometricallyConnected [UniversallySubmersive g]
    [GeometricallyConnected g] {X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) [Etale q]
    (φ' : pullback p g ⟶ Y) (hφ : φ' ≫ q = pullback.fst p g ≫ p) :
    pullback.fst (pullback.fst p g) (pullback.fst p g) ≫ φ' =
      pullback.snd (pullback.fst p g) (pullback.fst p g) ≫ φ' := by
  set h := pullback.fst p g
  have hc : (pullback.fst h h ≫ φ') ≫ q = (pullback.snd h h ≫ φ') ≫ q := by
    simp only [Category.assoc, hφ, pullback.condition_assoc]
  apply eq_of_range_lift_subset q hc
  set c := pullback.lift _ _ hc
  set r := pullback.fst h h ≫ h
  have : GeometricallyConnected r := geometricallyConnected_comp _ _
  have : LocallyQuasiFinite (pullback.fst q q ≫ q) :=
    locallyQuasiFinite_of_formallyUnramified _
  rintro _ ⟨z, rfl⟩
  -- the fibre `F` of `r` through `z`, and the discrete fibre `D` of `Y ×_S Y` below it
  set F := r ⁻¹' {r z}
  have hF : _root_.IsConnected F := r.isConnected_preimage_singleton _
  set D := (pullback.fst q q ≫ q) ⁻¹' {p (r z)}
  have hD : DiscreteTopology D :=
    ((pullback.fst q q ≫ q).isDiscrete_preimage_singleton _).to_subtype
  have hcF (w) (hw : w ∈ F) : c w ∈ D := by
    have : c ≫ pullback.fst q q ≫ q = r ≫ p := by simp [c, r, h, hφ]
    change (pullback.fst q q ≫ q) (c w) = p (r z)
    rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply, show r w = r z from hw]
  set W := c ⁻¹' Set.range (pullback.diagonal q)
  have hW : IsOpen W :=
    (pullback.diagonal q).isOpenEmbedding.isOpen_range.preimage c.continuous
  obtain ⟨O, hO, hOD⟩ : ∃ O, IsOpen O ∧
      Subtype.val ⁻¹' O = {d : D | d.1 ∉ Set.range (pullback.diagonal q)} :=
    isOpen_induced_iff.mp (isOpen_discrete _)
  have hmem (w) (hw : w ∈ F) : c w ∈ O ↔ c w ∉ Set.range (pullback.diagonal q) :=
    Set.ext_iff.mp hOD ⟨c w, hcF w hw⟩
  -- a point of `F` in the coincidence locus, coming from the diagonal of `h`
  obtain ⟨x', hx'⟩ := h.surjective (r z)
  set w₀ := pullback.diagonal h x'
  have hw₀F : w₀ ∈ F := by
    change r w₀ = r z
    rw [← hx', ← Scheme.Hom.comp_apply]
    simp [r]
  have hw₀W : w₀ ∈ W := by
    have : pullback.diagonal h ≫ c = φ' ≫ pullback.diagonal q := by
      apply pullback.hom_ext <;> simp [c]
    refine ⟨φ' x', ?_⟩
    change _ = c (pullback.diagonal h x')
    rw [← Scheme.Hom.comp_apply, ← this, Scheme.Hom.comp_apply]
  have hcover : F ⊆ W ∪ c ⁻¹' O := fun w hw ↦ by
    by_cases hw' : c w ∈ Set.range (pullback.diagonal q)
    · exact Or.inl hw'
    · exact Or.inr ((hmem w hw).mpr hw')
  have hdisj : F ∩ (W ∩ c ⁻¹' O) = ∅ := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hw hwW hwO
    exact (hmem w hw).mp hwO hwW
  have hFW : F ⊆ W := by
    rcases isPreconnected_iff_subset_of_disjoint.mp hF.isPreconnected W (c ⁻¹' O) hW
      (hO.preimage c.continuous) hcover hdisj with hsub | hsub
    · exact hsub
    · exact absurd (hsub hw₀F) ((hmem w₀ hw₀F).not.mpr (not_not.mpr hw₀W))
  exact hFW rfl

/-- IX.3.4, second assertion: along a universally submersive morphism with geometrically
connected fibres, every `S`-morphism `X ×_S S' ⟶ Y` into an étale `Y` comes from a unique
`S`-morphism `X ⟶ Y`. -/
theorem existsUnique_hom_of_geometricallyConnected [UniversallySubmersive g]
    [GeometricallyConnected g] {X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) [Etale q]
    (φ' : pullback p g ⟶ Y) (hφ : φ' ≫ q = pullback.fst p g ≫ p) :
    ∃! φ : X ⟶ Y, φ ≫ q = p ∧ pullback.fst p g ≫ φ = φ' :=
  existsUnique_hom_of_universallySubmersive g p q φ' hφ
    (kernelPair_condition_of_geometricallyConnected g p q φ' hφ)

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.3.4, second assertion: base change of étale schemes along a universally submersive
morphism with geometrically connected fibres is fully faithful. -/
noncomputable def fullyFaithfulPullbackEtaleOfGeometricallyConnected [UniversallySubmersive g]
    [GeometricallyConnected g] : (MorphismProperty.Over.pullback @Etale ⊤ g).FullyFaithful :=
  have := full_overPullback_of_exists g @Etale fun _ _ p q _ hq φ' hφ ↦
    have : Etale q := hq
    (existsUnique_hom_of_geometricallyConnected g p q φ' hφ).exists
  .ofFullyFaithful _

end Connected

end SGA.SGA1.ExposeIX
