/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import SGA.SGA1.ExposeI.Etale

/-!
# SGA 1, Exposé I, §5: the fundamental property of étale morphisms

The main theorem I.5.1 is that an étale radicial morphism is an open immersion.
Mathlib calls radicial morphisms `UniversallyInjective` (injective with purely
inseparable residue extensions, Stacks 01S4). The argument recorded here is:
the diagonal of an étale morphism is an open immersion, a radicial morphism has
surjective diagonal, so the diagonal is an isomorphism and the morphism is a
monomorphism; a flat monomorphism of finite presentation is an open immersion.

The corollaries I.5.2–I.5.6 are proved in full. For I.5.5 and I.5.6 we follow
SGA's "topological" argument through sections (I.5.3), so the closed immersion
`S₀ ⟶ S` only needs to be surjective: no nilpotence hypothesis is used. The
fibrewise criteria I.5.7–I.5.9 are in `Fibrewise.lean`.
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.1, sufficiency: an étale universally injective morphism is an open immersion. -/
theorem isOpenImmersion_of_etale_of_universallyInjective [Etale f] [UniversallyInjective f] :
    IsOpenImmersion f := by
  have : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr
      ⟨inferInstance, (UniversallyInjective.iff_diagonal f).mp inferInstance⟩
  have : Mono f := (pullback.isIso_diagonal_iff f).mp inferInstance
  exact IsOpenImmersion.of_flat_of_mono f

/-- I.5.1, necessity: an open immersion is étale and radicial. -/
theorem etale_and_universallyInjective_of_isOpenImmersion [IsOpenImmersion f] :
    Etale f ∧ UniversallyInjective f :=
  ⟨inferInstance, inferInstance⟩

/-- I.5.1: étale and radicial if and only if an open immersion. -/
theorem isOpenImmersion_iff_etale_and_universallyInjective :
    IsOpenImmersion f ↔ Etale f ∧ UniversallyInjective f :=
  ⟨fun _ ↦ etale_and_universallyInjective_of_isOpenImmersion f,
    fun ⟨_, _⟩ ↦ isOpenImmersion_of_etale_of_universallyInjective f⟩

/-- I.5.1: an étale morphism is an isomorphism iff it is surjective and radicial. -/
theorem isIso_iff_etale_and_universallyInjective_and_surjective :
    IsIso f ↔ Etale f ∧ UniversallyInjective f ∧ Surjective f := by
  rw [isIso_iff_isOpenImmersion_and_surjective, isOpenImmersion_iff_etale_and_universallyInjective,
    and_assoc]

/-- I.5.2, first step: a closed immersion which is étale is an open immersion. -/
theorem isOpenImmersion_of_isClosedImmersion_of_etale [IsClosedImmersion f] [Etale f] :
    IsOpenImmersion f :=
  isOpenImmersion_of_etale_of_universallyInjective f

/-- The range of a morphism which is both an open and a closed immersion, out of a
connected scheme, is the connected component of each of its points. -/
theorem range_eq_connectedComponent [IsOpenImmersion f] [IsClosedImmersion f]
    [PreconnectedSpace X] (x : X) : Set.range f = connectedComponent (f x) :=
  le_antisymm ((isPreconnected_range f.continuous).subset_connectedComponent ⟨x, rfl⟩)
    (IsClopen.connectedComponent_subset
      ⟨f.isClosedEmbedding.isClosed_range, f.isOpenEmbedding.isOpen_range⟩ ⟨x, rfl⟩)

/-- I.5.2: an étale closed immersion out of a connected scheme is an isomorphism onto
a connected component, i.e. an open immersion whose image is a connected component. -/
theorem isOpenImmersion_and_range_eq_connectedComponent [IsClosedImmersion f] [Etale f]
    [PreconnectedSpace X] (x : X) :
    IsOpenImmersion f ∧ Set.range f = connectedComponent (f x) := by
  have := isOpenImmersion_of_isClosedImmersion_of_etale f
  exact ⟨this, range_eq_connectedComponent f x⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.3: a section of a separated morphism is a closed immersion. -/
theorem isClosedImmersion_of_section {s : Y ⟶ X} (hs : s ≫ f = 𝟙 Y) [IsSeparated f] :
    IsClosedImmersion s := by
  have : IsIso (s ≫ f) := hs.symm ▸ inferInstance
  have : IsClosedImmersion (s ≫ f) := inferInstance
  exact IsClosedImmersion.of_comp s f

set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.3: a section of an unramified morphism is étale (I.4.8). -/
theorem etale_of_section {s : Y ⟶ X} (hs : s ≫ f = 𝟙 Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : Etale s := by
  have : Etale (s ≫ f) := hs.symm ▸ (inferInstance : Etale (𝟙 Y))
  exact Etale.of_comp s f

/-- I.5.3: a section of an unramified morphism is an open immersion, being an étale
monomorphism. (Separatedness is not needed for this part.) -/
theorem isOpenImmersion_of_section {s : Y ⟶ X} (hs : s ≫ f = 𝟙 Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : IsOpenImmersion s := by
  have := etale_of_section f hs
  have : IsSplitMono s := ⟨⟨⟨f, hs⟩⟩⟩
  exact IsOpenImmersion.of_flat_of_mono s

/-- I.5.3: over a connected base, a section of a separated unramified morphism is an
isomorphism onto a connected component: it is an open immersion whose range is the
connected component of each of its points. -/
theorem isOpenImmersion_and_range_eq_connectedComponent_of_section {s : Y ⟶ X}
    (hs : s ≫ f = 𝟙 Y) [IsSeparated f] [FormallyUnramified f] [LocallyOfFiniteType f]
    [PreconnectedSpace Y] (y : Y) :
    IsOpenImmersion s ∧ Set.range s = connectedComponent (s y) := by
  have := isClosedImmersion_of_section f hs
  have := isOpenImmersion_of_section f hs
  exact ⟨this, range_eq_connectedComponent s y⟩

/-- Two sections of the same morphism which are open immersions with the same range
are equal. -/
theorem section_eq_of_range_eq {s t : Y ⟶ X} [IsOpenImmersion s] [IsOpenImmersion t]
    (hs : s ≫ f = 𝟙 Y) (ht : t ≫ f = 𝟙 Y) (h : Set.range s = Set.range t) : s = t := by
  have e := IsOpenImmersion.isoOfRangeEq_hom_fac s t h
  have : (IsOpenImmersion.isoOfRangeEq s t h).hom = 𝟙 Y := calc
    _ = (IsOpenImmersion.isoOfRangeEq s t h).hom ≫ t ≫ f := by rw [ht, Category.comp_id]
    _ = 𝟙 Y := by rw [← Category.assoc, e, hs]
  rw [← e, this, Category.id_comp]

/-- I.5.3: over a connected base, a section of a separated unramified morphism is
known once its value at one point is known. -/
theorem section_eq_of_apply_eq {s t : Y ⟶ X} (hs : s ≫ f = 𝟙 Y) (ht : t ≫ f = 𝟙 Y)
    [IsSeparated f] [FormallyUnramified f] [LocallyOfFiniteType f] [PreconnectedSpace Y]
    (y : Y) (hy : s y = t y) : s = t := by
  obtain ⟨_, hs'⟩ := isOpenImmersion_and_range_eq_connectedComponent_of_section f hs y
  obtain ⟨_, ht'⟩ := isOpenImmersion_and_range_eq_connectedComponent_of_section f ht y
  exact section_eq_of_range_eq f hs ht (by rw [hs', ht', hy])

/-- The image `U` of a section `s` which is an open immersion satisfies `U ≅ Y` via the
projection. -/
lemma isIso_opensRange_ι_comp_of_section {s : Y ⟶ X} [IsOpenImmersion s] (hs : s ≫ f = 𝟙 Y) :
    IsIso (s.opensRange.ι ≫ f) := by
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, hs, Category.comp_id]
  infer_instance

/-- I.5.3: over a connected base, the sections of a separated unramified morphism
`f : X ⟶ Y` correspond bijectively to the connected components `U` of `X` which are
open and such that `U ⟶ Y` is an isomorphism. -/
noncomputable def sectionEquivConnectedComponent [IsSeparated f] [FormallyUnramified f]
    [LocallyOfFiniteType f] [ConnectedSpace Y] :
    {s : Y ⟶ X // s ≫ f = 𝟙 Y} ≃
      {U : X.Opens // (∃ x, (U : Set X) = connectedComponent x) ∧ IsIso (U.ι ≫ f)} where
  toFun s :=
    have := isOpenImmersion_of_section f s.2
    ⟨s.1.opensRange, ⟨s.1 (Classical.arbitrary Y), by
      rw [Scheme.Hom.coe_opensRange]
      exact (isOpenImmersion_and_range_eq_connectedComponent_of_section f s.2 _).2⟩,
      isIso_opensRange_ι_comp_of_section f s.2⟩
  invFun U := ⟨have := U.2.2; inv (U.1.ι ≫ f) ≫ U.1.ι, by simp⟩
  left_inv s := by
    have := isOpenImmersion_of_section f s.2
    have := isIso_opensRange_ι_comp_of_section f s.2
    apply Subtype.ext
    change inv (s.1.opensRange.ι ≫ f) ≫ s.1.opensRange.ι = s.1
    have e : s.1.opensRange.ι ≫ f = s.1.isoOpensRange.inv := by
      rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, s.2, Category.comp_id]
    have : inv (s.1.opensRange.ι ≫ f) = s.1.isoOpensRange.hom :=
      IsIso.inv_eq_of_hom_inv_id (by rw [e, Iso.inv_hom_id])
    rw [this, Scheme.Hom.isoOpensRange_hom_ι]
  right_inv U := by
    have := U.2.2
    apply Subtype.ext
    change (inv (U.1.ι ≫ f) ≫ U.1.ι).opensRange = U.1
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.4: let `X` be unramified and separated over `S` and `Y` connected. Two
`S`-morphisms `Y ⟶ X` which agree geometrically at a point `y` (same image `x` and
same residue field map `κ(x) → κ(y)`, i.e. the same composite `Spec κ(y) ⟶ X`) are
equal. -/
theorem hom_eq_of_fromSpecResidueField_comp_eq {S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    [IsSeparated p] [FormallyUnramified p] [LocallyOfFiniteType p] [PreconnectedSpace Y]
    {g₁ g₂ : Y ⟶ X} (hg₁ : g₁ ≫ p = q) (hg₂ : g₂ ≫ p = q) (y : Y)
    (h : Y.fromSpecResidueField y ≫ g₁ = Y.fromSpecResidueField y ≫ g₂) : g₁ = g₂ := by
  let s₁ : Y ⟶ pullback p q := pullback.lift g₁ (𝟙 Y) (by simp [hg₁])
  let s₂ : Y ⟶ pullback p q := pullback.lift g₂ (𝟙 Y) (by simp [hg₂])
  have hs₁ : s₁ ≫ pullback.snd p q = 𝟙 Y := pullback.lift_snd _ _ _
  have hs₂ : s₂ ≫ pullback.snd p q = 𝟙 Y := pullback.lift_snd _ _ _
  have hy : Y.fromSpecResidueField y ≫ s₁ = Y.fromSpecResidueField y ≫ s₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact h
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hpt : s₁ y = s₂ y := by
    obtain ⟨z⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
    have := congr($(hy) z)
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using this
  have := section_eq_of_apply_eq (pullback.snd p q) hs₁ hs₂ y hpt
  calc g₁ = s₁ ≫ pullback.fst p q := (pullback.lift_fst _ _ _).symm
    _ = s₂ ≫ pullback.fst p q := by rw [this]
    _ = g₂ := pullback.lift_fst _ _ _

/-- A surjective closed immersion is an open map (it is a homeomorphism). -/
lemma isOpenMap_of_isClosedImmersion_of_surjective {Z W : Scheme.{u}} (i : Z ⟶ W)
    [IsClosedImmersion i] [Surjective i] : IsOpenMap i := by
  intro V hV
  have hb : Function.Bijective i := ⟨i.isClosedEmbedding.injective, i.surjective⟩
  rw [← compl_compl V, Set.image_compl_eq hb]
  exact (i.isClosedEmbedding.isClosedMap _ hV.isClosed_compl).isOpen_compl

set_option backward.isDefEq.respectTransparency.types false in
/-- The residue field maps of a closed immersion are surjective. -/
lemma residueFieldMap_surjective_of_isClosedImmersion {Z W : Scheme.{u}} (i : Z ⟶ W)
    [IsClosedImmersion i] (z : Z) : Function.Surjective (i.residueFieldMap z) := by
  have h := congr(($(Scheme.residue_residueFieldMap i z)).hom)
  have hs : Function.Surjective ((i.stalkMap z ≫ Z.residue z).hom) :=
    (IsLocalRing.residue_surjective).comp (i.stalkMap_surjective z)
  rw [← h, CommRingCat.hom_comp, RingHom.coe_comp] at hs
  exact Function.Surjective.of_comp hs

/-- A bijective homomorphism of fields is purely inseparable. -/
lemma ringHom_isPurelyInseparable_of_bijective {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (hφ : Function.Bijective φ) : φ.IsPurelyInseparable := by
  algebraize [φ]
  exact (AlgEquiv.ofBijective (Algebra.ofId K L) hφ).isPurelyInseparable

set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.5, existence of sections (the case `Y = S`): let `i : S₀ ⟶ S` be a closed
immersion with the same underlying space as `S`. An `S`-morphism `S₀ ⟶ X` into an
étale `S`-scheme extends to a section of `X ⟶ S`. As in SGA, the image of `S₀` is an
open subscheme `U` of `X` which is étale and radicial over `S`, hence isomorphic to
`S` by I.5.1. -/
theorem exists_section_of_etale {S S₀ : Scheme.{u}} (p : X ⟶ S) [Etale p] (i : S₀ ⟶ S)
    [IsClosedImmersion i] [Surjective i] (σ₀ : S₀ ⟶ X) (hσ₀ : σ₀ ≫ p = i) :
    ∃ σ : S ⟶ X, σ ≫ p = 𝟙 S ∧ i ≫ σ = σ₀ := by
  -- the induced section of `X ×_S S₀ ⟶ S₀` is an open immersion
  let s₀ : S₀ ⟶ pullback p i := pullback.lift σ₀ (𝟙 S₀) (by simp [hσ₀])
  have hs₀ : s₀ ≫ pullback.snd p i = 𝟙 S₀ := pullback.lift_snd _ _ _
  have : IsOpenImmersion s₀ := isOpenImmersion_of_section (pullback.snd p i) hs₀
  have hσs : s₀ ≫ pullback.fst p i = σ₀ := pullback.lift_fst _ _ _
  -- so the range of `σ₀` is open, `X ×_S S₀ ⟶ X` being a homeomorphism
  have hopen : IsOpen (Set.range σ₀) := by
    have : Set.range σ₀ = pullback.fst p i '' Set.range s₀ := by
      rw [← hσs, ← Set.range_comp]; rfl
    rw [this]
    exact isOpenMap_of_isClosedImmersion_of_surjective _ _ s₀.isOpenEmbedding.isOpen_range
  let U : X.Opens := ⟨Set.range σ₀, hopen⟩
  let σ₀' : S₀ ⟶ U := IsOpenImmersion.lift U.ι σ₀ (by simp [U])
  have hσ₀' : σ₀' ≫ U.ι = σ₀ := IsOpenImmersion.lift_fac _ _ _
  let q := U.ι ≫ p
  have hq : σ₀' ≫ q = i := by simp only [q, ← Category.assoc, hσ₀', hσ₀]
  have hsurj : Function.Surjective σ₀' := by
    rintro ⟨u, a, rfl⟩
    refine ⟨a, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hσ₀']
    rfl
  have : Surjective q := ⟨fun s ↦ by
    obtain ⟨a, rfl⟩ := i.surjective s
    exact ⟨σ₀' a, by rw [← Scheme.Hom.comp_apply, hq]⟩⟩
  -- `U ⟶ S` is radicial: injective, with trivial residue field extensions
  have : UniversallyInjective q := by
    have key : UniversallyInjective q ↔ Function.Injective q ∧
        ∀ x, (q.residueFieldMap x).hom.IsPurelyInseparable :=
      (tfae_universallyInjective q).out 1 3
    refine key.mpr ⟨?_, ?_⟩
    · intro u v h
      obtain ⟨a, rfl⟩ := hsurj u
      obtain ⟨b, rfl⟩ := hsurj v
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq] at h
      rw [i.isClosedEmbedding.injective h]
    · intro u
      obtain ⟨a, rfl⟩ := hsurj u
      apply ringHom_isPurelyInseparable_of_bijective
      refine ⟨RingHom.injective _, ?_⟩
      have hi : Function.Surjective ((σ₀' ≫ q).residueFieldMap a) := by
        clear_value q
        subst hq
        exact residueFieldMap_surjective_of_isClosedImmersion _ a
      rw [Scheme.residueFieldMap_comp] at hi
      replace hi : Function.Surjective
          ((σ₀'.residueFieldMap a).hom ∘ (q.residueFieldMap (σ₀' a)).hom) := hi
      intro y
      obtain ⟨x, hx⟩ := hi ((σ₀'.residueFieldMap a).hom y)
      exact ⟨x, RingHom.injective _ hx⟩
  -- hence `U ⟶ S` is an isomorphism (I.5.1), whose inverse is the section
  have : IsOpenImmersion q := isOpenImmersion_of_etale_of_universallyInjective q
  have : IsIso q := (isIso_iff_isOpenImmersion_and_surjective q).mpr ⟨inferInstance, inferInstance⟩
  have hiq : i ≫ inv q = σ₀' := by rw [← hq]; simp
  exact ⟨inv q ≫ U.ι, by simp [q], by rw [← Category.assoc, hiq, hσ₀']⟩

/-- I.5.5, uniqueness of sections: two sections of an unramified morphism which agree
after composing with a surjective morphism `S₀ ⟶ S` are equal. -/
theorem section_eq_of_comp_eq {S S₀ : Scheme.{u}} (p : X ⟶ S) [FormallyUnramified p]
    [LocallyOfFiniteType p] (i : S₀ ⟶ S) [Surjective i] {σ τ : S ⟶ X}
    (hσ : σ ≫ p = 𝟙 S) (hτ : τ ≫ p = 𝟙 S) (h : i ≫ σ = i ≫ τ) : σ = τ := by
  have := isOpenImmersion_of_section p hσ
  have := isOpenImmersion_of_section p hτ
  refine section_eq_of_range_eq p hσ hτ ?_
  have hr (ρ : S ⟶ X) : Set.range ρ = Set.range (i ≫ ρ) := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨a, rfl⟩ := i.surjective s
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨i a, rfl⟩
  rw [hr σ, hr τ, h]

/-- I.5.5, uniqueness, in mathlib's form: morphisms into a formally unramified
`S`-scheme are determined by their restriction along a nilpotent closed immersion. -/
theorem hom_ext_of_formallyUnramified {Z' Z : Scheme.{u}} (i : Z' ⟶ Z)
    (hi : IsNilpotent i.ker) [IsClosedImmersion i] {g₁ g₂ : Z ⟶ X}
    (hig : i ≫ g₁ = i ≫ g₂) (hgf : g₁ ≫ f = g₂ ≫ f) [FormallyUnramified f] : g₁ = g₂ :=
  FormallyUnramified.hom_ext i hi f hig hgf

set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.6 (theorem on extending liftings): let `X ⟶ S` be étale and `i : Y₀ ⟶ Y` a
bijective closed immersion (a closed immersion is injective, so we only ask that it be
surjective). Every commutative square with sides `Y₀ ⟶ X` and `Y ⟶ S` has a unique
diagonal `Y ⟶ X` making both triangles commute. -/
theorem existsUnique_lift_of_etale {S Y₀ : Scheme.{u}} (p : X ⟶ S) [Etale p]
    (i : Y₀ ⟶ Y) [IsClosedImmersion i] [Surjective i] (g : Y ⟶ S) (h : Y₀ ⟶ X)
    (w : h ≫ p = i ≫ g) : ∃! φ : Y ⟶ X, i ≫ φ = h ∧ φ ≫ p = g := by
  let h' : Y₀ ⟶ pullback p g := pullback.lift h i w
  obtain ⟨σ, hσ, hiσ⟩ := exists_section_of_etale (pullback.snd p g) i h' (pullback.lift_snd _ _ _)
  refine ⟨σ ≫ pullback.fst p g, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, hiσ, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  · rintro φ ⟨hφ₁, hφ₂⟩
    let σ' : Y ⟶ pullback p g := pullback.lift φ (𝟙 Y) (by simp [hφ₂])
    have hσ' : σ' ≫ pullback.snd p g = 𝟙 Y := pullback.lift_snd _ _ _
    have : σ' = σ := section_eq_of_comp_eq (pullback.snd p g) i hσ' hσ (by
      rw [hiσ]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hφ₁]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id])
    rw [← this, pullback.lift_fst]

set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.5: let `X` be étale over `S` and `S₀ ⟶ S` a closed immersion with the same
underlying space. For every `S`-scheme `Y`, base change
`Hom_S(Y, X) → Hom_{S₀}(Y₀, X₀)`, `φ ↦ φ ×_S S₀`, is bijective
(`Y₀ = Y ×_S S₀`, `X₀ = X ×_S S₀`). -/
theorem bijective_baseChange_hom_of_etale {S S₀ : Scheme.{u}} (p : X ⟶ S) [Etale p]
    (i : S₀ ⟶ S) [IsClosedImmersion i] [Surjective i] (q : Y ⟶ S) :
    Function.Bijective fun φ : {φ : Y ⟶ X // φ ≫ p = q} ↦
      (⟨pullback.lift (pullback.fst q i ≫ φ.1) (pullback.snd q i)
          (by rw [Category.assoc, φ.2, pullback.condition]), pullback.lift_snd _ _ _⟩ :
        {ψ : pullback q i ⟶ pullback p i // ψ ≫ pullback.snd p i = pullback.snd q i}) := by
  refine ⟨fun φ₁ φ₂ e ↦ Subtype.ext ?_, fun ψ ↦ ?_⟩
  · have e := congr($(congrArg Subtype.val e) ≫ pullback.fst p i)
    simp only [pullback.lift_fst] at e
    exact (existsUnique_lift_of_etale p (pullback.fst q i) q (pullback.fst q i ≫ φ₁.1)
      (by simp [φ₁.2])).unique ⟨rfl, φ₁.2⟩ ⟨e.symm, φ₂.2⟩
  · obtain ⟨φ, ⟨hφ₁, hφ₂⟩, -⟩ := existsUnique_lift_of_etale p (pullback.fst q i) q
      (ψ.1 ≫ pullback.fst p i) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, ψ.2, pullback.condition])
    refine ⟨⟨φ, hφ₂⟩, Subtype.ext ?_⟩
    apply pullback.hom_ext
    · dsimp only
      rw [pullback.lift_fst, hφ₁]
    · dsimp only
      rw [pullback.lift_snd, ψ.2]

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `X ↦ X ×_S S₀` from étale `S`-schemes to étale `S₀`-schemes of the
scholium to I.5.5 and of I.8.3. -/
noncomputable abbrev etaleBaseChange {S S₀ : Scheme.{u}} (i : S₀ ⟶ S) : S.Etale ⥤ S₀.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ i

set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.5, scholium: base change along a closed immersion `S₀ ⟶ S` with the same
underlying space is a fully faithful functor from étale `S`-schemes to étale
`S₀`-schemes. -/
theorem etaleBaseChange_full_and_faithful {S S₀ : Scheme.{u}} (i : S₀ ⟶ S)
    [IsClosedImmersion i] [Surjective i] :
    (etaleBaseChange i).Full ∧ (etaleBaseChange i).Faithful := by
  refine ⟨⟨fun {A B} ψ ↦ ?_⟩, ⟨fun {A B} f g e ↦ ?_⟩⟩
  · let ψ' : pullback A.hom i ⟶ pullback B.hom i := ψ.left
    have hψ : ψ' ≫ pullback.snd B.hom i = pullback.snd A.hom i := MorphismProperty.Over.w ψ
    obtain ⟨φ, ⟨hφ₁, hφ₂⟩, -⟩ := existsUnique_lift_of_etale B.hom (pullback.fst A.hom i) A.hom
      (ψ' ≫ pullback.fst B.hom i) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hψ, pullback.condition])
    refine ⟨MorphismProperty.Over.homMk φ hφ₂, MorphismProperty.Over.Hom.ext ?_⟩
    change pullback.lift (pullback.fst A.hom i ≫ φ) (pullback.snd A.hom i) _ = ψ'
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hφ₁
    · exact (pullback.lift_snd _ _ _).trans hψ.symm
  · have e : pullback.lift (pullback.fst A.hom i ≫ f.left) (pullback.snd A.hom i) _ =
        pullback.lift (pullback.fst A.hom i ≫ g.left) (pullback.snd A.hom i) _ :=
      congr($(e).left)
    have e' := congr($e ≫ pullback.fst B.hom i)
    rw [pullback.lift_fst, pullback.lift_fst] at e'
    apply MorphismProperty.Over.Hom.ext
    exact (existsUnique_lift_of_etale B.hom (pullback.fst A.hom i) A.hom
      (pullback.fst A.hom i ≫ f.left) (by simp)).unique ⟨rfl, by simp⟩ ⟨e'.symm, by simp⟩

end SGA.SGA1.ExposeI
