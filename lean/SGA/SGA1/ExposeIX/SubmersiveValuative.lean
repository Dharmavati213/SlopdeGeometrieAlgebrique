/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk
import SGA.Foundations.CommAlg.DominatingDVRLift
import SGA.SGA1.ExposeIX.Submersive

/-!
# SGA 1, Exposé IX, 2.6: the valuative criterion for universally submersive morphisms

IX.2.6 (sufficiency, `universallySubmersiveValuativeCriterion`): let `g : S' ⟶ S` be quasi-compact
with `S` locally noetherian. If for every discrete valuation ring `R` and every `Spec R ⟶ S` the
preimage in `S' ×_S Spec R` of the closed point of `Spec R` is not open, then `g` is universally
submersive. This proves `UniversallySubmersiveValuativeCriterionStatement`; together with the
necessity (`not_isOpen_preimage_closedPoint`, `Submersive.lean`) it gives the equivalence
`universallySubmersive_iff_forall_not_isOpen_of_quasiCompact`. SGA assumes `g` of finite type;
only quasi-compactness is used.

SGA only says that the criterion follows "easily" from the criterion IV.6.3 for a constructible
subset of a noetherian space to be open. We follow instead the valuative approach of Rydh
(*Submersions and effective descent of étale morphisms*, §2), with the following steps.

* `isClosed_image_of_stableUnderSpecialization`: the image of a closed subset under a
  quasi-compact morphism is closed as soon as it is stable under specialization (Stacks 01K9).
* `Submersive.of_quasiCompact_of_exists_specializes`: a quasi-compact morphism along which every
  specialization `y' ⤳ y` lifts to a specialization `x' ⤳ x` is submersive.
* `exists_localDomain_of_specializes`: a specialization `x' ⤳ x` in a scheme is the image of the
  specialization from the generic to the closed point of `Spec E`, for a local domain `E`.
* `LiftsLocalDomains g`: every `Spec D ⟶ S`, `D` a local domain, lifts to `S'` after replacing `D`
  by a local domain `E` dominating it. This implies that `g` is universally submersive if `g` is
  quasi-compact (`universallySubmersive_of_liftsLocalDomains`), and the hypothesis of IX.2.6 is the
  same property for discrete valuation rings (`liftsDVRs_of_forall_not_isOpen`).
* `liftsLocalDomains_of_liftsDVRs`: for `g` quasi-compact and `S` locally noetherian, it is enough
  to lift discrete valuation rings. This is the algebraic statement
  `Algebra.exists_hasDominatingPoint_of_forall_isDiscreteValuationRing` applied to the stalk
  `𝒪_{S,s}` and a finite affine cover of `S' ×_S Spec 𝒪_{S,s}`; it rests on EGA II 7.1.7
  (`IsLocalRing.exists_injective_isLocalHom_isDiscreteValuationRing`).
-/

universe u

open CategoryTheory Limits IsLocalRing Topology

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

/-! ### Closed images and submersive morphisms -/

/-- The image of a closed subset `Z` under a quasi-compact morphism is closed as soon as it is
stable under specialization (Stacks 01K9; mathlib proves the version for specializing maps,
`QuasiCompact.isClosedMap_iff_specializingMap`). -/
theorem isClosed_image_of_stableUnderSpecialization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] {Z : Set X} (hZ : IsClosed Z) (hs : StableUnderSpecialization (f '' Z)) :
    IsClosed (f '' Z) := by
  wlog hY : ∃ R, Y = Spec R generalizing X Y
  · let 𝒰 := Y.affineCover
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq y
    have hP := IsPullback.of_hasPullback f (𝒰.f i)
    have hcl : IsClosed (pullback.snd f (𝒰.f i) '' (pullback.fst f (𝒰.f i) ⁻¹' Z)) := by
      refine this (pullback.snd f (𝒰.f i))
        (hZ.preimage (pullback.fst f (𝒰.f i)).continuous) ?_ ⟨_, rfl⟩
      rw [Scheme.image_preimage_eq_of_isPullback hP]
      exact hs.preimage (𝒰.f i).continuous
    rw [Scheme.image_preimage_eq_of_isPullback hP] at hcl
    refine ⟨𝒰.f i '' (𝒰.f i ⁻¹' (f '' Z))ᶜ, ?_,
      (𝒰.f i).isOpenEmbedding.isOpenMap _ hcl.isOpen_compl, ⟨x, hy, rfl⟩⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hz
  obtain ⟨R, rfl⟩ := hY
  obtain ⟨T, q, hq⟩ := compactSpace_iff_exists.mp (QuasiCompact.compactSpace_of_compactSpace f)
  have key : (q ≫ f) '' (q ⁻¹' Z) = f '' Z := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Set.image_preimage_eq _ hq]
  rw [← key] at hs ⊢
  have hZ' : IsClosed (q ⁻¹' Z) := hZ.preimage q.continuous
  generalize q ≫ f = g at hs ⊢
  generalize q ⁻¹' Z = Z' at hs hZ' ⊢
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  exact PrimeSpectrum.isClosed_image_of_stableUnderSpecialization φ.hom Z' hZ' hs

/-- A quasi-compact morphism along which every specialization `y' ⤳ y` lifts to a specialization
`x' ⤳ x` (with `f x' = y'`, `f x = y`) is submersive. -/
theorem Submersive.of_quasiCompact_of_exists_specializes {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (h : ∀ y' y : Y, y' ⤳ y → ∃ x' x : X, x' ⤳ x ∧ f x' = y' ∧ f x = y) :
    Submersive f := by
  have hsurj : Function.Surjective f := fun y ↦ by
    obtain ⟨x', _, _, h1, _⟩ := h y y specializes_rfl
    exact ⟨x', h1⟩
  refine ⟨Topology.isQuotientMap_iff_isClosed.mpr ⟨hsurj, fun s ↦
    ⟨fun hs ↦ hs.preimage f.continuous, fun hs ↦ ?_⟩⟩⟩
  rw [← Set.image_preimage_eq s hsurj]
  refine isClosed_image_of_stableUnderSpecialization f hs ?_
  rw [Set.image_preimage_eq s hsurj]
  intro y y'' hyy hy
  obtain ⟨x, x'', hxx, rfl, rfl⟩ := h y y'' hyy
  exact hs.stableUnderSpecialization hxx hy

/-! ### Specializations and local domains -/

/-- A specialization `x' ⤳ x` in a scheme is the image of the specialization from the generic
point to the closed point of `Spec E`, for a local domain `E` (a quotient of `𝒪_{X,x}`). -/
theorem exists_localDomain_of_specializes {X : Scheme.{u}} {x' x : X} (h : x' ⤳ x) :
    ∃ (E : Type u) (_ : CommRing E) (_ : IsDomain E) (_ : IsLocalRing E)
      (l : Spec (.of E) ⟶ X),
      l (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E) = x' ∧ l (closedPoint E) = x := by
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x p = x' := by
    have : x' ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact h
    exact this
  let E := X.presheaf.stalk x ⧸ p.asIdeal
  let π : X.presheaf.stalk x →+* E := Ideal.Quotient.mk p.asIdeal
  have : IsLocalRing E := IsLocalRing.of_surjective' π Ideal.Quotient.mk_surjective
  have : IsLocalHom π := IsLocalHom.of_surjective π Ideal.Quotient.mk_surjective
  refine ⟨E, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom π) ≫ X.fromSpecStalk x, ?_, ?_⟩
  · change X.fromSpecStalk x (Spec.map (CommRingCat.ofHom π) _) = x'
    rw [← hp]
    congr 1
    apply PrimeSpectrum.ext
    change (⊥ : Ideal E).comap π = p.asIdeal
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  · change X.fromSpecStalk x (Spec.map (CommRingCat.ofHom π) _) = x
    have : Spec.map (CommRingCat.ofHom π) (closedPoint E) =
        closedPoint (X.presheaf.stalk x) := IsLocalRing.comap_closedPoint π
    rw [this, Scheme.fromSpecStalk_closedPoint]

/-- For a ring map `ρ : D → E` with `E` a domain: if `Spec ρ` maps the generic point to the
generic point, `ρ` is injective. -/
lemma injective_of_specMap_bot {D E : Type u} [CommRing D] [CommRing E] [IsDomain E]
    [IsDomain D] (ρ : D →+* E)
    (h : Spec.map (CommRingCat.ofHom ρ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E) =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D)) : Function.Injective ρ := by
  rw [injective_iff_map_eq_zero]
  intro d hd
  have : (⊥ : Ideal E).comap ρ = ⊥ := congrArg PrimeSpectrum.asIdeal h
  have hd' : d ∈ (⊥ : Ideal E).comap ρ := by simp [hd]
  rw [this] at hd'
  exact hd'

/-- For an injective local `ρ : D → E` of local domains, `Spec ρ` maps the generic point to the
generic point. -/
lemma specMap_bot_of_injective {D E : Type u} [CommRing D] [CommRing E] [IsDomain E]
    [IsDomain D] (ρ : D →+* E) (hρ : Function.Injective ρ) :
    Spec.map (CommRingCat.ofHom ρ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E) =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) := by
  apply PrimeSpectrum.ext
  change (⊥ : Ideal E).comap ρ = ⊥
  rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot ρ).mp hρ]

/-! ### Lifting local domains -/

/-- `g : S' ⟶ S` *lifts local domains*: for every local domain `D` and `τ : Spec D ⟶ S` there are
a local domain `E`, an injective local homomorphism `ρ : D → E` and `l : Spec E ⟶ S'` with
`l ≫ g = Spec ρ ≫ τ`. (Then the specialization from the generic to the closed point of `Spec D`
lifts to `S' ×_S Spec D`.) -/
def LiftsLocalDomains {S' S : Scheme.{u}} (g : S' ⟶ S) : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D] (τ : Spec (.of D) ⟶ S),
    ∃ (E : Type u) (_ : CommRing E) (_ : IsDomain E) (_ : IsLocalRing E) (ρ : D →+* E)
      (l : Spec (.of E) ⟶ S'), Function.Injective ρ ∧ IsLocalHom ρ ∧
        l ≫ g = Spec.map (CommRingCat.ofHom ρ) ≫ τ

/-- `g : S' ⟶ S` *lifts discrete valuation rings*: `LiftsLocalDomains` restricted to discrete
valuation rings `D`. -/
def LiftsDVRs {S' S : Scheme.{u}} (g : S' ⟶ S) : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (τ : Spec (.of D) ⟶ S),
    ∃ (E : Type u) (_ : CommRing E) (_ : IsDomain E) (_ : IsLocalRing E) (ρ : D →+* E)
      (l : Spec (.of E) ⟶ S'), Function.Injective ρ ∧ IsLocalHom ρ ∧
        l ≫ g = Spec.map (CommRingCat.ofHom ρ) ≫ τ

/-- A quasi-compact morphism which lifts local domains is universally submersive: in every base
change, specializations lift (`exists_localDomain_of_specializes`), so it is submersive
(`Submersive.of_quasiCompact_of_exists_specializes`). -/
theorem universallySubmersive_of_liftsLocalDomains {S' S : Scheme.{u}} (g : S' ⟶ S)
    [QuasiCompact g] (hg : LiftsLocalDomains g) : UniversallySubmersive g := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have : QuasiCompact f' := MorphismProperty.of_isPullback H.flip ‹_›
  apply Submersive.of_quasiCompact_of_exists_specializes
  intro y' y hyy
  obtain ⟨D, _, _, _, τ', hτ'₁, hτ'₂⟩ := exists_localDomain_of_specializes hyy
  obtain ⟨E, _, _, _, ρ, l, hρ, hloc, hl⟩ := hg D (τ' ≫ i₂)
  let l' : Spec (.of E) ⟶ X' :=
    H.lift (Spec.map (CommRingCat.ofHom ρ) ≫ τ') l (by rw [Category.assoc, hl])
  have hl' : l' ≫ f' = Spec.map (CommRingCat.ofHom ρ) ≫ τ' := H.lift_fst _ _ _
  set pb : Spec (.of E) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E) with hpb
  set pc : Spec (.of E) := closedPoint E with hpc
  have hb : Spec.map (CommRingCat.ofHom ρ) pb = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) :=
    specMap_bot_of_injective ρ hρ
  have hc : Spec.map (CommRingCat.ofHom ρ) pc = closedPoint D := IsLocalRing.comap_closedPoint ρ
  refine ⟨l' pb, l' pc, (IsLocalRing.specializes_closedPoint (R := E) _).map l'.continuous, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hl', Scheme.Hom.comp_apply, hb]
    exact hτ'₁
  · rw [← Scheme.Hom.comp_apply, hl', Scheme.Hom.comp_apply, hc]
    exact hτ'₂

/-- In a discrete valuation ring a point of the spectrum which is not the closed point is the
generic point. -/
lemma eq_bot_of_ne_closedPoint {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (x : PrimeSpectrum R) (hx : x ≠ closedPoint R) :
    x = ⟨⊥, Ideal.isPrime_bot⟩ := by
  apply PrimeSpectrum.ext
  by_contra h
  apply hx
  apply PrimeSpectrum.ext
  exact IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal_of_ne_bot h)

/-- The hypothesis of IX.2.6 implies that `g` lifts discrete valuation rings: if the preimage of
the closed point of `Spec R` in `S' ×_S Spec R` is not open, some point of the generic fibre
specializes to a point of the closed fibre (`isClosed_image_of_stableUnderSpecialization`), and
that specialization comes from a local domain (`exists_localDomain_of_specializes`). -/
theorem liftsDVRs_of_forall_not_isOpen {S' S : Scheme.{u}} (g : S' ⟶ S)
    (H : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (t : Spec (.of R) ⟶ S), ¬ IsOpen (pullback.snd g t ⁻¹' {closedPoint R})) :
    LiftsDVRs g := by
  intro R _ _ _ t
  let snd := pullback.snd g t
  let V : (Spec (.of R)).Opens :=
    ⟨{closedPoint R}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl⟩
  let P := pullback g t
  let W : P.Opens := snd ⁻¹ᵁ V
  have hWset : (W : Set P) = (snd ⁻¹' {closedPoint R})ᶜ := rfl
  obtain ⟨ξ, hξ, ζ, hζ, hξζ⟩ : ∃ ξ ∈ (W : Set P), ∃ ζ ∉ (W : Set P), ξ ⤳ ζ := by
    by_contra hne
    push Not at hne
    have hqcV : QuasiCompact V.ι := inferInstance
    have hqc : QuasiCompact W.ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict snd V) hqcV
    have hcl : IsClosed (W.ι '' Set.univ) := by
      refine isClosed_image_of_stableUnderSpecialization W.ι isClosed_univ ?_
      rw [Set.image_univ, Scheme.Opens.range_ι]
      intro a b hab ha
      by_contra hb
      exact hne a ha b hb hab
    rw [Set.image_univ, Scheme.Opens.range_ι, hWset, isClosed_compl_iff] at hcl
    exact H R t hcl
  obtain ⟨E, _, _, _, l₀, hl₀₁, hl₀₂⟩ := exists_localDomain_of_specializes hξζ
  obtain ⟨ρ', hρ'⟩ := Spec.map_surjective (l₀ ≫ snd)
  obtain ⟨ρ, rfl⟩ : ∃ ρ : R →+* E, CommRingCat.ofHom ρ = ρ' := ⟨ρ'.hom, CommRingCat.ofHom_hom ρ'⟩
  set pb : Spec (.of E) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E) with hpb
  set pc : Spec (.of E) := closedPoint E with hpc
  have hc : Spec.map (CommRingCat.ofHom ρ) pc = closedPoint R := by
    rw [hρ', Scheme.Hom.comp_apply, hl₀₂]
    by_contra h
    exact hζ h
  have hb : Spec.map (CommRingCat.ofHom ρ) pb = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
    apply eq_bot_of_ne_closedPoint
    rw [hρ', Scheme.Hom.comp_apply, hl₀₁]
    exact hξ
  refine ⟨E, inferInstance, inferInstance, inferInstance, ρ, l₀ ≫ pullback.fst g t,
    injective_of_specMap_bot ρ hb, (isLocalHom_iff_comap_closedPoint ρ).mpr hc, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ t) hρ'.symm

/-- For `g` quasi-compact and `S` locally noetherian, lifting discrete valuation rings implies
lifting all local domains. Over the stalk `A₀ = 𝒪_{S,s}` (noetherian) this is
`Algebra.exists_hasDominatingPoint_of_forall_isDiscreteValuationRing`, applied to the rings of a
finite affine open cover of `S' ×_S Spec A₀`. -/
theorem liftsLocalDomains_of_liftsDVRs {S' S : Scheme.{u}} (g : S' ⟶ S) [QuasiCompact g]
    [IsLocallyNoetherian S] (hg : LiftsDVRs g) : LiftsLocalDomains g := by
  classical
  intro D _ _ _ τ
  let s := τ (closedPoint D)
  let A₀ := S.presheaf.stalk s
  let ψ : A₀ ⟶ CommRingCat.of D := Scheme.stalkClosedPointTo τ
  have hτ : Spec.map ψ ≫ S.fromSpecStalk s = τ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk τ
  let P := pullback g (S.fromSpecStalk s)
  let g₀ : P ⟶ Spec A₀ := pullback.snd g (S.fromSpecStalk s)
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace g₀
  let 𝒜 := P.affineOpenCover
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : P ↦ Set.range (𝒜.f (𝒜.idx x)))
    (fun x ↦ (𝒜.f (𝒜.idx x)).isOpenEmbedding.isOpen_range)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, 𝒜.covers x⟩)
  let B : t → CommRingCat.{u} := fun i ↦ 𝒜.X (𝒜.idx i)
  have hφ : ∀ i : t, ∃ φ : A₀ ⟶ B i, Spec.map φ = 𝒜.f (𝒜.idx i) ≫ g₀ := fun i ↦
    Spec.map_surjective _
  choose φ hφ using hφ
  let : ∀ i : t, Algebra A₀ (B i) := fun i ↦ (φ i).hom.toAlgebra
  let : Algebra A₀ D := ψ.hom.toAlgebra
  -- Points of the charts `B i` with values in local domains.
  have hchart : ∀ (E : Type u) [CommRing E] [IsLocalRing E] (l₀ : Spec (.of E) ⟶ P),
      ∃ (i : t) (β : B i →+* E), l₀ = Spec.map (CommRingCat.ofHom β) ≫ 𝒜.f (𝒜.idx i) := by
    intro E _ _ l₀
    obtain ⟨i, hi⟩ : ∃ i ∈ t, l₀ (closedPoint E) ∈ Set.range (𝒜.f (𝒜.idx i)) := by
      have := ht (Set.mem_univ (l₀ (closedPoint E)))
      simpa using this
    obtain ⟨hit, hmem⟩ := hi
    have hrange : Set.range l₀ ⊆ Set.range (𝒜.f (𝒜.idx i)) := by
      rintro _ ⟨y, rfl⟩
      exact ((IsLocalRing.specializes_closedPoint y).map l₀.continuous).mem_open
        (𝒜.f (𝒜.idx i)).isOpenEmbedding.isOpen_range hmem
    obtain ⟨β', hβ'⟩ := Spec.map_surjective (IsOpenImmersion.lift (𝒜.f (𝒜.idx i)) l₀ hrange)
    refine ⟨⟨i, hit⟩, β'.hom, ?_⟩
    rw [CommRingCat.ofHom_hom, hβ', IsOpenImmersion.lift_fac]
  -- The hypothesis over discrete valuation rings, in algebraic form.
  have Halg : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Algebra A₀ R], ∃ i : t, Algebra.HasDominatingPoint A₀ (B i) R := by
    intro R _ _ _ _
    obtain ⟨E, _, _, _, ρ, l, hρ, hloc, hl⟩ :=
      hg R (Spec.map (CommRingCat.ofHom (algebraMap A₀ R)) ≫ S.fromSpecStalk s)
    let l₀ : Spec (.of E) ⟶ P := pullback.lift l
      (Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom (algebraMap A₀ R)))
      (hl.trans (Category.assoc _ _ _).symm)
    obtain ⟨i, β, hβ⟩ := hchart E l₀
    refine ⟨i, E, inferInstance, inferInstance, inferInstance, ρ, β, hρ, hloc, ?_⟩
    have key : Spec.map (CommRingCat.ofHom β) ≫ Spec.map (φ i) =
        Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom (algebraMap A₀ R)) := by
      rw [hφ i, ← Category.assoc, ← hβ]
      exact pullback.lift_snd _ _ _
    rw [← Spec.map_comp, ← Spec.map_comp] at key
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  obtain ⟨i, E, _, _, _, ρ, β, hρ, hloc, hcomm⟩ :=
    Algebra.exists_hasDominatingPoint_of_forall_isDiscreteValuationRing (A₀ := A₀)
      (fun i : t ↦ (B i : Type u)) Halg D
  refine ⟨E, inferInstance, inferInstance, inferInstance, ρ,
    Spec.map (CommRingCat.ofHom β) ≫ 𝒜.f (𝒜.idx i) ≫ pullback.fst g (S.fromSpecStalk s),
    hρ, hloc, ?_⟩
  have h2 : φ i ≫ CommRingCat.ofHom β = ψ ≫ CommRingCat.ofHom ρ :=
    CommRingCat.hom_ext hcomm
  have h2' : Spec.map (CommRingCat.ofHom β) ≫ Spec.map (φ i) =
      Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map ψ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map h2
  calc (Spec.map (CommRingCat.ofHom β) ≫ 𝒜.f (𝒜.idx i) ≫ pullback.fst g (S.fromSpecStalk s)) ≫ g
      = Spec.map (CommRingCat.ofHom β) ≫ (𝒜.f (𝒜.idx i) ≫ g₀) ≫ S.fromSpecStalk s := by
        simp only [Category.assoc, pullback.condition, g₀]
    _ = (Spec.map (CommRingCat.ofHom β) ≫ Spec.map (φ i)) ≫ S.fromSpecStalk s := by
        rw [← hφ i, Category.assoc]
    _ = Spec.map (CommRingCat.ofHom ρ) ≫ τ := by
        rw [h2', Category.assoc, hτ]

/-- IX.2.6, sufficiency (valuative criterion): let `g : S' ⟶ S` be quasi-compact with
`S` locally noetherian. If for every discrete valuation ring `R` and every `t : Spec R ⟶ S` the
preimage in `S' ×_S Spec R` of the closed point of `Spec R` is not open, then `g` is universally
submersive. (SGA assumes `g` of finite type; this is not needed.) -/
theorem universallySubmersive_of_forall_not_isOpen {S' S : Scheme.{u}} (g : S' ⟶ S)
    [QuasiCompact g] [IsLocallyNoetherian S]
    (H : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (t : Spec (.of R) ⟶ S), ¬ IsOpen (pullback.snd g t ⁻¹' {closedPoint R})) :
    UniversallySubmersive g :=
  universallySubmersive_of_liftsLocalDomains g
    (liftsLocalDomains_of_liftsDVRs g (liftsDVRs_of_forall_not_isOpen g H))

/-- IX.2.6, sufficiency, in the form of `UniversallySubmersiveValuativeCriterionStatement`
(where `g` is also assumed locally of finite type, a hypothesis the proof does not use). -/
theorem universallySubmersiveValuativeCriterion :
    UniversallySubmersiveValuativeCriterionStatement.{u} :=
  fun _ _ g _ _ _ H ↦ universallySubmersive_of_forall_not_isOpen g H

/-- IX.2.6 (valuative criterion, both directions): a quasi-compact morphism `g : S' ⟶ S` with `S`
locally noetherian is universally submersive iff for every discrete valuation ring `R` and every
`Spec R ⟶ S`, the preimage in `S' ×_S Spec R` of the closed point of `Spec R` is not open. SGA
assumes `g` of finite type; here `g` is only assumed quasi-compact. -/
theorem universallySubmersive_iff_forall_not_isOpen_of_quasiCompact {S' S : Scheme.{u}}
    (g : S' ⟶ S) [QuasiCompact g] [IsLocallyNoetherian S] :
    UniversallySubmersive g ↔
      ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        (t : Spec (.of R) ⟶ S),
        ¬ IsOpen (pullback.snd g t ⁻¹' {closedPoint R}) :=
  ⟨fun _ R _ _ _ t ↦ not_isOpen_preimage_closedPoint g R t,
    universallySubmersive_of_forall_not_isOpen g⟩

end SGA.SGA1.ExposeIX
