/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.Normal
import SGA.Foundations.Dimension.Scheme
import SGA.SGA1.ExposeXIII.DesingularizationCurves

/-!
# Strong desingularization of curves over a perfect field

SGA 5 I 3.1.5 in dimension `≤ 1`, in the form of `IsStronglyDesingularizable`
(`SGA.SGA1.ExposeXIII.stronglyDesingularizableUpTo_one`): over a perfect field `k`, every integral
scheme `Z` of finite type over `k` of dimension `≤ 1` is strongly desingularizable. For a nonempty
regular open `U ⊆ Z`, take the normalization `ν : Z' ⟶ Z`
(`SGA.SGA1.ExposeXIII.isStronglyDesingularizable_of_topologicalKrullDim_le_one`):

* `ν` is finite, hence proper, and `Z'` is regular (`isRegularScheme_normalization`), hence smooth
  over `k` (`SGA.SGA1.ExposeX.smooth_of_isNormalScheme_of_topologicalKrullDim_le_one`);
* `ν` is an isomorphism over `U`, which is normal
  (`AlgebraicGeometry.isIso_fromNormalization_restrict_of_isIntegrallyClosed`);
* `Y = Z' - ν⁻¹(U)` is a finite set of closed points (`isClosed_singleton_of_ne_genericPoint`,
  `TopologicalSpace.NoetherianSpace.finite_of_isClosed_of_forall_isClosed_singleton`);
* around each `y ∈ Y` there is an open `Spec R` meeting `Y` only in `y`, with `r ∈ R` generating the
  maximal ideal of `y` (`exists_chart_of_ne_genericPoint`, from a uniformizer of the discrete
  valuation ring `𝒪_{Z',y}` and `Ideal.exists_notMem_map_eq_span_singleton`);
* there `Z'` is smooth of relative dimension `1` (`isSmoothOfRelativeDimensionAt_of_smooth`,
  `topologicalKrullDimAt_eq_one`) and `V(r) = Spec κ(y)` is étale over `k`, `κ(y)` being a finite
  separable extension (`AlgebraicGeometry.etale_subschemeι_ofIdealTop_comp`); so `{r}` has strict
  normal crossings (`isStrictNormalCrossings_of_isMaximal`) and `Y` is the support of a divisor
  with normal crossings relative to `k`.

This discharges the strong desingularization hypothesis of XIII.3.5 (and XIII.4.6) when the
relevant schemes have dimension `≤ 1` over a perfect field, e.g. for relative curves (the hypothesis
is asked over an algebraic closure, which is perfect).

## References

* [SGA 5, Exposé I, 3.1.5][sga5]; [EGA IV, 7.9][EGA4]
* [SGA 1, Exposé XIII, 2.1][sga1] (divisors with normal crossings)
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXIII

set_option backward.isDefEq.respectTransparency false in
/-- A scheme smooth over a field `k` is smooth of relative dimension `n` (over `k`) on a
neighbourhood of every point where its local dimension is `n`. -/
theorem isSmoothOfRelativeDimensionAt_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) (n : ℕ) (hx : topologicalKrullDimAt X x = n) :
    IsSmoothOfRelativeDimensionAt f n x := by
  obtain ⟨U, hU, V, hV, hxV, e, hst⟩ := Smooth.exists_isStandardSmooth f x
  algebraize [(f.appLE U V e).hom]
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := (‹Algebra.IsStandardSmooth Γ(Spec (.of k), U) Γ(X, V)›).out
  have hP : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension P.dimension :=
    P.isStandardSmoothOfRelativeDimension rfl
  have hres : SmoothOfRelativeDimension P.dimension (f.resLE U V e) := by
    have : IsAffine V := hV
    have : IsAffine U := hU
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)]
    have : (RingHom.toMorphismProperty
        (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension P.dimension))).RespectsIso :=
      RingHom.toMorphismProperty_respectsIso_iff.mp
        (HasRingHomProperty.isLocal_ringHomProperty
          (@SmoothOfRelativeDimension P.dimension)).respectsIso
    exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension P.dimension)))
      (arrowResLEAppIso f U V e)).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hP)
  have hVf : SmoothOfRelativeDimension P.dimension (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    exact (inferInstance : SmoothOfRelativeDimension (P.dimension + 0) (f.resLE U V e ≫ U.ι))
  have hdim := topologicalKrullDimAt_eq_of_smoothOfRelativeDimension (Field.toIsField k) (V.ι ≫ f)
    P.dimension ⟨x, hxV⟩
  have hdim' : topologicalKrullDimAt V.toScheme ⟨x, hxV⟩ = topologicalKrullDimAt X x :=
    V.2.topologicalKrullDimAt_eq ⟨x, hxV⟩
  have heq : P.dimension = n := by
    have h := hdim.symm.trans (hdim'.trans hx)
    exact_mod_cast h
  exact ⟨V, hxV, heq ▸ hVf⟩

/-- In an integral scheme of dimension `≤ 1`, every point other than the generic point is
closed. -/
lemma isClosed_singleton_of_ne_genericPoint {X : Scheme.{u}} [IsIntegral X]
    (hX : topologicalKrullDim X ≤ 1) {y : X} (hy : y ≠ genericPoint X) :
    IsClosed ({y} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  have hyz : y ⤳ z := specializes_iff_mem_closure.mpr hz
  by_contra hne
  have h₁ : z < y := lt_iff_le_not_ge.mpr ⟨hyz, fun h ↦ hne (Specializes.antisymm h hyz).eq⟩
  have hηy : genericPoint X ⤳ y := (genericPoint_spec X).specializes (Set.mem_univ y)
  have h₂ : y < genericPoint X :=
    lt_iff_le_not_ge.mpr ⟨hηy, fun h ↦ hy (Specializes.antisymm h hηy).eq⟩
  have hc : (2 : ℕ∞) ≤ Order.coheight z := by
    have e₁ := Order.coheight_add_one_le h₁
    have e₂ := Order.coheight_add_one_le h₂
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (genericPoint X) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight y + 1 := by gcongr
      _ ≤ Order.coheight z := e₁
  have hd := (ExposeX.ringKrullDim_stalk_le_topologicalKrullDim z).trans hX
  rw [ringKrullDim_stalk_eq_coheight] at hd
  have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) := (WithBot.coe_le_coe.mpr hc).trans hd
  exact absurd this (by decide)

set_option backward.isDefEq.respectTransparency false in
/-- **Charts at a closed point of a regular curve.** Let `X` be a regular integral locally
noetherian scheme of dimension `≤ 1` and `x` a point other than the generic point. Inside any open
neighbourhood `O` of `x` there is an open `Spec R ⊆ O` containing `x` and `r ∈ R` generating the
maximal ideal of `x` (a uniformizer at `x` which is a unit elsewhere on `Spec R`). -/
theorem exists_chart_of_ne_genericPoint {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hreg : ExposeX.IsRegularScheme X) (hX : topologicalKrullDim X ≤ 1) {x : X}
    (hx : x ≠ genericPoint X) {O : X.Opens} (hxO : x ∈ O) :
    ∃ (R : CommRingCat.{u}) (e : Spec R ⟶ X) (_ : IsOpenImmersion e) (r : R),
      Set.range e ⊆ O ∧ x ∈ Set.range e ∧ (Ideal.span {r}).IsMaximal ∧
        PrimeSpectrum.zeroLocus {r} = e ⁻¹' {x} := by
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV₀, hV₀O⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (SetLike.mem_coe.mpr hxO) O.2
  have : Nonempty V₀ := ⟨⟨x, hxV₀⟩⟩
  have : IsNoetherianRing Γ(X, V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩
  set P := hV₀.primeIdealOf ⟨x, hxV₀⟩ with hPdef
  have hPx : hV₀.fromSpec P = x := hV₀.fromSpec_primeIdealOf ⟨x, hxV₀⟩
  -- `P` is maximal: `x` is a closed point
  have hPmax : P.asIdeal.IsMaximal := by
    have hcl : IsClosed ({x} : Set X) := isClosed_singleton_of_ne_genericPoint hX hx
    have hpre : hV₀.fromSpec ⁻¹' {x} = {P} := by
      ext q
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h ↦ hV₀.fromSpec.isOpenEmbedding.injective (h.trans hPx.symm),
        fun h ↦ h ▸ hPx⟩
    have := hcl.preimage hV₀.fromSpec.continuous
    rw [hpre] at this
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).mp this
  -- the local ring at `P` is a discrete valuation ring
  have : IsRegularLocalRing (Localization.AtPrime P.asIdeal) := by
    have := hreg (hV₀.fromSpec P)
    exact IsRegularLocalRing.of_ringEquiv (hV₀.localizationAtPrimeEquivStalk P).symm
  have hdim : ringKrullDim (Localization.AtPrime P.asIdeal) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (hV₀.localizationAtPrimeEquivStalk P)]
    exact (ExposeX.ringKrullDim_stalk_le_topologicalKrullDim _).trans hX
  have : IsPrincipalIdealRing (Localization.AtPrime P.asIdeal) :=
    ExposeX.isPrincipalIdealRing_of_isIntegrallyClosed_of_ringKrullDim_le_one hdim
  obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal
    (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal))).principal
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.asIdeal.primeCompl π
  dsimp only at hπ
  have hspan : P.asIdeal.map (algebraMap Γ(X, V₀) (Localization.AtPrime P.asIdeal)) =
      Ideal.span {algebraMap Γ(X, V₀) (Localization.AtPrime P.asIdeal) a} := by
    have hu : IsUnit (IsLocalization.mk' (Localization.AtPrime P.asIdeal) (1 : Γ(X, V₀)) s) :=
      IsUnit.of_mul_eq_one (algebraMap Γ(X, V₀) (Localization.AtPrime P.asIdeal) (s : Γ(X, V₀)))
        (by rw [IsLocalization.mk'_spec, map_one])
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal, hπ, IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.span_singleton_mul_right_unit hu _
  have ha : a ∈ P.asIdeal := by
    have hmem : algebraMap Γ(X, V₀) (Localization.AtPrime P.asIdeal) a ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P.asIdeal (Localization.AtPrime P.asIdeal),
        hspan]
      exact Ideal.mem_span_singleton_self _
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P.asIdeal a).mp hmem
  obtain ⟨t, ht, hteq⟩ := Ideal.exists_notMem_map_eq_span_singleton P.asIdeal
    (IsNoetherian.noetherian _) a ha hspan
  let R := CommRingCat.of (Localization.Away t)
  let ι : Γ(X, V₀) ⟶ R := CommRingCat.ofHom (algebraMap Γ(X, V₀) (Localization.Away t))
  have hR := hteq (Localization.Away t)
  have hdisj : Disjoint (Submonoid.powers t : Set Γ(X, V₀)) (P.asIdeal : Set Γ(X, V₀)) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime t).mpr ht
  have hmax : (P.asIdeal.map (algebraMap Γ(X, V₀) (Localization.Away t))).IsMaximal :=
    IsLocalization.isMaximal_of_isMaximal_disjoint (Submonoid.powers t) _ P.asIdeal hdisj
  refine ⟨R, Spec.map ι ≫ hV₀.fromSpec, inferInstance,
    algebraMap Γ(X, V₀) (Localization.Away t) a, ?_, ?_, hR ▸ hmax, ?_⟩
  · rintro _ ⟨q, rfl⟩
    refine hV₀O ?_
    rw [← hV₀.range_fromSpec]
    exact ⟨_, rfl⟩
  · let q : PrimeSpectrum (Localization.Away t) := ⟨_, hmax.isPrime⟩
    refine ⟨q, ?_⟩
    rw [Scheme.Hom.comp_apply, Spec.map_apply]
    have : PrimeSpectrum.comap ι.hom q = P := PrimeSpectrum.ext
      (IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers t) (Localization.Away t)
        hPmax.isPrime hdisj)
    rw [this]
    exact hPx
  · ext q
    simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
      Set.mem_preimage, Set.mem_singleton_iff]
    rw [Scheme.Hom.comp_apply, Spec.map_apply]
    constructor
    · intro hq
      have hle : P.asIdeal ≤ (PrimeSpectrum.comap ι.hom q).asIdeal := by
        rw [PrimeSpectrum.comap_asIdeal, ← Ideal.map_le_iff_le_comap]
        change P.asIdeal.map (algebraMap Γ(X, V₀) (Localization.Away t)) ≤ q.asIdeal
        rw [hR, Ideal.span_le, Set.singleton_subset_iff]
        exact hq
      have heq : PrimeSpectrum.comap ι.hom q = P :=
        (PrimeSpectrum.ext (hPmax.eq_of_le (PrimeSpectrum.comap ι.hom q).isPrime.ne_top hle)).symm
      rw [heq]
      exact hPx
    · intro hq
      have heq : PrimeSpectrum.comap ι.hom q = P :=
        hV₀.fromSpec.isOpenEmbedding.injective (hq.trans hPx.symm)
      have : a ∈ (PrimeSpectrum.comap ι.hom q).asIdeal := heq ▸ ha
      exact this

/-- An integral scheme `X` of dimension `≤ 1` locally of finite type over a field, with a point
`x` other than its generic point, has dimension `1` at every point. -/
lemma topologicalKrullDimAt_eq_one {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] (hX : topologicalKrullDim X ≤ 1) {x : X}
    (hx : x ≠ genericPoint X) (y : X) : topologicalKrullDimAt X y = 1 := by
  have hall (z : X) : topologicalKrullDimAt X z = topologicalKrullDimAt X y :=
    topologicalKrullDimAt_eq_of_isIntegral g z y
  have hsup : topologicalKrullDim X = topologicalKrullDimAt X y := by
    rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt]
    exact le_antisymm (iSup_le fun z ↦ (hall z).le) (le_iSup_of_le y le_rfl)
  refine le_antisymm (hsup ▸ hX) ?_
  rw [← hsup]
  have hηx : genericPoint X ⤳ x := (genericPoint_spec X).specializes (Set.mem_univ x)
  have hlt : x < genericPoint X :=
    lt_iff_le_not_ge.mpr ⟨hηx, fun h ↦ hx (Specializes.antisymm h hηx).eq⟩
  have hc : (1 : ℕ∞) ≤ Order.coheight x := by
    have := Order.coheight_add_one_le hlt
    exact le_trans (by simp) this
  have hd := ExposeX.ringKrullDim_stalk_le_topologicalKrullDim x
  rw [ringKrullDim_stalk_eq_coheight] at hd
  exact (WithBot.coe_le_coe.mpr hc).trans hd

set_option backward.isDefEq.respectTransparency false in
/-- The strict normal crossings condition for a single function `f` on an affine scheme `X` locally
of finite type over a perfect field, if `f` generates a maximal ideal and `X` is smooth of relative
dimension `1` at the points where `f` vanishes: there `V(f)` is a closed point with separable
residue field, étale over `k`. -/
theorem isStrictNormalCrossings_of_isMaximal {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] (f : Γ(X, ⊤))
    (hf : (Ideal.span {f}).IsMaximal)
    (hsm : ∀ v ∈ X.zeroLocus {f}, IsSmoothOfRelativeDimensionAt g 1 v) :
    IsStrictNormalCrossings g (fun _ : Unit ↦ f) := by
  intro v hv
  have hv' : v ∈ X.zeroLocus {f} := by simpa using hv
  have hI : {i : Unit | v ∈ X.zeroLocus {(fun _ : Unit ↦ f) i}} = Set.univ :=
    Set.eq_univ_of_forall fun _ ↦ hv'
  refine ⟨1, 0, hsm v hv', by rw [hI]; simp, ?_⟩
  rw [hI]
  have hJ : zeroSubscheme (fun _ : Unit ↦ f) Set.univ =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {f}) := by
    rw [zeroSubscheme, Set.image_univ, Set.range_const]
  rw [hJ]
  have hmem : v ∈ Set.range (Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    change v ∈ X.zeroLocus (U := ⊤) ((Ideal.span {f} : Ideal Γ(X, ⊤)) : Set Γ(X, ⊤))
    rw [Scheme.zeroLocus_span]
    exact hv'
  obtain ⟨w, hw⟩ := hmem
  refine ⟨w, hw, ⊤, trivial, ?_⟩
  rw [← Etale.iff_smoothOfRelativeDimension_zero]
  have := etale_subschemeι_ofIdealTop_comp g (Ideal.span {f})
  infer_instance

section Strong

variable {Z : Scheme.{u}} [IsIntegral Z]

/-- `Spec K(Z) ⟶ Z`, the generic point of the integral scheme `Z`. -/
local notation "η" => Z.fromSpecStalk (genericPoint Z)

set_option backward.isDefEq.respectTransparency false in
/-- **SGA 5 I 3.1.5 in dimension `≤ 1`** (in the form of `IsStronglyDesingularizable`): an integral
scheme `Z` of finite type over a perfect field `k`, of dimension `≤ 1`, is strongly
desingularizable. For a nonempty regular open `U`, the normalization `ν : Z' ⟶ Z` is finite, `Z'`
is regular (a smooth curve), `ν` is an isomorphism over `U`, and the complement of `ν⁻¹(U)` is a
finite set of closed points, each cut out near itself by a uniformizer, whose residue field is
separable over `k`: a divisor with normal crossings relative to `k`. -/
theorem isStronglyDesingularizable_of_topologicalKrullDim_le_one {k : Type u} [Field k]
    [PerfectField k] (p : Z ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hZ : topologicalKrullDim Z ≤ 1) :
    IsStronglyDesingularizable p := by
  intro U hU hUreg
  have : IsFinite (η).fromNormalization := isFinite_fromNormalization_fromSpecStalk_genericPoint p
  have hreg' : ExposeX.IsRegularScheme (η).normalization :=
    isRegularScheme_normalization p hZ
  refine ⟨_, (η).fromNormalization, inferInstance, hreg', ?_, ?_⟩
  · refine isIso_fromNormalization_restrict_of_isIntegrallyClosed fun z hz ↦ ?_
    have := hUreg ⟨z, hz⟩
    have : IsRegularLocalRing (Z.presheaf.stalk z) :=
      IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨z, hz⟩).commRingCatIsoToRingEquiv
    infer_instance
  -- the normalization `(η).normalization` is a smooth curve
  have : IsLocallyNoetherian (η).normalization :=
    LocallyOfFiniteType.isLocallyNoetherian ((η).fromNormalization ≫ p)
  have hdim' : topologicalKrullDim (η).normalization ≤ 1 :=
    ((η).fromNormalization.topologicalKrullDim_le_of_locallyQuasiFinite).trans hZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace p
  have : CompactSpace (η).normalization :=
    QuasiCompact.compactSpace_of_compactSpace (η).fromNormalization
  have : IsNoetherian (η).normalization := {}
  have hnorm : ExposeI.IsNormalScheme (η).normalization := fun z ↦ by
    have := hreg' z
    exact ⟨inferInstance, inferInstance⟩
  have : Smooth ((η).fromNormalization ≫ p) :=
    ExposeX.smooth_of_isNormalScheme_of_topologicalKrullDim_le_one ((η).fromNormalization ≫ p) hnorm
      hdim'
  -- the complement `Y` of `ν⁻¹(U)` is a finite set of closed points
  set Y : Set (η).normalization :=
    (((η).fromNormalization ⁻¹ᵁ U : (η).normalization.Opens) : Set (η).normalization)ᶜ with hY
  have hYc : IsClosed Y := ((η).fromNormalization ⁻¹ᵁ U).2.isClosed_compl
  have hηY : genericPoint (η).normalization ∉ Y := by
    obtain ⟨u, hu⟩ := hU
    obtain ⟨z', hz'⟩ := (η).fromNormalization.surjective u
    have hne : ((η).fromNormalization ⁻¹ᵁ U : Set (η).normalization).Nonempty :=
      ⟨z', show (η).fromNormalization z' ∈ U from hz' ▸ hu⟩
    simp only [hY, Set.mem_compl_iff, not_not]
    exact ((genericPoint_spec (η).normalization).mem_open_set_iff
      ((η).fromNormalization ⁻¹ᵁ U).2).mpr
      (by simpa using hne)
  have hne (y : Y) : (y : (η).normalization) ≠ genericPoint (η).normalization :=
    fun h ↦ hηY (h ▸ y.2)
  have hYcl (y : (η).normalization) (hy : y ∈ Y) : IsClosed ({y} : Set (η).normalization) :=
    isClosed_singleton_of_ne_genericPoint hdim' fun h ↦ hηY (h ▸ hy)
  have hYfin : Y.Finite :=
    TopologicalSpace.NoetherianSpace.finite_of_isClosed_of_forall_isClosed_singleton hYc hYcl
  have hO (y : Y) : IsOpen ((Y \ {(y : (η).normalization)})ᶜ) := by
    refine isOpen_compl_iff.mpr ?_
    rw [← Set.biUnion_of_singleton (Y \ {(y : (η).normalization)})]
    exact Set.Finite.isClosed_biUnion (hYfin.subset Set.sdiff_subset) fun z hz ↦ hYcl z hz.1
  -- charts at the points of `Y`
  have hchart (y : Y) := exists_chart_of_ne_genericPoint hreg' hdim' (hne y)
    (O := ⟨_, hO y⟩) (by simp)
  choose R e he r hrO hxr hmax hzl using hchart
  -- the normal crossings structure: `ν⁻¹(U)` and the charts at the points of `Y`
  let W : Option Y → Scheme.{u} := fun a ↦
    Option.rec ((η).fromNormalization ⁻¹ᵁ U).toScheme (fun y ↦ Spec (R y)) a
  let E : ∀ a, W a ⟶ (η).normalization := fun a ↦
    Option.rec (motive := fun a ↦ W a ⟶ (η).normalization) ((η).fromNormalization ⁻¹ᵁ U).ι
      (fun y ↦ e y) a
  refine ⟨Option Y, W, E, ?_, ?_, ?_⟩
  · rintro (_ | y)
    · exact inferInstanceAs (Etale ((η).fromNormalization ⁻¹ᵁ U).ι)
    · have := he y
      exact inferInstanceAs (Etale (e y))
  · refine Set.eq_univ_of_forall fun z ↦ Set.mem_iUnion.mpr ?_
    by_cases hz : z ∈ Y
    · exact ⟨some ⟨z, hz⟩, hxr ⟨z, hz⟩⟩
    · refine ⟨none, ?_⟩
      change z ∈ Set.range ((η).fromNormalization ⁻¹ᵁ U).ι
      rw [Scheme.Opens.range_ι]
      simpa [hY] using hz
  · rintro (_ | y)
    · refine ⟨Empty, inferInstance, Empty.elim, fun x hx ↦ by simp at hx, ?_⟩
      ext z
      simp only [Set.mem_preimage, Set.mem_iUnion, IsEmpty.exists_iff, iff_false]
      change ¬ (((η).fromNormalization ⁻¹ᵁ U).ι z ∈ Y)
      simp only [hY, Set.mem_compl_iff, not_not]
      exact z.2
    · have hpre : e y ⁻¹' Y = e y ⁻¹' {(y : (η).normalization)} := by
        ext q
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        refine ⟨fun hq ↦ ?_, fun hq ↦ hq ▸ y.2⟩
        by_contra hqy
        exact hrO y ⟨q, rfl⟩ ⟨hq, hqy⟩
      have hzl' : (Spec (R y)).zeroLocus {(Scheme.ΓSpecIso (R y)).inv (r y)} =
          e y ⁻¹' {(y : (η).normalization)} := by
        rw [Scheme.zeroLocus_singleton, basicOpen_eq_of_affine, ← hzl y]
        ext q
        change q ∉ PrimeSpectrum.basicOpen (r y) ↔ q ∈ PrimeSpectrum.zeroLocus {r y}
        rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
        exact not_not.trans Iff.rfl
      have hmax' : (Ideal.span {(Scheme.ΓSpecIso (R y)).inv (r y)}).IsMaximal := by
        have := hmax y
        have h := Ideal.map_isMaximal_of_equiv
          (Scheme.ΓSpecIso (R y)).symm.commRingCatIsoToRingEquiv (p := Ideal.span {r y})
        rwa [Ideal.map_span, Set.image_singleton] at h
      refine ⟨Unit, inferInstance, fun _ ↦ (Scheme.ΓSpecIso (R y)).inv (r y),
        isStrictNormalCrossings_of_isMaximal (e y ≫ (η).fromNormalization ≫ p) _ hmax'
          fun v hv ↦ ?_, ?_⟩
      · refine isSmoothOfRelativeDimensionAt_of_smooth _ v 1 ?_
        rw [← (e y).isOpenEmbedding.topologicalKrullDimAt_eq v]
        exact topologicalKrullDimAt_eq_one ((η).fromNormalization ≫ p) hdim' (hne y) _
      · change e y ⁻¹' Y = _
        rw [hpre, ← hzl', Set.iUnion_const]

end Strong

/-- **SGA 5 I 3.1.5 in dimension `≤ 1`** (the strong desingularization hypothesis of XIII.3.5 and
4.6 for curves): over a perfect field `k`, the integral schemes of finite type of dimension `≤ 1`
are strongly desingularizable. -/
theorem stronglyDesingularizableUpTo_one (k : Type u) [Field k] [PerfectField k] :
    StronglyDesingularizableUpTo k 1 :=
  fun _ p _ _ _ hZ ↦ isStronglyDesingularizable_of_topologicalKrullDim_le_one p hZ

/-- The strong desingularization hypothesis of XIII.3.5 (`GenericSpecializationStatement`) holds for
relative curves: if the generic fibre of `f : X ⟶ S` has dimension `≤ 1`, the integral schemes of
finite type of that dimension over an algebraic closure of `κ(s)` are strongly
desingularizable. -/
theorem stronglyDesingularizableUpTo_genericFibre_of_dim_le_one {X S : Scheme.{u}}
    [IrreducibleSpace S] (f : X ⟶ S)
    (hX : topologicalKrullDim
      ↥(pullback f (S.fromSpecResidueField (genericPoint S)) : Scheme.{u}) ≤ 1) :
    StronglyDesingularizableUpTo (AlgebraicClosure (S.residueField (genericPoint S)))
      (topologicalKrullDim
        ↥(pullback f (S.fromSpecResidueField (genericPoint S)) : Scheme.{u})) :=
  (stronglyDesingularizableUpTo_one _).mono hX

end SGA.SGA1.ExposeXIII
