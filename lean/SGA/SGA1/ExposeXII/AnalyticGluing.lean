/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.GluingLocalization
import SGA.Foundations.Formal.FormalScheme
import SGA.SGA1.ExposeXII.MorphismComparisonScheme
import SGA.SGA1.ExposeXII.SchemePoints

/-!
# SGA 1, Exposé XII, 1.1: the analytic space `X^an` of a separated scheme

For `X` a separated `ℂ`-scheme locally of finite type, `X^an` (`AnalyticGluing.analyticSpace X`)
is glued from the analytic spaces `U^an` of the affine opens `U` of `X` (`chart X U`, the
non-reduced `affineAnalytification`) along the `(U ∩ V)^an`, which are affine because `X` is
separated. Main results:

* for a localization `A → A_a`, `Spec(A_a)^an → Spec(A)^an` is an open immersion onto `φ⁻¹(D(a))`
  (`isOpenImmersion_affineAnalytificationMap_of_isLocalization`,
  `range_affineAnalytificationMap_of_isLocalization`); hence for affine opens `V ≤ U`,
  `V^an → U^an` is an open immersion onto the points over `V` (`isOpenImmersion_chartMap`,
  `range_chartMap`; via `SheafedSpace.IsOpenImmersion.of_stalk_iso` and basic opens);
* the gluing data (`glueData`, for any family `S` of affine opens; the cocycle condition through
  the triple intersections, `isIso_tripleToPullback`), the open immersions `ι U : U^an → X^an`,
  the canonical morphism `φ = toScheme X : X^an → X` (XII.1.1), which is a comparison morphism
  (`isComparison_toScheme`, XII.2.1), injective on points with image the closed points of `X`
  (`injective_toScheme_base`, `range_toScheme_base`);
* gluing along any family of affine opens that is a basis gives `X^an` again
  (`isIso_gluedToAnalytic`), which is how `f^an` is built (`AnalyticGluingMap.lean`).

SGA defines `X^an` for every `X` locally of finite type; the separatedness assumption is a
restriction of this file (non-separated `X` would need gluing along the non-affine `U ∩ V`).

SGA characterizes `X^an` by a universal property (it represents `Y ↦ Hom_ℂ(Y, X)` on analytic
spaces). That property is proved only for affine `X` and tested on local models
(`AffineAnalytification.existsUnique_comp_affineToSpec`); for the glued `X^an` it is not proved.

The reduced space `(X^an)_red` is `SchemePoints.analytification ℂ X` (`Analytic.lean`, defined for
every `X`, with underlying space `X(ℂ)`). `AnalyticGluingPoints.lean` identifies the underlying
spaces (`pointsHomeomorph X : X^an ≃ₜ X(ℂ)`); `AnalyticGluingReduced.lean` proves, for affine `X`,
that the reduced structure sheaf is the reduction of `𝒪_{X^an}` (the sheaf-level statement for
non-affine `X` is not formalized). Facts about the topology of `X(ℂ)` should be transported along
`pointsHomeomorph`, not proved again for `analyticSpace X`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AnalyticGeometry Topology

namespace SGA.SGA1.ExposeXII

namespace AffineAnalytification

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {A B : Type} [CommRing A]
  [Algebra 𝕜 A] [Algebra.FinitePresentation 𝕜 A] [CommRing B] [Algebra 𝕜 B]
  [Algebra.FinitePresentation 𝕜 B]

omit [CompleteSpace 𝕜] [Algebra.FinitePresentation 𝕜 B] in
/-- A localization `e : A → B = A_a`, transported to the chosen presentation of `A`: an
isomorphism of `𝕜`-algebras between the standard presentation `𝕜[x, t]/(g, t q - 1)` of the
localization (`q` a lift of `a`) and `B`, compatible with `e`. -/
lemma exists_localizationPresentation (e : A →ₐ[𝕜] B) (a : A)
    (h : letI := e.toRingHom.toAlgebra; IsLocalization.Away a B) :
    ∃ (q : MvPolynomial (Fin (presentationVars 𝕜 A)) 𝕜)
      (θ : PresentedAlgebra (localizationPolys (presentationPolys 𝕜 A) q) ≃ₐ[𝕜] B),
      Ideal.Quotient.mk _ q = (presentationEquiv 𝕜 A).symm a ∧
      θ.toAlgHom.comp (localizationAlgHom _ q) = e.comp (presentationEquiv 𝕜 A).toAlgHom := by
  set g := presentationPolys 𝕜 A
  set pA := presentationEquiv 𝕜 A
  obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective (pA.symm a)
  let ℓ := localizationAlgHom g q
  have hu : IsUnit ((e.toRingHom.comp pA.toRingEquiv.toRingHom) (classOfPoly g q)) := by
    let := e.toRingHom.toAlgebra
    have : (e.toRingHom.comp pA.toRingEquiv.toRingHom) (classOfPoly g q) = algebraMap A B a := by
      change e (pA (Ideal.Quotient.mk _ q)) = e a
      rw [hq, AlgEquiv.apply_symm_apply]
    rw [this]
    exact IsLocalization.Away.algebraMap_isUnit a
  have hu' : IsUnit ((ℓ.toRingHom.comp pA.symm.toRingEquiv.toRingHom) a) := by
    change IsUnit (ℓ (pA.symm a))
    rw [← hq]
    exact isUnit_localizationAlgHom g q
  let : Algebra (PresentedAlgebra g) (PresentedAlgebra (localizationPolys g q)) :=
    ℓ.toRingHom.toAlgebra
  have := isLocalization_away_localizationAlgHom g q
  let θ : PresentedAlgebra (localizationPolys g q) →+* B :=
    IsLocalization.Away.lift (classOfPoly g q) hu
  have hθ (x : PresentedAlgebra g) : θ (ℓ x) = e (pA x) :=
    IsLocalization.Away.lift_eq (classOfPoly g q) hu x
  let : Algebra A B := e.toRingHom.toAlgebra
  let θ' : B →+* PresentedAlgebra (localizationPolys g q) := IsLocalization.Away.lift a hu'
  have hθ' (y : A) : θ' (e y) = ℓ (pA.symm y) := IsLocalization.Away.lift_eq a hu' y
  have h₁ : θ'.comp θ = RingHom.id _ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (classOfPoly g q))
      (RingHom.ext fun x ↦ ?_)
    change θ' (θ (ℓ x)) = ℓ x
    rw [hθ, hθ', AlgEquiv.symm_apply_apply]
  have h₂ : θ.comp θ' = RingHom.id _ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers a) (RingHom.ext fun y ↦ ?_)
    change θ (θ' (e y)) = e y
    rw [hθ', hθ, AlgEquiv.apply_symm_apply]
  let θe : PresentedAlgebra (localizationPolys g q) ≃ₐ[𝕜] B :=
    { toRingEquiv := RingEquiv.ofRingHom θ θ' h₂ h₁
      commutes' := fun c ↦ by
        change θ (algebraMap 𝕜 _ c) = algebraMap 𝕜 B c
        rw [← ℓ.commutes c, hθ, AlgEquiv.commutes, AlgHom.commutes] }
  exact ⟨q, θe, hq, AlgHom.ext fun x ↦ hθ x⟩

lemma affineToSpec_base_asIdeal (x : affineAnalytification 𝕜 A) :
    ((affineToSpec 𝕜 A).base x).asIdeal =
      ((toSpec (presentationPolys 𝕜 A)).base x).asIdeal.comap
        (presentationEquiv 𝕜 A).symm.toRingEquiv.toRingHom :=
  rfl

/-- XII.1.1: for a localization `e : A → B = A_a`, `f^an : Spec(B)^an → Spec(A)^an` is the
analytic map of the standard presentation of `A_a` followed by an isomorphism. -/
lemma affineAnalytificationMap_eq_of_isLocalization (e : A →ₐ[𝕜] B) (a : A)
    (h : letI := e.toRingHom.toAlgebra; IsLocalization.Away a B) :
    ∃ (q : MvPolynomial (Fin (presentationVars 𝕜 A)) 𝕜)
      (i : affineAnalytification 𝕜 B ⟶ analytification
        (localizationPolys (presentationPolys 𝕜 A) q)),
      IsIso i ∧ Ideal.Quotient.mk _ q = (presentationEquiv 𝕜 A).symm a ∧
      affineAnalytificationMap e = i ≫ analytificationMap _ _
        (localizationAlgHom (presentationPolys 𝕜 A) q) := by
  obtain ⟨q, θ, hq, hθ⟩ := exists_localizationPresentation e a h
  let ψ := θ.trans (presentationEquiv 𝕜 B).symm
  have key : presentedHom e = ψ.toAlgHom.comp (localizationAlgHom _ q) := by
    ext x
    change (presentationEquiv 𝕜 B).symm (e (presentationEquiv 𝕜 A x)) =
      (presentationEquiv 𝕜 B).symm (θ (localizationAlgHom _ q x))
    exact congrArg _ (DFunLike.congr_fun hθ x).symm
  refine ⟨q, analytificationMap _ _ ψ.toAlgHom, ?_, hq, ?_⟩
  · have : analytificationMap _ _ ψ.toAlgHom = (analytificationIso ψ.symm).hom := rfl
    rw [this]
    infer_instance
  · rw [affineAnalytificationMap, key, analytificationMap_comp]

/-- XII.1.1: for a localization `e : A → B = A_a` of finitely presented `𝕜`-algebras,
`Spec(B)^an → Spec(A)^an` is an open immersion. -/
theorem isOpenImmersion_affineAnalytificationMap_of_isLocalization (e : A →ₐ[𝕜] B) (a : A)
    (h : letI := e.toRingHom.toAlgebra; IsLocalization.Away a B) :
    LocallyRingedSpace.IsOpenImmersion (affineAnalytificationMap e) := by
  obtain ⟨q, i, hi, -, he⟩ := affineAnalytificationMap_eq_of_isLocalization e a h
  have := isOpenImmersion_analytificationMap_localization (presentationPolys 𝕜 A) q
  rw [he]
  infer_instance

/-- XII.1.1: for a localization `e : A → B = A_a` of finitely presented `𝕜`-algebras, the image
of `Spec(B)^an → Spec(A)^an` is `φ⁻¹(D(a))`. -/
theorem range_affineAnalytificationMap_of_isLocalization (e : A →ₐ[𝕜] B) (a : A)
    (h : letI := e.toRingHom.toAlgebra; IsLocalization.Away a B) :
    Set.range (affineAnalytificationMap e).base =
      {x | a ∉ ((affineToSpec 𝕜 A).base x).asIdeal} := by
  obtain ⟨q, i, hi, hq, he⟩ := affineAnalytificationMap_eq_of_isLocalization e a h
  have hsurj : Function.Surjective i.base := by
    have : IsIso i.base := by
      have : IsIso ((LocallyRingedSpace.forgetToTop).map i) := inferInstance
      exact this
    exact (TopCat.homeoOfIso (asIso i.base)).surjective
  ext x
  have hr : x ∈ Set.range (affineAnalytificationMap e).base ↔
      x ∈ Set.range
        (analytificationMap _ _ (localizationAlgHom (presentationPolys 𝕜 A) q)).base := by
    rw [he]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨i.base y, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨y, rfl⟩ := hsurj z
      exact ⟨y, rfl⟩
  rw [hr, Set.mem_ofPred_eq, affineToSpec_base_asIdeal, Ideal.mem_comap,
    mem_range_analytificationMap_localization, eval_ne_zero_iff_notMem_toSpec, hq]
  rfl

end AffineAnalytification

/-! ### The analytic charts of a scheme -/

namespace AnalyticGluing

open AffineAnalytification LocallyRingedSpaceComparison SchemePoints

attribute [local instance] sectionsAlgebra

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]

lemma finitePresentation_sections (U : X.affineOpens) : Algebra.FinitePresentation ℂ Γ(X, U) :=
  have := finiteType_sections (K := ℂ) U.2
  Algebra.FinitePresentation.of_finiteType.mp ‹_›

attribute [local instance] finitePresentation_sections

/-- The analytic space `U^an` of an affine open `U` of `X` (XII.1.1). -/
abbrev chart (U : X.affineOpens) : LocallyRingedSpace.{0} := affineAnalytification ℂ Γ(X, U)

variable {X}

/-- For affine opens `V ≤ U`, the morphism `V^an → U^an` (XII.1.2). -/
def chartMap {U V : X.affineOpens} (h : V ≤ U) : chart X V ⟶ chart X U :=
  affineAnalytificationMap (resAlgHom (K := ℂ) (X := X) (show (V : X.Opens) ≤ U from h))

omit [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] in
lemma isAffineOpen (U : X.affineOpens) : IsAffineOpen (U : X.Opens) := U.2

/-- The open immersion `Spec Γ(X, U) → X` of an affine open, as a morphism of locally ringed
spaces. -/
def fromSpecLRS (U : X.affineOpens) :
    Spec.locallyRingedSpaceObj (CommRingCat.of Γ(X, U)) ⟶ X.toLocallyRingedSpace :=
  (isAffineOpen U).fromSpec.toLRSHom

instance (U : X.affineOpens) : LocallyRingedSpace.IsOpenImmersion (fromSpecLRS U) :=
  (inferInstance : IsOpenImmersion (isAffineOpen U).fromSpec)

/-- The canonical morphism `φ_U : U^an → U ⊆ X`. -/
def chartToScheme (U : X.affineOpens) : chart X U ⟶ X.toLocallyRingedSpace :=
  affineToSpec ℂ Γ(X, U) ≫ fromSpecLRS U

lemma chartMap_id (U : X.affineOpens) : chartMap (le_refl U) = 𝟙 _ := by
  rw [chartMap, ← affineAnalytificationMap_id]
  congr 1
  ext a
  change X.presheaf.map (homOfLE _).op a = a
  rw [show (homOfLE (le_refl (U : X.Opens))).op = 𝟙 _ from rfl, X.presheaf.map_id]
  rfl

@[reassoc]
lemma chartMap_comp {U V W : X.affineOpens} (h₁ : W ≤ V) (h₂ : V ≤ U) :
    chartMap h₁ ≫ chartMap h₂ = chartMap (h₁.trans h₂) := by
  rw [chartMap, chartMap, chartMap, ← affineAnalytificationMap_comp]
  congr 1
  ext a
  change X.presheaf.map (homOfLE _).op (X.presheaf.map (homOfLE _).op a) =
    X.presheaf.map (homOfLE _).op a
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

@[reassoc]
lemma chartMap_chartToScheme {U V : X.affineOpens} (h : V ≤ U) :
    chartMap h ≫ chartToScheme U = chartToScheme V := by
  rw [chartMap, chartToScheme, chartToScheme, ← Category.assoc,
    affineAnalytificationMap_comp_affineToSpec, Category.assoc]
  congr 1
  have := IsAffineOpen.map_fromSpec (isAffineOpen U) (isAffineOpen V)
    (homOfLE (show (V : X.Opens) ≤ U from h)).op
  exact congrArg Scheme.Hom.toLRSHom this

/-- XII.2.1: `φ_U : U^an → X` is a comparison morphism. -/
lemma isComparison_chartToScheme (U : X.affineOpens) : IsComparison (chartToScheme U) :=
  (isComparison_affineToSpec ℂ Γ(X, U)).comp_isOpenImmersion _

/-! ### Chart maps are open immersions -/

lemma injective_affineToSpec_base (𝕜 : Type) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (A : Type) [CommRing A] [Algebra 𝕜 A] [Algebra.FinitePresentation 𝕜 A] :
    Function.Injective (affineToSpec 𝕜 A).base := by
  intro x y hxy
  obtain ⟨φ, rfl⟩ := (affinePointsHomeomorph 𝕜 A).surjective x
  obtain ⟨ψ, rfl⟩ := (affinePointsHomeomorph 𝕜 A).surjective y
  rw [affineToSpec_base_affinePointsHomeomorph, affineToSpec_base_affinePointsHomeomorph] at hxy
  rw [Points.toPrimeSpectrum_injective hxy]

lemma injective_chartToScheme_base (U : X.affineOpens) :
    Function.Injective (chartToScheme U).base :=
  (isAffineOpen U).fromSpec.isOpenEmbedding.injective.comp (injective_affineToSpec_base ℂ _)

lemma injective_chartMap_base {U V : X.affineOpens} (h : V ≤ U) :
    Function.Injective (chartMap h).base := by
  intro x y hxy
  apply injective_chartToScheme_base V
  rw [← chartMap_chartToScheme h]
  change (chartToScheme U).base ((chartMap h).base x) = (chartToScheme U).base ((chartMap h).base y)
  rw [hxy]

/-- A point `x` of `V^an` lies over the open `X.basicOpen t` (`t ∈ Γ(X, V)`) iff `t` does not vanish
at `φ(x)`. -/
lemma chartToScheme_base_mem_basicOpen_iff (V : X.affineOpens) (t : Γ(X, V))
    (x : chart X V) :
    (chartToScheme V).base x ∈ X.basicOpen t ↔ t ∉ ((affineToSpec ℂ Γ(X, V)).base x).asIdeal :=
  SetLike.ext_iff.mp ((isAffineOpen V).fromSpec_preimage_basicOpen (f := t))
    ((affineToSpec ℂ Γ(X, V)).base x)

/-- For affine opens `D ≤ V` with `D = X.basicOpen t`, the chart map `D^an → V^an` is an open
immersion onto the set of points lying over `D`. -/
lemma isOpenImmersion_chartMap_of_eq_basicOpen {V D : X.affineOpens} (h : D ≤ V) (t : Γ(X, V))
    (ht : (D : X.Opens) = X.basicOpen t) : LocallyRingedSpace.IsOpenImmersion (chartMap h) :=
  isOpenImmersion_affineAnalytificationMap_of_isLocalization _ t
    ((isAffineOpen V).isLocalization_of_eq_basicOpen t (homOfLE h) ht)

lemma range_chartMap_of_eq_basicOpen {V D : X.affineOpens} (h : D ≤ V) (t : Γ(X, V))
    (ht : (D : X.Opens) = X.basicOpen t) :
    Set.range (chartMap h).base = (chartToScheme V).base ⁻¹' (D : Set X) := by
  rw [chartMap, range_affineAnalytificationMap_of_isLocalization _ t
    ((isAffineOpen V).isLocalization_of_eq_basicOpen t (homOfLE h) ht)]
  ext x
  rw [Set.mem_preimage, ht, SetLike.mem_coe, chartToScheme_base_mem_basicOpen_iff]
  rfl

lemma chartToScheme_base_mem (V : X.affineOpens) (x : chart X V) :
    (chartToScheme V).base x ∈ (V : X.Opens) := by
  change _ ∈ (V : Set X)
  rw [← (isAffineOpen V).range_fromSpec]
  exact ⟨_, rfl⟩

/-- Every point of `V^an` lies in the image of the chart of a basic open `D(s) ⊆ V` of `U`,
`s ∈ Γ(X, U)`, for affine opens `V ≤ U`. -/
lemma exists_basicOpen_chart {U V : X.affineOpens} (h : V ≤ U) (x : chart X V) :
    ∃ (D : X.affineOpens) (hDV : D ≤ V) (s : Γ(X, U)),
      (D : X.Opens) = X.basicOpen s ∧ x ∈ Set.range (chartMap hDV).base := by
  have hxV := chartToScheme_base_mem V x
  obtain ⟨s, hsV, hxs⟩ := (isAffineOpen U).exists_basicOpen_le ⟨_, hxV⟩ (h hxV)
  let D : X.affineOpens := ⟨X.basicOpen s, (isAffineOpen U).basicOpen s⟩
  have hDV : D ≤ V := hsV
  refine ⟨D, hDV, s, rfl, ?_⟩
  have ht : (D : X.Opens) = X.basicOpen (X.presheaf.map (homOfLE h).op s) := by
    rw [Scheme.basicOpen_res]
    exact (inf_eq_right.mpr hsV).symm
  rw [range_chartMap_of_eq_basicOpen hDV _ ht]
  exact hxs

/-- XII.1.1: for affine opens `V ≤ U` of `X`, the morphism `V^an → U^an` is an open
immersion. -/
theorem isOpenImmersion_chartMap {U V : X.affineOpens} (h : V ≤ U) :
    LocallyRingedSpace.IsOpenImmersion (chartMap h) := by
  -- local structure: near each point, `chartMap h` is `D^an → U^an` composed with the inverse of
  -- `D^an → V^an`, for a basic open `D` of `U`
  have loc (x : chart X V) : ∃ (D : X.affineOpens) (hDV : D ≤ V) (y : chart X D),
      LocallyRingedSpace.IsOpenImmersion (chartMap hDV) ∧
      LocallyRingedSpace.IsOpenImmersion (chartMap (hDV.trans h)) ∧ (chartMap hDV).base y = x := by
    obtain ⟨D, hDV, s, hs, y, hy⟩ := exists_basicOpen_chart h x
    have ht : (D : X.Opens) = X.basicOpen (X.presheaf.map (homOfLE h).op s) := by
      rw [Scheme.basicOpen_res, ← hs]
      exact (inf_eq_right.mpr hDV).symm
    exact ⟨D, hDV, y, isOpenImmersion_chartMap_of_eq_basicOpen hDV _ ht,
      isOpenImmersion_chartMap_of_eq_basicOpen (hDV.trans h) s hs, hy⟩
  have hstalk (x : chart X V) : IsIso ((chartMap h).stalkMap x) := by
    obtain ⟨D, hDV, y, h₁, h₂, rfl⟩ := loc x
    have : LocallyRingedSpace.IsOpenImmersion (chartMap hDV ≫ chartMap h) := by
      rw [chartMap_comp]
      exact h₂
    have : IsIso ((chartMap hDV ≫ chartMap h).stalkMap y) := inferInstance
    rw [LocallyRingedSpace.stalkMap_comp] at this
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance this
  have hopen : IsOpenEmbedding (chartMap h).base := by
    refine .of_continuous_injective_isOpenMap (chartMap h).base.hom.continuous
      (injective_chartMap_base h) (isOpenMap_iff_nhds_le.mpr fun x ↦ ?_)
    obtain ⟨D, hDV, y, h₁, h₂, rfl⟩ := loc x
    have o₁ : IsOpenEmbedding (chartMap hDV).base := h₁.base_open
    have o₂ : IsOpenEmbedding (chartMap (hDV.trans h)).base := h₂.base_open
    have e₁ := o₁.map_nhds_eq y
    have e₂ := o₂.map_nhds_eq y
    rw [← chartMap_comp hDV h] at e₂
    have e₂' : Filter.map ((chartMap h).base ∘ (chartMap hDV).base) (𝓝 y) =
        𝓝 ((chartMap h).base ((chartMap hDV).base y)) := e₂
    rw [← e₁, Filter.map_map, e₂']
  exact LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _ hopen

instance {U V : X.affineOpens} (h : V ≤ U) : LocallyRingedSpace.IsOpenImmersion (chartMap h) :=
  isOpenImmersion_chartMap h

lemma comp_base_apply' {A B C : LocallyRingedSpace.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g).base x = g.base (f.base x) :=
  rfl

lemma base_apply_eq_of_eq {A B : LocallyRingedSpace.{0}} {m₁ m₂ : A ⟶ B} (e : m₁ = m₂) (p : A) :
    m₁.base p = m₂.base p := by
  rw [e]

/-- XII.1.1: for affine opens `V ≤ U`, the image of `V^an → U^an` is the set of points of `U^an`
lying over `V`. -/
theorem range_chartMap {U V : X.affineOpens} (h : V ≤ U) :
    Set.range (chartMap h).base = (chartToScheme U).base ⁻¹' (V : Set X) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [Set.mem_preimage, ← comp_base_apply', chartMap_chartToScheme]
    exact chartToScheme_base_mem V x
  · intro hy
    obtain ⟨s, hsV, hys⟩ := (isAffineOpen U).exists_basicOpen_le ⟨_, hy⟩
      (chartToScheme_base_mem U y)
    let D : X.affineOpens := ⟨X.basicOpen s, (isAffineOpen U).basicOpen s⟩
    have hDV : D ≤ V := hsV
    have hy' : y ∈ Set.range (chartMap (hDV.trans h)).base := by
      rw [range_chartMap_of_eq_basicOpen (hDV.trans h) s rfl]
      exact hys
    obtain ⟨z, rfl⟩ := hy'
    refine ⟨(chartMap hDV).base z, ?_⟩
    rw [← comp_base_apply', chartMap_comp]

/-! ### Gluing the charts of a separated scheme -/

variable [IsSeparated (X ↘ Spec (.of ℂ))]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of ℂ))] in
/-- A scheme separated over `Spec ℂ` is separated (mathlib's `Scheme.IsSeparated`), so that
intersections of affine opens are affine (`IsAffineOpen.inf`). -/
lemma isSeparated_scheme : X.IsSeparated :=
  (IsSeparated.hasAffineProperty.iff_of_isAffine (f := X ↘ Spec (.of ℂ))).mp inferInstance

/-- The intersection of two affine opens of a separated scheme, as an affine open. -/
def inter (U V : X.affineOpens) : X.affineOpens :=
  have := isSeparated_scheme (X := X)
  ⟨(U : X.Opens) ⊓ (V : X.Opens), (isAffineOpen U).inf (isAffineOpen V)⟩

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of ℂ))] in
lemma inter_le_left (U V : X.affineOpens) : inter U V ≤ U := by
  change (U : X.Opens) ⊓ (V : X.Opens) ≤ U
  exact inf_le_left

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of ℂ))] in
lemma inter_le_right (U V : X.affineOpens) : inter U V ≤ V := by
  change (U : X.Opens) ⊓ (V : X.Opens) ≤ V
  exact inf_le_right

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of ℂ))] in
lemma inter_le_inter_comm (U V : X.affineOpens) : inter U V ≤ inter V U := by
  change (U : X.Opens) ⊓ (V : X.Opens) ≤ (V : X.Opens) ⊓ (U : X.Opens)
  rw [inf_comm]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of ℂ))] in
lemma le_inter {U V W : X.affineOpens} (h₁ : W ≤ U) (h₂ : W ≤ V) : W ≤ inter U V := by
  change (W : X.Opens) ≤ (U : X.Opens) ⊓ (V : X.Opens)
  exact le_inf h₁ h₂

/-- The triple intersection `(i ∩ j) ∩ k`. -/
abbrev triple (i j k : X.affineOpens) : X.affineOpens := inter (inter i j) k

/-- The range condition for the transition maps `t'` of the gluing data. -/
lemma range_subset_range_chartMap_inter (i j k : X.affineOpens) :
    Set.range (pullback.fst (chartMap (inter_le_left i j)) (chartMap (inter_le_left i k)) ≫
      chartMap (inter_le_inter_comm i j) ≫ chartMap (inter_le_left j i)).base ⊆
      Set.range (chartMap (inter_le_left j k)).base := by
  rw [range_chartMap]
  rintro _ ⟨p, rfl⟩
  have e₁ : pullback.fst (chartMap (inter_le_left i j)) (chartMap (inter_le_left i k)) ≫
      chartMap (inter_le_inter_comm i j) ≫ chartMap (inter_le_left j i) ≫ chartToScheme j =
      pullback.fst _ _ ≫ chartToScheme (inter i j) := by
    rw [chartMap_chartToScheme, chartMap_chartToScheme]
  have e₂ : pullback.fst (chartMap (inter_le_left i j)) (chartMap (inter_le_left i k)) ≫
      chartToScheme (inter i j) = pullback.snd _ _ ≫ chartToScheme (inter i k) := by
    rw [← chartMap_chartToScheme (inter_le_left i j), pullback.condition_assoc,
      chartMap_chartToScheme]
  rw [Set.mem_preimage, ← comp_base_apply']
  simp only [Category.assoc]
  rw [e₁]
  have hj : (pullback.fst _ _ ≫ chartToScheme (inter i j)).base p ∈ (inter i j : X.Opens) :=
    chartToScheme_base_mem _ _
  have hk : (pullback.fst _ _ ≫ chartToScheme (inter i j)).base p ∈ (inter i k : X.Opens) := by
    rw [base_apply_eq_of_eq e₂]
    exact chartToScheme_base_mem _ _
  exact ⟨inter_le_right i j hj, inter_le_right i k hk⟩

omit [IsSeparated (X ↘ Spec (CommRingCat.of ℂ))] in
lemma chartMap_eq_id {U : X.affineOpens} (h : U ≤ U) : chartMap h = 𝟙 _ :=
  chartMap_id U

section Triple

variable (a b c : X.affineOpens)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of ℂ))] in
lemma triple_le_inter_left : triple a b c ≤ inter a b := inter_le_left _ _

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of ℂ))] in
lemma triple_le_inter_right : triple a b c ≤ inter a c :=
  le_inter ((inter_le_left _ _).trans (inter_le_left a b)) (inter_le_right _ _)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of ℂ))] in
lemma triple_le_triple : triple a b c ≤ triple b c a :=
  le_inter (le_inter ((triple_le_inter_left a b c).trans (inter_le_right a b))
    (inter_le_right _ _)) ((triple_le_inter_left a b c).trans (inter_le_left a b))

/-- The triple intersection chart `((a ∩ b) ∩ c)^an`, mapped to the fibre product
`(a ∩ b)^an ×_{a^an} (a ∩ c)^an`. -/
def tripleToPullback :
    chart X (triple a b c) ⟶
      pullback (chartMap (inter_le_left a b)) (chartMap (inter_le_left a c)) :=
  pullback.lift (chartMap (triple_le_inter_left a b c)) (chartMap (triple_le_inter_right a b c))
    (by rw [chartMap_comp, chartMap_comp])

@[reassoc (attr := simp)]
lemma tripleToPullback_fst :
    tripleToPullback a b c ≫ pullback.fst _ _ = chartMap (triple_le_inter_left a b c) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma tripleToPullback_snd :
    tripleToPullback a b c ≫ pullback.snd _ _ = chartMap (triple_le_inter_right a b c) :=
  pullback.lift_snd _ _ _

/-- The triple intersection chart is the fibre product: `tripleToPullback` is an isomorphism. -/
instance isIso_tripleToPullback : IsIso (tripleToPullback a b c) := by
  let m := pullback.fst (chartMap (inter_le_left a b)) (chartMap (inter_le_left a c)) ≫
    chartMap (inter_le_left a b)
  have hT : triple a b c ≤ a := (triple_le_inter_left a b c).trans (inter_le_left a b)
  have hm : tripleToPullback a b c ≫ m = chartMap hT := by
    simp only [m, tripleToPullback_fst_assoc, chartMap_comp]
  have hrange : Set.range m.base ⊆ Set.range (chartMap hT).base := by
    rw [range_chartMap]
    rintro _ ⟨p, rfl⟩
    have e₁ : m ≫ chartToScheme a = pullback.fst _ _ ≫ chartToScheme (inter a b) := by
      simp only [m, Category.assoc, chartMap_chartToScheme]
    have e₂ : m ≫ chartToScheme a = pullback.snd _ _ ≫ chartToScheme (inter a c) := by
      simp only [m, Category.assoc]
      rw [pullback.condition_assoc, chartMap_chartToScheme]
    rw [Set.mem_preimage, ← comp_base_apply']
    have h₁ : (m ≫ chartToScheme a).base p ∈ (inter a b : X.Opens) := by
      rw [base_apply_eq_of_eq e₁]
      exact chartToScheme_base_mem _ _
    have h₂ : (m ≫ chartToScheme a).base p ∈ (inter a c : X.Opens) := by
      rw [base_apply_eq_of_eq e₂]
      exact chartToScheme_base_mem _ _
    exact ⟨h₁, inter_le_right a c h₂⟩
  let L := LocallyRingedSpace.IsOpenImmersion.lift (chartMap hT) m hrange
  have hL : L ≫ chartMap hT = m := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  refine ⟨L, ?_, ?_⟩
  · rw [← cancel_mono (chartMap hT), Category.assoc, hL, hm, Category.id_comp]
  · rw [← cancel_mono m, Category.assoc, hm, hL, Category.id_comp]

end Triple

/-- The transition maps `t'` of the gluing data. -/
def transition' (i j k : X.affineOpens) :
    pullback (chartMap (inter_le_left i j)) (chartMap (inter_le_left i k)) ⟶
      pullback (chartMap (inter_le_left j k)) (chartMap (inter_le_left j i)) :=
  pullback.lift
    (LocallyRingedSpace.IsOpenImmersion.lift (chartMap (inter_le_left j k))
      (pullback.fst _ _ ≫ chartMap (inter_le_inter_comm i j) ≫ chartMap (inter_le_left j i))
      (range_subset_range_chartMap_inter i j k))
    (pullback.fst _ _ ≫ chartMap (inter_le_inter_comm i j))
    (by rw [LocallyRingedSpace.IsOpenImmersion.lift_fac, Category.assoc])

@[reassoc]
lemma tripleToPullback_transition' (a b c : X.affineOpens) :
    tripleToPullback a b c ≫ transition' a b c =
      chartMap (triple_le_triple a b c) ≫ tripleToPullback b c a := by
  apply pullback.hom_ext
  · rw [← cancel_mono (chartMap (inter_le_left b c))]
    simp only [transition', Category.assoc, pullback.lift_fst_assoc,
      LocallyRingedSpace.IsOpenImmersion.lift_fac, tripleToPullback_fst_assoc,
      tripleToPullback_fst, chartMap_comp]
  · simp only [transition', Category.assoc, pullback.lift_snd, tripleToPullback_fst_assoc,
      tripleToPullback_snd, chartMap_comp]

lemma transition'_cocycle (i j k : X.affineOpens) :
    transition' i j k ≫ transition' j k i ≫ transition' k i j = 𝟙 _ := by
  rw [← cancel_epi (tripleToPullback i j k), Category.comp_id,
    tripleToPullback_transition'_assoc, tripleToPullback_transition'_assoc,
    tripleToPullback_transition', chartMap_comp_assoc, chartMap_comp_assoc, chartMap_eq_id,
    Category.id_comp]

variable (X) in
/-- XII.1.1: the gluing data of the analytic spaces `U^an`, `U` in a family `S` of affine opens of
a separated scheme `X` locally of finite type over `ℂ`, along the `(U ∩ V)^an`. For `S` the set of
all affine opens this gives `X^an` (`analyticSpace`). -/
def glueData (S : Set X.affineOpens) : LocallyRingedSpace.GlueData where
  J := S
  U i := chart X i.1
  V ij := chart X (inter ij.1.1 ij.2.1)
  f i j := chartMap (inter_le_left i.1 j.1)
  f_id i := ⟨chartMap (le_inter (le_refl i.1) (le_refl i.1)),
    by rw [chartMap_comp, chartMap_eq_id], by rw [chartMap_comp, chartMap_eq_id]⟩
  f_open i j := inferInstance
  t i j := chartMap (inter_le_inter_comm i.1 j.1)
  t_id i := chartMap_eq_id _
  t' i j k := transition' i.1 j.1 k.1
  t_fac i j k := pullback.lift_snd _ _ _
  cocycle i j k := transition'_cocycle i.1 j.1 k.1

section Family

variable (S : Set X.affineOpens)

/-- The analytic space glued from the charts `U^an`, `U ∈ S`. -/
def gluedSpace : LocallyRingedSpace.{0} := (glueData X S).toGlueData.glued

/-- The open immersion `U^an → X^an_S`, `U ∈ S`. -/
def gluedι (U : S) : chart X U.1 ⟶ gluedSpace S := (glueData X S).toGlueData.ι U

instance (U : S) : LocallyRingedSpace.IsOpenImmersion (gluedι S U) :=
  (glueData X S).ι_isOpenImmersion U

lemma gluedι_jointly_surjective (x : gluedSpace S) : ∃ (U : S) (y : chart X U.1),
    (gluedι S U).base y = x :=
  (glueData X S).ι_jointly_surjective x

@[reassoc]
lemma gluedι_glue_condition (U V : S) :
    chartMap (inter_le_inter_comm U.1 V.1) ≫ chartMap (inter_le_left V.1 U.1) ≫ gluedι S V =
      chartMap (inter_le_left U.1 V.1) ≫ gluedι S U :=
  (glueData X S).toGlueData.glue_condition U V

lemma chartToScheme_glue_condition (i j : X.affineOpens) :
    chartMap (inter_le_left i j) ≫ chartToScheme i =
      (chartMap (inter_le_inter_comm i j) ≫ chartMap (inter_le_left j i)) ≫ chartToScheme j := by
  rw [Category.assoc, chartMap_chartToScheme, chartMap_chartToScheme, chartMap_chartToScheme]

/-- The canonical morphism `X^an_S → X`. -/
def gluedToScheme : gluedSpace S ⟶ X.toLocallyRingedSpace :=
  Multicoequalizer.desc _ _ (fun U ↦ chartToScheme U.1) fun ⟨i, j⟩ ↦
    chartToScheme_glue_condition i.1 j.1

@[reassoc (attr := simp)]
lemma gluedι_gluedToScheme (U : S) : gluedι S U ≫ gluedToScheme S = chartToScheme U.1 :=
  Multicoequalizer.π_desc (glueData X S).toGlueData.diagram _ _ _ U

lemma isComparison_gluedToScheme : IsComparison (gluedToScheme S) :=
  IsComparison.of_cover (gluedι S) (gluedι_jointly_surjective S) fun U ↦ by
    rw [gluedι_gluedToScheme]
    exact isComparison_chartToScheme U.1

/-- `X^an_S → X` is injective on points. -/
lemma injective_gluedToScheme_base : Function.Injective (gluedToScheme S).base := by
  intro a b hab
  obtain ⟨U, y, rfl⟩ := gluedι_jointly_surjective S a
  obtain ⟨V, z, rfl⟩ := gluedι_jointly_surjective S b
  rw [← comp_base_apply', ← comp_base_apply', gluedι_gluedToScheme,
    gluedι_gluedToScheme] at hab
  have hyV : (chartToScheme U.1).base y ∈ (V.1 : Set X) := hab ▸ chartToScheme_base_mem V.1 z
  have hzU : (chartToScheme V.1).base z ∈ (U.1 : Set X) := hab.symm ▸ chartToScheme_base_mem U.1 y
  obtain ⟨w, rfl⟩ : y ∈ Set.range (chartMap (inter_le_left U.1 V.1)).base := by
    rw [range_chartMap]
    exact ⟨chartToScheme_base_mem U.1 y, hyV⟩
  obtain ⟨w', rfl⟩ : z ∈ Set.range (chartMap (inter_le_left V.1 U.1)).base := by
    rw [range_chartMap]
    exact ⟨chartToScheme_base_mem V.1 z, hzU⟩
  have hw : (chartMap (inter_le_inter_comm U.1 V.1)).base w = w' := by
    apply injective_chartToScheme_base
    rw [← comp_base_apply', chartMap_chartToScheme]
    rw [← comp_base_apply', ← comp_base_apply', chartMap_chartToScheme,
      chartMap_chartToScheme] at hab
    exact hab
  rw [← hw, ← comp_base_apply', ← comp_base_apply', ← comp_base_apply',
    gluedι_glue_condition, comp_base_apply']

/-- For `V ≤ U` in `S`, the chart of `V` factors through that of `U`. -/
@[reassoc (attr := simp)]
lemma chartMap_gluedι {U V : S} (h : V.1 ≤ U.1) : chartMap h ≫ gluedι S U = gluedι S V := by
  have e := gluedι_glue_condition S V U
  have hV : V.1 ≤ inter V.1 U.1 := le_inter (le_refl _) h
  have := congrArg (chartMap hV ≫ ·) e
  simp only [chartMap_comp_assoc, chartMap_eq_id, Category.id_comp] at this
  exact this

end Family

/-! ### The analytic space `X^an` of a separated scheme -/

variable (X) in
/-- XII.1.1: the analytic space `X^an` of a separated scheme `X` locally of finite type over
`ℂ`, glued from the analytic spaces `U^an` of all affine opens `U` of `X` along the
`(U ∩ V)^an`. Its structure sheaf is not reduced in general.

Deviations from XII.1.1: `X` is assumed separated, and SGA's defining universal property
(representability of `Y ↦ Hom_ℂ(Y, X)` on analytic spaces) is not proved for this object; what is
proved is that it is an analytic space (`isAnalyticSpace_analyticSpace`) with a canonical
comparison morphism `φ = toScheme X` (`isComparison_toScheme`, `range_toScheme_base`). -/
def analyticSpace : LocallyRingedSpace.{0} := gluedSpace (Set.univ : Set X.affineOpens)

/-- The open immersion `U^an → X^an` of the chart of an affine open `U`. -/
def ι (U : X.affineOpens) : chart X U ⟶ analyticSpace X :=
  gluedι (Set.univ : Set X.affineOpens) ⟨U, Set.mem_univ U⟩

instance (U : X.affineOpens) : LocallyRingedSpace.IsOpenImmersion (ι U) :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (gluedι _ _))

lemma ι_jointly_surjective (x : analyticSpace X) : ∃ (U : X.affineOpens) (y : chart X U),
    (ι U).base y = x := by
  obtain ⟨U, y, rfl⟩ := gluedι_jointly_surjective _ x
  exact ⟨U.1, y, rfl⟩

variable (X) in
/-- XII.1.1: the canonical morphism `φ : X^an → X`. -/
def toScheme : analyticSpace X ⟶ X.toLocallyRingedSpace :=
  gluedToScheme (Set.univ : Set X.affineOpens)

@[reassoc (attr := simp)]
lemma ι_toScheme (U : X.affineOpens) : ι U ≫ toScheme X = chartToScheme U :=
  gluedι_gluedToScheme (Set.univ : Set X.affineOpens) ⟨U, Set.mem_univ U⟩

/-- XII.2.1: `φ : X^an → X` is a comparison morphism: its stalk maps are flat local
homomorphisms of noetherian local rings with `𝔪_{φ(x)} 𝒪_{X^an,x} = 𝔪_x` and trivial residue
field extension. -/
theorem isComparison_toScheme : IsComparison (toScheme X) :=
  isComparison_gluedToScheme _

/-- XII.1.1: `φ : X^an → X` is injective on points. -/
theorem injective_toScheme_base : Function.Injective (toScheme X).base :=
  injective_gluedToScheme_base _

omit [IsSeparated (X ↘ Spec (CommRingCat.of ℂ))] in
lemma range_chartToScheme_base_subset (U : X.affineOpens) :
    Set.range (chartToScheme U).base ⊆ closedPoints X := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of ℂ))
  rintro _ ⟨y, rfl⟩
  have hy : (affineToSpec ℂ Γ(X, U)).base y ∈ closedPoints (Spec Γ(X, U)) := by
    have := range_affineToSpec_base (A := Γ(X, U))
    exact this ▸ Set.mem_range_self y
  exact (isAffineOpen U).fromSpec.closePoints_subset_preimage_closedPoints hy

omit [IsSeparated (X ↘ Spec (CommRingCat.of ℂ))] in
lemma closedPoints_inter_subset_range_chartToScheme_base (U : X.affineOpens) :
    closedPoints X ∩ (U : Set X) ⊆ Set.range (chartToScheme U).base := by
  rintro x ⟨hx, hxU⟩
  rw [← (isAffineOpen U).range_fromSpec] at hxU
  obtain ⟨P, rfl⟩ := hxU
  have hP : P ∈ closedPoints (Spec Γ(X, U)) :=
    preimage_closedPoints_subset (isAffineOpen U).fromSpec.isOpenEmbedding.injective
      (isAffineOpen U).fromSpec.continuous hx
  have := range_affineToSpec_base (A := Γ(X, U))
  have hP' : P ∈ closedPoints (PrimeSpectrum Γ(X, U)) := hP
  rw [← this] at hP'
  obtain ⟨y, rfl⟩ := hP'
  exact ⟨y, rfl⟩

@[reassoc (attr := simp)]
lemma chartMap_ι {U V : X.affineOpens} (h : V ≤ U) : chartMap h ≫ ι U = ι V :=
  chartMap_gluedι (Set.univ : Set X.affineOpens) (U := ⟨U, Set.mem_univ U⟩)
    (V := ⟨V, Set.mem_univ V⟩) h

/-! ### Independence of the family of charts -/

section Basis

variable (S : Set X.affineOpens)

/-- The comparison morphism `X^an_S → X^an`. -/
def gluedToAnalytic : gluedSpace S ⟶ analyticSpace X :=
  Multicoequalizer.desc _ _ (fun U ↦ ι U.1) fun ⟨i, j⟩ ↦
    ((glueData X (Set.univ : Set X.affineOpens)).toGlueData.glue_condition
      ⟨i.1, Set.mem_univ _⟩ ⟨j.1, Set.mem_univ _⟩).symm

@[reassoc (attr := simp)]
lemma gluedι_gluedToAnalytic (U : S) : gluedι S U ≫ gluedToAnalytic S = ι U.1 :=
  Multicoequalizer.π_desc (glueData X S).toGlueData.diagram _ _ _ U

lemma gluedι_gluedToAnalytic_toScheme (U : S) :
    gluedι S U ≫ gluedToAnalytic S ≫ toScheme X = gluedι S U ≫ gluedToScheme S := by
  rw [gluedι_gluedToAnalytic_assoc, ι_toScheme, gluedι_gluedToScheme]

@[reassoc (attr := simp)]
lemma gluedToAnalytic_toScheme : gluedToAnalytic S ≫ toScheme X = gluedToScheme S :=
  Multicoequalizer.hom_ext _ _ _ fun U ↦ gluedι_gluedToAnalytic_toScheme S U

/-- If every point of every affine open `U` lies in a member of `S` contained in `U`, the
analytic space glued from the charts in `S` is `X^an`. -/
theorem isIso_gluedToAnalytic
    (hS : ∀ (U : X.affineOpens) (x : X), x ∈ (U : X.Opens) →
      ∃ W ∈ S, W ≤ U ∧ x ∈ (W : X.Opens)) :
    IsIso (gluedToAnalytic S) := by
  have hinj : Function.Injective (gluedToAnalytic S).base := by
    intro a b hab
    apply injective_gluedToScheme_base S
    rw [← gluedToAnalytic_toScheme, comp_base_apply', comp_base_apply', hab]
  have hsurj : Function.Surjective (gluedToAnalytic S).base := by
    intro x
    obtain ⟨U, y, rfl⟩ := ι_jointly_surjective x
    obtain ⟨W, hWS, hWU, hW⟩ := hS U _ (chartToScheme_base_mem U y)
    have : y ∈ Set.range (chartMap hWU).base := by
      rw [range_chartMap]
      exact hW
    obtain ⟨w, rfl⟩ := this
    refine ⟨(gluedι S ⟨W, hWS⟩).base w, ?_⟩
    rw [← comp_base_apply', ← comp_base_apply', gluedι_gluedToAnalytic, chartMap_ι]
  have hstalk (x : gluedSpace S) : IsIso ((gluedToAnalytic S).stalkMap x) := by
    obtain ⟨U, y, rfl⟩ := gluedι_jointly_surjective S x
    have : LocallyRingedSpace.IsOpenImmersion (gluedι S U ≫ gluedToAnalytic S) := by
      rw [gluedι_gluedToAnalytic]
      infer_instance
    have : IsIso ((gluedι S U ≫ gluedToAnalytic S).stalkMap y) := inferInstance
    rw [LocallyRingedSpace.stalkMap_comp] at this
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance this
  have hopen : IsOpenEmbedding (gluedToAnalytic S).base := by
    refine .of_continuous_injective_isOpenMap (gluedToAnalytic S).base.hom.continuous hinj
      (isOpenMap_iff_nhds_le.mpr fun x ↦ ?_)
    obtain ⟨U, y, rfl⟩ := gluedι_jointly_surjective S x
    have o₁ : IsOpenEmbedding (gluedι S U).base :=
      (inferInstance : LocallyRingedSpace.IsOpenImmersion (gluedι S U)).base_open
    have o₂ : IsOpenEmbedding (ι U.1).base :=
      (inferInstance : LocallyRingedSpace.IsOpenImmersion (ι U.1)).base_open
    have e₁ := o₁.map_nhds_eq y
    have e₂ := o₂.map_nhds_eq y
    rw [← gluedι_gluedToAnalytic S U] at e₂
    have e₂' : Filter.map ((gluedToAnalytic S).base ∘ (gluedι S U).base) (𝓝 y) =
        𝓝 ((gluedToAnalytic S).base ((gluedι S U).base y)) := e₂
    rw [← e₁, Filter.map_map, e₂']
  have := LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _ hopen
  have : Epi (gluedToAnalytic S).base := by
    rw [TopCat.epi_iff_surjective]
    exact hsurj
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

end Basis

/-- XII.1.1: the image of `φ : X^an → X` is the set of closed points of `X`. -/
theorem range_toScheme_base : Set.range (toScheme X).base = closedPoints X := by
  apply subset_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨U, y, rfl⟩ := ι_jointly_surjective x
    rw [← comp_base_apply', ι_toScheme]
    exact range_chartToScheme_base_subset U ⟨y, rfl⟩
  · intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    obtain ⟨y, rfl⟩ := closedPoints_inter_subset_range_chartToScheme_base ⟨U, hU⟩ ⟨hx, hxU⟩
    exact ⟨(ι ⟨U, hU⟩).base y, by rw [← comp_base_apply', ι_toScheme]⟩

/-- XII.1.1: `X^an` is an analytic space: every point has an open neighbourhood isomorphic to a
local model (the chart of an affine open). -/
theorem isAnalyticSpace_analyticSpace : IsAnalyticSpace ℂ (analyticSpace X) := by
  intro x
  obtain ⟨U, y, rfl⟩ := ι_jointly_surjective x
  have ho : IsOpenEmbedding (ι U).base :=
    (inferInstance : LocallyRingedSpace.IsOpenImmersion (ι U)).base_open
  let W : TopologicalSpace.Opens (analyticSpace X) := ⟨Set.range (ι U).base, ho.isOpen_range⟩
  have hW : Set.range ((analyticSpace X).ofRestrict W.isOpenEmbedding).base =
      Set.range (ι U).base := by
    change Set.range (Subtype.val : W → analyticSpace X) = _
    rw [Subtype.range_coe]
    rfl
  refine ⟨W, ⟨y, rfl⟩, presentationVars ℂ Γ(X, U), polynomialModel (presentationPolys ℂ Γ(X, U)),
    ⟨LocallyRingedSpace.isoOfRangeEq ((analyticSpace X).ofRestrict W.isOpenEmbedding) (ι U) hW⟩⟩

end AnalyticGluing

end SGA.SGA1.ExposeXII
