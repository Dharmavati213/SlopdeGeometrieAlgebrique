/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannCurves
import SGA.SGA1.ExposeXII.RiemannReductionProduct
import SGA.SGA1.ExposeXII.RiemannHigherDescentAffine
import SGA.SGA1.ExposeXII.RiemannSimplyConnected
import SGA.Foundations.CommAlg.NoetherFiniteness
import SGA.Foundations.Dimension.Integral
import SGA.SGA1.ExposeXII.StatementCorollaries
import SGA.SGA1.ExposeXII.RiemannLocalChart

/-!
# SGA 1, Exposé XII, 5.1 for affine curves

`curveRiemannExistence : CurveRiemannExistenceStatement`: for `A` of finite type over `ℂ` of
Krull dimension at most `1`, the functor `Ψ : S ↦ S(ℂ)` from finite étale `A`-algebras to finite
coverings of `X(ℂ)`, `X = Spec A`, is an equivalence of categories. This is XII.5.1 for affine
curves (singular, reducible, non-reduced allowed), proved by this project's route:

1. normal curves: `isEquivalence_pointsFunctor_of_isIntegrallyClosed`
   (`SGA.SGA1.ExposeXII.RiemannExtension`: Noether normalization onto `ℂ ∖ S` over a dense open,
   XII.5.1 for `ℂ ∖ S` through compact Riemann surfaces, extension across finitely many points);
   normal domains of dimension `0` are `ℂ`, with `X(ℂ)` a point
   (`isEquivalence_pointsFunctor_of_isIntegrallyClosed_of_le_one`);
2. the normalization `A → ∏_p B_p` (`RiemannNormalization.normalizationPi`), `p` running over the
   minimal primes of `A` and `B_p` the integral closure of `A/p` in its fraction field, is finite
   (E. Noether, x29's `Algebra.FiniteType.finite_integralClosure`) and surjective on spectra
   (`RiemannNormalization.comap_surjective_normalization`); XII.5.1 holds for the product
   (`isEquivalence_pointsFunctor_pi`);
3. descent along it (XII.5.1, proof of 2) a)): ret-hd's scheme form
   `RiemannHigher.mem_essImage_schemePointsFunctor_of_isFinite`, here for a finite map surjective
   on spectra rather than injective (`mem_essImage_of_finite_of_comap_surjective`), which also
   covers the nilradical.

Corollaries: the scheme form for curves (`schemeCurveRiemannExistence`, `X` locally of finite type
over `ℂ` with `topologicalKrullDim X ≤ 1`, by gluing over affine opens), XII.5.2 for affine curves
(`curveFundamentalGroupComparison`: `π₁^et` is the profinite completion of `π₁(X(ℂ))`) and the
dimension-`≤ 1` case of ret-hd's `DivisorExtensionStatement` (`curveDivisorExtension`). The
reduction to normal domains, `isEquivalence_pointsFunctor_of_forall_normalization`, holds in every
dimension (ret-hd's step 5).

SGA's own proof of XII.5.1 goes through normalization (2) a)), the regular locus (2) b)) and, for
affine regular `X`, compactification, resolution of singularities and GAGA (2) c)); only the
first step is shared with the route here.
-/

noncomputable section

open CategoryTheory Topology Set Module AlgebraicGeometry CommAlgCat Opposite

namespace SGA.SGA1.ExposeXII

open RiemannHigher

attribute [local instance] SchemePoints.specOver locallyOfFiniteType_specOver in
/-- XII.5.1, proof of 2) a), descent along a finite map surjective on spectra: for a finite
`φ : A → B` of `ℂ`-algebras of finite type with `Spec B → Spec A` surjective (e.g. the
normalization of a non-reduced `A`) and a finite covering `E` of `A(ℂ)` whose pullback to
`B(ℂ)` comes from a finite étale `B`-algebra, `E` comes from a finite étale `A`-algebra. This is
ret-hd's `mem_essImage_schemePointsFunctor_of_isFinite` for `Spec B → Spec A`, as in their
`riemannExistenceFiniteDescent` (which asks `φ` injective instead). -/
theorem mem_essImage_of_finite_of_comap_surjective {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra.FiniteType ℂ A] [Algebra.FiniteType ℂ B]
    (φ : A →ₐ[ℂ] B) (hfin : φ.toRingHom.Finite)
    (hsurj : Function.Surjective (PrimeSpectrum.comap φ.toRingHom))
    (E : TopCat.FiniteCovering (TopCat.of (Points ℂ A)))
    (h : (pointsFunctor ℂ B).essImage ((TopCat.FiniteCovering.baseChange (pointsHom φ)).obj E)) :
    (pointsFunctor ℂ A).essImage E := by
  rw [mem_essImage_pointsFunctor_iff] at h ⊢
  have : IsFinite (specMap φ) := (IsFinite.SpecMap_iff _).mpr hfin
  have : Surjective (specMap φ) := ⟨(hsurj :)⟩
  refine mem_essImage_schemePointsFunctor_of_isFinite (specMap φ) _ ?_
  obtain ⟨Y, ⟨j⟩⟩ := h
  exact ⟨Y, ⟨j ≪≫ baseChangeSpecIso φ E⟩⟩

/-- XII.5.1 for normal affine curves, including dimension `0`: for `B` a normal domain of finite
type over `ℂ` with `ringKrullDim B ≤ 1`, `Ψ` is an equivalence. In dimension `0`, `B` is a field
and `X(ℂ)` is a point (`isEquivalence_pointsFunctor_of_simplyConnectedSpace`); in dimension `1`
this is `isEquivalence_pointsFunctor_of_isIntegrallyClosed`. -/
theorem isEquivalence_pointsFunctor_of_isIntegrallyClosed_of_le_one (B : Type) [CommRing B]
    [IsDomain B] [IsIntegrallyClosed B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (hdim : ringKrullDim B ≤ 1) : (pointsFunctor ℂ B).IsEquivalence := by
  rcases eq_or_ne (ringKrullDim B) 1 with h1 | h1
  · exact isEquivalence_pointsFunctor_of_isIntegrallyClosed B h1
  -- dimension `0`: `B` is a field and `X(ℂ)` is a point
  have h0 : ringKrullDim B ≤ 0 := by
    rcases h : ringKrullDim B with _ | n
    · exact bot_le
    · rw [h] at hdim h1
      change ((n : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞) at hdim
      change ((n : ℕ∞) : WithBot ℕ∞) ≠ ((1 : ℕ∞) : WithBot ℕ∞) at h1
      have hn : n < 1 := lt_of_le_of_ne (WithBot.coe_le_coe.mp hdim)
        fun h' ↦ h1 (congrArg _ h')
      rw [Order.lt_one_iff.mp hn]
      rfl
  have : Ring.KrullDimLE 0 B := Ring.krullDimLE_iff.mpr h0
  let := (Ring.KrullDimLE.isField_of_isDomain (R := B)).toField
  have : Subsingleton (Points ℂ B) := ⟨fun φ ψ ↦ Points.eq_of_ker_eq (by
    rw [(Ideal.eq_bot_or_top (Points.ker φ)).resolve_right (Ideal.IsMaximal.ne_top inferInstance),
      (Ideal.eq_bot_or_top (Points.ker ψ)).resolve_right (Ideal.IsMaximal.ne_top inferInstance)])⟩
  have : Nonempty (Points ℂ B) := (Points.nonempty_iff_nontrivial ℂ B).mpr inferInstance
  exact isEquivalence_pointsFunctor_of_simplyConnectedSpace B

namespace RiemannNormalization

variable (A : Type) [CommRing A] [Algebra ℂ A]

/-- The normalization of `A/p`: the integral closure of `A/p` in its fraction field. -/
abbrev normalization (p : Ideal A) : Type := integralClosure (A ⧸ p) (FractionRing (A ⧸ p))

/-- The normalization of `A`: the product of the normalizations of the `A/p`, `p` running over the
minimal primes of `A`. -/
abbrev normalizationPi : Type := ∀ p : minimalPrimes A, normalization A p.1

variable {A} [Algebra.FiniteType ℂ A]

section Prime

variable (p : Ideal A) [p.IsPrime]

instance : Algebra.FiniteType ℂ (normalization A p) := by
  have : Module.Finite (A ⧸ p) (normalization A p) :=
    Algebra.FiniteType.finite_integralClosure ℂ (A ⧸ p) (FractionRing (A ⧸ p))
      (FractionRing (A ⧸ p))
  exact .trans (S := A ⧸ p) inferInstance inferInstance

instance : IsIntegrallyClosed (normalization A p) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (A ⧸ p))

instance : Module.Finite A (normalization A p) := by
  have : Module.Finite (A ⧸ p) (normalization A p) :=
    Algebra.FiniteType.finite_integralClosure ℂ (A ⧸ p) (FractionRing (A ⧸ p))
      (FractionRing (A ⧸ p))
  exact Module.Finite.trans (A ⧸ p) _

omit [Algebra ℂ A] [Algebra.FiniteType ℂ A] [p.IsPrime] in
lemma ringKrullDim_normalization_le : ringKrullDim (normalization A p) ≤ ringKrullDim A :=
  (ringKrullDim_le_of_isIntegral (R := A ⧸ p)).trans (ringKrullDim_quotient_le p)

/-- XII.5.1 for the normalization of `A/p`, `A` of dimension at most `1`. -/
lemma isEquivalence_pointsFunctor_normalization (hdim : ringKrullDim A ≤ 1) :
    (pointsFunctor ℂ (normalization A p)).IsEquivalence :=
  isEquivalence_pointsFunctor_of_isIntegrallyClosed_of_le_one _
    ((ringKrullDim_normalization_le p).trans hdim)

end Prime

instance (p : minimalPrimes A) : p.1.IsPrime := p.2.1.1

instance : Finite (minimalPrimes A) :=
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  (minimalPrimes.finite_of_isNoetherianRing A).to_subtype

instance : Algebra.FiniteType ℂ (normalizationPi A) :=
  have (p : minimalPrimes A) : Algebra.FinitePresentation ℂ (normalization A p.1) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  inferInstance

omit [Algebra ℂ A] [Algebra.FiniteType ℂ A] in
/-- `Spec` of the normalization maps onto `Spec A`: every prime of `A` contains a minimal prime
`p`, and lifts to the normalization of `A/p` (going up). -/
theorem comap_surjective_normalization :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (normalizationPi A))) := by
  intro P
  obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le (show ⊥ ≤ P.asIdeal from bot_le)
  let p' : minimalPrimes A := ⟨p, hp⟩
  have : p.IsPrime := p'.2.1.1
  let P' : Ideal (A ⧸ p) := P.asIdeal.map (Ideal.Quotient.mk p)
  have hker : RingHom.ker (Ideal.Quotient.mk p) ≤ P.asIdeal := by
    rw [Ideal.mk_ker]
    exact hpP
  have : P'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hinj : Function.Injective (algebraMap (A ⧸ p) (normalization A p)) := fun x y hxy ↦
    IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p)) (congrArg Subtype.val hxy)
  obtain ⟨Q, -, hQ, hQP⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := normalization A p) P' ⊥ (by
      rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le)
  refine ⟨⟨Q.comap (Pi.evalRingHom (fun p : minimalPrimes A ↦ normalization A p.1) p'),
    by have := hQ; infer_instance⟩, ?_⟩
  ext a
  change algebraMap A (normalizationPi A) a p' ∈ Q ↔ a ∈ P.asIdeal
  have h1 : algebraMap A (normalizationPi A) a p' =
      algebraMap (A ⧸ p) (normalization A p) (Ideal.Quotient.mk p a) := rfl
  rw [h1, ← Ideal.mem_comap, hQP, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · rintro ⟨b, hb, hba⟩
    rw [Ideal.Quotient.eq] at hba
    have := P.asIdeal.sub_mem hb (hpP hba)
    rwa [sub_sub_cancel] at this
  · exact fun ha ↦ ⟨a, ha, rfl⟩

end RiemannNormalization

open RiemannNormalization in
/-- **Reduction of XII.5.1 to normal domains** (XII.5.1, proof of 2) a), in every dimension): for
`A` of finite type over `ℂ`, if `Ψ` is an equivalence for the normalization of `A/p` for every
minimal prime `p` of `A`, then it is an equivalence for `A`. Descent
(`mem_essImage_of_finite_of_comap_surjective`) along the finite map `A → ∏_p normalization A p`,
surjective on spectra (`comap_surjective_normalization`), for which XII.5.1 holds
(`isEquivalence_pointsFunctor_pi`). -/
theorem isEquivalence_pointsFunctor_of_forall_normalization (A : Type) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A]
    (h : ∀ p : minimalPrimes A, (pointsFunctor ℂ (normalization A p.1)).IsEquivalence) :
    (pointsFunctor ℂ A).IsEquivalence := by
  have hR := isEquivalence_pointsFunctor_pi (fun p : minimalPrimes A ↦ normalization A p.1) h
  let φ : A →ₐ[ℂ] normalizationPi A := IsScalarTower.toAlgHom ℂ A (normalizationPi A)
  have hfin : φ.toRingHom.Finite := RingHom.finite_algebraMap.mpr inferInstance
  exact { essSurj := ⟨fun E ↦ mem_essImage_of_finite_of_comap_surjective φ hfin
    comap_surjective_normalization E (Functor.EssSurj.mem_essImage _ _)⟩ }

open RiemannNormalization in
/-- **XII.5.1 for affine curves** (`CurveRiemannExistenceStatement`; this project's route): for `A`
of finite type over `ℂ` with `ringKrullDim A ≤ 1`, the functor `Ψ : S ↦ S(ℂ)` from finite étale
`A`-algebras to finite coverings of `X(ℂ)`, `X = Spec A`, is an equivalence of categories. Proof:
`isEquivalence_pointsFunctor_of_forall_normalization`, the normalizations being normal domains of
dimension `≤ 1` (`isEquivalence_pointsFunctor_normalization`). -/
theorem curveRiemannExistence : CurveRiemannExistenceStatement := fun A _ _ _ hdim ↦
  isEquivalence_pointsFunctor_of_forall_normalization A fun p ↦
    isEquivalence_pointsFunctor_normalization p.1 hdim

/-- XII.5.2 for affine curves: for `A` of finite type over `ℂ` with `ringKrullDim A ≤ 1` and
`Spec A` connected, the étale fundamental group of `X = Spec A` at `x ∈ X(ℂ)` (the automorphism
group of the fibre functor at `x`) is the profinite completion of `π₁(X(ℂ), x)`. From
`curveRiemannExistence`, XII.2.4 (`Points.connectedComparison`) and the topological input
`coveringFundamentalGroupStatement`, as in `fundamentalGroupComparison`. -/
theorem curveFundamentalGroupComparison (A : Type) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (hdim : ringKrullDim A ≤ 1) (hA : ConnectedSpace (PrimeSpectrum A))
    (x : Points ℂ A) :
    Nonempty (Aut (etaleFiber ℂ A x) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (FundamentalGroup (Points ℂ A) x))) := by
  have := curveRiemannExistence A hdim
  obtain ⟨e⟩ := coveringFundamentalGroupStatement A (Points.connectedComparison A hA) x
  exact ⟨(autContinuousMulEquiv (pointsFunctor ℂ A)
    (pointsFunctorCompFiberIso ℂ A x)).symm.trans e⟩

/-- The ring of sections of an affine open of a scheme of dimension `≤ 1` has dimension `≤ 1`. -/
lemma ringKrullDim_sections_le {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(X, U) ≤ topologicalKrullDim X := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
  change topologicalKrullDim (Spec Γ(X, U)) ≤ _
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
  exact topologicalKrullDim_subspace_le X U

/-- **XII.5.1 for curves, scheme form**: for `X` locally of finite type over `ℂ` with
`topologicalKrullDim X ≤ 1` (`X : Scheme.{0}`), the functor `Ψ` from finite étale coverings of `X`
to finite coverings of `X(ℂ)` is an equivalence. From the affine form `curveRiemannExistence` by
gluing over the affine opens (`RiemannLocal.isEquivalence_schemePointsFunctor_of_essSurj`). -/
theorem schemeCurveRiemannExistence (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (hdim : topologicalKrullDim X ≤ 1) :
    (schemePointsFunctor ℂ X).IsEquivalence := by
  refine RiemannLocal.isEquivalence_schemePointsFunctor_of_essSurj fun U ↦ ?_
  let := SchemePoints.sectionsAlgebra (K := ℂ) U.1
  have := SchemePoints.finiteType_sections (K := ℂ) U.2
  have := curveRiemannExistence Γ(X, U.1) ((ringKrullDim_sections_le U.2).trans hdim)
  infer_instance

/-- The dimension `≤ 1` part of the extension of XII.5.1 across divisors (ret-hd's
`CurveDivisorExtensionStatement`), from `curveRiemannExistence` through ret-hd's
`curveDivisorExtension_of_curveRiemannExistence`. -/
theorem curveDivisorExtension : CurveDivisorExtensionStatement :=
  curveDivisorExtension_of_curveRiemannExistence curveRiemannExistence

end SGA.SGA1.ExposeXII
