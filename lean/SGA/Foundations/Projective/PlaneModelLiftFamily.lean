/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Projective.PlaneModelFamily
import SGA.Foundations.Projective.PlaneModelLift
import SGA.Foundations.Projective.BertiniConnected
import SGA.Foundations.Fields.GeometricallyReduced
import SGA.Foundations.Cohomology.GeometricConnectedness
import SGA.Foundations.Cohomology.SteinFactorization
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Lifting a hypersurface over a complete discrete valuation ring

Let `R` be a discrete valuation ring with uniformizer `π`, complete for the `π`-adic topology,
with residue field `k` (through `φ : R → k`), and let `G ∈ R[xᵢ : i ∈ σ]` be homogeneous such that
its reduction `F = φ(G)` is a prime element of `k[xᵢ]` of the same total degree. This is the
situation of a lift of a projective plane curve `V₊(F)` to the Witt vectors. Then the family
`f : V₊(G) ⟶ Spec R` (`ProjHypersurface.toSpec`):

* is integral, flat and proper, with `V₊(G)` closed in `ℙ(σ; Spec R)` (`PlaneModelFamily`);
* has special fibre `V₊(F)` (`ProjHypersurface.isPullback_baseChange`);
* is geometrically reduced when `R` has characteristic `0` and `k` is perfect
  (`ProjHypersurface.geometricallyReduced_toSpec`);
* satisfies `Γ(V₊(G), 𝒪) = R` when `k` is algebraically closed and `σ` finite
  (`ProjHypersurface.bijective_appTop`), hence is geometrically connected by Zariski's
  connectedness theorem (`ProjHypersurface.geometricallyConnected_toSpec`).

The equality `Γ(V₊(G), 𝒪) = R` uses no cohomology: a global section is integral over `R`; on the
chart `D₊(xᵢ)` its restriction lies in a noetherian domain `B` with `B ⧸ π B` a domain (the chart
of `V₊(F)`), and an element of such a `B` integral over the complete ring `R` with algebraically
closed residue field lies in `R` (`IsAdicComplete.mem_range_algebraMap_of_aeval_eq_zero`).

## References

* [EGA III₁, 4.3.12] (connectedness of the fibres of a proper flat family)
* [EGA IV₂, 4.6.1] (reduced schemes over perfect fields)
-/

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization AlgebraicGeometry
  ProjectiveSpace TensorProduct

noncomputable section

namespace AlgebraicGeometry.ProjHypersurface

section Algebra

variable {σ R k : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [UniqueFactorizationMonoid R] [Field k] (φ : R →+* k)
  (hker : RingHom.ker φ = IsLocalRing.maximalIdeal R)
  {G : MvPolynomial σ R} {d : ℕ} (hG : G.IsHomogeneous d)
  (hF : Prime (map φ G)) (hdeg : (map φ G).totalDegree = G.totalDegree)

omit [IsDomain R] [IsLocalRing R] [UniqueFactorizationMonoid R] in
include hF hdeg in
/-- The lift `G` has positive total degree. -/
lemma totalDegree_pos : 0 < G.totalDegree := by
  rw [← hdeg, Nat.pos_iff_ne_zero]
  intro h
  have hc := totalDegree_eq_zero_iff_eq_C.mp h
  set c := coeff 0 (map φ G)
  have hc0 : c ≠ 0 := by intro h0; rw [h0, C_0] at hc; exact hF.ne_zero hc
  exact hF.not_isUnit (hc ▸ (Ne.isUnit hc0).map C)

omit [IsLocalRing R] [UniqueFactorizationMonoid R] in
include hF hdeg in
/-- No nonzero constant is divisible by `G`. -/
lemma not_dvd_C {r : R} (hr : r ≠ 0) : ¬ G ∣ C r := by
  rintro ⟨h, hh⟩
  have hG0 : G ≠ 0 := by rintro rfl; rw [zero_mul, C_eq_zero] at hh; exact hr hh
  have hh0 : h ≠ 0 := by rintro rfl; rw [mul_zero, C_eq_zero] at hh; exact hr hh
  have := congrArg totalDegree hh
  rw [totalDegree_C, totalDegree_mul_of_isDomain hG0 hh0] at this
  have := totalDegree_pos φ hF hdeg
  omega

include hker hF hdeg in
/-- `R[xᵢ] ⧸ (G)` is a domain. -/
theorem isDomain_quotient : IsDomain (MvPolynomial σ R ⧸ (ideal G hG).toIdeal) := by
  have hp := prime_of_prime_map φ hker hF hdeg
  rw [toIdeal_ideal, Ideal.Quotient.isDomain_iff_prime]
  exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp

omit [IsLocalRing R] [UniqueFactorizationMonoid R] in
include hF hdeg in
/-- `R → R[xᵢ] ⧸ (G)` is injective. -/
theorem injective_algebraMap :
    Function.Injective (algebraMap R (MvPolynomial σ R ⧸ (ideal G hG).toIdeal)) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  rw [IsScalarTower.algebraMap_apply R (MvPolynomial σ R), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem, toIdeal_ideal, Ideal.mem_span_singleton] at hr
  exact not_dvd_C φ hF hdeg hr0 hr

omit [IsDomain R] [IsLocalRing R] [UniqueFactorizationMonoid R] in
/-- The class of `xᵢ` in `R[xᵢ] ⧸ (G)` is nonzero if `xᵢ` is not divisible by the reduction of
`G`. -/
lemma mk_X_ne_zero {i : σ} (hX : X i ∉ Ideal.span {map φ G}) :
    Ideal.Quotient.mk (ideal G hG).toIdeal (X i) ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem, toIdeal_ideal, Ideal.mem_span_singleton]
  rintro ⟨h, hh⟩
  refine hX (Ideal.mem_span_singleton.mpr ⟨map φ h, ?_⟩)
  rw [← map_mul, ← hh, map_X]

end Algebra

section Reduced

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {σ : Type u}

/-- If `F'` generates a prime ideal of `L[xᵢ]`, `L` a perfect field, then `K[xᵢ] ⧸ (F')` is
reduced for every field `K ⊇ L` (EGA IV 4.6.1). -/
lemma isReduced_quotient_map_of_isPrime {L K : Type u} [Field L] [PerfectField L] [Field K]
    [Algebra L K] {F' : MvPolynomial σ L} {d : ℕ} (hF' : F'.IsHomogeneous d)
    (hp : (Ideal.span {F'}).IsPrime) :
    _root_.IsReduced (MvPolynomial σ K ⧸ Ideal.span {map (algebraMap L K) F'}) := by
  have : IsDomain (MvPolynomial σ L ⧸ (ideal F' hF').toIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hp
  have : Algebra.IsGeometricallyReduced L (MvPolynomial σ L ⧸ (ideal F' hF').toIdeal) :=
    .of_perfectField L _
  have : _root_.IsReduced (K ⊗[L] (MvPolynomial σ L ⧸ (ideal F' hF').toIdeal)) :=
    Algebra.IsGeometricallyReduced.isReduced_tensorProduct K
  exact isReduced_of_injective (baseChangeEquiv K F' hF').symm.toRingHom
    (baseChangeEquiv K F' hF').symm.injective

variable {R k : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field k]
  (φ : R →+* k) (hφ : Function.Surjective φ)
  (hker : RingHom.ker φ = IsLocalRing.maximalIdeal R)
  {G : MvPolynomial σ R} {d : ℕ} (hG : G.IsHomogeneous d)
  (hF : Prime (map φ G)) (hdeg : (map φ G).totalDegree = G.totalDegree)

include hφ hker hG hF hdeg in
/-- **The fibres of the lift are geometrically reduced**: for every field `K` over `R`,
`K[xᵢ] ⧸ (G)` is reduced (`R` of characteristic `0`, `k` perfect). Over the generic point,
`G` stays prime in `Frac(R)[xᵢ]`; over the closed point, `G` becomes the prime `F`. -/
theorem isReduced_quotient_map [CharZero R] [PerfectField k] (K : Type u) [Field K]
    [Algebra R K] :
    _root_.IsReduced (MvPolynomial σ K ⧸ Ideal.span {map (algebraMap R K) G}) := by
  have hp : (RingHom.ker (algebraMap R K)).IsPrime := RingHom.ker_isPrime _
  by_cases h0 : RingHom.ker (algebraMap R K) = ⊥
  · -- a point of characteristic `0`
    have hinj : Function.Injective (algebraMap R K) := (RingHom.injective_iff_ker_eq_bot _).mpr h0
    let K₀ := FractionRing R
    let _ : Algebra K₀ K := (IsFractionRing.lift hinj).toAlgebra
    have htower : IsScalarTower R K₀ K :=
      IsScalarTower.of_algebraMap_eq fun r ↦ (IsFractionRing.lift_algebraMap hinj r).symm
    have : CharZero K₀ := charZero_of_injective_algebraMap (IsFractionRing.injective R K₀)
    have hp₀ : (Ideal.span {map (algebraMap R K₀) G}).IsPrime := by
      have hprime : (Ideal.span {G}).IsPrime :=
        (Ideal.span_singleton_prime (prime_of_prime_map φ hker hF hdeg).ne_zero).mpr
          (prime_of_prime_map φ hker hF hdeg)
      have := IsLocalization.isPrime_of_isPrime_disjoint
        ((nonZeroDivisors R).map (C (σ := σ))) (MvPolynomial σ K₀) (Ideal.span {G}) hprime (by
          rw [Set.disjoint_left]
          rintro _ ⟨r, hr, rfl⟩ hmem
          exact not_dvd_C φ hF hdeg (nonZeroDivisors.ne_zero hr)
            (Ideal.mem_span_singleton.mp hmem))
      rwa [Ideal.map_span, Set.image_singleton, algebraMap_def] at this
    have := isReduced_quotient_map_of_isPrime (L := K₀) (K := K) (isHomogeneous_map _ hG) hp₀
    rwa [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  · -- the closed point
    have hmax : RingHom.ker (algebraMap R K) = RingHom.ker φ := by
      rw [hker]
      exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal h0)
    let φ' : k →+* K := (Ideal.Quotient.lift (RingHom.ker φ) (algebraMap R K)
      (fun r hr ↦ by rwa [← hmax, RingHom.mem_ker] at hr)).comp
        (RingHom.quotientKerEquivOfSurjective hφ).symm.toRingHom
    have hφ' : ∀ r, φ' (φ r) = algebraMap R K r := fun r ↦ by
      simp [φ', RingHom.quotientKerEquivOfSurjective_symm_apply]
    let _ : Algebra k K := φ'.toAlgebra
    have hp' : (Ideal.span {map φ G}).IsPrime := (Ideal.span_singleton_prime hF.ne_zero).mpr hF
    have := isReduced_quotient_map_of_isPrime (L := k) (K := K) (isHomogeneous_map φ hG) hp'
    rwa [MvPolynomial.map_map,
      show (algebraMap k K).comp φ = algebraMap R K from RingHom.ext hφ'] at this

include hφ hker hF hdeg in
/-- **The lift is geometrically reduced over `R`** (`R` of characteristic `0`, `k` perfect). -/
theorem geometricallyReduced_toSpec [CharZero R] [PerfectField k] :
    GeometricallyReduced (toSpec G hG) := by
  constructor
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  have e := h.isoIsPullback _ _ (isPullback_baseChange K G hG)
  have : _root_.IsReduced (MvPolynomial σ K ⧸
      (ideal (map (algebraMap R K) G) (isHomogeneous_map (algebraMap R K) hG)).toIdeal) :=
    isReduced_quotient_map φ hφ hker hG hF hdeg K
  have : IsReduced (projHypersurface (map (algebraMap R K) G)
      (isHomogeneous_map (algebraMap R K) hG)) := Proj.isReduced_of_isReduced
  exact isReduced_of_isOpenImmersion e.hom

end Reduced

section Chart

variable {σ R k : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field k]
  (φ : R →+* k) (hφ : Function.Surjective φ) {π : R} (hker : RingHom.ker φ = Ideal.span {π})
  {G : MvPolynomial σ R} {d : ℕ} (hG : G.IsHomogeneous d)
  (hF : Prime (map φ G)) (hdeg : (map φ G).totalDegree = G.totalDegree)
  {i₀ : σ} (hX : X i₀ ∉ Ideal.span {map φ G})

include hφ in
lemma ker_eq_maximalIdeal : RingHom.ker φ = IsLocalRing.maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ hφ)

/-- The class of `x_{i₀}`, an element of degree `1` of `R[xᵢ] ⧸ (G)`. -/
abbrev chartElem (G : MvPolynomial σ R) {d : ℕ} (hG : G.IsHomogeneous d) (i₀ : σ) :
    MvPolynomial σ R ⧸ (ideal G hG).toIdeal :=
  Ideal.Quotient.mk _ (X i₀)

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma chartElem_mem (i₀ : σ) : chartElem G hG i₀ ∈ (ideal G hG).quotientGrading 1 :=
  HomogeneousIdeal.mk_mem_quotientGrading (X_mem_grading i₀)

/-- The ring of the chart `D₊(x_{i₀})` of `V₊(G)`. -/
abbrev Chart (G : MvPolynomial σ R) {d : ℕ} (hG : G.IsHomogeneous d) (i₀ : σ) : Type u :=
  Away (ideal G hG).quotientGrading (chartElem G hG i₀)

include hφ hF hdeg hX in
theorem isDomain_chart : IsDomain (Chart G hG i₀) := by
  have := isDomain_quotient φ (ker_eq_maximalIdeal φ hφ) hG hF hdeg
  exact Proj.isDomain_away (mk_X_ne_zero φ hG hX)

include hF hdeg hX in
omit [IsDiscreteValuationRing R] in
theorem injective_algebraMap_chart [IsLocalRing R] [UniqueFactorizationMonoid R]
    (hker' : RingHom.ker φ = IsLocalRing.maximalIdeal R) :
    Function.Injective (algebraMap R (Chart G hG i₀)) := by
  have := isDomain_quotient φ hker' hG hF hdeg
  have hs : chartElem G hG i₀ ≠ 0 := mk_X_ne_zero φ hG hX
  intro r r' h
  have h' := congrArg HomogeneousLocalization.val h
  rw [HomogeneousLocalization.val_algebraMap, HomogeneousLocalization.val_algebraMap,
    IsScalarTower.algebraMap_apply R (MvPolynomial σ R ⧸ (ideal G hG).toIdeal),
    IsScalarTower.algebraMap_apply R (MvPolynomial σ R ⧸ (ideal G hG).toIdeal)
      (Localization.Away (chartElem G hG i₀)) r'] at h'
  exact injective_algebraMap φ hG hF hdeg (IsLocalization.injective _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hs) h')

omit [IsDomain R] [IsDiscreteValuationRing R] in
include hφ hker hF hX in
/-- **The chart modulo `π` is a domain**: `B ⧸ π B ≅ k ⊗_R B ≅ (k ⊗_R A)_(1 ⊗ x_{i₀})`, the chart
of `V₊(F)`, so `π B` is prime. -/
theorem isPrime_span_chart : (Ideal.span {algebraMap R (Chart G hG i₀) π}).IsPrime := by
  let _ : Algebra R k := φ.toAlgebra
  have hF' : Prime (map (algebraMap R k) G) := hF
  -- `k ⊗_R A` is a domain
  have hA : IsDomain (k ⊗[R] (MvPolynomial σ R ⧸ (ideal G hG).toIdeal)) := by
    have : IsDomain (MvPolynomial σ k ⧸
        (ideal (map (algebraMap R k) G) (isHomogeneous_map (algebraMap R k) hG)).toIdeal) :=
      (Ideal.Quotient.isDomain_iff_prime _).mpr ((Ideal.span_singleton_prime hF'.ne_zero).mpr hF')
    exact MulEquiv.isDomain _ (baseChangeEquiv k G hG).toMulEquiv
  have hs : (1 : k) ⊗ₜ[R] chartElem G hG i₀ ≠ 0 := by
    intro h
    have h' := congrArg (baseChangeEquiv k G hG) h
    rw [baseChangeEquiv_tmul, one_smul, map_zero, map_X, Ideal.Quotient.eq_zero_iff_mem,
      toIdeal_ideal] at h'
    exact hX h'
  have hD : IsDomain (Away (baseChangeGrading k G hG) ((1 : k) ⊗ₜ[R] chartElem G hG i₀)) :=
    Proj.isDomain_away hs
  -- `R ⧸ (π) ≅ k`
  let e₂ : (R ⧸ Ideal.span {π}) ≃ₐ[R] k :=
    (Ideal.quotientEquivAlgOfEq R hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R k) hφ)
  let e : (Chart G hG i₀ ⧸ (Ideal.span {π}).map (algebraMap R (Chart G hG i₀))) ≃+*
      Away (baseChangeGrading k G hG) ((1 : k) ⊗ₜ[R] chartElem G hG i₀) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Chart G hG i₀)
      (Ideal.span {π} : Ideal R)).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : Chart G hG i₀ ≃ₐ[R] Chart G hG i₀)
        e₂).toRingEquiv.trans
        ((Algebra.TensorProduct.comm R (Chart G hG i₀) k).toRingEquiv.trans
          (Proj.awayBaseChangeEquiv k (ideal G hG).quotientGrading
            (chartElem_mem hG i₀)).toRingEquiv))
  have : IsDomain (Chart G hG i₀ ⧸ (Ideal.span {π}).map (algebraMap R (Chart G hG i₀))) :=
    MulEquiv.isDomain _ e.toMulEquiv
  rw [Ideal.map_span, Set.image_singleton] at this
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this

theorem isNoetherianRing_chart [Finite σ] : IsNoetherianRing (Chart G hG i₀) := by
  set q := (ideal G hG).quotientGrading
  have hsurj : Function.Surjective (algebraMap R (q 0)) := by
    rintro ⟨_, P, hP, rfl⟩
    have hP' : P.IsHomogeneous 0 := mem_grading.mp hP
    obtain hPC := totalDegree_eq_zero_iff_eq_C.mp (by simpa using hP'.totalDegree_le)
    refine ⟨P.coeff 0, Subtype.ext ?_⟩
    change Ideal.Quotient.mk _ (C (P.coeff 0)) = Ideal.Quotient.mk _ P
    rw [← hPC]
  have : IsNoetherianRing (q 0) := isNoetherianRing_of_surjective R (q 0) _ hsurj
  have : IsScalarTower R (q 0) (MvPolynomial σ R ⧸ (ideal G hG).toIdeal) :=
    ⟨fun r a b ↦ by
      change ((r • a : q 0) : _) * b = r • ((a : _) * b)
      rw [Submodule.coe_smul, smul_mul_assoc]⟩
  have : Algebra.FiniteType (q 0) (MvPolynomial σ R ⧸ (ideal G hG).toIdeal) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have := HomogeneousLocalization.Away.finiteType (𝒜 := q) (chartElem G hG i₀) 1
    (chartElem_mem hG i₀)
  exact Algebra.FiniteType.isNoetherianRing (q 0) _

include hφ hker hF hdeg hX in
/-- The chart is `π`-adically separated (Krull's intersection theorem). -/
theorem eq_zero_of_forall_mem_span_pow_chart [Finite σ] (x : Chart G hG i₀)
    (hx : ∀ n, x ∈ Ideal.span {algebraMap R (Chart G hG i₀) π ^ n}) : x = 0 := by
  have := isDomain_chart φ hφ hG hF hdeg hX
  have := isNoetherianRing_chart hG (i₀ := i₀)
  have hH := IsHausdorff.of_isDomain (Ideal.span {algebraMap R (Chart G hG i₀) π})
    (isPrime_span_chart φ hφ hker hG hF hX).ne_top
  refine hH.haus x fun n ↦ ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact hx n

end Chart

section Sections

variable {σ R k : Type u} [Finite σ] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field k] [IsAlgClosed k] (φ : R →+* k) (hφ : Function.Surjective φ) {π : R}
  (hker : RingHom.ker φ = Ideal.span {π}) [IsAdicComplete (Ideal.span {π}) R]
  {G : MvPolynomial σ R} {d : ℕ} (hG : G.IsHomogeneous d)
  (hF : Prime (map φ G)) (hdeg : (map φ G).totalDegree = G.totalDegree)
  {i₀ : σ} (hX : X i₀ ∉ Ideal.span {map φ G})

include hφ hker hF hdeg hX in
/-- **`Γ(V₊(G), 𝒪) = R`**: the structure morphism induces a bijection on global sections
(`R` complete with algebraically closed residue field `k`, `σ` finite). A global section is
integral over `R`; on the chart `D₊(x_{i₀})` it lies in `R` by
`IsAdicComplete.mem_range_algebraMap_of_aeval_eq_zero`. -/
theorem bijective_appTop : Function.Bijective (toSpec G hG).appTop.hom := by
  set f := toSpec G hG
  set B := Chart G hG i₀
  set s := chartElem G hG i₀
  have hker' := ker_eq_maximalIdeal φ hφ
  have := isDomain_quotient φ hker' hG hF hdeg
  have := isDomain_chart φ hφ hG hF hdeg hX
  have : IsIntegral (projHypersurface G hG) :=
    Proj.isIntegral_of_isDomain (chartElem_mem hG i₀) one_pos (mk_X_ne_zero φ hG hX)
  let j := Proj.awayι (ideal G hG).quotientGrading s (chartElem_mem hG i₀) one_pos
  let ι : Γ(projHypersurface G hG, ⊤) ⟶ CommRingCat.of B :=
    j.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom
  have hcomp : f.appTop ≫ ι =
      (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom (algebraMap R B) := by
    have h1 : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
      Proj.awayι_toSpecBase _ _ one_pos
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop, h1, Scheme.ΓSpecIso_naturality]
  -- `ι` is injective: restriction to a nonempty open of an integral scheme
  have hι : Function.Injective ι.hom := by
    have hne : Nonempty ((Proj.basicOpen (ideal G hG).quotientGrading s).ι ''ᵁ ⊤) := by
      rw [Scheme.Opens.ι_image_top]
      obtain ⟨pt⟩ : Nonempty (Spec (.of B)) := inferInstance
      refine ⟨⟨j pt, ?_⟩⟩
      rw [← Proj.opensRange_awayι _ s (chartElem_mem hG i₀) one_pos]
      exact ⟨pt, rfl⟩
    have h1 : Function.Injective
        (Proj.basicOpen (ideal G hG).quotientGrading s).ι.appTop.hom := by
      rw [Scheme.Opens.ι_appTop]
      exact map_injective_of_isIntegral _ _
    have : IsIso ((Proj.basicOpenIsoSpec (ideal G hG).quotientGrading s (chartElem_mem hG i₀)
        one_pos).inv.app ⊤) := inferInstance
    have h2 : Function.Injective
        ((Proj.basicOpenIsoSpec (ideal G hG).quotientGrading s (chartElem_mem hG i₀)
          one_pos).inv.app ⊤).hom :=
      (ConcreteCategory.bijective_of_isIso _).1
    have h3 : Function.Injective (Scheme.ΓSpecIso (.of B)).hom.hom :=
      (ConcreteCategory.bijective_of_isIso _).1
    exact h3.comp (h2.comp h1)
  -- `f^♯` followed by `ι` is `R → B`
  have hcomp' (r : Γ(Spec (.of R), ⊤)) :
      ι.hom (f.appTop.hom r) = algebraMap R B ((Scheme.ΓSpecIso (.of R)).hom.hom r) :=
    congrArg (fun g ↦ g.hom r) hcomp
  have hinjR : Function.Injective (algebraMap R B) :=
    injective_algebraMap_chart φ hG hF hdeg hX hker'
  refine ⟨fun a b hab ↦ ?_, fun b ↦ ?_⟩
  · -- injectivity
    have h := congrArg ι.hom hab
    rw [hcomp', hcomp'] at h
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).1 (hinjR h)
  · -- surjectivity: `b` is integral over `R`
    have hfin := CohomologyAux.finite_app_of_isProper f (isAffineOpen_top (Spec (.of R)))
    obtain ⟨P, hPm, hPb⟩ := hfin.to_isIntegral b
    set Q := P.map (Scheme.ΓSpecIso (.of R)).hom.hom
    have hQβ : Polynomial.aeval (ι.hom b) Q = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      have : (algebraMap R B).comp (Scheme.ΓSpecIso (.of R)).hom.hom = ι.hom.comp f.appTop.hom :=
        RingHom.ext fun r ↦ (hcomp' r).symm
      rw [this, ← Polynomial.hom_eval₂]
      exact (congrArg (fun z ↦ ι.hom z) hPb).trans (map_zero _)
    have hQ : Q.map φ ≠ 0 := ((hPm.map _).map φ).ne_zero
    have hπ : algebraMap R B π ≠ 0 := by
      intro h
      have hπ0 : π = 0 := hinjR (h.trans (map_zero _).symm)
      have : IsLocalRing.maximalIdeal R = ⊥ := by
        rw [← hker', hker, hπ0, Ideal.span_singleton_eq_bot]
      exact IsDiscreteValuationRing.not_a_field R this
    obtain ⟨r, hr⟩ := IsAdicComplete.mem_range_algebraMap_of_aeval_eq_zero φ hφ hker
      (isPrime_span_chart φ hφ hker hG hF hX) hπ
      (eq_zero_of_forall_mem_span_pow_chart φ hφ hker hG hF hdeg hX) hQ hQβ
    refine ⟨(Scheme.ΓSpecIso (.of R)).inv.hom r, hι ?_⟩
    rw [hcomp', ← hr]
    congr 1
    exact (Scheme.ΓSpecIso (.of R)).inv_hom_id_apply r

include hφ hker hF hdeg hX in
/-- **The lift is geometrically connected over `R`** (Zariski's connectedness theorem, from
`Γ(V₊(G), 𝒪) = R`, `bijective_appTop`). -/
theorem geometricallyConnected_toSpec : GeometricallyConnected (toSpec G hG) := by
  set f := toSpec G hG
  have htop : IsIso (f.app ⊤) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_appTop φ hφ hker hG hF hdeg hX)
  have : CompactSpace (projHypersurface G hG) := QuasiCompact.compactSpace_of_compactSpace f
  refine CohomologyAux.geometricallyConnected_of_isIso_app f fun V ↦ ?_
  refine CohomologyAux.isIso_app_of_basis f (fun V y hy ↦ ?_) V
  obtain ⟨r, hrV, hyr⟩ := (isAffineOpen_top (Spec (.of R))).exists_basicOpen_le ⟨y, hy⟩ trivial
  refine ⟨_, hyr, hrV, CohomologyAux.isIso_app_basicOpen f (isAffineOpen_top _)
    isCompact_univ (isQuasiSeparated_univ) htop r⟩

end Sections

end AlgebraicGeometry.ProjHypersurface
