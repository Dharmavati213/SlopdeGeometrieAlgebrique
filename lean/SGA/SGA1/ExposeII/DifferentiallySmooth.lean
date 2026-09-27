/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeII.RegularImmersionSmooth
import SGA.SGA1.ExposeII.RegularSystemFiltration
import SGA.SGA1.ExposeII.SmoothDescent
import SGA.Foundations.Fields.Separable

/-!
# SGA 1, Exposé II, remarks II.4.18: smooth = flat + differentially smooth

`X` is *differentially smooth* over `S` when the diagonal `X → X ×_S X` is a regular immersion.
The remarks II.4.18 conclude: `X`, locally of finite type over `S`, is smooth iff it is flat and
differentially smooth (flatness is essential: think of a closed subscheme of `S`). We prove the
affine form over a noetherian base (`smooth_iff_flat_and_isRegularIdeal_diagonal`), following
SGA: the base change `X ×_S X → X` along the flat `X → S` has the diagonal as a section, which is
a regular immersion, so `X ×_S X` is smooth over `X` along the diagonal (II.4.17); by II.4.13
(`SGA.SGA1.ExposeII.SmoothDescent`) `X` is then smooth over `S` at every point. The same argument
gives the pointwise form for flat `X`
(`isSmoothAt_iff_exists_isRegularSystemOfGenerators_diagonal`), hence II.5.5, (i) ⇔ (iii) over a
field, and at the generic point II.5.6, (iii) ⇔ (iv). With the completion form of II.4.14, a
system of generators of the ideal of the diagonal is regular iff `𝒫^∞` is a power series ring
(`isRegularSystemOfGenerators_diagonal_iff_bijective_powerSeriesMap`); for II.5.6 this gives the
literal form of (iii): `K` is separable over `k` iff the completion of `K ⊗_k K` along the
diagonal is a power series ring over `K`
(`isGeometricallyReduced_fractionRing_iff_exists_bijective_powerSeriesMap`).
-/

universe u

open Algebra
open scoped TensorProduct

namespace SGA.SGA1.ExposeII

/-- Remarks II.4.18, affine form: let `S` be of finite type over a noetherian ring `R`. Then
`X = Spec S` is smooth over `R` iff it is flat over `R` and differentially smooth, i.e. the kernel
of the multiplication `S ⊗_R S → S` (the ideal of the diagonal) is a regular ideal. -/
theorem smooth_iff_flat_and_isRegularIdeal_diagonal {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [FiniteType R S] :
    Smooth R S ↔ Module.Flat R S ∧ IsRegularIdeal (KaehlerDifferential.ideal R S) := by
  refine ⟨fun _ ↦ ⟨inferInstance, isRegularIdeal_diagonal⟩, fun ⟨_, h⟩ ↦ ?_⟩
  have : FinitePresentation R S := FinitePresentation.of_finiteType.mp inferInstance
  have : IsNoetherianRing S := FiniteType.isNoetherianRing R S
  -- `S ⊗_R S` is smooth over `S` along the diagonal section (II.4.17)
  let σ : S ⊗[R] S →ₐ[S] S := TensorProduct.lmul'' R
  have hσ := (forall_isSmoothAt_iff_isRegularIdeal_ker σ).mpr h
  -- hence `S` is smooth over `R` at every point (II.4.13)
  refine ⟨(smoothLocus_eq_univ_iff (R := R) (A := S)).mp ?_, inferInstance⟩
  refine Set.eq_univ_of_forall fun Q ↦ ?_
  have : (Q.asIdeal.comap σ).IsPrime := Ideal.comap_isPrime _ _
  have hker : RingHom.ker σ ≤ Q.asIdeal.comap σ := fun x hx ↦ by
    rw [Ideal.mem_comap, (RingHom.mem_ker).mp hx]
    exact Q.asIdeal.zero_mem
  have := hσ (Q.asIdeal.comap σ) hker
  refine isSmoothAt_of_isSmoothAt_tensorProduct R S S (Q.asIdeal.comap σ) Q.asIdeal ?_
  ext x
  change (1 : S) * x ∈ Q.asIdeal ↔ x ∈ Q.asIdeal
  rw [one_mul]

/-- Remarks II.4.18, pointwise affine form: let `S` be of finite type and flat over a noetherian
ring `R`, and `Q` a prime of `S` (a point `x`). Then `S` is smooth over `R` at `Q` iff `X = Spec S`
is differentially smooth at `x`: the ideal of the diagonal has a regular system of generators at
the point `Δ(x)` (the prime `μ⁻¹(Q)` of `S ⊗_R S`, `μ` the multiplication). The flatness is only
needed for "if". -/
theorem isSmoothAt_iff_exists_isRegularSystemOfGenerators_diagonal {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [FiniteType R S] [Module.Flat R S]
    (Q : Ideal S) [Q.IsPrime] :
    IsSmoothAt R Q ↔ ∃ (n : ℕ) (x : Fin n →
      Localization.AtPrime (Q.comap (TensorProduct.lmul'' R : S ⊗[R] S →ₐ[S] S))),
      Ideal.span (Set.range x) = (KaehlerDifferential.ideal R S).map (algebraMap _ _) ∧
        IsRegularSystemOfGenerators x := by
  have : FinitePresentation R S := FinitePresentation.of_finiteType.mp inferInstance
  have : IsNoetherianRing S := FiniteType.isNoetherianRing R S
  have hker : RingHom.ker (TensorProduct.lmul'' R : S ⊗[R] S →ₐ[S] S) ≤
      Q.comap (TensorProduct.lmul'' R : S ⊗[R] S →ₐ[S] S) := fun x hx ↦ by
    rw [Ideal.mem_comap, (RingHom.mem_ker).mp hx]
    exact Q.zero_mem
  have hQ : (Q.comap (TensorProduct.lmul'' R : S ⊗[R] S →ₐ[S] S)).comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) = Q := by
    ext x
    change (1 : S) * x ∈ Q ↔ x ∈ Q
    rw [one_mul]
  rw [← isSmoothAt_tensorProduct_iff R S S _ Q hQ]
  exact isSmoothAt_iff_exists_isRegularSystemOfGenerators_ker _ _ hker

/-- II.5.5, (i) ⇔ (iii), affine form: a scheme `X = Spec S` of finite type over a field `k` is
smooth at `x` iff it is differentially smooth at `x` (the ideal of the diagonal has a regular
system of generators at `Δ(x)`), `X` being flat over `k`. -/
theorem isSmoothAt_iff_differentiallySmoothAt_of_field {k S : Type u} [Field k] [CommRing S]
    [Algebra k S] [FiniteType k S] (Q : Ideal S) [Q.IsPrime] :
    IsSmoothAt k Q ↔ ∃ (n : ℕ) (x : Fin n →
      Localization.AtPrime (Q.comap (TensorProduct.lmul'' k : S ⊗[k] S →ₐ[S] S))),
      Ideal.span (Set.range x) = (KaehlerDifferential.ideal k S).map (algebraMap _ _) ∧
        IsRegularSystemOfGenerators x :=
  isSmoothAt_iff_exists_isRegularSystemOfGenerators_diagonal Q

set_option backward.isDefEq.respectTransparency false in
/-- II.5.6, (iii) ⇔ (iv), for a finitely generated field extension `K = Frac S` of `k` (`S` a domain
of finite type over `k`, `x` the generic point of `Spec S`): `K` is separable over `k` iff the ideal
of the diagonal of `K ⊗_k K` (computed in the local ring of `S ⊗_k S` at the diagonal point `Δ(x)`,
whose localization `K ⊗_k K` is) admits a regular system of generators, i.e. (II.4.14,
`isRegularSystemOfGenerators_iff_bijective_powerSeriesMap`) the completion `O'` of SGA is a
formal power series ring over `K`. This is II.5.5, (i) ⇔ (iii) at the generic point. -/
theorem isGeometricallyReduced_fractionRing_iff_exists_isRegularSystemOfGenerators
    {k S : Type u} [Field k] [CommRing S] [IsDomain S] [Algebra k S] [FiniteType k S] :
    IsGeometricallyReduced k (FractionRing S) ↔ ∃ (n : ℕ) (x : Fin n →
      Localization.AtPrime ((⊥ : Ideal S).comap (TensorProduct.lmul'' k : S ⊗[k] S →ₐ[S] S))),
      Ideal.span (Set.range x) = (KaehlerDifferential.ideal k S).map (algebraMap _ _) ∧
        IsRegularSystemOfGenerators x := by
  rw [← isSmoothAt_iff_differentiallySmoothAt_of_field (⊥ : Ideal S)]
  have : IsLocalization (nonZeroDivisors S) (Localization.AtPrime (⊥ : Ideal S)) := by
    rw [← Ideal.primeCompl_bot]
    infer_instance
  let e : Localization.AtPrime (⊥ : Ideal S) ≃ₐ[S] FractionRing S :=
    IsLocalization.algEquiv (nonZeroDivisors S) _ _
  have : EssFiniteType k (FractionRing S) := .comp k S _
  rw [← formallySmooth_iff_isGeometricallyReduced]
  exact ⟨fun h ↦ .of_equiv (e.restrictScalars k).symm, fun h ↦ .of_equiv (e.restrictScalars k)⟩

/-- Remarks II.4.18, `𝒫^∞`, affine form: let `x₁,…,xₙ` generate the ideal `I` of the diagonal of
`X = Spec S` over `Spec R`. Then they form a regular system of generators of `I` (so that `X` is
differentially smooth) iff `𝒫^∞_{X/R}`, the `I`-adic completion of `S ⊗_R S` (an `S`-algebra
through the first factor), is the formal power series ring `S[[t₁,…,tₙ]]`, through `tᵢ ↦ xᵢ`. -/
theorem isRegularSystemOfGenerators_diagonal_iff_bijective_powerSeriesMap {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] {n : ℕ} (x : Fin n → S ⊗[R] S)
    (hx : Ideal.span (Set.range x) = KaehlerDifferential.ideal R S) :
    IsRegularSystemOfGenerators x ↔ Function.Bijective (powerSeriesMap (B := S) x) :=
  isRegularSystemOfGenerators_iff_bijective_powerSeriesMap_of_section
    (TensorProduct.lmul'' R) hx

section Generic

open IsLocalRing TensorProduct

variable (k S : Type u) [Field k] [CommRing S] [IsDomain S] [Algebra k S]

/-- The prime of `S ⊗_k S` of the diagonal point `Δ(x)`, `x` the generic point of `Spec S`. -/
abbrev diagonalGenericPrime : Ideal (S ⊗[k] S) :=
  (⊥ : Ideal S).comap (TensorProduct.lmul'' k : S ⊗[k] S →ₐ[S] S)

/-- `K = Frac S → (S ⊗_k S)_{Δ(x)}`, through the first factor. -/
noncomputable def fractionRingToDiagonalLocalization :
    FractionRing S →+* Localization.AtPrime (diagonalGenericPrime k S) :=
  IsLocalization.lift (M := nonZeroDivisors S) (S := FractionRing S)
    (g := (algebraMap (S ⊗[k] S) (Localization.AtPrime (diagonalGenericPrime k S))).comp
      Algebra.TensorProduct.includeLeftRingHom) fun s ↦ by
    refine IsLocalization.map_units (M := (diagonalGenericPrime k S).primeCompl) _
      ⟨s.1 ⊗ₜ 1, ?_⟩
    change s.1 ⊗ₜ[k] (1 : S) ∉ diagonalGenericPrime k S
    rw [Ideal.mem_comap, Ideal.mem_bot]
    have : (TensorProduct.lmul'' k : S ⊗[k] S →ₐ[S] S) (s.1 ⊗ₜ 1) = s.1 * 1 :=
      Algebra.TensorProduct.lmul'_apply_tmul (R := k) s.1 1
    rw [this, mul_one]
    exact nonZeroDivisors.ne_zero s.2

/-- The residue map `(S ⊗_k S)_{Δ(x)} → K`. -/
noncomputable def diagonalLocalizationToFractionRing :
    Localization.AtPrime (diagonalGenericPrime k S) →+* FractionRing S :=
  IsLocalization.lift (M := (diagonalGenericPrime k S).primeCompl)
    (g := (algebraMap S (FractionRing S)).comp
      (TensorProduct.lmul'' k : S ⊗[k] S →ₐ[S] S).toRingHom) fun a ↦ by
    refine IsUnit.mk0 _ ?_
    have ha := a.2
    simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, Ideal.mem_comap, Ideal.mem_bot] at ha
    simpa using ha

lemma diagonalLocalizationToFractionRing_algebraMap (z : S ⊗[k] S) :
    diagonalLocalizationToFractionRing k S (algebraMap _ _ z) =
      algebraMap S (FractionRing S) ((TensorProduct.lmul'' k : S ⊗[k] S →ₐ[S] S) z) :=
  IsLocalization.lift_eq _ z

lemma fractionRingToDiagonalLocalization_algebraMap (s : S) :
    fractionRingToDiagonalLocalization k S (algebraMap S _ s) =
      algebraMap (S ⊗[k] S) _ (s ⊗ₜ[k] (1 : S)) :=
  IsLocalization.lift_eq _ s

lemma diagonalLocalizationToFractionRing_comp :
    (diagonalLocalizationToFractionRing k S).comp (fractionRingToDiagonalLocalization k S) =
      RingHom.id _ := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors S)
  refine RingHom.ext fun s ↦ ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, fractionRingToDiagonalLocalization_algebraMap,
    diagonalLocalizationToFractionRing_algebraMap, RingHom.comp_apply, RingHom.id_apply]
  congr 1
  exact (Algebra.TensorProduct.lmul'_apply_tmul (R := k) s 1).trans (mul_one s)

omit [IsDomain S] in
lemma kaehlerDifferentialIdeal_eq_diagonalGenericPrime :
    KaehlerDifferential.ideal k S = diagonalGenericPrime k S := by
  ext z
  rfl

variable [FiniteType k S]

set_option backward.isDefEq.respectTransparency false in
/-- **II.5.6, (iii) ⇔ (iv)**, literal form: let `K = Frac S` be a finitely generated field
extension of `k` (`S` a domain of finite type over `k`). Then `K` is separable over `k` iff the
completion `O'` of `K ⊗_k K` along the ideal of the diagonal is a formal power series ring over
`K`: for a system of generators `x₁,…,xₙ` of that ideal, `K[[t₁,…,tₙ]] → O'`, `tᵢ ↦ xᵢ`, is an
isomorphism. The completion is computed in the local ring of `S ⊗_k S` at the diagonal point
`Δ(x)`, `x` the generic point of `Spec S` (which is the local ring of `K ⊗_k K` at the diagonal,
and has the same completion since the ideal of the diagonal of `K ⊗_k K` is maximal); it is a
`K`-algebra through the first factor. -/
theorem isGeometricallyReduced_fractionRing_iff_exists_bijective_powerSeriesMap :
    letI := (fractionRingToDiagonalLocalization k S).toAlgebra
    IsGeometricallyReduced k (FractionRing S) ↔
      ∃ (n : ℕ) (x : Fin n → Localization.AtPrime (diagonalGenericPrime k S)),
        Ideal.span (Set.range x) = (KaehlerDifferential.ideal k S).map (algebraMap _ _) ∧
          Function.Bijective (powerSeriesMap (B := FractionRing S) x) := by
  let := (fractionRingToDiagonalLocalization k S).toAlgebra
  rw [isGeometricallyReduced_fractionRing_iff_exists_isRegularSystemOfGenerators]
  let σA : Localization.AtPrime (diagonalGenericPrime k S) →ₐ[FractionRing S] FractionRing S :=
    { diagonalLocalizationToFractionRing k S with
      commutes' q := congr($(diagonalLocalizationToFractionRing_comp k S) q) }
  have hker : (KaehlerDifferential.ideal k S).map
      (algebraMap _ (Localization.AtPrime (diagonalGenericPrime k S))) = RingHom.ker σA := by
    rw [kaehlerDifferentialIdeal_eq_diagonalGenericPrime, Localization.AtPrime.map_eq_maximalIdeal]
    refine le_antisymm ?_ (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top σA))
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro z hz
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change diagonalLocalizationToFractionRing k S (algebraMap _ _ z) = 0
    rw [diagonalLocalizationToFractionRing_algebraMap]
    rw [Ideal.mem_comap, Ideal.mem_bot] at hz
    rw [hz, map_zero]
  refine exists_congr fun n ↦ exists_congr fun x ↦ and_congr_right fun hx ↦ ?_
  exact isRegularSystemOfGenerators_iff_bijective_powerSeriesMap_of_section σA (hx.trans hker)

end Generic

end SGA.SGA1.ExposeII
