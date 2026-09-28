/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Smooth.Field
import SGA.Foundations.CommAlg.RegularLocalRing
import SGA.Foundations.Fields.Separable
import SGA.SGA1.ExposeII.Generalities
import SGA.SGA1.ExposeII.Jacobian
import SGA.SGA1.ExposeII.Permanence
import SGA.SGA1.ExposeII.RegularImmersionSmooth
import SGA.SGA1.ExposeII.RegularSequence

/-!
# SGA 1, Exposé II, §5: the case of a ground field

Over a field `k` we prove:

* II.5.3, II.5.4, first half: the local rings of a scheme smooth over `k` are regular (for
  algebras, pointwise, and for schemes), via the regularity results of §3;
* II.5.10 and II.5.3, converse: at a point `x` with `κ(x)` separable over `k` (in the sense of
  `Algebra.IsGeometricallyReduced`, `SGA.Foundations.Fields`), `X` is smooth at `x` iff `𝒪_x` is
  regular. As in the N.B. after II.5.3 this is II.4.15 applied to the point: a regular system of
  parameters is a regular sequence, hence a regular system of generators of `𝔪_x`;
* II.5.4, converse: over a perfect field a regular algebra of finite type is smooth;
* II.5.5, (i) ⇔ (iv) (global affine form, and at a point with basic open neighbourhoods, over a
  perfect extension `k'`);
* II.5.9, (i) ⇔ (ii): `𝒪_x` regular and `κ(x)` separable iff `X` smooth at `x` and
  `𝔪_x/𝔪_x² → Ω¹_{X/k}(x)` injective (II.4.10 (iv) applied to the point);
* II.5.2, (iv) ⇒ (iii): at a point with residue field unramified (finite separable) over `k`,
  generators of `𝔪_x` have differentials generating `Ω¹_{X/k}(x)`;
* II.5.6 for a finitely generated field extension `K / k`: (i) ⇔ (ii) ⇔ (ii bis) ⇔ (iv) ⇔ smooth,
  and the errata (from `SGA.Foundations.Fields`); the `dxᵢ` of a separating transcendence basis
  form a basis of `Ω¹_{K/k}`; the remark after II.5.7.

II.5.1 is in `SGA.SGA1.ExposeII.FieldEtale`; II.5.2, II.5.5 (i) ⇔ (ii) ⇔ (ii bis), II.5.7, II.5.8
and II.5.9 (iii)–(iv) are in `SGA.SGA1.ExposeII.FieldSmooth`, II.5.5 (i) ⇔ (iii) (differential
smoothness) and condition (iii) of II.5.6 (through regular systems of generators of the ideal of
the diagonal) in `SGA.SGA1.ExposeII.DifferentiallySmooth`.
-/

universe u

open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace SGA.SGA1.ExposeII

section Regular

variable (k : Type u) [Field k]

/-- II.5.3, II.5.4 (first half), affine form: an algebra smooth over a field has regular local
rings. -/
theorem isRegularLocalRing_localization_of_smooth_field {S : Type u} [CommRing S] [Algebra k S]
    [Smooth k S] (Q : Ideal S) [Q.IsPrime] : IsRegularLocalRing (Localization.AtPrime Q) :=
  isRegularLocalRing_localization_of_smooth (R := k) Q

open AlgebraicGeometry in
/-- II.5.3, II.5.4 (first half): if `X` is smooth over a field `k`, then `X` is regular. -/
theorem isRegularLocalRing_stalk_of_smooth_field {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [AlgebraicGeometry.Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  refine isRegularLocalRing_stalk_of_smooth f (fun y ↦ ?_) x
  have : IsRegularRing Γ(Spec (.of k), ⊤) :=
    .of_ringEquiv (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  exact isRegularLocalRing_stalk_of_isRegularRing (isAffineOpen_top (Spec (.of k)))
    (⟨y, trivial⟩ : (⊤ : (Spec (.of k)).Opens))

/-- II.5.10, local form (the converse of II.5.3 at an arbitrary point): let `S` be of finite type
over a field `k` and `Q` a prime of `S` (a point `x`) whose residue field `κ(x)` is formally
smooth over `k`. If `𝒪_x` is regular, then `S` is smooth over `k` at `Q`. As in the N.B. after
II.5.3, this is II.4.15 applied to the subscheme `{x}`: a regular system of parameters of `𝒪_x`
is a regular sequence, hence a regular system of generators of `𝔪_x`. -/
theorem isSmoothAt_of_isRegularLocalRing {S : Type u} [CommRing S] [Algebra k S]
    [FiniteType k S] (Q : Ideal S) [Q.IsPrime] [IsRegularLocalRing (Localization.AtPrime Q)]
    [FormallySmooth k Q.ResidueField] : IsSmoothAt k Q := by
  obtain ⟨rs, -, hspan, hreg⟩ :=
    IsRegularLocalRing.exists_isRegular_ofList_eq_maximalIdeal (R := Localization.AtPrime Q)
  have hx := isRegularSystemOfGenerators_of_isWeaklyRegular rs hreg.toIsWeaklyRegular
  have hxJ : Ideal.span (Set.range fun i : Fin rs.length ↦ rs[i]) =
      maximalIdeal (Localization.AtPrime Q) := by
    rw [← hspan]
    change _ = Ideal.span {r | r ∈ rs}
    congr 1
    ext z
    simp [List.mem_iff_getElem, Fin.exists_iff]
  exact isSmoothAt_of_isRegularSystemOfGenerators Q _ le_rfl
    (inferInstanceAs (FormallySmooth k Q.ResidueField)) _ hxJ hx

/-- II.5.3, pointwise first half: if `S` (of finite type over `k`) is smooth over `k` at `Q`, then
`𝒪_x = S_Q` is regular. -/
theorem isRegularLocalRing_of_isSmoothAt {S : Type u} [CommRing S] [Algebra k S] [FiniteType k S]
    (Q : Ideal S) [Q.IsPrime] [IsSmoothAt k Q] : IsRegularLocalRing (Localization.AtPrime Q) := by
  have : FinitePresentation k S := FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨f, hf, _⟩ := IsSmoothAt.exists_notMem_smooth k Q
  have hdisj : Disjoint (Submonoid.powers f : Set S) Q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  have := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) (Localization.Away f) Q ‹_› hdisj
  have := isRegularLocalRing_localization_of_smooth_field k (S := Localization.Away f)
    (Q.map (algebraMap S (Localization.Away f)))
  have hQ : (Q.map (algebraMap S (Localization.Away f))).under S = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› hdisj
  have key (I : Ideal S) [I.IsPrime] (hI : I = Q)
      (h : IsRegularLocalRing (Localization.AtPrime I)) :
      IsRegularLocalRing (Localization.AtPrime Q) := by
    subst hI; exact h
  exact key _ (by rwa [← Ideal.under_def]) (.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (.powers f)
      (Q.map (algebraMap S (Localization.Away f)))).toRingEquiv.symm)

/-- II.5.10: let `x` be a point of a scheme of finite type over a field `k` (a prime `Q` of an
algebra `S` of finite type over `k`) such that `κ(x)` is a separable extension of `k` (in the
sense of `Algebra.IsGeometricallyReduced`, i.e. `L ⊗_k κ(x)` reduced for all `L / k`). Then `S` is
smooth over `k` at `x` iff `𝒪_x` is regular. -/
theorem isSmoothAt_iff_isRegularLocalRing {S : Type u} [CommRing S] [Algebra k S]
    [FiniteType k S] (Q : Ideal S) [Q.IsPrime] [IsGeometricallyReduced k Q.ResidueField] :
    IsSmoothAt k Q ↔ IsRegularLocalRing (Localization.AtPrime Q) := by
  refine ⟨fun _ ↦ isRegularLocalRing_of_isSmoothAt k Q, fun _ ↦ ?_⟩
  have : EssFiniteType k Q.ResidueField := .comp k S _
  have : FormallySmooth k Q.ResidueField := formallySmooth_iff_isGeometricallyReduced.mpr ‹_›
  exact isSmoothAt_of_isRegularLocalRing k Q

/-- II.5.3, converse: let `S` be of finite type over `k` and `𝔪` a maximal ideal (a closed point
`x`) with `κ(x) = S/𝔪` separable over `k` (it is finite over `k` by the Nullstellensatz). If
`𝒪_x` is regular, then `S` is smooth over `k` at `𝔪`. -/
theorem isSmoothAt_of_isRegularLocalRing_of_isMaximal (S : Type u) [CommRing S] [Algebra k S]
    [FiniteType k S] (M : Ideal S) [M.IsMaximal] (hsep : Algebra.IsSeparable k (S ⧸ M))
    (hreg : IsRegularLocalRing (Localization.AtPrime M)) : IsSmoothAt k M := by
  let := Ideal.Quotient.field M
  let e : (S ⧸ M) ≃ₐ[k] M.ResidueField :=
    .ofBijective (IsScalarTower.toAlgHom k (S ⧸ M) M.ResidueField)
      M.bijective_algebraMap_quotient_residueField
  have := hsep
  have : FormallyEtale k (S ⧸ M) := .of_isSeparable k _
  have : FormallySmooth k M.ResidueField := .of_equiv e
  exact isSmoothAt_of_isRegularLocalRing k M

/-- II.5.4, converse, deduced from II.5.3 as in SGA: over a perfect field, an algebra of finite
type all of whose local rings are regular is smooth. (SGA: `X` smooth at every closed point,
hence everywhere since the smooth locus is open.) -/
theorem smooth_of_isRegularLocalRing [PerfectField k] {S : Type u} [CommRing S] [Algebra k S]
    [FiniteType k S]
    (h : ∀ (Q : Ideal S) [Q.IsPrime], IsRegularLocalRing (Localization.AtPrime Q)) :
    Smooth k S := by
  have : FinitePresentation k S := FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun Q ↦ ?_), inferInstance⟩
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q.asIdeal Q.2.ne_top
  have := hM
  let := Ideal.Quotient.field M
  have : Module.Finite k (S ⧸ M) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ M)
  have : Algebra.IsAlgebraic k (S ⧸ M) := Algebra.IsIntegral.isAlgebraic
  have hM' : (⟨M, hM.isPrime⟩ : PrimeSpectrum S) ∈ smoothLocus k S :=
    isSmoothAt_of_isRegularLocalRing_of_isMaximal k S M inferInstance (h M)
  have hsp : Q ⤳ ⟨M, hM.isPrime⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hQM
  exact hsp.mem_open isOpen_smoothLocus hM'

/-- Over the residue field, an injective `I/I² → κ ⊗ Ω` for `I = 𝔪` has a left inverse. -/
lemma exists_leftInverse_kerCotangentToTensor {R P : Type*} [CommRing R] [CommRing P]
    [Algebra R P] [IsLocalRing P]
    (hinj : Function.Injective (kerCotangentToTensor R P (ResidueField P))) :
    ∃ l, l ∘ₗ kerCotangentToTensor R P (ResidueField P) = LinearMap.id := by
  have hker : maximalIdeal P = RingHom.ker (algebraMap P (ResidueField P)) := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  let e := Ideal.Cotangent.equivOfEq _ _ hker
  let g : CotangentSpace P →ₗ[ResidueField P] ResidueField P ⊗[P] Ω[P⁄R] :=
    (kerCotangentToTensor R P (ResidueField P) ∘ₗ e.toLinearMap).extendScalarsOfSurjective
      residue_surjective
  have hg : LinearMap.ker g = ⊥ :=
    LinearMap.ker_eq_bot.mpr (hinj.comp e.injective)
  obtain ⟨l, hl⟩ := g.exists_leftInverse_of_injective hg
  refine ⟨e.toLinearMap ∘ₗ l.restrictScalars P, LinearMap.ext fun c ↦ ?_⟩
  obtain ⟨c, rfl⟩ := e.surjective c
  have := LinearMap.congr_fun hl c
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] at this ⊢
  change e (l (g c)) = e c
  rw [this]

/-- II.5.9, (i) ⇔ (ii): let `x` be a point of a scheme of finite type over `k` (a prime `Q` of an
algebra `S` of finite type over `k`). Then `𝒪_x` is regular and `κ(x)` is separable over `k` iff
`X` is smooth over `k` at `x` and the canonical map `𝔪_x/𝔪_x² → Ω¹_{𝒪_x/k} ⊗ κ(x)` is injective.
(Separability of `κ(x)` is `Algebra.IsGeometricallyReduced`.) -/
theorem isRegularLocalRing_and_isGeometricallyReduced_iff {S : Type u} [CommRing S]
    [Algebra k S] [FiniteType k S] (Q : Ideal S) [Q.IsPrime] :
    (IsRegularLocalRing (Localization.AtPrime Q) ∧ IsGeometricallyReduced k Q.ResidueField) ↔
      (IsSmoothAt k Q ∧ Function.Injective (kerCotangentToTensor k (Localization.AtPrime Q)
        (ResidueField (Localization.AtPrime Q)))) := by
  have : EssFiniteType k Q.ResidueField := .comp k S _
  constructor
  · rintro ⟨hreg, hsep⟩
    have hsm : IsSmoothAt k Q := (isSmoothAt_iff_isRegularLocalRing k Q).mpr hreg
    refine ⟨hsm, ?_⟩
    have : FormallySmooth k (ResidueField (Localization.AtPrime Q)) :=
      formallySmooth_iff_isGeometricallyReduced.mpr hsep
    obtain ⟨l, hl⟩ := (formallySmooth_iff_split_injection k (Localization.AtPrime Q)
      (ResidueField (Localization.AtPrime Q)) residue_surjective).mp this
    exact Function.LeftInverse.injective (g := l) fun x ↦ LinearMap.congr_fun hl x
  · rintro ⟨hsm, hinj⟩
    refine ⟨isRegularLocalRing_of_isSmoothAt k Q, ?_⟩
    have : FormallySmooth k (ResidueField (Localization.AtPrime Q)) :=
      (formallySmooth_iff_split_injection k (Localization.AtPrime Q)
        (ResidueField (Localization.AtPrime Q)) residue_surjective).mpr
        (exists_leftInverse_kerCotangentToTensor hinj)
    exact FormallySmooth.isGeometricallyReduced

open AlgebraicGeometry in
/-- II.5.5, (i) ⇒ (iv) (global form): if `X` is smooth over `k`, then `X ⊗_k k'` is regular for
every field extension `k'` of `k` (smoothness is stable under base change and implies
regularity). -/
theorem isRegularLocalRing_stalk_baseChange_of_smooth {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [AlgebraicGeometry.Smooth f] (k' : Type u) [Field k'] [Algebra k k']
    (x : (CategoryTheory.Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :
      Scheme.{u})) :
    IsRegularLocalRing ((CategoryTheory.Limits.pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))).presheaf.stalk x) :=
  isRegularLocalRing_stalk_of_smooth_field k' (CategoryTheory.Limits.pullback.snd _ _) x

/-- II.5.5, (iv) ⇒ (i) (global affine form), deduced as in SGA from II.5.4 over a perfect
extension `k'` and the descent II.4.13: if `k' ⊗_k S` is regular for a perfect extension `k'`
of `k`, then `S` is smooth over `k`. -/
theorem smooth_of_isRegularLocalRing_baseChange (k' : Type u) [Field k'] [Algebra k k']
    [PerfectField k'] {S : Type u} [CommRing S] [Algebra k S] [FiniteType k S]
    (h : ∀ (Q : Ideal (k' ⊗[k] S)) [Q.IsPrime], IsRegularLocalRing (Localization.AtPrime Q)) :
    Smooth k S := by
  have : Smooth k' (k' ⊗[k] S) := smooth_of_isRegularLocalRing k' h
  exact .of_smooth_tensorProduct_of_faithfullyFlat k'

/-- II.5.5, (i) ⇔ (iv) (affine form, with basic open neighbourhoods): let `S` be of finite type
over `k`, `k'` a perfect extension of `k` and `Q` a prime of `S` (a point `x`). Then `S` is
smooth over `k` at `Q` iff `Q` has a neighbourhood `D(f)` such that `k' ⊗_k S_f` is regular. -/
theorem isSmoothAt_iff_exists_isRegularLocalRing_baseChange (k' : Type u) [Field k']
    [Algebra k k'] [PerfectField k'] {S : Type u} [CommRing S] [Algebra k S] [FiniteType k S]
    (Q : Ideal S) [Q.IsPrime] :
    IsSmoothAt k Q ↔ ∃ f ∉ Q, ∀ (P : Ideal (k' ⊗[k] Localization.Away f)) [P.IsPrime],
      IsRegularLocalRing (Localization.AtPrime P) := by
  have : FinitePresentation k S := FinitePresentation.of_finiteType.mp inferInstance
  constructor
  · intro
    obtain ⟨f, hf, hsm⟩ := IsSmoothAt.exists_notMem_smooth k Q
    exact ⟨f, hf, fun P _ ↦ isRegularLocalRing_localization_of_smooth_field k' P⟩
  · rintro ⟨f, hf, h⟩
    have : FinitePresentation S (Localization.Away f) := IsLocalization.Away.finitePresentation f
    have : FiniteType k (Localization.Away f) := .trans (S := S) inferInstance inferInstance
    have : Smooth k (Localization.Away f) := smooth_of_isRegularLocalRing_baseChange k k' h
    have hQ : (⟨Q, ‹_›⟩ : PrimeSpectrum S) ∈ smoothLocus k S :=
      (basicOpen_subset_smoothLocus_iff_smooth (R := k) (f := f)).mpr this hf
    exact hQ

end Regular

section Cotangent

variable {k P : Type u} [Field k] [CommRing P] [IsLocalRing P] [Algebra k P]

/-- II.5.2, (iv) ⇒ (iii): let `P = 𝒪_x` be a local `k`-algebra whose residue field is unramified
(e.g. finite separable) over `k`. If `f₁,…,fₙ` generate `𝔪_x`, then the `dfᵢ(x)` generate
`Ω¹_{X/k}(x) = κ(x) ⊗ Ω¹_{P/k}` (by the exact sequence (5.1), since `Ω¹_{κ(x)/k} = 0`). -/
theorem span_tmul_D_eq_top_of_span_eq_maximalIdeal [FormallyUnramified k (ResidueField P)]
    {ι : Type*} (f : ι → P) (hf : Ideal.span (Set.range f) = maximalIdeal P) :
    Submodule.span (ResidueField P)
      (Set.range fun i ↦ (1 : ResidueField P) ⊗ₜ[P] D k P (f i)) = ⊤ := by
  set V := Submodule.span (ResidueField P)
    (Set.range fun i ↦ (1 : ResidueField P) ⊗ₜ[P] D k P (f i))
  have hker : RingHom.ker (algebraMap P (ResidueField P)) = maximalIdeal P := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  -- every element of `κ ⊗ Ω¹_P` is `1 ⊗ dz` for some `z ∈ 𝔪`
  have hrange := KaehlerDifferential.range_kerCotangentToTensor k P (ResidueField P)
    residue_surjective
  have hmem (z : P) (hz : z ∈ maximalIdeal P) :
      (1 : ResidueField P) ⊗ₜ[P] D k P z ∈ V := by
    rw [← hf] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => simpa [tmul_add] using V.add_mem ha hb
    | smul a z hz hzV =>
      have hz' : z ∈ maximalIdeal P := hf ▸ hz
      have : (1 : ResidueField P) ⊗ₜ[P] D k P (a • z) =
          residue P a • ((1 : ResidueField P) ⊗ₜ[P] D k P z) := by
        rw [smul_eq_mul, Derivation.leibniz, tmul_add, tmul_smul, tmul_smul,
          ← algebraMap_smul (ResidueField P) z, ResidueField.algebraMap_eq,
          (residue_eq_zero_iff z).mpr hz', zero_smul, add_zero,
          ← algebraMap_smul (ResidueField P) a, ResidueField.algebraMap_eq]
      rw [this]
      exact V.smul_mem _ hzV
  refine eq_top_iff.mpr fun ω _ ↦ ?_
  have hω : ω ∈ LinearMap.range (kerCotangentToTensor k P (ResidueField P)) := by
    rw [hrange]
    exact Subsingleton.elim (α := Ω[ResidueField P⁄k]) _ _
  obtain ⟨c, rfl⟩ := hω
  obtain ⟨⟨z, hz⟩, rfl⟩ := Ideal.toCotangent_surjective _ c
  rw [kerCotangentToTensor_toCotangent]
  exact hmem z (hker ▸ hz)

end Cotangent

section SeparablyGenerated

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- II.5.6, (i) ⇒ smooth: a separable extension of a purely transcendental extension
`k(t₁,…,tₙ)` is formally smooth over `k` (mathlib). -/
theorem formallySmooth_of_separablyGenerated {ι : Type*} {x : ι → K}
    (hx : AlgebraicIndependent k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K] : FormallySmooth k K :=
  .of_algebraicIndependent_of_isSeparable hx

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- II.5.6, (i) ⇒ (ii), and the remark after II.5.6: if `K` is separable algebraic over
`k(x₁,…,xₙ)` with the `xᵢ` algebraically independent (a separating transcendence basis), then
the `dxᵢ` form a basis of `Ω¹_{K/k}`; in particular it is free of rank the transcendence
degree. -/
theorem exists_basis_kaehler_of_algebraicIndependent {ι : Type u} {x : ι → K}
    (hx : AlgebraicIndependent k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K] :
    ∃ b : Module.Basis ι K Ω[K⁄k], ∀ i, b i = D k K (x i) := by
  let A := Algebra.adjoin k (Set.range x)
  let L := IntermediateField.adjoin k (Set.range x)
  let e : MvPolynomial ι k ≃ₐ[k] A := hx.aevalEquiv
  let : Algebra (MvPolynomial ι k) A := e.toRingEquiv.toRingHom.toAlgebra
  let : Algebra (MvPolynomial ι k) K := ((algebraMap A K).comp e.toRingEquiv.toRingHom).toAlgebra
  have : IsScalarTower (MvPolynomial ι k) A K := .of_algebraMap_eq' rfl
  have : IsScalarTower k (MvPolynomial ι k) K := .of_algebraMap_eq fun r ↦ by
    change _ = algebraMap A K (hx.aevalEquiv (MvPolynomial.C r))
    rw [hx.algebraMap_aevalEquiv]
    simp
  have : FormallyEtale (MvPolynomial ι k) A :=
    .of_equiv (R := MvPolynomial ι k) (A := MvPolynomial ι k)
      (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun _ ↦ rfl)
  have : FormallyEtale A L := .of_isLocalization (nonZeroDivisors A)
  have : FormallyEtale L K := .of_isSeparable L K
  have : FormallyEtale A K := .comp A L K
  have : FormallyEtale (MvPolynomial ι k) K := .comp _ A K
  refine ⟨basisKaehlerOfFormallyEtale ι, fun i ↦ ?_⟩
  rw [basisKaehlerOfFormallyEtale_apply]
  congr 1
  change algebraMap A K (hx.aevalEquiv (MvPolynomial.X i)) = x i
  rw [hx.algebraMap_aevalEquiv]
  simp

/-- II.5.6, for a finitely generated field extension `K / k` (SGA allows a local Artin ring
essentially of finite type over `k`; here `K` is a field). The following are equivalent:
(i) `K` is separable algebraic over a purely transcendental `k(t₁,…,tₙ)`; (ii) `Ω¹_{K/k}` has rank
`n = trdeg_k K`; (ii bis) `Ω¹_{K/k}` has rank `≤ n` (it is generated by `n` elements); (iv) `K` is
separable over `k`; and `K` is (formally) smooth over `k`. Condition (iii) (the completion of
`K ⊗_k K` along the diagonal is a power series ring) is
`isGeometricallyReduced_fractionRing_iff_exists_isRegularSystemOfGenerators`. -/
theorem isSeparablyGenerated_tfae (K : Type u) [Field K] [Algebra k K] [EssFiniteType k K] :
    List.TFAE [IsSeparablyGenerated k K, Module.rank K Ω[K⁄k] = trdeg k K,
      Module.rank K Ω[K⁄k] ≤ trdeg k K, IsGeometricallyReduced k K, FormallySmooth k K] := by
  tfae_have 1 ↔ 2 := isSeparablyGenerated_iff_rank_kaehlerDifferential_eq
  tfae_have 1 ↔ 3 := isSeparablyGenerated_iff_rank_kaehlerDifferential_le
  tfae_have 1 ↔ 4 := isGeometricallyReduced_iff_isSeparablyGenerated.symm
  tfae_have 4 ↔ 5 := formallySmooth_iff_isGeometricallyReduced.symm
  tfae_finish

/-- II.5.6, (ii bis) ⇒ (i): if `Ω¹_{K/k}` is generated by `n = trdeg_k K` elements, `K` is
separably generated over `k` (`SGA.Foundations`). -/
alias isSeparablyGenerated_of_span_eq_top := IsSeparablyGenerated.of_span_eq_top

/-- The errata to II.5.6: if `K / k` is finitely generated and separable and the `dxᵢ` form a
basis of `Ω¹_{K/k}`, then the `xᵢ` are algebraically independent, and even a separating
transcendence basis (`SGA.Foundations`, via MacLane's criterion). -/
alias isTranscendenceBasis_of_basis_kaehlerDifferential :=
  IsSeparablyGenerated.isTranscendenceBasis_of_basis

/-- The remark after II.5.6 (and the parenthesis in II.5.8 (ii)): for `n = trdeg_k K` elements
`xᵢ` of a finitely generated extension `K / k`, the `xᵢ` form a separating transcendence basis
iff the `dxᵢ` form a basis of `Ω¹_{K/k}` iff they generate it (`SGA.Foundations`). -/
alias isTranscendenceBasis_tfae := isTranscendenceBasis_and_isSeparable_tfae

/-- The remark after II.5.7: an algebraic extension `K / k` is smooth iff it is separable. For a
finite inseparable `K / k`, `Ω¹_{K/k}` is free and `Spec K` is reduced, but `K` is not smooth over
`k` (`SGA.Foundations`). -/
alias formallySmooth_iff_isSeparable_of_isAlgebraic := formallySmooth_iff_isSeparable

end SeparablyGenerated

end SGA.SGA1.ExposeII
