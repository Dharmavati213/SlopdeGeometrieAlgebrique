/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.TensorProduct.Nontrivial
import SGA.Foundations.ConstructibleNoetherian
import SGA.Foundations.Fields.GeometricallyConnected

/-!
# Absolute irreducibility of a polynomial spreads out (Bertini–Noether)

Let `R` be a noetherian domain and `g ∈ R[X₁, …, Xₙ]` a polynomial which is absolutely
irreducible over the fraction field of `R`: its image in `Ω[X₁, …, Xₙ]` is irreducible for an
algebraically closed field `Ω ⊇ R`. Then there is `a ≠ 0` in `R` such that for every ring map
`φ : R ⟶ K` to a field with `φ a ≠ 0`, the image of `g` in `K[X₁, …, Xₙ]` is irreducible
(`MvPolynomial.exists_ne_zero_forall_irreducible_map`).

This is the Bertini–Noether lemma (Fried–Jarden, *Field Arithmetic*, Prop. 9.4.3; E. Noether's
forms for absolute irreducibility), one of the inputs of EGA IV 9.7.7. The proof uses Chevalley's
theorem instead of Noether's forms: the factorizations `g = h₁ h₂` with `h₁`, `h₂` non-constant of
total degree at most `deg g` are the points of finitely many affine schemes of finite type over
`R` (`MvPolynomial.BertiniNoether.factorAlgebra`), so the set of primes `𝔭` of `R` over which `g`
becomes reducible over some field is constructible (`MvPolynomial.BertiniNoether.badSet`); by the
Nullstellensatz it does not contain the generic point, hence it misses a basic open `D(a)`.

## References

* [M. Fried, M. Jarden, *Field Arithmetic*, Prop. 9.4.3][FriedJarden]
* [EGA IV₃, 9.7.5, 9.7.7][EGA4]
-/

universe u v w

open MvPolynomial Topology TensorProduct

namespace MvPolynomial

namespace BertiniNoether

variable {R : Type u} [CommRing R] {σ : Type v} [Fintype σ] [DecidableEq σ] (g : MvPolynomial σ R)

/-- The monomials with every exponent at most `g.totalDegree`. -/
noncomputable def monomials : Finset (σ →₀ ℕ) :=
  (Finset.univ : Finset (σ → Fin (g.totalDegree + 1))).image
    fun e ↦ Finsupp.equivFunOnFinite.symm fun i ↦ (e i : ℕ)

lemma mem_monomials {m : σ →₀ ℕ} (hm : ∀ i, m i ≤ g.totalDegree) : m ∈ monomials g := by
  classical
  refine Finset.mem_image.mpr ⟨fun i ↦ ⟨m i, Nat.lt_succ_of_le (hm i)⟩, Finset.mem_univ _, ?_⟩
  ext i
  simp

/-- The ring of coefficients of two generic polynomials with monomials in `monomials g`. -/
abbrev Coeffs : Type (max u v) := MvPolynomial (monomials g ⊕ monomials g) R

/-- The generic polynomial with coefficients the variables `inl m` (resp. `inr m`). -/
noncomputable def generic (b : Bool) : MvPolynomial σ (Coeffs g) :=
  ∑ m : monomials g, monomial m.1 (X (if b then Sum.inl m else Sum.inr m))

/-- The relations `h₁ h₂ = g` between the coefficients of two generic polynomials. -/
noncomputable def relations : Ideal (Coeffs g) :=
  Ideal.span (Set.range fun μ : σ →₀ ℕ ↦
    (generic g true * generic g false - map (algebraMap R (Coeffs g)) g).coeff μ)

/-- The coefficient of `X^{m₁}` in `h₁` times that of `X^{m₂}` in `h₂`, in the quotient. -/
noncomputable def leadingProduct (m₁ m₂ : monomials g) : Coeffs g ⧸ relations g :=
  Ideal.Quotient.mk _ (X (Sum.inl m₁) * X (Sum.inr m₂))

/-- The `R`-algebra whose points over a field `K` are the factorizations `g = h₁ h₂` in
`K[X]` with `h₁`, `h₂` supported in `monomials g` and with nonzero coefficients at `X^{m₁}`,
`X^{m₂}`. -/
abbrev factorAlgebra (m₁ m₂ : monomials g) : Type (max u v) :=
  Localization.Away (leadingProduct g m₁ m₂)

/-- The primes `𝔭` of `R` over which `g` has a factorization into two non-constant polynomials
supported in `monomials g`, over some field. -/
def badSet : Set (PrimeSpectrum R) :=
  ⋃ (m₁ : monomials g) (m₂ : monomials g) (_ : m₁.1 ≠ 0 ∧ m₂.1 ≠ 0),
    Set.range (PrimeSpectrum.comap (algebraMap R (factorAlgebra g m₁ m₂)))

/-- A polynomial supported in `monomials g` is the image of the generic polynomial under the
evaluation of its variables at its coefficients. -/
lemma map_generic {K : Type w} [CommRing K] (ψ : Coeffs g →+* K) (b : Bool)
    (h : MvPolynomial σ K) (hh : ∀ m ∈ h.support, m ∈ monomials g)
    (hψ : ∀ m : monomials g, ψ (X (if b then Sum.inl m else Sum.inr m)) = h.coeff m.1) :
    map ψ (generic g b) = h := by
  classical
  rw [generic, map_sum]
  simp only [map_monomial, hψ]
  rw [Finset.sum_coe_sort (monomials g) fun m ↦ monomial m (h.coeff m)]
  conv_rhs => rw [h.as_sum]
  exact (Finset.sum_subset hh (fun m _ hm ↦ by rw [notMem_support_iff.mp hm, monomial_zero])).symm

/-- **Universal property of `factorAlgebra`**: a factorization `map φ g = h₁ h₂` over a field `K`,
with `h₁`, `h₂` supported in `monomials g` and with nonzero coefficients at `X^{m₁}`, `X^{m₂}`,
gives a ring map `factorAlgebra g m₁ m₂ ⟶ K` extending `φ`; so `ker φ` lies in `badSet g`. -/
lemma ker_mem_badSet {K : Type w} [Field K] (φ : R →+* K) (h₁ h₂ : MvPolynomial σ K)
    (hh₁ : ∀ m ∈ h₁.support, m ∈ monomials g) (hh₂ : ∀ m ∈ h₂.support, m ∈ monomials g)
    (hprod : h₁ * h₂ = map φ g) (m₁ m₂ : monomials g) (hm : m₁.1 ≠ 0 ∧ m₂.1 ≠ 0)
    (hc₁ : h₁.coeff m₁.1 ≠ 0) (hc₂ : h₂.coeff m₂.1 ≠ 0) :
    (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum R) ∈ badSet g := by
  let ψ₀ : Coeffs g →+* K :=
    eval₂Hom φ fun s ↦ Sum.elim (fun m ↦ h₁.coeff m.1) (fun m ↦ h₂.coeff m.1) s
  have hψC : ψ₀.comp (algebraMap R (Coeffs g)) = φ := by
    ext r
    simp [ψ₀]
  have hm₁ : map ψ₀ (generic g true) = h₁ := map_generic g ψ₀ true h₁ hh₁ fun m ↦ by simp [ψ₀]
  have hm₂ : map ψ₀ (generic g false) = h₂ := map_generic g ψ₀ false h₂ hh₂ fun m ↦ by simp [ψ₀]
  have hJ : ∀ a ∈ relations g, ψ₀ a = 0 := by
    intro a ha
    refine Submodule.span_induction (fun x hx ↦ ?_) (map_zero _) (fun x y _ _ hx hy ↦ ?_)
      (fun c x _ hx ↦ ?_) ha
    · obtain ⟨μ, rfl⟩ := hx
      rw [← coeff_map, map_sub, map_mul, hm₁, hm₂, map_map, hψC, hprod, sub_self, coeff_zero]
    · rw [map_add, hx, hy, add_zero]
    · rw [smul_eq_mul, map_mul, hx, mul_zero]
  let ψ₁ : Coeffs g ⧸ relations g →+* K := Ideal.Quotient.lift _ ψ₀ hJ
  have hu : IsUnit (ψ₁ (leadingProduct g m₁ m₂)) := by
    refine isUnit_iff_ne_zero.mpr ?_
    simp only [leadingProduct, ψ₁, Ideal.Quotient.lift_mk, map_mul]
    simpa [ψ₀] using mul_ne_zero hc₁ hc₂
  let ψ : factorAlgebra g m₁ m₂ →+* K := IsLocalization.Away.lift _ hu
  have hψ : ψ.comp (algebraMap R (factorAlgebra g m₁ m₂)) = φ := by
    ext r
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R (Coeffs g ⧸ relations g),
      IsLocalization.Away.lift_eq, IsScalarTower.algebraMap_apply R (Coeffs g)]
    change ψ₁ (Ideal.Quotient.mk _ _) = φ r
    rw [Ideal.Quotient.lift_mk]
    exact congrArg (fun f ↦ f r) hψC
  refine Set.mem_iUnion.mpr ⟨m₁, Set.mem_iUnion.mpr ⟨m₂, Set.mem_iUnion.mpr ⟨hm,
    ⟨⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩, ?_⟩⟩⟩⟩
  ext1
  change Ideal.comap _ (RingHom.ker ψ) = RingHom.ker φ
  rw [RingHom.comap_ker, hψ]

lemma coeff_generic (b : Bool) (m : monomials g) :
    (generic g b).coeff m.1 = X (if b then Sum.inl m else Sum.inr m) := by
  classical
  rw [generic, coeff_sum]
  simp_rw [coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro m' _ hm'
    rw [ite_eq_right_iff]
    intro h
    exact absurd (Subtype.ext h) hm'
  · intro h
    exact absurd (Finset.mem_univ m) h

instance [IsNoetherianRing R] (m₁ m₂ : monomials g) :
    Algebra.FinitePresentation R (factorAlgebra g m₁ m₂) := by
  have : Algebra.FiniteType R (Coeffs g ⧸ relations g) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R (relations g))
      (Ideal.Quotient.mkₐ_surjective R _)
  have : Algebra.FinitePresentation R (Coeffs g ⧸ relations g) :=
    Algebra.FinitePresentation.of_finiteType.mp this
  have : Algebra.FinitePresentation (Coeffs g ⧸ relations g) (factorAlgebra g m₁ m₂) :=
    IsLocalization.Away.finitePresentation (leadingProduct g m₁ m₂)
  exact Algebra.FinitePresentation.trans R (Coeffs g ⧸ relations g) _

/-- `badSet g` is constructible (Chevalley's theorem). -/
lemma isConstructible_badSet [IsNoetherianRing R] : IsConstructible (badSet g) := by
  refine IsConstructible.iUnion fun m₁ ↦ IsConstructible.iUnion fun m₂ ↦
    IsConstructible.iUnion fun _ ↦ ?_
  rw [← Set.image_univ]
  exact PrimeSpectrum.isConstructible_comap_image
    (RingHom.finitePresentation_algebraMap.mpr inferInstance) IsConstructible.univ

omit [Fintype σ] [DecidableEq σ] in
/-- A polynomial over a reduced ring with a nonzero coefficient at a nonconstant monomial is not
a unit. -/
lemma not_isUnit_of_coeff_ne_zero {K : Type w} [CommRing K] [IsReduced K] {h : MvPolynomial σ K}
    {m : σ →₀ ℕ} (hm : m ≠ 0) (hc : h.coeff m ≠ 0) : ¬ IsUnit h := by
  classical
  rw [isUnit_iff_eq_C_of_isReduced]
  rintro ⟨r, -, rfl⟩
  rw [coeff_C] at hc
  split_ifs at hc with h
  · exact hm h.symm
  · exact hc rfl

omit [Fintype σ] [DecidableEq σ] in
/-- A nonzero non-unit polynomial over a field has a nonzero coefficient at a nonconstant
monomial. -/
lemma exists_coeff_ne_zero_of_not_isUnit {K : Type w} [Field K] {h : MvPolynomial σ K}
    (h0 : h ≠ 0) (hu : ¬ IsUnit h) : ∃ m ≠ 0, h.coeff m ≠ 0 := by
  classical
  by_contra hc
  push Not at hc
  have e : h = C (h.coeff 0) := by
    ext m
    by_cases hm : m = 0
    · subst hm
      simp
    · rw [coeff_C]
      split_ifs with h
      · exact absurd h.symm hm
      · exact hc m hm
  apply hu
  rw [e]
  refine (isUnit_iff_ne_zero.mpr fun h00 ↦ h0 ?_).map (C : K →+* MvPolynomial σ K)
  rw [e, h00, C_0]

variable [IsDomain R]

/-- The generic point of `Spec R` is not in `badSet g` when `g` is irreducible over an
algebraically closed field `Ω ⊇ R` (by the Nullstellensatz, a point of `factorAlgebra` over the
generic point gives a factorization of `g` over `Ω`). -/
lemma bot_notMem_badSet [IsNoetherianRing R] {Ω : Type w} [Field Ω] [IsAlgClosed Ω]
    [Algebra R Ω] (hinj : Function.Injective (algebraMap R Ω))
    (hg : Irreducible (map (algebraMap R Ω) g)) :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∉ badSet g := by
  intro hmem
  simp only [badSet, Set.mem_iUnion] at hmem
  obtain ⟨m₁, m₂, hm, 𝔔, h𝔔⟩ := hmem
  -- `U ⊗_R Ω` is nonzero
  have hcomap : Ideal.comap (algebraMap R (factorAlgebra g m₁ m₂)) 𝔔.asIdeal = ⊥ :=
    congrArg PrimeSpectrum.asIdeal h𝔔
  have hinjQ : Function.Injective
      (algebraMap R (factorAlgebra g m₁ m₂ ⧸ 𝔔.asIdeal)) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    have : r ∈ Ideal.comap (algebraMap R (factorAlgebra g m₁ m₂)) 𝔔.asIdeal := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      exact hr
    rw [hcomap] at this
    exact this
  have : Nontrivial ((factorAlgebra g m₁ m₂ ⧸ 𝔔.asIdeal) ⊗[R] Ω) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain R _ _ hinjQ hinj
  have : Nontrivial (Ω ⊗[R] factorAlgebra g m₁ m₂) :=
    ((Algebra.TensorProduct.comm R Ω _).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R Ω)
        (Ideal.Quotient.mkₐ R 𝔔.asIdeal)).toRingHom).domain_nontrivial
  -- a point over `Ω` (Nullstellensatz)
  obtain ⟨χ⟩ := IsAlgClosed.nonempty_algHom Ω (Ω ⊗[R] factorAlgebra g m₁ m₂)
  let ψ : factorAlgebra g m₁ m₂ →+* Ω :=
    χ.toRingHom.comp (Algebra.TensorProduct.includeRight.toRingHom)
  have hψ (r : R) : ψ (algebraMap R _ r) = algebraMap R Ω r := by
    simp only [ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, IsScalarTower.algebraMap_apply R Ω (Ω ⊗[R] factorAlgebra g m₁ m₂),
      Algebra.algebraMap_self, RingHom.id_apply]
  let ψ₀ : Coeffs g →+* Ω :=
    ψ.comp ((algebraMap (Coeffs g ⧸ relations g) _).comp (Ideal.Quotient.mk _))
  have hψ₀C : ψ₀.comp (algebraMap R (Coeffs g)) = algebraMap R Ω := by
    ext r
    simp only [ψ₀, RingHom.comp_apply]
    rw [← hψ, IsScalarTower.algebraMap_apply R (Coeffs g ⧸ relations g) (factorAlgebra g m₁ m₂)]
    rfl
  let h₁ := map ψ₀ (generic g true)
  let h₂ := map ψ₀ (generic g false)
  have hprod : h₁ * h₂ = map (algebraMap R Ω) g := by
    rw [← sub_eq_zero, ← hψ₀C, ← map_map, ← map_mul, ← map_sub]
    ext μ
    rw [coeff_map, coeff_zero]
    simp only [ψ₀, RingHom.comp_apply]
    have hmem : coeff μ (generic g true * generic g false - map (algebraMap R (Coeffs g)) g) ∈
        relations g := Ideal.subset_span (Set.mem_range_self μ)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero, map_zero]
  -- the leading coefficients are nonzero
  have hunit : IsUnit (ψ₀ (X (Sum.inl m₁)) * ψ₀ (X (Sum.inr m₂))) := by
    rw [← map_mul]
    exact (IsLocalization.Away.algebraMap_isUnit (leadingProduct g m₁ m₂)).map ψ
  have hc₁ : h₁.coeff m₁.1 ≠ 0 := by
    rw [coeff_map, coeff_generic]
    exact left_ne_zero_of_mul hunit.ne_zero
  have hc₂ : h₂.coeff m₂.1 ≠ 0 := by
    rw [coeff_map, coeff_generic]
    exact right_ne_zero_of_mul hunit.ne_zero
  rcases hg.isUnit_or_isUnit hprod.symm with h | h
  · exact not_isUnit_of_coeff_ne_zero hm.1 hc₁ h
  · exact not_isUnit_of_coeff_ne_zero hm.2 hc₂ h

end BertiniNoether

open BertiniNoether in
/-- **Bertini–Noether** (Fried–Jarden, Prop. 9.4.3): let `R` be a noetherian domain and
`g ∈ R[X_σ]` (`σ` finite) whose image over some algebraically closed field `Ω ⊇ R` is irreducible.
Then there is `a ≠ 0` in `R` such that for every ring map `φ : R ⟶ K` to a field with
`φ a ≠ 0`, the image of `g` in `K[X_σ]` is irreducible. -/
theorem exists_ne_zero_forall_irreducible_map {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {σ : Type v} [Finite σ] (g : MvPolynomial σ R) {Ω : Type w} [Field Ω]
    [IsAlgClosed Ω] [Algebra R Ω] (hinj : Function.Injective (algebraMap R Ω))
    (hg : Irreducible (map (algebraMap R Ω) g)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (K : Type*) [Field K] (φ : R →+* K), φ a ≠ 0 → Irreducible (map φ g) := by
  classical
  have := Fintype.ofFinite σ
  -- a neighbourhood `D(a')` of the generic point misses `badSet g`
  have hη : IsGenericPoint (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) Set.univ := by
    rw [isGenericPoint_iff_specializes]
    exact fun x ↦ ⟨fun _ ↦ trivial, fun _ ↦ (PrimeSpectrum.le_iff_specializes _ x).mp bot_le⟩
  obtain ⟨W, hWo, hηW, hW⟩ := (isConstructible_badSet g).compl.exists_isOpen_of_isGenericPoint
    isClosed_univ hη (bot_notMem_badSet g hinj hg)
  obtain ⟨_, ⟨a', rfl⟩, ha'η, ha'W⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hηW hWo
  have ha' : a' ≠ 0 := fun h ↦ ha'η (by simp [h])
  -- a nonconstant coefficient `c` of `g`
  have hg0 : map (algebraMap R Ω) g ≠ 0 := hg.ne_zero
  obtain ⟨m₀, hm₀, hc₀⟩ := exists_coeff_ne_zero_of_not_isUnit hg0 hg.not_isUnit
  rw [coeff_map] at hc₀
  have hc : g.coeff m₀ ≠ 0 := fun h ↦ hc₀ (by rw [h, map_zero])
  refine ⟨a' * g.coeff m₀, mul_ne_zero ha' hc, fun K _ φ hφ ↦ ?_⟩
  have hφa' : φ a' ≠ 0 := fun h ↦ hφ (by rw [map_mul, h, zero_mul])
  have hφc : φ (g.coeff m₀) ≠ 0 := fun h ↦ hφ (by rw [map_mul, h, mul_zero])
  have hgφc : (map φ g).coeff m₀ ≠ 0 := by rwa [coeff_map]
  have hgφ0 : map φ g ≠ 0 := fun h ↦ hgφc (by rw [h, coeff_zero])
  refine ⟨not_isUnit_of_coeff_ne_zero hm₀ hgφc, fun h₁ h₂ hprod ↦ ?_⟩
  by_contra hnu
  push Not at hnu
  obtain ⟨hu₁, hu₂⟩ := hnu
  have h₁0 : h₁ ≠ 0 := fun h ↦ hgφ0 (by rw [hprod, h, zero_mul])
  have h₂0 : h₂ ≠ 0 := fun h ↦ hgφ0 (by rw [hprod, h, mul_zero])
  obtain ⟨n₁, hn₁, hd₁⟩ := exists_coeff_ne_zero_of_not_isUnit h₁0 hu₁
  obtain ⟨n₂, hn₂, hd₂⟩ := exists_coeff_ne_zero_of_not_isUnit h₂0 hu₂
  -- the factors are supported in `monomials g`
  have hdeg : h₁.totalDegree + h₂.totalDegree ≤ g.totalDegree := by
    rw [← totalDegree_mul_of_isDomain h₁0 h₂0, ← hprod]
    exact Finset.sup_mono (support_map_subset _ _)
  have hsupp (h : MvPolynomial σ K) (hle : h.totalDegree ≤ g.totalDegree) :
      ∀ m ∈ h.support, m ∈ monomials g := fun m hm ↦
    mem_monomials g fun i ↦ ((Finsupp.le_degree i m).trans (le_totalDegree hm)).trans hle
  have hs₁ := hsupp h₁ (le_trans (Nat.le_add_right _ _) hdeg)
  have hs₂ := hsupp h₂ (le_trans (Nat.le_add_left _ _) hdeg)
  have hn₁' : n₁ ∈ monomials g := hs₁ n₁ (mem_support_iff.mpr hd₁)
  have hn₂' : n₂ ∈ monomials g := hs₂ n₂ (mem_support_iff.mpr hd₂)
  have hbad := ker_mem_badSet g φ h₁ h₂ hs₁ hs₂ hprod.symm ⟨n₁, hn₁'⟩ ⟨n₂, hn₂'⟩ ⟨hn₁, hn₂⟩ hd₁ hd₂
  exact hW ⟨ha'W (show a' ∉ RingHom.ker φ from hφa'), trivial⟩ hbad

end MvPolynomial
