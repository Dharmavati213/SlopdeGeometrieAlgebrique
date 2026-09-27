/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.CechMonomial
import SGA.Foundations.Cohomology.AffineOpenVanishing
import SGA.Foundations.Cohomology.Statements
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Cohomology of the structure sheaf of projective space

Let `A` be a commutative ring, `σ` a finite non-empty type and `X = Proj A[xᵢ : i ∈ σ]`. We compute
the cohomology of `𝒪_X` with the Čech complex of the standard affine cover by the `D₊(xᵢ)`
(Stacks Project, Tag 01XT; EGA III 2.1.12; Hartshorne III.5.1): `Γ(X, 𝒪_X) = A` and
`Hᵖ(X, 𝒪_X) = 0` for `p > 0`. In particular `ProjectiveSpaceStructureSheafStatement` holds.

All the rings `Γ(D₊(x_I), 𝒪_X) = A[xᵢ]_{(x_I)}` embed into the Laurent polynomial ring
`A[xᵢ^{±1}]` (`projectiveSpace.Laurent`), with image the span of the monomials `x^μ` of degree `0`
with `μᵢ ≥ 0` for `i ∉ I`. The Čech complex is then exact monomial by monomial
(`TopCat.Presheaf.exists_cechDConst_eq_of_support`).

## Main results

* `AlgebraicGeometry.projectiveSpace.sectionToLaurent`: the embedding of `Γ(V, 𝒪_X)` into
  `A[xᵢ^{±1}]`, for `V` containing the torus `D₊(∏ xᵢ)`.
* `AlgebraicGeometry.projectiveSpace.H_structureSheaf_subsingleton`: `Hᵖ(X, 𝒪_X) = 0` for `p > 0`.
* `AlgebraicGeometry.projectiveSpace.isIso_toSpecZero_appTop`: `A = Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.projectiveSpaceStructureSheafStatement`.
-/

universe v u

open CategoryTheory TopologicalSpace Opposite MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

/-- The structure sheaf of a scheme, as a module over itself, is quasi-coherent. -/
instance CohomologyAux.isQuasicoherent_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Limits.coproductUniqueIso fun _ : PUnit ↦ SheafOfModules.unit X.ringCatSheaf)
    (inferInstanceAs (SheafOfModules.free (R := X.ringCatSheaf) PUnit).IsQuasicoherent)

namespace projectiveSpace

variable (σ : Type v) (A : Type u) [CommRing A]

section Laurent

/-- The exponent map `ℕ^{(σ)} → ℤ^σ`. -/
def expHom : (σ →₀ ℕ) →+ (σ → ℤ) where
  toFun ν i := ν i
  map_zero' := by ext; simp
  map_add' ν ν' := by ext; simp

variable {σ} in
@[simp]
lemma expHom_apply (ν : σ →₀ ℕ) (i : σ) : expHom σ ν i = ν i := rfl

lemma expHom_injective : Function.Injective (expHom σ) :=
  fun ν ν' h ↦ Finsupp.ext fun i ↦ by
    have := congrFun h i
    simp only [expHom_apply, Nat.cast_inj] at this
    exact this

variable {σ} in
lemma mem_range_expHom [Finite σ] {μ : σ → ℤ} (h : ∀ i, 0 ≤ μ i) : μ ∈ Set.range (expHom σ) :=
  have := Fintype.ofFinite σ
  ⟨Finsupp.equivFunOnFinite.symm fun i ↦ (μ i).toNat, funext fun i ↦ by simp [h i]⟩

/-- The Laurent polynomial ring `A[xᵢ^{±1} : i ∈ σ]`. -/
abbrev Laurent := AddMonoidAlgebra A (σ → ℤ)

/-- The inclusion `A[xᵢ] → A[xᵢ^{±1}]`. -/
noncomputable def toLaurent : MvPolynomial σ A →+* Laurent σ A :=
  AddMonoidAlgebra.mapDomainRingHom A (expHom σ)

variable {σ A}

lemma toLaurent_injective : Function.Injective (toLaurent σ A) :=
  AddMonoidAlgebra.mapDomain_injective (expHom_injective σ)

lemma coeff_toLaurent_expHom (p : MvPolynomial σ A) (ν : σ →₀ ℕ) :
    (toLaurent σ A p).coeff (expHom σ ν) = p.coeff ν :=
  Finsupp.mapDomain_apply (expHom_injective σ) _ _

lemma coeff_toLaurent_of_notMem (p : MvPolynomial σ A) {μ : σ → ℤ}
    (hμ : μ ∉ Set.range (expHom σ)) : (toLaurent σ A p).coeff μ = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ hμ

lemma toLaurent_monomial (ν : σ →₀ ℕ) (a : A) :
    toLaurent σ A (monomial ν a) = AddMonoidAlgebra.single (expHom σ ν) a :=
  AddMonoidAlgebra.mapDomain_single

/-- A Laurent polynomial all of whose exponents are non-negative is a polynomial. -/
lemma exists_toLaurent_eq [Finite σ] {ℓ : Laurent σ A} (h : ∀ μ ∈ ℓ.coeff.support, ∀ i, 0 ≤ μ i) :
    ∃ p, toLaurent σ A p = ℓ :=
  ⟨AddMonoidAlgebra.comapDomain _ (expHom_injective σ) ℓ,
    AddMonoidAlgebra.mapDomain_comapDomain (fun μ hμ ↦ mem_range_expHom (h μ hμ)) _⟩

variable (σ) in
/-- The indicator function of `I ⊆ σ`, the exponent of `x_I = ∏_{i ∈ I} xᵢ`. -/
def indicator [DecidableEq σ] (I : Finset σ) : σ → ℤ := fun i ↦ if i ∈ I then 1 else 0

variable (σ A) in
/-- The monomial `x_I = ∏_{i ∈ I} xᵢ`. -/
noncomputable def prodX (I : Finset σ) : MvPolynomial σ A := ∏ i ∈ I, X i

lemma prodX_mem (I : Finset σ) : prodX σ A I ∈ homogeneousSubmodule σ A I.card := by
  rw [mem_homogeneousSubmodule, prodX]
  simpa using IsHomogeneous.prod I (fun i ↦ (X i : MvPolynomial σ A)) (fun _ ↦ 1)
    fun i _ ↦ isHomogeneous_X A i

lemma toLaurent_X [DecidableEq σ] (i : σ) :
    toLaurent σ A (X i) = AddMonoidAlgebra.single (Pi.single i 1) 1 := by
  rw [X, toLaurent_monomial]
  congr 1
  funext j
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

lemma toLaurent_prodX [DecidableEq σ] (I : Finset σ) :
    toLaurent σ A (prodX σ A I) = AddMonoidAlgebra.single (indicator σ I) 1 := by
  rw [prodX, map_prod]
  simp only [toLaurent_X]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one]
  congr 1
  funext j
  simp [indicator, Finset.sum_apply, Pi.single_apply]

variable (σ A) in
/-- The Laurent monomial `x_I⁻¹`. -/
noncomputable def invX [DecidableEq σ] (I : Finset σ) : Laurent σ A :=
  AddMonoidAlgebra.single (-indicator σ I) 1

lemma toLaurent_prodX_mul_invX [DecidableEq σ] (I : Finset σ) :
    toLaurent σ A (prodX σ A I) * invX σ A I = 1 := by
  rw [toLaurent_prodX, invX, AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]
  rfl

lemma coeff_mul_single_one (x : Laurent σ A) (m μ : σ → ℤ) :
    (x * AddMonoidAlgebra.single m 1).coeff μ = x.coeff (μ - m) := by
  conv_lhs => rw [← sub_add_cancel μ m]
  rw [AddMonoidAlgebra.coeff_mul_single_add, mul_one]

lemma invX_pow [DecidableEq σ] (I : Finset σ) (n : ℕ) :
    invX σ A I ^ n = AddMonoidAlgebra.single (-(n • indicator σ I)) 1 := by
  rw [invX, AddMonoidAlgebra.single_pow, one_pow, smul_neg]

lemma sum_indicator [Fintype σ] [DecidableEq σ] (I : Finset σ) :
    ∑ i, indicator σ I i = I.card := by
  simp [indicator]

end Laurent

section Away

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ A} [DecidableEq σ]

/-- The exponents `μ` of the Laurent monomials `x^μ` which lie in `A[xᵢ]_{(x_I)}`: those of
degree `0` with `μᵢ ≥ 0` for `i ∉ I`. -/
def monomialSet [Fintype σ] (I : Finset σ) : Set (σ → ℤ) :=
  {μ | ∑ i, μ i = 0 ∧ ∀ i ∉ I, 0 ≤ μ i}

variable (σ A) in
/-- The embedding `A[xᵢ]_{(x_I)} → A[xᵢ^{±1}]` of the degree-`0` part of the localization at
`x_I`. -/
noncomputable def awayToLaurent (I : Finset σ) :
    Away (homogeneousSubmodule σ A) (prodX σ A I) →+* Laurent σ A :=
  (Localization.awayLift (toLaurent σ A) (prodX σ A I)
    (isUnit_iff_exists_inv.mpr ⟨_, toLaurent_prodX_mul_invX I⟩)).comp (algebraMap _ _)

lemma awayToLaurent_mk (I : Finset σ) {d : ℕ} (hf : prodX σ A I ∈ homogeneousSubmodule σ A d)
    (n : ℕ) (a : MvPolynomial σ A) (ha : a ∈ homogeneousSubmodule σ A (n • d)) :
    awayToLaurent σ A I (Away.mk _ hf n a ha) = toLaurent σ A a * invX σ A I ^ n := by
  simp only [awayToLaurent, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  exact Localization.awayLift_mk _ _ _ _ (toLaurent_prodX_mul_invX I) n

lemma awayToLaurent_injective (I : Finset σ) : Function.Injective (awayToLaurent σ A I) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (prodX_mem I) y
  rw [awayToLaurent_mk] at hy
  have h0 : toLaurent σ A a = 0 := by
    have := congrArg (· * toLaurent σ A (prodX σ A I) ^ n) hy
    simpa only [zero_mul, mul_assoc, ← mul_pow, mul_comm (invX σ A I),
      toLaurent_prodX_mul_invX, one_pow, mul_one] using this
  obtain rfl : a = 0 := toLaurent_injective (h0.trans (map_zero _).symm)
  ext
  simp [Localization.mk_zero]

omit [DecidableEq σ] in
lemma sum_expHom [Fintype σ] (ν : σ →₀ ℕ) : ∑ i, expHom σ ν i = ν.degree := by
  rw [Finsupp.degree_eq_sum]
  simp

lemma sum_expHom_sub [Fintype σ] (ν : σ →₀ ℕ) (n : ℕ) (I : Finset σ) :
    ∑ i, (expHom σ ν - n • indicator σ I) i = (ν.degree : ℤ) - n * I.card := by
  have h (i : σ) : (n • indicator σ I) i = n * indicator σ I i := by simp
  simp only [Pi.sub_apply, h, Finset.sum_sub_distrib, sum_expHom, ← Finset.mul_sum, sum_indicator]

omit [DecidableEq σ] in
lemma degree_of_mem_support {n : ℕ} {a : MvPolynomial σ A}
    (ha : a ∈ homogeneousSubmodule σ A n) {ν : σ →₀ ℕ} (hν : a.coeff ν ≠ 0) : ν.degree = n := by
  have := (mem_homogeneousSubmodule _ _).mp ha hν
  rwa [Finsupp.degree_eq_weight_one]

lemma range_awayToLaurent [Fintype σ] (I : Finset σ) :
    Set.range (awayToLaurent σ A I) = {ℓ | ↑ℓ.coeff.support ⊆ monomialSet I} := by
  ext ℓ
  refine ⟨?_, fun hℓ ↦ ?_⟩
  · rintro ⟨y, rfl⟩ μ hμ
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (prodX_mem I) y
    rw [Finset.mem_coe, Finsupp.mem_support_iff, awayToLaurent_mk, invX_pow,
      coeff_mul_single_one, sub_neg_eq_add] at hμ
    by_cases hr : μ + n • indicator σ I ∈ Set.range (expHom σ)
    · obtain ⟨ν, hν⟩ := hr
      rw [← hν, coeff_toLaurent_expHom] at hμ
      have hdeg := degree_of_mem_support ha hμ
      have hμν : μ = expHom σ ν - n • indicator σ I := by rw [hν]; abel
      refine ⟨?_, fun i hi ↦ ?_⟩
      · rw [hμν, sum_expHom_sub, hdeg]
        simp
      · rw [hμν]
        simp [indicator, hi]
    · exact absurd (coeff_toLaurent_of_notMem a hr) hμ
  · -- a common bound for the negative exponents of `ℓ`
    set n : ℕ := ∑ μ ∈ ℓ.coeff.support, ∑ i, (-μ i).toNat with hn
    have hbound : ∀ μ ∈ ℓ.coeff.support, ∀ i, -μ i ≤ n := fun μ hμ i ↦ by
      refine (Int.self_le_toNat (-μ i)).trans (Nat.cast_le.mpr ?_)
      exact (Finset.single_le_sum (f := fun j ↦ (-μ j).toNat) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ i)).trans (Finset.single_le_sum
          (f := fun μ : σ → ℤ ↦ ∑ j, (-μ j).toNat) (fun _ _ ↦ Nat.zero_le _) hμ)
    set ℓ' := ℓ * AddMonoidAlgebra.single (n • indicator σ I) 1 with hℓ'
    have hcoeff (μ : σ → ℤ) : ℓ'.coeff μ = ℓ.coeff (μ - n • indicator σ I) :=
      coeff_mul_single_one _ _ _
    obtain ⟨a, ha⟩ : ∃ a, toLaurent σ A a = ℓ' := by
      refine exists_toLaurent_eq fun μ hμ i ↦ ?_
      rw [Finsupp.mem_support_iff, hcoeff] at hμ
      have h1 := hbound _ (Finsupp.mem_support_iff.mpr hμ) i
      have h2 := (hℓ (Finsupp.mem_support_iff.mpr hμ)).2 i
      by_cases hi : i ∈ I
      · have hind : (n • indicator σ I) i = (n : ℤ) := by simp [indicator, hi]
        rw [Pi.sub_apply, hind] at h1
        linarith
      · simpa [indicator, hi] using h2 hi
    have hhom : a ∈ homogeneousSubmodule σ A (n • I.card) := by
      rw [mem_homogeneousSubmodule]
      intro ν hν
      change Finsupp.weight (fun _ ↦ 1) ν = _
      rw [← Finsupp.degree_eq_weight_one]
      rw [← coeff_toLaurent_expHom, ha, hcoeff] at hν
      have h := (hℓ (Finsupp.mem_support_iff.mpr hν)).1
      rw [sum_expHom_sub, sub_eq_zero] at h
      rw [smul_eq_mul]
      exact_mod_cast h
    refine ⟨Away.mk _ (prodX_mem I) n a hhom, ?_⟩
    rw [awayToLaurent_mk, ha, hℓ', invX_pow, mul_assoc, AddMonoidAlgebra.single_mul_single,
      add_neg_cancel, mul_one]
    exact mul_one ℓ

lemma prodX_univ_eq [Fintype σ] (I : Finset σ) :
    prodX σ A Finset.univ = prodX σ A I * prodX σ A Iᶜ :=
  (Finset.prod_mul_prod_compl I _).symm

lemma awayToLaurent_awayMap [Fintype σ] (I : Finset σ) (y : Away _ (prodX σ A I)) :
    awayToLaurent σ A Finset.univ (awayMap _ (prodX_mem Iᶜ) (prodX_univ_eq I) y) =
      awayToLaurent σ A I y := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (prodX_mem I) y
  rw [awayMap_mk, awayToLaurent_mk, awayToLaurent_mk, map_mul, map_pow, mul_assoc, ← mul_pow,
    toLaurent_prodX, invX, invX, AddMonoidAlgebra.single_mul_single, one_mul]
  congr 4
  funext i
  by_cases hi : i ∈ I <;> simp [indicator, hi]

end Away

section Sections

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ A} [Fintype σ] [DecidableEq σ] [Nonempty σ]

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
lemma presheaf_map_map_apply {X : Scheme.{u}} {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁)
    (h₂ : V₃ ≤ V₂) (r : Γ(X, V₁)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op r) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op r := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

omit [DecidableEq σ] in
lemma card_univ_pos : 0 < (Finset.univ : Finset σ).card := Finset.univ_nonempty.card_pos

variable (σ A) in
/-- The torus `D₊(∏ᵢ xᵢ)` of `Proj A[xᵢ]`. -/
noncomputable abbrev torus : (Proj (homogeneousSubmodule σ A)).Opens :=
  Proj.basicOpen _ (prodX σ A Finset.univ)

variable (σ A) in
/-- The embedding of the ring of sections of `𝒪` over an open `V` containing the torus into
the Laurent polynomial ring: restrict to the torus `D₊(∏ᵢ xᵢ)`, whose ring of sections is
`A[xᵢ]_{(∏ᵢ xᵢ)} ⊆ A[xᵢ^{±1}]`. -/
noncomputable def sectionToLaurent (V : (Proj (homogeneousSubmodule σ A)).Opens)
    (hV : torus σ A ≤ V) : Γ(Proj (homogeneousSubmodule σ A), V) →+* Laurent σ A :=
  (awayToLaurent σ A Finset.univ).comp
    ((Proj.basicOpenIsoAway _ (prodX σ A Finset.univ) (prodX_mem _) card_univ_pos).inv.hom.comp
      ((Proj (homogeneousSubmodule σ A)).presheaf.map (homOfLE hV).op).hom)

lemma sectionToLaurent_map {V V' : (Proj (homogeneousSubmodule σ A)).Opens} (hV : torus σ A ≤ V)
    (hV' : torus σ A ≤ V') (h : V' ≤ V) (s : Γ(Proj (homogeneousSubmodule σ A), V)) :
    sectionToLaurent σ A V' hV' ((Proj (homogeneousSubmodule σ A)).presheaf.map (homOfLE h).op s) =
      sectionToLaurent σ A V hV s := by
  simp only [sectionToLaurent, RingHom.coe_comp, Function.comp_apply]
  erw [presheaf_map_map_apply]

omit [DecidableEq σ] [Nonempty σ] in
lemma torus_le_basicOpen_prodX (I : Finset σ) :
    torus σ A ≤ Proj.basicOpen _ (prodX σ A I) := by
  classical
  exact Proj.basicOpen_mono _ _ _ ⟨prodX σ A Iᶜ, prodX_univ_eq I⟩

lemma sectionToLaurent_awayToSection (I : Finset σ) (y : Away _ (prodX σ A I)) :
    sectionToLaurent σ A _ (torus_le_basicOpen_prodX I) (Proj.awayToSection _ _ y) =
      awayToLaurent σ A I y := by
  have h := congrArg (fun φ ↦ φ y)
    (Proj.awayMap_awayToSection (homogeneousSubmodule σ A) (prodX_mem Iᶜ) (prodX_univ_eq I))
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
  simp only [sectionToLaurent, RingHom.coe_comp, Function.comp_apply]
  erw [← h]
  have e := (Proj.basicOpenIsoAway _ _ (prodX_mem (Finset.univ : Finset σ))
    card_univ_pos).hom_inv_id_apply
      (awayMap (homogeneousSubmodule σ A) (prodX_mem Iᶜ) (prodX_univ_eq I) y)
  rw [Proj.basicOpenIsoAway_hom] at e
  erw [e]
  exact awayToLaurent_awayMap I y

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
lemma surjective_awayToSection (I : Finset σ) (hI : I.Nonempty) :
    Function.Surjective (Proj.awayToSection (homogeneousSubmodule σ A) (prodX σ A I)) := by
  intro s
  refine ⟨(Proj.basicOpenIsoAway _ _ (prodX_mem I) hI.card_pos).inv s, ?_⟩
  rw [← Proj.basicOpenIsoAway_hom _ _ (prodX_mem I) hI.card_pos, Iso.inv_hom_id_apply]

lemma injective_sectionToLaurent_of_eq {V : (Proj (homogeneousSubmodule σ A)).Opens}
    {I : Finset σ} (hI : I.Nonempty) (hV : V = Proj.basicOpen _ (prodX σ A I))
    (hV' : torus σ A ≤ V) : Function.Injective (sectionToLaurent σ A V hV') := by
  subst hV
  intro s t hst
  obtain ⟨y, rfl⟩ := surjective_awayToSection I hI s
  obtain ⟨z, rfl⟩ := surjective_awayToSection I hI t
  rw [sectionToLaurent_awayToSection, sectionToLaurent_awayToSection] at hst
  rw [awayToLaurent_injective I hst]

lemma range_sectionToLaurent_of_eq {V : (Proj (homogeneousSubmodule σ A)).Opens}
    {I : Finset σ} (hI : I.Nonempty) (hV : V = Proj.basicOpen _ (prodX σ A I))
    (hV' : torus σ A ≤ V) :
    Set.range (sectionToLaurent σ A V hV') = {ℓ | ↑ℓ.coeff.support ⊆ monomialSet I} := by
  subst hV
  rw [← range_awayToLaurent I]
  ext ℓ
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨y, rfl⟩ := surjective_awayToSection I hI s
    exact ⟨y, (sectionToLaurent_awayToSection I y).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, sectionToLaurent_awayToSection I y⟩

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
lemma basicOpen_prodX (I : Finset σ) :
    Proj.basicOpen (homogeneousSubmodule σ A) (prodX σ A I) =
      ⨅ i ∈ I, Proj.basicOpen (homogeneousSubmodule σ A) (X i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [prodX]
  | insert a I ha ih => rw [prodX, Finset.prod_insert ha, Proj.basicOpen_mul, ← prodX, ih,
      Finset.iInf_insert]

end Sections

section Cech

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ A} [Fintype σ] [DecidableEq σ] [Nonempty σ]

variable (σ A) in
/-- The standard affine cover of `Proj A[xᵢ]` by the `D₊(xᵢ)`. -/
noncomputable abbrev stdCover : σ → (Proj (homogeneousSubmodule σ A)).Opens :=
  fun i ↦ Proj.basicOpen _ (X i)

omit [Fintype σ] [Nonempty σ] in
lemma cechOpen_stdCover {m : ℕ} (x : Fin (m + 1) → σ) :
    TopCat.Presheaf.cechOpen (stdCover σ A) x =
      Proj.basicOpen _ (prodX σ A (Finset.univ.image x)) := by
  rw [basicOpen_prodX]
  refine le_antisymm (le_iInf₂ fun i hi ↦ ?_) (le_iInf fun a ↦ ?_)
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
    exact TopCat.Presheaf.cechOpen_le _ x a
  · exact iInf₂_le (x a) (Finset.mem_image_of_mem x (Finset.mem_univ a))

omit [Fintype σ] [Nonempty σ] in
lemma image_nonempty {m : ℕ} (x : Fin (m + 1) → σ) : (Finset.univ.image x).Nonempty :=
  Finset.univ_nonempty.image x

omit [DecidableEq σ] [Nonempty σ] in
lemma torus_le_cechOpen {m : ℕ} (x : Fin (m + 1) → σ) :
    torus σ A ≤ TopCat.Presheaf.cechOpen (stdCover σ A) x := by
  classical
  rw [cechOpen_stdCover]
  exact torus_le_basicOpen_prodX _

variable (σ A) in
omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
lemma adjoin_range_X :
    Algebra.adjoin (homogeneousSubmodule σ A 0) (Set.range (X : σ → MvPolynomial σ A)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact Subalgebra.algebraMap_mem _
      (⟨C r, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C σ r)⟩ :
        homogeneousSubmodule σ A 0)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

variable (σ A) in
omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
/-- The `D₊(xᵢ)` cover `Proj A[xᵢ]`. -/
lemma iSup_stdCover : ⨆ i, stdCover σ A i = ⊤ :=
  Proj.iSup_basicOpen_eq_top' _ _
    (fun i ↦ ⟨1, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X A i)⟩) (adjoin_range_X σ A)

omit [DecidableEq σ] in
variable (σ) in
/-- For an exponent `μ`, an index `i` with `μᵢ ≥ 0` if there is one. -/
noncomputable def nonnegIndex (μ : σ → ℤ) : σ :=
  haveI := Classical.dec
  if h : ∃ i, 0 ≤ μ i then h.choose else Classical.arbitrary σ

omit [DecidableEq σ] in
lemma nonnegIndex_spec {μ : σ → ℤ} (hμ : ∑ i, μ i = 0) : 0 ≤ μ (nonnegIndex σ μ) := by
  have h : ∃ i, 0 ≤ μ i := by
    by_contra h'
    push Not at h'
    have := Finset.sum_neg (fun i _ ↦ h' i) (Finset.univ_nonempty (α := σ))
    omega
  rw [nonnegIndex, dite_eq_left h]
  exact h.choose_spec

lemma nonnegIndex_mem {m : ℕ} (y : Fin (m + 1) → σ) (μ : σ → ℤ)
    (hμ : μ ∈ monomialSet (Finset.univ.image (Fin.cons (nonnegIndex σ μ) y : Fin (m + 2) → σ))) :
    μ ∈ monomialSet (Finset.univ.image y) := by
  refine ⟨hμ.1, fun i hi ↦ ?_⟩
  by_cases hk : i = nonnegIndex σ μ
  · rw [hk]
    exact nonnegIndex_spec hμ.1
  · refine hμ.2 i fun h ↦ ?_
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
    induction a using Fin.cases with
    | zero => exact hk (by simpa using ha.symm)
    | succ a => exact hi (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, by simpa using ha⟩)

variable (σ A) in
/-- The structure sheaf of `Proj A[xᵢ]`, as a module over itself. -/
noncomputable abbrev structureModule : (Proj (homogeneousSubmodule σ A)).Modules :=
  SheafOfModules.unit _

/-- The embeddings of the terms of the Čech complex of `𝒪` into the Laurent polynomials. -/
noncomputable def cechEmbedding {m : ℕ} (x : Fin (m + 1) → σ) :
    (structureModule σ A).toAbSheaf.obj.obj (op (TopCat.Presheaf.cechOpen (stdCover σ A) x)) →+
      ((σ → ℤ) →₀ A) :=
  AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom.comp
    (sectionToLaurent σ A _ (torus_le_cechOpen x)).toAddMonoidHom

lemma range_cechEmbedding {m : ℕ} (x : Fin (m + 1) → σ) :
    Set.range (cechEmbedding (A := A) x) =
      {f | ↑f.support ⊆ monomialSet (Finset.univ.image x)} := by
  have h := range_sectionToLaurent_of_eq (A := A) (image_nonempty x) (cechOpen_stdCover x)
    (torus_le_cechOpen x)
  ext f
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨s, rfl⟩
    exact (h.le ⟨s, rfl⟩ : _)
  · obtain ⟨s, hs⟩ : AddMonoidAlgebra.ofCoeff f ∈ Set.range (sectionToLaurent σ A _
        (torus_le_cechOpen x)) := by
      rw [h]
      exact hf
    exact ⟨s, congrArg AddMonoidAlgebra.coeff hs⟩

omit [Fintype σ] [DecidableEq σ] in
/-- The Čech complex of `𝒪` for the standard cover of `Proj A[xᵢ]` is exact in positive degrees
(Stacks Project, Tag 01XT, in degree `0`). -/
theorem cechComplex_exactAt [Finite σ] (p : ℕ) :
    (TopCat.Presheaf.cechComplex (stdCover σ A) (structureModule σ A).toAbSheaf.obj).ExactAt
      (p + 1) := by
  classical
  have := Fintype.ofFinite σ
  refine TopCat.Presheaf.cechComplex_exactAt_of_embedding _ _ (fun x ↦ cechEmbedding x)
    (fun x y h s ↦ congrArg AddMonoidAlgebra.coeff (sectionToLaurent_map _ _ h s))
    (fun x ↦ AddMonoidAlgebra.coeffAddEquiv.injective.comp
      (injective_sectionToLaurent_of_eq (image_nonempty x) (cechOpen_stdCover x) _)) p
    fun c hc hdc ↦ ?_
  obtain ⟨b, hb, hdb⟩ := TopCat.Presheaf.exists_cechDConst_eq_of_support
    (fun x ↦ monomialSet (Finset.univ.image x)) (nonnegIndex σ) nonnegIndex_mem c
    (fun x ↦ by simpa [range_cechEmbedding] using hc x) hdc
  exact ⟨b, fun y ↦ by simpa [range_cechEmbedding] using hb y, hdb⟩

end Cech

section Vanishing

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `Hᵖ(ℙʳ_A, 𝒪) = 0` for `p > 0` (Stacks Project, Tag 01XT; EGA III 2.1.12; Hartshorne III.5.1),
for `ℙʳ_A = Proj A[x₀, …, x_r]`. -/
theorem H_structureModule_subsingleton (r p : ℕ) :
    Subsingleton ((structureModule (Fin (r + 1)) A).H (p + 1)) := by
  have hF {m : ℕ} (x : Fin (m + 1) → Fin (r + 1)) (q : ℕ) :
      Subsingleton ((structureModule (Fin (r + 1)) A).toAbSheaf.H' (q + 1)
        (TopCat.Presheaf.cechOpen (stdCover (Fin (r + 1)) A) x)) :=
    (structureModule _ A).H'_subsingleton_of_isAffineOpen (by
      rw [cechOpen_stdCover]
      exact Proj.isAffineOpen_basicOpen _ _ (prodX_mem _) (image_nonempty x).card_pos) q
  have h := (TopCat.Sheaf.cechComplex_exactAt_iff_subsingleton_H' (X := (Proj _).carrier)
    (stdCover (Fin (r + 1)) A) p _ hF).mp (cechComplex_exactAt p)
  rw [iSup_stdCover] at h
  exact h

end Vanishing

end projectiveSpace

section toSpecZero

variable {R ι : Type u} [CommRing R] [SetLike ι R] [AddSubgroupClass ι R] (𝒜 : ℕ → ι)
  [GradedRing 𝒜]

/-- The restriction to `D₊(f)` of the global section of `Proj A` defined by `a ∈ A₀` is
`a / 1 ∈ A_{(f)} = Γ(D₊(f), 𝒪)`. -/
lemma CohomologyAux.toSpecZero_appTop_map {f : R} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.toSpecZero 𝒜).appTop ≫
        (Proj 𝒜).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 f ≤ ⊤)).op =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (fromZeroRingHom 𝒜 (.powers f)) ≫
        Proj.awayToSection 𝒜 f := by
  have h := congrArg Scheme.Hom.appTop (Proj.awayι_toSpecZero 𝒜 f f_deg hm)
  rw [Scheme.Hom.comp_appTop, Proj.awayι, Scheme.Hom.comp_appTop] at h
  have h2 := congrArg (· ≫ (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom.appTop) h
  simp only [Category.assoc] at h2
  have e : (Proj.basicOpenToSpec 𝒜 f).appTop = _ := Proj.basicOpenToSpec_app_top 𝒜 f
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop, Category.comp_id,
    Proj.basicOpenIsoSpec_hom, e, Scheme.ΓSpecIso_naturality_assoc] at h2
  have h3 := congrArg (· ≫ (Proj.basicOpen 𝒜 f).topIso.hom) h2
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h3
  rw [← h3]
  congr 1

end toSpecZero

namespace projectiveSpace

section Global

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ : Type v} {A : Type u} [CommRing A] [Fintype σ] [DecidableEq σ] [Nonempty σ]

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
lemma prodX_singleton (i : σ) : prodX σ A {i} = X i :=
  Finset.prod_singleton _ _

omit [Fintype σ] [Nonempty σ] in
lemma awayToLaurent_fromZeroRingHom (I : Finset σ) (a : homogeneousSubmodule σ A 0) :
    awayToLaurent σ A I (fromZeroRingHom _ _ a) = toLaurent σ A a.1 := by
  simp only [awayToLaurent, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply]
  change Localization.awayLift _ _ _ (Localization.mk a.1 1) = _
  rw [Localization.mk_one_eq_algebraMap]
  exact IsLocalization.lift_eq _ _

lemma sectionToLaurent_appTop (z : Γ(Spec (.of (homogeneousSubmodule σ A 0)), ⊤)) :
    sectionToLaurent σ A ⊤ le_top ((Proj.toSpecZero (homogeneousSubmodule σ A)).appTop z) =
      toLaurent σ A ((Scheme.ΓSpecIso _).hom z).1 := by
  rw [← sectionToLaurent_map le_top (torus_le_basicOpen_prodX Finset.univ) le_top]
  have h := congrArg (fun φ ↦ φ z) (CohomologyAux.toSpecZero_appTop_map (homogeneousSubmodule σ A)
    (prodX_mem (Finset.univ : Finset σ)) card_univ_pos)
  simp only [CommRingCat.comp_apply] at h
  erw [h, sectionToLaurent_awayToSection]
  exact awayToLaurent_fromZeroRingHom _ _

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
lemma stdCover_eq (i : σ) :
    stdCover σ A i = Proj.basicOpen (homogeneousSubmodule σ A) (prodX σ A {i}) := by
  rw [prodX_singleton]

omit [DecidableEq σ] [Nonempty σ] in
lemma torus_le_stdCover (i : σ) : torus σ A ≤ stdCover σ A i := by
  rw [stdCover_eq]
  exact torus_le_basicOpen_prodX _

lemma injective_sectionToLaurent_top : Function.Injective (sectionToLaurent σ A ⊤ le_top) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Sheaf.eq_of_locally_eq' (Proj (homogeneousSubmodule σ A)).sheaf (stdCover σ A) ⊤
    (fun i ↦ homOfLE le_top) (iSup_stdCover σ A).ge s 0 fun i ↦ ?_
  refine injective_sectionToLaurent_of_eq (Finset.singleton_nonempty i) (stdCover_eq i)
    (torus_le_stdCover i) ?_
  change sectionToLaurent σ A _ (torus_le_stdCover i)
      ((Proj (homogeneousSubmodule σ A)).presheaf.map (homOfLE le_top).op s) =
    sectionToLaurent σ A _ (torus_le_stdCover i)
      ((Proj (homogeneousSubmodule σ A)).presheaf.map (homOfLE le_top).op 0)
  rw [map_zero, map_zero, sectionToLaurent_map le_top (torus_le_stdCover i) le_top, hs]

lemma sectionToLaurent_top_eq_single (s : Γ(Proj (homogeneousSubmodule σ A), ⊤)) :
    sectionToLaurent σ A ⊤ le_top s =
      AddMonoidAlgebra.single 0 ((sectionToLaurent σ A ⊤ le_top s).coeff 0) := by
  set ℓ := sectionToLaurent σ A ⊤ le_top s with hℓ
  have hmem (i : σ) : ↑ℓ.coeff.support ⊆ monomialSet {i} := by
    have hr := range_sectionToLaurent_of_eq (Finset.singleton_nonempty i) (stdCover_eq i)
      (torus_le_stdCover (A := A) i)
    have hℓi : ℓ ∈ Set.range (sectionToLaurent σ A _ (torus_le_stdCover i)) :=
      ⟨(Proj _).presheaf.map (homOfLE le_top).op s, sectionToLaurent_map _ _ _ s⟩
    rw [hr] at hℓi
    exact hℓi
  have hsupp : ∀ μ ∈ ℓ.coeff.support, μ = 0 := by
    intro μ hμ
    have hsum := (hmem (Classical.arbitrary σ) hμ).1
    have hnn (k : σ) : 0 ≤ μ k := by
      by_cases hk : ∃ i, i ≠ k
      · obtain ⟨i, hik⟩ := hk
        exact (hmem i hμ).2 k (by simpa [eq_comm] using hik)
      · push Not at hk
        have : ∑ i, μ i = μ k :=
          Finset.sum_eq_single k (fun b _ hb ↦ absurd (hk b) hb) (by simp)
        omega
    funext k
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hnn i)).mp hsum k (Finset.mem_univ k)
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun μ ↦ ?_)
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with hμ
  · rw [hμ]
  · exact Finsupp.notMem_support_iff.mp fun h ↦ hμ (hsupp μ h).symm

omit [Fintype σ] [DecidableEq σ] in
/-- `Γ(ℙ(σ)_A, 𝒪) = A` (Stacks Project, Tag 01XT; EGA III 2.1.12; Hartshorne III.5.1 (a)): the
structure morphism `Proj A[xᵢ] ⟶ Spec A₀` induces an isomorphism on global sections. -/
theorem isIso_toSpecZero_appTop [Finite σ] :
    IsIso (Proj.toSpecZero (homogeneousSubmodule σ A)).appTop := by
  classical
  have := Fintype.ofFinite σ
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun z z' hzz' ↦ ?_, fun s ↦ ?_⟩
  · have h := congrArg (sectionToLaurent σ A ⊤ le_top) hzz'
    rw [sectionToLaurent_appTop, sectionToLaurent_appTop] at h
    have h' := congrArg (Scheme.ΓSpecIso _).inv (Subtype.ext (toLaurent_injective h))
    simpa using h'
  · let a : homogeneousSubmodule σ A 0 :=
      ⟨C ((sectionToLaurent σ A ⊤ le_top s).coeff 0),
        (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C σ _)⟩
    refine ⟨(Scheme.ΓSpecIso _).inv a, injective_sectionToLaurent_top ?_⟩
    rw [sectionToLaurent_appTop, Iso.inv_hom_id_apply, sectionToLaurent_top_eq_single s]
    change toLaurent σ A (C _) = _
    rw [C_apply, toLaurent_monomial, map_zero]

end Global

end projectiveSpace

/-- **Cohomology of the structure sheaf of projective space** (Stacks Project, Tag 01XT;
EGA III 2.1.12; Hartshorne III.5.1): `Γ(ℙʳ_A, 𝒪) = A` and `Hᵖ(ℙʳ_A, 𝒪) = 0` for `p > 0`. -/
theorem projectiveSpaceStructureSheafStatement : ProjectiveSpaceStructureSheafStatement.{u} :=
  fun A r ↦ ⟨projectiveSpace.isIso_toSpecZero_appTop (σ := Fin (r + 1)) (A := A),
    fun p ↦ projectiveSpace.H_structureModule_subsingleton A r p⟩

end AlgebraicGeometry

