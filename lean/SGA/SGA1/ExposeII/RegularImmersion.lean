/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import SGA.SGA1.ExposeII.Coordinates
import SGA.SGA1.ExposeII.Criteria

/-!
# SGA 1, Exposé II, §4 (4.14–4.19): regular immersions

II.4.14 calls `x₁,…,xₙ ∈ A` a *regular system of generators* of `J = (x₁,…,xₙ)` when the
canonical surjection `(A/J)[t₁,…,tₙ] → gr_J(A)` is an isomorphism. Mathlib has no associated
graded ring; the injectivity of this graded map is the usual notion of a *quasi-regular*
sequence: a homogeneous polynomial `F` of degree `d` with `F(x) ∈ J^{d+1}` has all its
coefficients in `J`. This is our definition `IsRegularSystemOfGenerators`. We prove:

* if `J = A`, every system of generators is regular (II.4.14);
* the classes of a regular system of generators form a basis of `J/J²` over `A/J`
  (II.4.14 (ii)), hence a regular system of generators of a proper ideal has the minimum number
  of elements (II.4.14);
* regularity is preserved by flat base change (via the equational criterion of flatness), and
  the variables of a polynomial ring are a regular system of generators;
* II.4.15, (i) ⇒ (ii): if `X` and `Y ⊆ X` are smooth over `S` at `x`, then `Y → X` is a regular
  immersion at `x` (local form, noetherian base), with its consequences II.4.16 (⇒) and
  II.4.17 (i) ⇒ (ii) (sections of smooth morphisms) and II.4.18 (the diagonal of a smooth
  scheme is a regular immersion), in affine form.

Regular ideals (II.4.14) are defined by the local condition. The converse II.4.15 (ii) ⇒ (i),
which uses the local flatness criterion through the associated graded ring (IV.5.6), is in
`SGA.SGA1.ExposeII.RegularImmersionSmooth`. That `A`-sequences are regular systems of generators
is in `SGA.SGA1.ExposeII.RegularSequence`, formula (4.4) in `SGA.SGA1.ExposeII.PrincipalParts`, the
characterisation "smooth = flat + differentially smooth" of the remarks II.4.18 in
`SGA.SGA1.ExposeII.DifferentiallySmooth`, and the characterisation of regular systems of
generators by completions (II.4.14, II.4.17 (iii)) in `SGA.SGA1.ExposeII.RegularSystemFiltration`.
The characterisation by `A`-sequences in noetherian local rings is in
`SGA.SGA1.ExposeII.RegularSequence`. Not formalized: the sheaves `𝒫ⁿ` and `𝒫^∞` of the remarks
II.4.18, and the terminological remark II.4.19.
-/

universe u

open MvPolynomial
open scoped TensorProduct

namespace SGA.SGA1.ExposeII

section RegularSystem

variable {A : Type*} [CommRing A] {ι : Type*} (x : ι → A)

/-- II.4.14: `x` is a *regular system of generators* of `J = (xᵢ)` if the canonical map
`(A/J)[tᵢ] → gr_J(A)` is injective (it is always surjective): a homogeneous polynomial of
degree `d` whose value at `x` lies in `J^{d+1}` has all its coefficients in `J`. -/
def IsRegularSystemOfGenerators : Prop :=
  ∀ (d : ℕ) (F : MvPolynomial ι A), F.IsHomogeneous d →
    eval x F ∈ Ideal.span (Set.range x) ^ (d + 1) → ∀ m, F.coeff m ∈ Ideal.span (Set.range x)

/-- II.4.14: if `J = A`, every system of generators of `J` is regular. -/
theorem isRegularSystemOfGenerators_of_span_eq_top (h : Ideal.span (Set.range x) = ⊤) :
    IsRegularSystemOfGenerators x := fun _ _ _ _ _ ↦ h ▸ Submodule.mem_top

variable {x}

/-- The degree-one part of the definition: a linear relation `∑ cᵢ xᵢ ∈ J²` has coefficients
in `J`. -/
theorem IsRegularSystemOfGenerators.mem_of_sum_mem_sq (hx : IsRegularSystemOfGenerators x)
    (s : Finset ι) (c : ι → A) (h : ∑ i ∈ s, c i * x i ∈ Ideal.span (Set.range x) ^ 2) (i : ι)
    (hi : i ∈ s) : c i ∈ Ideal.span (Set.range x) := by
  classical
  let F : MvPolynomial ι A := ∑ j ∈ s, C (c j) * X j
  have hF : F.IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun j _ ↦ by
      simpa using (isHomogeneous_C (σ := ι) (c j)).mul (isHomogeneous_X A j)
  have := hx 1 F hF (by simpa [F] using h) (Finsupp.single i 1)
  simpa [F, coeff_sum, coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff, hi] using this

private lemma span_toCotangent_eq_top {κ : Type*} (y : κ → A)
    (hy : ∀ i, y i ∈ Ideal.span (Set.range x))
    (hspan : Ideal.span (Set.range y) = Ideal.span (Set.range x)) :
    Submodule.span (A ⧸ Ideal.span (Set.range x))
      (Set.range fun i ↦ (Ideal.span (Set.range x)).toCotangent ⟨y i, hy i⟩) = ⊤ := by
  set J := Ideal.span (Set.range x)
  have h₁ : Submodule.span A (Set.range fun i ↦ (⟨y i, hy i⟩ : J)) = ⊤ :=
    (span_subtype_eq_top_iff J J rfl y hy).mpr hspan
  have hr : (Set.range fun i ↦ J.toCotangent ⟨y i, hy i⟩) =
      J.toCotangent '' Set.range (fun i ↦ (⟨y i, hy i⟩ : J)) := by
    rw [← Set.range_comp]
    rfl
  have h₂ : Submodule.span A (Set.range fun i ↦ J.toCotangent ⟨y i, hy i⟩) = ⊤ := by
    rw [hr, ← Submodule.map_span, h₁, Submodule.map_top, J.toCotangent_range]
  refine eq_top_iff.mpr fun z _ ↦ ?_
  exact Submodule.span_le_restrictScalars A (A ⧸ J) _ (h₂ ▸ Submodule.mem_top : z ∈ _)

/-- II.4.14 (ii): the classes of a regular system of generators `xᵢ` form a basis of the
`A/J`-module `J/J²`. -/
noncomputable def IsRegularSystemOfGenerators.basisCotangent
    (hx : IsRegularSystemOfGenerators x) :
    Module.Basis ι (A ⧸ Ideal.span (Set.range x)) (Ideal.span (Set.range x)).Cotangent := by
  classical
  set J := Ideal.span (Set.range x)
  refine Module.Basis.mk (v := fun i ↦ J.toCotangent ⟨x i, Ideal.subset_span ⟨i, rfl⟩⟩) ?_
    (span_toCotangent_eq_top x (fun i ↦ Ideal.subset_span ⟨i, rfl⟩) rfl).ge
  rw [linearIndependent_iff']
  intro s g hg i hi
  choose c hc using fun i ↦ Ideal.Quotient.mk_surjective (I := J) (g i)
  have hsum : ∑ j ∈ s, g j • J.toCotangent ⟨x j, Ideal.subset_span ⟨j, rfl⟩⟩ =
      J.toCotangent ⟨∑ j ∈ s, c j * x j,
        Ideal.sum_mem _ fun j _ ↦ J.mul_mem_left _ (Ideal.subset_span ⟨j, rfl⟩)⟩ := by
    simp_rw [← hc, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul, ← map_smul, ← map_sum]
    congr 1
    ext
    simp [smul_eq_mul]
  rw [hsum, Ideal.toCotangent_eq_zero] at hg
  rw [← hc, Ideal.Quotient.eq_zero_iff_mem]
  exact hx.mem_of_sum_mem_sq s c hg i hi

/-- II.4.14: if `J ≠ A`, a regular system of generators of `J` is a minimal system of
generators (minimum number of elements). -/
theorem IsRegularSystemOfGenerators.card_le [Finite ι] (hx : IsRegularSystemOfGenerators x)
    (hJ : Ideal.span (Set.range x) ≠ ⊤) {m : ℕ} (y : Fin m → A)
    (hy : Ideal.span (Set.range y) = Ideal.span (Set.range x)) : Nat.card ι ≤ m := by
  classical
  have := Fintype.ofFinite ι
  set J := Ideal.span (Set.range x)
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have hyJ (i : Fin m) : y i ∈ J := hy ▸ Ideal.subset_span ⟨i, rfl⟩
  have hsp := span_toCotangent_eq_top (x := x) y hyJ hy
  have := linearIndependent_le_span _ hx.basisCotangent.linearIndependent _ hsp
  rw [Cardinal.mk_fintype, Nat.cast_le] at this
  rw [Nat.card_eq_fintype_card]
  exact this.trans ((Fintype.card_range_le _).trans (by simp))

variable (x)

/-- The image of the ideal of variables under `tᵢ ↦ xᵢ` is `J = (xᵢ)`. -/
lemma map_eval_idealOfVars :
    (idealOfVars ι A).map (eval x) = Ideal.span (Set.range x) := by
  rw [idealOfVars, Ideal.map_span, ← Set.range_comp]
  congr 1
  ext; simp

/-- `J^n` consists of the values at `x` of polynomials all of whose monomials have degree
`≥ n`. -/
lemma mem_span_pow_iff_exists (n : ℕ) (z : A) :
    z ∈ Ideal.span (Set.range x) ^ n ↔ ∃ h ∈ idealOfVars ι A ^ n, eval x h = z := by
  constructor
  · intro hz
    rw [← map_eval_idealOfVars, ← Ideal.map_pow] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨h, hh, rfl⟩ := hz
      exact ⟨h, hh, rfl⟩
    | zero => exact ⟨0, zero_mem _, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨h, hh, rfl⟩ := ha
      obtain ⟨h', hh', rfl⟩ := hb
      exact ⟨h + h', add_mem hh hh', map_add _ _ _⟩
    | smul a b _ hb =>
      obtain ⟨h, hh, rfl⟩ := hb
      exact ⟨C a * h, Ideal.mul_mem_left _ _ hh, by simp⟩
  · rintro ⟨h, hh, rfl⟩
    rw [← map_eval_idealOfVars, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hh

/-- The value of the monomial `t^ν` at `x`. -/
private noncomputable def monomialValue (ν : ι →₀ ℕ) : A := ν.prod fun i e ↦ x i ^ e

private lemma eval_monomial_eq (ν : ι →₀ ℕ) (a : A) :
    eval x (monomial ν a) = a * monomialValue x ν := by
  simp [monomialValue, eval_monomial]

variable {x} in
/-- II.4.14: a regular system of generators stays regular after a flat extension of scalars
(`gr` commutes with flat base change). The proof uses the equational criterion of flatness. -/
theorem IsRegularSystemOfGenerators.map_of_flat {B : Type*} [CommRing B] [Algebra A B]
    [Module.Flat A B] (hx : IsRegularSystemOfGenerators x) :
    IsRegularSystemOfGenerators (algebraMap A B ∘ x) := by
  classical
  intro d F hF hmem μ
  set J := Ideal.span (Set.range x)
  have hJ' : Ideal.span (Set.range (algebraMap A B ∘ x)) = J.map (algebraMap A B) := by
    rw [Ideal.map_span, Set.range_comp]
  obtain ⟨H, hH, hHF⟩ := (mem_span_pow_iff_exists _ (d + 1) _).mp hmem
  set G := F - H with hGdef
  -- the coefficients of `G` in low degree
  have hGlow (m : ι →₀ ℕ) (hm : m.degree ≠ d) (hm' : m.degree < d + 1) : G.coeff m = 0 := by
    rw [hGdef, coeff_sub, hF.coeff_eq_zero hm,
      (mem_pow_idealOfVars_iff' (d + 1) H).mp hH m hm', sub_zero]
  -- the relation `∑ t^ν(x) • G_ν = 0` in `B`
  have hrel : ∑ ν : G.support, monomialValue x ν • G.coeff ν = 0 := by
    have : eval (algebraMap A B ∘ x) G = 0 := by
      rw [hGdef, map_sub, ← hHF, sub_self]
    rw [eval_eq] at this
    rw [← this, Finset.sum_coe_sort G.support (fun ν ↦ monomialValue x ν • G.coeff ν)]
    refine Finset.sum_congr rfl fun ν _ ↦ ?_
    simp [monomialValue, Algebra.smul_def, Finsupp.prod, map_prod, mul_comm]
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  -- the coefficients `a ν j` with `ν` of degree `d` lie in `J`
  have haJ (ν : G.support) (hν : ν.1.degree = d) (j : Fin k) : a ν j ∈ J := by
    let P : MvPolynomial ι A := ∑ ν' : G.support, monomial ν'.1 (a ν' j)
    have hPcoeff (m : ι →₀ ℕ) : P.coeff m = if h : m ∈ G.support then a ⟨m, h⟩ j else 0 := by
      simp only [P, coeff_sum, coeff_monomial]
      split_ifs with h
      · rw [Finset.sum_eq_single ⟨m, h⟩ (fun b _ hb ↦ by
          have : b.1 ≠ m := fun e ↦ hb (Subtype.ext e)
          simp [this]) (by simp)]
        simp
      · refine Finset.sum_eq_zero fun b _ ↦ ?_
        have : b.1 ≠ m := fun e ↦ h (by rw [← e]; exact b.2)
        simp [this]
    have hPeval : eval x P = 0 := by
      simp only [P, map_sum, eval_monomial_eq]
      rw [← ha j]
      exact Finset.sum_congr rfl fun ν' _ ↦ mul_comm _ _
    let Q := homogeneousComponent d P
    have hPQ : P - Q ∈ idealOfVars ι A ^ (d + 1) := by
      rw [mem_pow_idealOfVars_iff']
      intro m hm
      rw [coeff_sub, coeff_homogeneousComponent]
      by_cases hmd : m.degree = d
      · simp [hmd]
      · have hm' : m ∉ G.support := MvPolynomial.notMem_support_iff.mpr (hGlow m hmd hm)
        simp [hmd, hPcoeff, hm']
    have hQ : eval x Q ∈ J ^ (d + 1) := by
      have := (mem_span_pow_iff_exists x (d + 1) _).mpr ⟨_, hPQ, rfl⟩
      rw [map_sub, hPeval, zero_sub, neg_mem_iff] at this
      exact this
    have := hx d Q (homogeneousComponent_isHomogeneous d P) hQ ν
    rwa [show Q.coeff ν = a ν j by simp [Q, coeff_homogeneousComponent, hν, hPcoeff, ν.2]]
      at this
  -- conclusion
  rw [hJ']
  by_cases hμ : μ.degree = d
  · have hFG : F.coeff μ = G.coeff μ := by
      rw [hGdef, coeff_sub, (mem_pow_idealOfVars_iff' (d + 1) H).mp hH μ (by omega), sub_zero]
    rw [hFG]
    by_cases hsupp : μ ∈ G.support
    · rw [show G.coeff μ = _ from hy ⟨μ, hsupp⟩]
      refine Ideal.sum_mem _ fun j _ ↦ ?_
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (haJ ⟨μ, hsupp⟩ hμ j))
    · rw [MvPolynomial.notMem_support_iff.mp hsupp]
      exact zero_mem _
  · rw [hF.coeff_eq_zero hμ]
    exact zero_mem _


/-- II.4.14: the variables `t₁,…,tₙ` form a regular system of generators of the ideal they
generate in `C[t₁,…,tₙ]`. -/
theorem isRegularSystemOfGenerators_X (C σ : Type*) [CommRing C] :
    IsRegularSystemOfGenerators (X : σ → MvPolynomial σ C) := by
  classical
  intro d F hF hmem μ
  change F.coeff μ ∈ idealOfVars σ C
  rw [← pow_one (idealOfVars σ C), mem_pow_idealOfVars_iff']
  intro m hm
  obtain rfl : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
  by_cases hμ : μ.degree = d
  · have h0 := (mem_pow_idealOfVars_iff' (d + 1) _).mp hmem μ (by omega)
    rw [eval_eq, coeff_sum] at h0
    rw [Finset.sum_eq_single μ] at h0
    · simpa [prod_X_pow_eq_monomial, coeff_mul_monomial'] using h0
    · intro ν hν hne
      rw [prod_X_pow_eq_monomial, coeff_mul_monomial', ite_eq_right_iff]
      intro hle
      have hdeg : ν.degree = d := by
        have := hF (mem_support_iff.mp hν)
        rw [Finsupp.degree_eq_weight_one]
        exact this
      have hsub : (μ - ν).degree = 0 := by
        have := map_add Finsupp.degree ν (μ - ν)
        rw [add_tsub_cancel_of_le hle] at this
        omega
      exact (hne (le_antisymm hle
        (tsub_eq_zero_iff_le.mp ((Finsupp.degree_eq_zero_iff _).mp hsub)))).elim
    · intro hμs
      simp [notMem_support_iff.mp hμs]
  · simp [hF.coeff_eq_zero hμ]

variable {x} in
/-- A regular system of generators stays regular under a ring isomorphism. -/
theorem IsRegularSystemOfGenerators.map_ringEquiv {B : Type*} [CommRing B] (e : A ≃+* B)
    (hx : IsRegularSystemOfGenerators x) : IsRegularSystemOfGenerators (e ∘ x) := by
  let := e.toRingHom.toAlgebra
  have : Module.Flat A B := RingHom.Flat.of_bijective e.bijective
  exact hx.map_of_flat (B := B)

/-- II.4.14: `t₁,…,tₚ` is a regular system of generators in `R[t₁,…,tₚ,s₁,…,s_q]`. -/
theorem isRegularSystemOfGenerators_X_inl (R σ τ : Type*) [CommRing R] :
    IsRegularSystemOfGenerators (fun i : σ ↦ (X (Sum.inl i) : MvPolynomial (σ ⊕ τ) R)) := by
  have := (isRegularSystemOfGenerators_X (MvPolynomial τ R) σ).map_ringEquiv
    (MvPolynomial.sumAlgEquiv R σ τ).symm.toRingEquiv
  convert this using 1
  ext i
  simp [sumAlgEquiv_symm_X]

end RegularSystem

section RegularIdeal

variable {A : Type*} [CommRing A]

/-- II.4.14: an ideal `J` of `A` is *regular* if for every prime `𝔭`, `J A_𝔭` admits a regular
system of generators. -/
def IsRegularIdeal (J : Ideal A) : Prop :=
  ∀ (p : Ideal A) [p.IsPrime], ∃ (n : ℕ) (x : Fin n → Localization.AtPrime p),
    Ideal.span (Set.range x) = J.map (algebraMap A _) ∧ IsRegularSystemOfGenerators x

/-- II.4.14: it suffices to check regularity at the primes containing `J`: at the others,
`J A_𝔭 = A_𝔭` and every system of generators is regular. -/
theorem isRegularIdeal_iff_forall_le {J : Ideal A} [IsNoetherianRing A] :
    IsRegularIdeal J ↔ ∀ (p : Ideal A) [p.IsPrime], J ≤ p →
      ∃ (n : ℕ) (x : Fin n → Localization.AtPrime p),
        Ideal.span (Set.range x) = J.map (algebraMap A _) ∧ IsRegularSystemOfGenerators x := by
  refine ⟨fun h p _ _ ↦ h p, fun h p _ ↦ ?_⟩
  by_cases hJp : J ≤ p
  · exact h p hJp
  · have htop : J.map (algebraMap A (Localization.AtPrime p)) = ⊤ := by
      obtain ⟨a, haJ, hap⟩ := Set.not_subset.mp hJp
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haJ)
        (IsLocalization.map_units _ (⟨a, hap⟩ : p.primeCompl))
    exact ⟨1, fun _ ↦ 1, by simp [htop], isRegularSystemOfGenerators_of_span_eq_top _
      (by simp)⟩

end RegularIdeal

section Statements

open Algebra IsLocalRing

/-- II.4.15, (i) ⇒ (ii), local form: let `P = 𝒪_{X,x}` be the local ring of a scheme `X` locally
of finite type over a noetherian `S = Spec R` (a localization of a finitely generated `R`-algebra
at a prime `Q`), with `X` smooth over `S` at `x`, and let `J ⊆ 𝔪_P` be the ideal of a closed
subscheme `Y` which is smooth over `S` at `x`. Then `J` admits a regular system of generators:
`Y → X` is a regular immersion at `x`.

The proof follows SGA: by II.4.10 there are étale coordinates `(g, h)` at `x` with `J = (g)`;
the variables `tᵢ` form a regular system of generators of `R[t, s]`, and regularity is
preserved by the flat map `R[t, s] → P`. -/
theorem exists_isRegularSystemOfGenerators_of_formallySmooth {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [FiniteType R S] (Q : Ideal S) [Q.IsPrime]
    [IsSmoothAt R Q] (J : Ideal (Localization.AtPrime Q)) (hJ : J ≤ maximalIdeal _)
    (hY : FormallySmooth R (Localization.AtPrime Q ⧸ J)) :
    ∃ (n : ℕ) (x : Fin n → Localization.AtPrime Q),
      Ideal.span (Set.range x) = J ∧ IsRegularSystemOfGenerators x := by
  set P := Localization.AtPrime Q
  have : FinitePresentation R S := FinitePresentation.of_finiteType.mp inferInstance
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have : EssFiniteType R P := .comp R S P
  have : Module.Free P Ω[P⁄R] := Module.free_of_flat_of_isLocalRing
  have : Module.Flat R P := IsSmoothAt.flat_localization Q
  obtain ⟨p, q, g, h, hgJ, hgh⟩ := (formallySmooth_quotient_iff_exists_formallyEtale J hJ
    (IsNoetherian.noetherian J)).mp hY
  refine ⟨p, g, hgJ, ?_⟩
  algebraize [(MvPolynomial.aeval (R := R) (Sum.elim g h)).toRingHom]
  have : IsScalarTower R (MvPolynomial (Fin p ⊕ Fin q) R) P :=
    .of_algHom (MvPolynomial.aeval (Sum.elim g h))
  -- `P` is flat over `R[t, s]`: it is formally smooth over it and a quotient of the flat
  -- noetherian `R[t, s]`-algebra `R[t, s] ⊗_R P`
  have hflat : Module.Flat (MvPolynomial (Fin p ⊕ Fin q) R) P := by
    let C := MvPolynomial (Fin p ⊕ Fin q) R ⊗[R] P
    let e : C ≃ₐ[R] MvPolynomial (Fin p ⊕ Fin q) P :=
      (Algebra.TensorProduct.comm R _ _).trans
        ((MvPolynomial.algebraTensorAlgEquiv R P).restrictScalars R)
    have : IsNoetherianRing C := isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv
    let f : C →ₐ[MvPolynomial (Fin p ⊕ Fin q) R] P :=
      Algebra.TensorProduct.lift (Algebra.ofId _ P) (AlgHom.id R P) fun _ _ ↦ .all _ _
    refine FormallySmooth.flat_of_algHom_of_isNoetherianRing f fun z ↦ ⟨1 ⊗ₜ z, ?_⟩
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.id_apply]
  have := (isRegularSystemOfGenerators_X_inl R (Fin p) (Fin q)).map_of_flat (B := P)
  convert this using 1
  ext i
  simp [RingHom.algebraMap_toAlgebra]

/-- II.4.9 (the final assertion) and II.4.10, (i) ⇒ (iv), local form: under the hypotheses of
`exists_isRegularSystemOfGenerators_of_formallySmooth`, `J/J²` is a free `𝒪_{Y,x}`-module, with
basis the classes of a system of generators of `J`. -/
theorem exists_basis_cotangent_of_formallySmooth {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [FiniteType R S] (Q : Ideal S) [Q.IsPrime]
    [IsSmoothAt R Q] (J : Ideal (Localization.AtPrime Q)) (hJ : J ≤ maximalIdeal _)
    (hY : FormallySmooth R (Localization.AtPrime Q ⧸ J)) :
    ∃ (n : ℕ) (x : Fin n → Localization.AtPrime Q), Ideal.span (Set.range x) = J ∧
      Nonempty (Module.Basis (Fin n) (Localization.AtPrime Q ⧸ J) J.Cotangent) := by
  obtain ⟨n, x, rfl, hx⟩ := exists_isRegularSystemOfGenerators_of_formallySmooth Q J hJ hY
  exact ⟨n, x, rfl, ⟨hx.basisCotangent⟩⟩

/-- II.4.16, (⇒), affine form: let `X = Spec S` be of finite type over a noetherian `Spec R` and
`Y = Spec (S/J)` a closed subscheme smooth over `R`. If `X` is smooth over `R` at the points of
`Y`, then `Y` is regularly immersed in `X`: `J` is a regular ideal. -/
theorem isRegularIdeal_of_formallySmooth_quotient {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [FiniteType R S] (J : Ideal S)
    (hY : FormallySmooth R (S ⧸ J)) (hX : ∀ (p : Ideal S) [p.IsPrime], J ≤ p → IsSmoothAt R p) :
    IsRegularIdeal J := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  rw [isRegularIdeal_iff_forall_le]
  intro p _ hJp
  have := hX p hJp
  set P := Localization.AtPrime p
  have hJ : J.map (algebraMap S P) ≤ maximalIdeal P := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hJp
  have hY' : FormallySmooth R (P ⧸ J.map (algebraMap S P)) := by
    have : FormallySmooth (S ⧸ J) (P ⧸ J.map (algebraMap S P)) :=
      .of_isLocalization (Algebra.algebraMapSubmonoid (S ⧸ J) p.primeCompl)
    have : IsScalarTower R (S ⧸ J) (P ⧸ J.map (algebraMap S P)) := by
      convert (IsScalarTower.of_algebraMap_eq (R := R) (S := S ⧸ J)
        (A := P ⧸ J.map (algebraMap S P)) fun _ ↦ rfl)
    exact .comp R (S ⧸ J) _
  exact exists_isRegularSystemOfGenerators_of_formallySmooth p _ hJ hY'

/-- II.4.17, (i) ⇒ (ii), affine form: a section of a smooth algebra over a noetherian ring is a
regular immersion: if `S` is smooth over `R` and `σ : S → R` is an `R`-algebra retraction (a
section of `Spec S → Spec R`), then `ker σ` is a regular ideal. -/
theorem isRegularIdeal_ker_of_section {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Smooth R S] (σ : S →ₐ[R] R) : IsRegularIdeal (RingHom.ker σ) := by
  have hsurj : Function.Surjective σ := fun r ↦ ⟨algebraMap R S r, σ.commutes r⟩
  refine isRegularIdeal_of_formallySmooth_quotient _
    (.of_equiv (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm) fun p _ _ ↦ ?_
  have := smoothLocus_eq_univ (R := R) (A := S) ▸ Set.mem_univ (⟨p, ‹_›⟩ : PrimeSpectrum S)
  exact this

/-- II.4.18, affine form: if `X = Spec S` is smooth over a noetherian `Spec R`, the diagonal
`X → X ×_R X` is a regular immersion: the kernel of `S ⊗_R S → S` is a regular ideal (`X` is
*differentially smooth*). As in SGA, this is II.4.16 applied to the smooth subscheme `X` of the
smooth scheme `X ×_R X`. -/
theorem isRegularIdeal_diagonal {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Smooth R S] : IsRegularIdeal (KaehlerDifferential.ideal R S) := by
  have : Smooth S (S ⊗[R] S) := inferInstance
  have : Smooth R (S ⊗[R] S) := .comp R S _
  have hsurj : Function.Surjective (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S) := fun a ↦
    ⟨a ⊗ₜ 1, by simp [Algebra.TensorProduct.lmul'_apply_tmul]⟩
  refine isRegularIdeal_of_formallySmooth_quotient _
    (.of_equiv (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm) fun p _ _ ↦ ?_
  have := smoothLocus_eq_univ (R := R) (A := S ⊗[R] S) ▸
    Set.mem_univ (⟨p, ‹_›⟩ : PrimeSpectrum (S ⊗[R] S))
  exact this

/-- II.4.18, degree-one part: the conormal module of the diagonal of a smooth `X`, which is
`Ω¹_{X/S}` by definition, is projective (locally free), as required by condition (b) of
II.4.14 for a regular ideal. -/
theorem projective_conormal_diagonal (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [FormallySmooth R S] : Module.Projective S Ω[S⁄R] :=
  inferInstance

end Statements

end SGA.SGA1.ExposeII
