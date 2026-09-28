/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeII.SmoothnessAux

/-!
# SGA 1, Exposé II, II.4.15–II.4.17: smoothness from regular immersions

Let `P = 𝒪_{X,x}` be the local ring of a scheme `X` of finite type over a noetherian
`S = Spec R`, and `J ⊆ 𝔪_P` the ideal of a closed subscheme `Y` which is smooth over `S` at `x`.
We prove the converse II.4.15, (ii) ⇒ (i): if `J` admits a regular system of generators, then
`X` is smooth over `S` at `x`. The proof is SGA's: a regular system of generators `g₁,…,gₙ` of
`J` defines `g : X → S[t₁,…,tₙ]`; the graded ring of `P` for `J` is `gr(R[t]) ⊗ P/J`, and `P/J`
is flat over `R[t]/(t) = R`, so `P` is flat over `R[t]` by the local flatness criterion
(IV.5.6); its fibre at `g(x)` is the fibre of `Y → S`, which is smooth, so `g` is smooth at `x`
by II.2.1, and so is `X → S`. (SGA completes the `gᵢ` to étale coordinates; this is not
needed.)

With the direction (i) ⇒ (ii) of `SGA.SGA1.ExposeII.RegularImmersion` this gives II.4.15, the
converse of II.4.16 and the equivalence (i) ⇔ (ii) of II.4.17 for sections, in affine form.
-/

universe u

open MvPolynomial IsLocalRing Algebra
open scoped TensorProduct

namespace SGA.SGA1.ExposeII

open SGA.SGA1.ExposeIV

/-- II.4.15, (ii) ⇒ (i), local form. Let `P = 𝒪_{X,x}` be the localization at a prime `Q` of an
algebra `S` of finite type over a noetherian ring `R`, and `J ⊆ 𝔪_P` an ideal such that
`P ⧸ J = 𝒪_{Y,x}` is formally smooth over `R` (`Y` smooth over `S` at `x`). If `J` admits a
regular system of generators (the immersion `Y → X` is regular at `x`), then `X` is smooth over
`S` at `x`. -/
theorem isSmoothAt_of_isRegularSystemOfGenerators {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [FiniteType R S] (Q : Ideal S) [Q.IsPrime]
    (J : Ideal (Localization.AtPrime Q)) (hJ : J ≤ maximalIdeal _)
    (hY : FormallySmooth R (Localization.AtPrime Q ⧸ J)) {n : ℕ}
    (x : Fin n → Localization.AtPrime Q) (hxJ : Ideal.span (Set.range x) = J)
    (hx : IsRegularSystemOfGenerators x) : IsSmoothAt R Q := by
  let P := Localization.AtPrime Q
  have : FinitePresentation R S := FinitePresentation.of_finiteType.mp inferInstance
  have : IsNoetherianRing S := FiniteType.isNoetherianRing R S
  have : IsNoetherianRing P := IsLocalization.isNoetherianRing Q.primeCompl P inferInstance
  -- replace `x` by a regular system of generators coming from `S`
  choose a s hs using fun i ↦ IsLocalization.exists_mk'_eq Q.primeCompl (x i)
  let u : Fin n → Pˣ := fun i ↦ (IsLocalization.map_units P (s i)).unit
  have hux : (fun i ↦ (u i : P) * x i) = fun i ↦ algebraMap S P (a i) := by
    funext i
    rw [← hs i, IsUnit.unit_spec, mul_comm, IsLocalization.mk'_spec]
  have hreg : IsRegularSystemOfGenerators fun i ↦ algebraMap S P (a i) := hux ▸ hx.units_mul u
  have hspan : Ideal.span (Set.range fun i ↦ algebraMap S P (a i)) = J := by
    rw [← hux, span_range_units_mul, hxJ]
  -- the morphism `g : X → S[t₁,…,tₙ]` defined by the `aᵢ`
  algebraize [(MvPolynomial.aeval (R := R) a).toRingHom]
  have : IsScalarTower R (MvPolynomial (Fin n) R) S := .of_algHom (MvPolynomial.aeval a)
  have : IsScalarTower R (MvPolynomial (Fin n) R) P := .to₁₂₄ _ _ S _
  have hy : (fun i ↦ algebraMap (MvPolynomial (Fin n) R) P (X i)) =
      fun i ↦ algebraMap S P (a i) := by
    funext i
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) R) S P]
    congr 1
    exact aeval_X a i
  set I := idealOfVars (Fin n) R
  have hIJ : I.map (algebraMap (MvPolynomial (Fin n) R) P) = J := by
    rw [Ideal.map_span, ← Set.range_comp, ← hspan, ← hy]
    rfl
  -- `R[t] / I = R`
  have hC (b : MvPolynomial (Fin n) R) :
      b - algebraMap R (MvPolynomial (Fin n) R) (b.coeff 0) ∈ I := by
    rw [← pow_one I, mem_pow_idealOfVars_iff']
    intro m hm
    obtain rfl : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
    rw [MvPolynomial.algebraMap_eq, coeff_sub, coeff_C,
      ite_eq_left_iff.mpr (fun h ↦ (h rfl).elim), sub_self]
  have hRI : Function.Surjective (algebraMap R (MvPolynomial (Fin n) R ⧸ I)) := by
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨f.coeff 0, ?_⟩
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq, ← neg_mem_iff, neg_sub]
    exact hC f
  -- `P / J` is flat over `R`, hence `P / IP` is flat over `R[t] / I`
  have := hY
  have hflatR : Module.Flat R (P ⧸ J) :=
    flat_of_formallySmooth_of_isLocalization (T := S) Q.primeCompl (Ideal.Quotient.mkₐ R J)
      Ideal.Quotient.mk_surjective
  rw [← hIJ] at hflatR hY
  have : IsScalarTower R (MvPolynomial (Fin n) R ⧸ I)
      (P ⧸ I.map (algebraMap (MvPolynomial (Fin n) R) P)) :=
    .to₁₃₄ R (MvPolynomial (Fin n) R) _ _
  have : Module.Flat (MvPolynomial (Fin n) R ⧸ I)
      (P ⧸ I.map (algebraMap (MvPolynomial (Fin n) R) P)) :=
    flat_of_surjective_algebraMap hRI
  have hflatI : Module.Flat (MvPolynomial (Fin n) R ⧸ I)
      ((MvPolynomial (Fin n) R ⧸ I) ⊗[MvPolynomial (Fin n) R] P) :=
    .of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor P I).symm.toLinearEquiv
  -- the local flatness criterion: `P` is flat over `R[t]`
  have hJrad : I.map (algebraMap (MvPolynomial (Fin n) R) P) ≤ Ideal.jacobson ⊥ := by
    rw [hIJ, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact hJ
  have h13 := (flat_tfae (B := P) P I hJrad).out 1 3
  have hflatA : Module.Flat (MvPolynomial (Fin n) R) P :=
    h13.2 ⟨hflatI, grMapInjective_idealOfVars (hy ▸ hreg)⟩
  -- the fibre of `g` at `g(x)` is the fibre of `Y → S` at the image of `x`
  set p := Q.under (MvPolynomial (Fin n) R)
  have hIp : I ≤ p := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change algebraMap (MvPolynomial (Fin n) R) S (X i) ∈ Q
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff P Q _).mp (hJ ?_)
    rw [← hspan]
    refine Ideal.subset_span ⟨i, ?_⟩
    simp only [RingHom.algebraMap_toAlgebra]
    congr 1
    exact (aeval_X a i).symm
  have hfib : FormallySmooth p.ResidueField (p.ResidueField ⊗[MvPolynomial (Fin n) R] P) :=
    formallySmooth_tensorProduct_of_quotient I (fun b ↦ ⟨_, hC b⟩) p.ResidueField
      fun b hb ↦ Ideal.algebraMap_residueField_eq_zero.mpr (hIp hb)
  -- hence `g` is smooth at `x` (II.2.1), and so is `X → S`
  have : FinitePresentation (MvPolynomial (Fin n) R) S :=
    .of_restrict_scalars_finitePresentation R (MvPolynomial (Fin n) R) S
  have : IsSmoothAt (MvPolynomial (Fin n) R) Q :=
    (isSmoothAt_iff_flat_and_formallySmooth_fiber p Q).mpr ⟨hflatA, hfib⟩
  exact FormallySmooth.comp R (MvPolynomial (Fin n) R) P

/-- II.4.15, local form: let `P = 𝒪_{X,x}` be the localization at a prime `Q` of an algebra `S`
of finite type over a noetherian ring `R`, and `J ⊆ 𝔪_P` an ideal with `P ⧸ J = 𝒪_{Y,x}`
formally smooth over `R`. Then `X` is smooth over `S` at `x` iff `J` admits a regular system of
generators, i.e. the immersion `Y → X` is regular at `x`. -/
theorem isSmoothAt_iff_exists_isRegularSystemOfGenerators {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [FiniteType R S] (Q : Ideal S) [Q.IsPrime]
    (J : Ideal (Localization.AtPrime Q)) (hJ : J ≤ maximalIdeal _)
    (hY : FormallySmooth R (Localization.AtPrime Q ⧸ J)) :
    IsSmoothAt R Q ↔ ∃ (n : ℕ) (x : Fin n → Localization.AtPrime Q),
      Ideal.span (Set.range x) = J ∧ IsRegularSystemOfGenerators x :=
  ⟨fun _ ↦ exists_isRegularSystemOfGenerators_of_formallySmooth Q J hJ hY,
    fun ⟨_, x, hxJ, hx⟩ ↦ isSmoothAt_of_isRegularSystemOfGenerators Q J hJ hY x hxJ hx⟩

/-- If `S ⧸ J` is formally smooth over `R`, so is its localization `S_𝔭 ⧸ J S_𝔭`. -/
lemma formallySmooth_localization_quotient {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (J : Ideal S) [FormallySmooth R (S ⧸ J)] (p : Ideal S) [p.IsPrime] :
    FormallySmooth R (Localization.AtPrime p ⧸ J.map (algebraMap S (Localization.AtPrime p))) := by
  set P := Localization.AtPrime p
  have : FormallySmooth (S ⧸ J) (P ⧸ J.map (algebraMap S P)) :=
    .of_isLocalization (Algebra.algebraMapSubmonoid (S ⧸ J) p.primeCompl)
  have : IsScalarTower R (S ⧸ J) (P ⧸ J.map (algebraMap S P)) := by
    convert (IsScalarTower.of_algebraMap_eq (R := R) (S := S ⧸ J)
      (A := P ⧸ J.map (algebraMap S P)) fun _ ↦ rfl)
  exact .comp R (S ⧸ J) _

/-- II.4.16, affine form: let `X = Spec S` be of finite type over a noetherian `Spec R` and
`Y = Spec (S/J)` a closed subscheme smooth over `R`. Then `X` is smooth over `R` at the points
of `Y` iff `Y` is regularly immersed in `X`, i.e. `J` is a regular ideal. -/
theorem forall_isSmoothAt_iff_isRegularIdeal {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [FiniteType R S] (J : Ideal S)
    (hY : FormallySmooth R (S ⧸ J)) :
    (∀ (p : Ideal S) [p.IsPrime], J ≤ p → IsSmoothAt R p) ↔ IsRegularIdeal J := by
  refine ⟨isRegularIdeal_of_formallySmooth_quotient J hY, fun h p _ hJp ↦ ?_⟩
  obtain ⟨n, x, hxJ, hx⟩ := h p
  have hJ : J.map (algebraMap S (Localization.AtPrime p)) ≤ maximalIdeal _ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hJp
  exact isSmoothAt_of_isRegularSystemOfGenerators p _ hJ
    (formallySmooth_localization_quotient J p) x hxJ hx

/-- II.4.17, (i) ⇔ (ii), affine local form: let `S` be of finite type over a noetherian ring `R`
and `σ : S → R` an `R`-algebra retraction (a section `i` of `Spec S → Spec R`, with ideal
`ker σ`). At a point `x = i(y)` of the section (a prime `Q ⊇ ker σ`), `S` is smooth over `R` iff
the section is a regular immersion at `y`, i.e. `ker σ` has a regular system of generators in
`S_Q`. -/
theorem isSmoothAt_iff_exists_isRegularSystemOfGenerators_ker {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [FiniteType R S] (σ : S →ₐ[R] R)
    (Q : Ideal S) [Q.IsPrime] (hQ : RingHom.ker σ ≤ Q) :
    IsSmoothAt R Q ↔ ∃ (n : ℕ) (x : Fin n → Localization.AtPrime Q),
      Ideal.span (Set.range x) = (RingHom.ker σ).map (algebraMap S _) ∧
        IsRegularSystemOfGenerators x := by
  have hsurj : Function.Surjective σ := fun r ↦ ⟨algebraMap R S r, σ.commutes r⟩
  have : FormallySmooth R (S ⧸ RingHom.ker σ) :=
    .of_equiv (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm
  have hJ : (RingHom.ker σ).map (algebraMap S (Localization.AtPrime Q)) ≤ maximalIdeal _ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hQ
  exact isSmoothAt_iff_exists_isRegularSystemOfGenerators Q _ hJ
    (formallySmooth_localization_quotient _ Q)

/-- II.4.17, (i) ⇔ (ii), affine global form: `S` is smooth over `R` along the section `σ` iff the
section is a regular immersion (`ker σ` is a regular ideal). -/
theorem forall_isSmoothAt_iff_isRegularIdeal_ker {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [FiniteType R S] (σ : S →ₐ[R] R) :
    (∀ (p : Ideal S) [p.IsPrime], RingHom.ker σ ≤ p → IsSmoothAt R p) ↔
      IsRegularIdeal (RingHom.ker σ) := by
  have hsurj : Function.Surjective σ := fun r ↦ ⟨algebraMap R S r, σ.commutes r⟩
  exact forall_isSmoothAt_iff_isRegularIdeal _
    (.of_equiv (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm)

end SGA.SGA1.ExposeII
