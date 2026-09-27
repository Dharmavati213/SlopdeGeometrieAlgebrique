/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import SGA.SGA1.ExposeI.CompleteLocal
import SGA.SGA1.ExposeI.Fundamental
import SGA.Foundations.Formal.FiniteEtale
import SGA.Foundations.Formal.EtaleCovering

/-!
# SGA 1, Exposé I, §8: infinitesimal lifting of étale schemes

I.8.1 (local existence of liftings) is proved in affine form for any closed subscheme
`Spec (A ⧸ I) ⊆ Spec A`: an étale `A ⧸ I`-algebra is, near any point, a standard étale
algebra `(A₀[t]/(F₀))[1/g₀]`, and lifting `F₀`, `g₀` (and the relation expressing
`F₀'` invertible) gives an étale `A`-algebra; the global affine form comes from
`SGA.Foundations.Formal.EtaleLift`. I.8.2 is proved over a local base, using I.7.5,
both under SGA's hypothesis (infinite residue field) and when the étale algebra is local.

Theorem I.8.3 (base change along a nilpotent thickening is an equivalence on étale
schemes) is split as in SGA: full faithfulness is I.5.5
(`etaleBaseChange_full_and_faithful`). For affine schemes and a nilpotent ideal, both
halves are proved (`bijective_map_quotient_of_isNilpotent`,
`exists_etale_lift_of_isNilpotent`); the latter lifts a global presentation of the étale
algebra with invertible Jacobian. For schemes, essential surjectivity (gluing the local
lifts) is IX.1.7, proved in Exposé IX; the equivalence is `etaleBaseChange_isEquivalence` in
`EtaleSiteInvariance`. I.8.4 is proved for
an adic noetherian ring `A` (the affine case, `Spf A`), from `SGA.Foundations.Formal`; the case
of a complete noetherian local ring also follows from I.6.1 for `A` and `A ⧸ I`.
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry CategoryTheory Algebra Polynomial TensorProduct IsLocalRing

variable {A : Type u} [CommRing A]

/-- Two standard étale pairs with the same `f` over `R` define isomorphic algebras when
`g₁` is invertible at a root of `f` exactly when `g₂` is. -/
noncomputable def StandardEtalePair.equivOfHasMapIff {R : Type*} [CommRing R]
    (P Q : StandardEtalePair R) (hf : P.f = Q.f)
    (hPQ : IsUnit (aeval Q.X P.g)) (hQP : IsUnit (aeval P.X Q.g)) : P.Ring ≃ₐ[R] Q.Ring := by
  have h₁ : P.HasMap Q.X := ⟨by rw [hf]; exact Q.hasMap_X.1, hPQ⟩
  have h₂ : Q.HasMap P.X := ⟨by rw [← hf]; exact P.hasMap_X.1, hQP⟩
  refine AlgEquiv.ofAlgHom (P.lift Q.X h₁) (Q.lift P.X h₂) (Q.hom_ext ?_) (P.hom_ext ?_)
  · simp only [AlgHom.coe_comp, Function.comp_apply, StandardEtalePair.lift_X, AlgHom.id_apply]
  · simp only [AlgHom.coe_comp, Function.comp_apply, StandardEtalePair.lift_X, AlgHom.id_apply]

/-- I.8.1, affine form: let `A₀ = A ⧸ I` and let `B₀` be an étale `A₀`-algebra. Every
prime `q₀` of `B₀` has a basic open neighbourhood `D(g)` which lifts to an étale
`A`-algebra: `B₀[1/g] ≅ A₀ ⊗_A B` with `B` étale over `A`. -/
theorem exists_etale_lift_away (I : Ideal A) (B₀ : Type u) [CommRing B₀] [Algebra (A ⧸ I) B₀]
    [Algebra.Etale (A ⧸ I) B₀] (q₀ : Ideal B₀) [q₀.IsPrime] :
    ∃ g ∉ q₀, ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Algebra.Etale A B ∧
      Nonempty ((A ⧸ I) ⊗[A] B ≃ₐ[A ⧸ I] Localization.Away g) := by
  obtain ⟨g, hg, hstd⟩ := IsEtaleAt.exists_isStandardEtale (R := A ⧸ I) q₀
  let P₀ := hstd.nonempty_standardEtalePresentation.some
  obtain ⟨p₁₀, p₂₀, n, hcond⟩ := P₀.cond
  let π : A →+* A ⧸ I := Ideal.Quotient.mk I
  obtain ⟨f, hf, -, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective π Ideal.Quotient.mk_surjective P₀.f) P₀.monic_f
  obtain ⟨g', hg'⟩ := Polynomial.map_surjective π Ideal.Quotient.mk_surjective P₀.g
  obtain ⟨p₁, hp₁⟩ := Polynomial.map_surjective π Ideal.Quotient.mk_surjective p₁₀
  obtain ⟨p₂, hp₂⟩ := Polynomial.map_surjective π Ideal.Quotient.mk_surjective p₂₀
  let Q : StandardEtalePair A :=
    ⟨f, hfm, g' * (derivative f * p₁ + f * p₂), ⟨p₁ * g', p₂ * g', 1, by ring⟩⟩
  let PQ : StandardEtalePresentation A Q.Ring :=
    ⟨Q, Q.X, Q.hasMap_X, by simpa [StandardEtalePair.lift_X_left] using Function.bijective_id⟩
  refine ⟨g, hg, Q.Ring, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  refine (PQ.baseChange (T := A ⧸ I)).equivRing.trans (AlgEquiv.trans ?_ P₀.equivRing.symm)
  have hfmap : (Q.map (algebraMap A (A ⧸ I))).f = P₀.f := hf
  have hgmap : (Q.map (algebraMap A (A ⧸ I))).g = P₀.g ^ (n + 1) := by
    change (g' * (derivative f * p₁ + f * p₂)).map π = _
    rw [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      ← derivative_map, hf, hg', hp₁, hp₂, hcond, pow_succ, mul_comm]
  refine StandardEtalePair.equivOfHasMapIff (Q.map (algebraMap A (A ⧸ I)))
    P₀.P hfmap ?_ ?_
  · rw [hgmap, map_pow]
    exact P₀.hasMap_X.2.pow _
  · have := (Q.map (algebraMap A (A ⧸ I))).hasMap_X.2
    rw [hgmap, map_pow] at this
    exact (isUnit_pow_iff (Nat.succ_ne_zero n)).mp this


/-- I.8.2, when the étale algebra is local: let `A` be local, `I` a proper ideal, and
`B₀` a finite étale local `A ⧸ I`-algebra. Then `B₀ ≅ (A ⧸ I) ⊗_A B` for a finite étale
`A`-algebra `B` (of the form `A[t]/(F)`). SGA instead assumes the residue field
infinite, which makes every finite étale algebra monogenic (I.7.5). -/
theorem exists_finite_etale_lift_of_isLocalRing [IsLocalRing A] (I : Ideal A) (B₀ : Type u)
    [CommRing B₀] [Algebra (A ⧸ I) B₀] [IsLocalRing B₀] [Module.Finite (A ⧸ I) B₀]
    [Algebra.Etale (A ⧸ I) B₀] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
      Nonempty ((A ⧸ I) ⊗[A] B ≃ₐ[A ⧸ I] B₀) := by
  have : Nontrivial (A ⧸ I) := (algebraMap (A ⧸ I) B₀).domain_nontrivial
  have : IsLocalRing (A ⧸ I) := .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨F₀, hF₀m, hF₀s, -, ⟨e⟩⟩ := exists_algEquiv_adjoinRoot_of_etale (A := A ⧸ I) (B := B₀)
  obtain ⟨F, hF, -, hFm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective F₀) hF₀m
  have hI : I ≤ maximalIdeal A := le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp ‹_›)
  let ψ : A ⧸ I →+* ResidueField A := Ideal.Quotient.factor hI
  have hψ : ψ.comp (Ideal.Quotient.mk I) = residue A := Ideal.Quotient.factor_comp_mk hI
  have hFs : F.Separable := separable_of_separable_map_residue hFm (by
    rw [← hψ, ← Polynomial.map_map, hF]; exact hF₀s.map)
  have := etale_adjoinRoot_of_separable hFm hFs
  have := hFm.finite_adjoinRoot
  refine ⟨AdjoinRoot F, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  have e₁ : AdjoinRoot (F.map (algebraMap A (A ⧸ I))) ≃ₐ[A ⧸ I] AdjoinRoot F₀ := by
    have : F.map (algebraMap A (A ⧸ I)) = F₀ := hF
    rw [this]
  exact (tensorAdjoinRootEquiv _ F).trans (e₁.trans e)

/-- I.8.1, global affine form: for every ideal `I` of `A`, every étale `A ⧸ I`-algebra `B₀` is
`(A ⧸ I) ⊗_A B` for an étale `A`-algebra `B` (`SGA.Foundations.Formal.EtaleLift`: lift a
presentation with invertible Jacobian and invert the lifted Jacobian). SGA only claims this
locally on `Spec B₀` (`exists_etale_lift_away`). -/
theorem exists_etale_lift (I : Ideal A) (B₀ : Type u) [CommRing B₀] [Algebra (A ⧸ I) B₀]
    [Algebra.Etale (A ⧸ I) B₀] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Algebra.Etale A B ∧
      Nonempty ((A ⧸ I) ⊗[A] B ≃ₐ[A ⧸ I] B₀) :=
  Algebra.Etale.exists_etale_tensorQuotient_equiv I B₀

/-- I.8.2, in SGA's form: let `A` be local with infinite residue field, `I` a proper ideal, and
`B₀` a finite étale `A ⧸ I`-algebra. Then `B₀ ≅ (A ⧸ I) ⊗_A B` for a finite étale `A`-algebra
`B` (of the form `A[t]/(F)`), as in I.8.1 with I.7.5 in place of I.7.6. -/
theorem exists_finite_etale_lift_of_infinite [IsLocalRing A] [Infinite (ResidueField A)]
    (I : Ideal A) (hI : I ≠ ⊤) (B₀ : Type u) [CommRing B₀] [Algebra (A ⧸ I) B₀]
    [Module.Finite (A ⧸ I) B₀] [Algebra.Etale (A ⧸ I) B₀] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
      Nonempty ((A ⧸ I) ⊗[A] B ≃ₐ[A ⧸ I] B₀) := by
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (A ⧸ I) := .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : Infinite (ResidueField (A ⧸ I)) :=
    .of_injective _ (ResidueField.map (Ideal.Quotient.mk I)).injective
  obtain ⟨F₀, hF₀m, hF₀s, -, ⟨e⟩⟩ :=
    exists_algEquiv_adjoinRoot_of_etale_of_infinite (A := A ⧸ I) (B := B₀)
  obtain ⟨F, hF, -, hFm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective F₀) hF₀m
  have hI' : I ≤ maximalIdeal A := le_maximalIdeal hI
  let ψ : A ⧸ I →+* ResidueField A := Ideal.Quotient.factor hI'
  have hψ : ψ.comp (Ideal.Quotient.mk I) = residue A := Ideal.Quotient.factor_comp_mk hI'
  have hFs : F.Separable := separable_of_separable_map_residue hFm (by
    rw [← hψ, ← Polynomial.map_map, hF]; exact hF₀s.map)
  have := etale_adjoinRoot_of_separable hFm hFs
  have := hFm.finite_adjoinRoot
  refine ⟨AdjoinRoot F, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  have e₁ : AdjoinRoot (F.map (algebraMap A (A ⧸ I))) ≃ₐ[A ⧸ I] AdjoinRoot F₀ := by
    have : F.map (algebraMap A (A ⧸ I)) = F₀ := hF
    rw [this]
  exact (tensorAdjoinRootEquiv _ F).trans (e₁.trans e)

/-- An element whose image under a surjection with nilpotent kernel is a unit is a unit. -/
lemma isUnit_of_isUnit_map_of_isNilpotent_ker {B C : Type*} [CommRing B] [CommRing C]
    (φ : B →+* C) (hφ : Function.Surjective φ) (hK : IsNilpotent (RingHom.ker φ)) {x : B}
    (hx : IsUnit (φ x)) : IsUnit x := by
  obtain ⟨y, hy⟩ := hφ (hx.unit⁻¹ : Cˣ)
  have h1 : x * y - 1 ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, map_mul, hy, map_one, IsUnit.mul_val_inv, sub_self]
  obtain ⟨n, hn⟩ := hK
  have hnil : IsNilpotent (x * y - 1) := ⟨n, by
    have := Ideal.pow_mem_pow h1 n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this⟩
  have : IsUnit (x * y) := by
    have := hnil.isUnit_one_add
    rwa [add_sub_cancel] at this
  exact isUnit_of_mul_isUnit_left this


/-- I.8.3, affine form of essential surjectivity: if `I` is a nilpotent ideal of `A`, every
étale `A ⧸ I`-algebra is `(A ⧸ I) ⊗_A B` for an étale `A`-algebra `B`. We lift a global
presentation `B₀ = A₀[x₁,…,xₙ]/(f₁,…,fₙ)` with invertible Jacobian (mathlib: étale
algebras are standard smooth of relative dimension `0`); the Jacobian stays invertible
since `I` is nilpotent. -/
theorem exists_etale_lift_of_isNilpotent (I : Ideal A) (hI : IsNilpotent I) (B₀ : Type u)
    [CommRing B₀] [Algebra (A ⧸ I) B₀] [Algebra.Etale (A ⧸ I) B₀] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Algebra.Etale A B ∧
      Nonempty ((A ⧸ I) ⊗[A] B ≃ₐ[A ⧸ I] B₀) := by
  classical
  obtain ⟨ι, σ, _, _, P₀, hP₀⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp ‹_›).out
  let π : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hπ : Function.Surjective (MvPolynomial.map π : MvPolynomial ι A → _) :=
    MvPolynomial.map_surjective π Ideal.Quotient.mk_surjective
  let rel : σ → MvPolynomial ι A := fun j ↦ Function.surjInv hπ (P₀.relation j)
  have hrel (j : σ) : MvPolynomial.map π (rel j) = P₀.relation j := Function.surjInv_eq hπ _
  let J : Ideal (MvPolynomial ι A) := Ideal.span (Set.range rel)
  let B := MvPolynomial ι A ⧸ J
  let P := PreSubmersivePresentation.naive (v := rel) P₀.map P₀.map_inj
  -- the comparison map `B → B₀`
  let ψ : MvPolynomial ι A →+* B₀ := (MvPolynomial.aeval P₀.val).toRingHom.comp (MvPolynomial.map π)
  have hψ : J ≤ RingHom.ker ψ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simp [ψ, hrel]
  let φ : B →+* B₀ := Ideal.Quotient.lift J ψ hψ
  have hφ (p : MvPolynomial ι A) : φ (Ideal.Quotient.mk J p) = ψ p := rfl
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨p₀, rfl⟩ := P₀.aeval_val_surjective y
    obtain ⟨p, rfl⟩ := hπ p₀
    exact ⟨Ideal.Quotient.mk J p, rfl⟩
  -- the kernel of `B → B₀` is `I B`, hence nilpotent
  have hker : RingHom.ker φ ≤ I.map (algebraMap A B) := by
    intro b hb
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [RingHom.mem_ker, hφ] at hb
    have h1 : MvPolynomial.map π p ∈ J.map (MvPolynomial.map π) := by
      rw [Ideal.map_span, ← Set.range_comp]
      have : (MvPolynomial.map π ∘ rel) = P₀.relation := funext hrel
      rw [this, P₀.span_range_relation_eq_ker, P₀.ker_eq_ker_aeval_val]
      exact hb
    obtain ⟨q, hq, hpq⟩ := (Ideal.mem_map_iff_of_surjective _ hπ).mp h1
    have h2 : p - q ∈ Ideal.map (MvPolynomial.C : A →+* MvPolynomial ι A) I := by
      rw [← Ideal.mk_ker (I := I), ← MvPolynomial.ker_map, RingHom.mem_ker, map_sub, hpq,
        sub_self]
    have : Ideal.Quotient.mk J p = Ideal.Quotient.mk J (p - q) := by
      rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hq, sub_zero]
    rw [this]
    have h3 := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) h2
    rwa [Ideal.map_map] at h3
  have hnil : IsNilpotent (RingHom.ker φ) := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, le_bot_iff.mp ?_⟩
    calc RingHom.ker φ ^ n ≤ (I.map (algebraMap A B)) ^ n := Ideal.pow_right_mono hker n
      _ = (I ^ n).map (algebraMap A B) := (Ideal.map_pow _ _ _).symm
      _ = ⊥ := by rw [hn, Ideal.zero_eq_bot, Ideal.map_bot]
  -- the Jacobian of the lifted presentation is invertible
  have := Fintype.ofFinite σ
  have hjac : IsUnit P.jacobian := by
    refine isUnit_of_isUnit_map_of_isNilpotent_ker φ hφsurj hnil ?_
    convert P₀.jacobian_isUnit using 1
    rw [P.jacobian_eq_jacobiMatrix_det, P₀.jacobian_eq_jacobiMatrix_det,
      Generators.algebraMap_apply P₀.toGenerators]
    change φ (Ideal.Quotient.mk J _) = _
    rw [hφ]
    simp only [ψ, RingHom.map_det]
    rw [← AlgHom.coe_toRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_comp, Function.comp_apply,
      PreSubmersivePresentation.jacobiMatrix_apply]
    rw [← MvPolynomial.pderiv_map]
    change MvPolynomial.aeval P₀.val
      (MvPolynomial.pderiv (P₀.map i) (MvPolynomial.map π (rel j))) = _
    rw [hrel]
    rfl
  let Q : SubmersivePresentation A B ι σ := ⟨P, hjac⟩
  have : IsStandardSmoothOfRelativeDimension 0 A B :=
    Q.isStandardSmoothOfRelativeDimension (by rw [← hP₀]; rfl)
  refine ⟨B, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  -- the reduction `(A ⧸ I) ⊗_A B = B ⧸ I B` is `B₀`
  have hφa (a : A) : φ (algebraMap A B a) = algebraMap (A ⧸ I) B₀ (π a) := by
    change φ (Ideal.Quotient.mk J (MvPolynomial.C a)) = _
    rw [hφ]
    simp [ψ, π]
  have hkereq : I.map (algebraMap A B) = RingHom.ker φ := by
    refine le_antisymm ?_ hker
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, hφa,
      show π a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha,
      map_zero]
  let e : (A ⧸ I) ⊗[A] B ≃+* B₀ :=
    (quotientEquivQuotientTensor I (B' := B)).symm.toRingEquiv.trans
      ((Ideal.quotEquivOfEq hkereq).trans (RingHom.quotientKerEquivOfSurjective hφsurj))
  refine AlgEquiv.ofRingEquiv (f := e) fun x ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : (Ideal.Quotient.mk I a ⊗ₜ[A] (1 : B) : (A ⧸ I) ⊗[A] B) =
      quotientEquivQuotientTensor I (Ideal.Quotient.mk _ (algebraMap A B a)) := by
    rw [quotientEquivQuotientTensor_mk, Algebra.algebraMap_eq_smul_one a, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rfl
  change e (Ideal.Quotient.mk I a ⊗ₜ[A] (1 : B)) = _
  rw [h1]
  simp only [e, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
    AlgEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  exact hφa a


/-- I.5.5 / I.8.3 for affine schemes and a nilpotent ideal `I`: if `B` is formally étale
over `A`, then `f ↦ (A ⧸ I) ⊗_A f` is a bijection
`Hom_A(B, B') → Hom_{A/I}((A ⧸ I) ⊗_A B, (A ⧸ I) ⊗_A B')` for every `A`-algebra `B'`. -/
theorem bijective_map_quotient_of_isNilpotent (I : Ideal A) (hI : IsNilpotent I)
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']
    [Algebra.FormallyEtale A B] :
    Function.Bijective fun f : B →ₐ[A] B' ↦
      Algebra.TensorProduct.map (AlgHom.id (A ⧸ I) (A ⧸ I)) f := by
  have hI' : IsNilpotent (I.map (algebraMap A B')) := by
    obtain ⟨n, hn⟩ := hI
    exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]; rfl⟩
  let e := quotientEquivQuotientTensor I (B' := B')
  refine ⟨fun f g hfg ↦ ?_, fun φ ↦ ?_⟩
  · refine Algebra.FormallyUnramified.ext (I := I.map (algebraMap A B')) hI' fun b ↦ ?_
    apply e.injective
    have := congr($hfg (1 ⊗ₜ b))
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at this
    rw [quotientEquivQuotientTensor_mk, quotientEquivQuotientTensor_mk]
    exact this
  · let φ₀ : B →ₐ[A] B' ⧸ I.map (algebraMap A B') :=
      (e.symm.toAlgHom).comp ((φ.restrictScalars A).comp Algebra.TensorProduct.includeRight)
    refine ⟨Algebra.FormallySmooth.lift _ hI' φ₀,
      Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_⟩
    ext b
    have := congr(e ($(Algebra.FormallySmooth.comp_lift _ hI' φ₀) b))
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, φ₀] at this
    rw [quotientEquivQuotientTensor_mk] at this
    simpa using this

/-- I.8.4, affine form, full faithfulness: if `A` is noetherian and `I`-adically complete,
`B ↦ (A ⧸ I) ⊗_A B` is fully faithful on finite étale algebras. -/
theorem finiteEtale_baseChange_quotient_full_and_faithful (I : Ideal A) [IsNoetherianRing A]
    [IsAdicComplete I A] :
    (CommAlgCat.FiniteEtale.baseChange.{u} A (A ⧸ I)).Full ∧
      (CommAlgCat.FiniteEtale.baseChange.{u} A (A ⧸ I)).Faithful := by
  refine ⟨⟨fun {X Y} φ ↦ ?_⟩, ⟨fun {X Y} f g h ↦ ?_⟩⟩
  · obtain ⟨f, hf⟩ := (bijective_map_quotient I (B := X.obj) (B' := Y.obj)).2 φ.hom.hom
    refine ⟨⟨CommAlgCat.ofHom f⟩, ?_⟩
    ext : 2
    exact hf
  · have h' : Algebra.TensorProduct.map (AlgHom.id (A ⧸ I) (A ⧸ I)) f.hom.hom =
        Algebra.TensorProduct.map (AlgHom.id (A ⧸ I) (A ⧸ I)) g.hom.hom :=
      congr($(h).hom.hom)
    have := (bijective_map_quotient I (B := X.obj) (B' := Y.obj)).1 h'
    ext : 2
    exact this

/-- I.8.4, affine form: if `A` is noetherian and `I`-adically complete, `B ↦ (A ⧸ I) ⊗_A B` is
an equivalence from finite étale `A`-algebras to finite étale `A ⧸ I`-algebras, i.e. étale
coverings of `Spf A` and of `Spec (A ⧸ I)` correspond (EGA IV 18.3; proved in
`SGA.Foundations.Formal.FiniteEtale`: full faithfulness as in I.8.4 above, and a finite étale
`A ⧸ I`-algebra lifts to an étale `A`-algebra whose `I`-adic completion is finite étale). The
form for a formal scheme given as a system of thickenings, deduced from I.8.3, is
`AlgebraicGeometry.Scheme.FormalFiniteEtale.isEquivalence_toZero`. -/
theorem isEquivalence_finiteEtale_baseChange_quotient (I : Ideal A) [IsNoetherianRing A]
    [IsAdicComplete I A] : (CommAlgCat.FiniteEtale.baseChange.{u} A (A ⧸ I)).IsEquivalence :=
  inferInstance

/-- Base change of finite étale algebras along `A → A₀` and then `A₀ → k` is base change
along `A → k`. -/
noncomputable def finiteEtaleBaseChangeCompIso (A₀ k : Type u) [CommRing A₀] [CommRing k]
    [Algebra A A₀] [Algebra A k] [Algebra A₀ k] [IsScalarTower A A₀ k] :
    CommAlgCat.FiniteEtale.baseChange.{u} A A₀ ⋙ CommAlgCat.FiniteEtale.baseChange.{u} A₀ k ≅
      CommAlgCat.FiniteEtale.baseChange.{u} A k :=
  NatIso.ofComponents (fun B ↦ CommAlgCat.FiniteEtale.isoMk
    (Algebra.TensorProduct.cancelBaseChange A A₀ k k B.obj)) fun {B B'} f ↦ by
    dsimp [CommAlgCat.FiniteEtale.baseChange]
    ext x
    simp [ObjectProperty.FullSubcategory.comp_hom, Algebra.TensorProduct.cancelBaseChange_tmul]

/-- I.8.4 for a complete noetherian local ring `A` and a proper ideal `I` (the formal
spectrum `Spf A` for the `I`-adic topology): `B ↦ (A ⧸ I) ⊗_A B` is an equivalence between
finite étale `A`-algebras and finite étale `A ⧸ I`-algebras. Both sides are equivalent to
finite étale algebras over the common residue field (I.6.1). -/
theorem isEquivalence_finiteEtale_baseChange_quotient_of_isLocalRing [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] (I : Ideal A) (hI : I ≠ ⊤) :
    (CommAlgCat.FiniteEtale.baseChange.{u} A (A ⧸ I)).IsEquivalence := by
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (A ⧸ I) := .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let k := ResidueField (A ⧸ I)
  have hk : Function.Surjective (algebraMap A k) := by
    rw [IsScalarTower.algebraMap_eq A (A ⧸ I) k]
    exact residue_surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (algebraMap A k) = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hk)
  have : IsAdicComplete (RingHom.ker (algebraMap A k)) A := hker ▸ inferInstance
  have h₀ : IsAdicComplete (maximalIdeal (A ⧸ I)) (A ⧸ I) := by
    have := isAdicComplete_of_finite (maximalIdeal A) (A ⧸ I)
    rw [← map_maximalIdeal_of_surjective (algebraMap A (A ⧸ I)) Ideal.Quotient.mk_surjective]
    exact (IsAdicComplete.map_algebraMap_iff _ _).mpr this
  have : IsAdicComplete (RingHom.ker (algebraMap (A ⧸ I) k)) (A ⧸ I) := by
    rw [show algebraMap (A ⧸ I) k = residue (A ⧸ I) from rfl, IsLocalRing.ker_residue]
    exact h₀
  have := isEquivalence_finiteEtale_baseChange_of_surjective hk
  have := isEquivalence_finiteEtale_baseChange_of_surjective (A := A ⧸ I) (k := k)
    residue_surjective
  let i := finiteEtaleBaseChangeCompIso (A := A) (A ⧸ I) k
  have : (CommAlgCat.FiniteEtale.baseChange.{u} A (A ⧸ I)).Faithful :=
    Functor.Faithful.of_comp_iso i
  have : (CommAlgCat.FiniteEtale.baseChange.{u} A (A ⧸ I)).Full :=
    Functor.Full.of_comp_faithful_iso i
  refine { essSurj := ⟨fun X₀ ↦ ?_⟩ }
  let H := CommAlgCat.FiniteEtale.baseChange.{u} A k
  let G₀ := CommAlgCat.FiniteEtale.baseChange.{u} (A ⧸ I) k
  let B := H.objPreimage (G₀.obj X₀)
  exact ⟨B, ⟨(Functor.FullyFaithful.ofFullyFaithful G₀).preimageIso
    ((i.app B).trans (H.objObjPreimageIso (G₀.obj X₀)))⟩⟩

end SGA.SGA1.ExposeI
