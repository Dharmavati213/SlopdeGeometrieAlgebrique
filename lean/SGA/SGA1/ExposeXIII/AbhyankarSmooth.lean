/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeXIII.AbhyankarBasic

/-!
# SGA 1, Exposé XIII, 5.4: smoothness of `X[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`

XIII.5.4, smoothness part (`rootAdjunctionSmoothStatement`): the `dfᵢ(x)` are linearly
independent (`linearIndependent_of_formallySmooth_quotient`, by the Jacobian criterion II.4.10
and Krull's height theorem), hence part of étale coordinates (II.4.11), and `X'` is étale over
`S[Tᵢ, sⱼ]` near `x'` (`isSmoothAt_of_algEquiv_kummerAlgebra`).
-/

universe u

open IsLocalRing
open scoped TensorProduct

namespace SGA.SGA1.ExposeXIII

variable {A : Type u} [CommRing A] {ι : Type*}

section RootAdjunctionSmooth

/-! ### XIII.5.4: smoothness of `X' = X[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` -/

open Algebra KaehlerDifferential TensorProduct

/-- XIII.5.4, the key step: let `P = 𝒪_{X,x}` be local, noetherian, essentially of finite type and
formally smooth over `R`, and `f₁, …, f_r` elements of `𝔪_P` generating an ideal `J` of height `r`
with `P/J` formally smooth over `R` (`V(f)` smooth of codimension `r` at `x`). Then the
differentials `dfᵢ(x)` are linearly independent in `Ω¹_{X/S}(x)`. -/
theorem linearIndependent_of_formallySmooth_quotient {R P : Type u} [CommRing R] [CommRing P]
    [Algebra R P] [IsLocalRing P] [IsNoetherianRing P] [FormallySmooth R P] [EssFiniteType R P]
    [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]] {r : ℕ} (f : Fin r → P)
    (hf : ∀ i, f i ∈ maximalIdeal P)
    (hY : FormallySmooth R (P ⧸ Ideal.span (Set.range f)))
    (hht : (Ideal.span (Set.range f)).height = r) :
    LinearIndependent (ResidueField P) fun i ↦ (1 : ResidueField P) ⊗ₜ[P] D R P (f i) := by
  classical
  set J := Ideal.span (Set.range f)
  have hJm : J ≤ maximalIdeal P := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hf i
  have hJfg : J.FG := ⟨Finset.univ.image f, by rw [Finset.coe_image, Finset.coe_univ,
    Set.image_univ]⟩
  obtain ⟨p, g, hgJ, hgli⟩ :=
    (SGA.SGA1.ExposeII.formallySmooth_quotient_iff_exists_linearIndependent J hJm hJfg).mp hY
  -- the map `x ↦ dx(x)` sends `J` into the span of the `dfᵢ(x)`
  let φ : P → ResidueField P ⊗[P] Ω[P⁄R] := fun x ↦ (1 : ResidueField P) ⊗ₜ[P] D R P x
  let V := Submodule.span (ResidueField P) (Set.range fun i ↦ φ (f i))
  have hJV : ∀ x ∈ J, φ x ∈ V := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero =>
      change (1 : ResidueField P) ⊗ₜ[P] D R P 0 ∈ V
      rw [map_zero, TensorProduct.tmul_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      change (1 : ResidueField P) ⊗ₜ[P] D R P (x + y) ∈ V
      rw [map_add, TensorProduct.tmul_add]
      exact add_mem hx hy
    | smul c x hxJ hx =>
      change (1 : ResidueField P) ⊗ₜ[P] D R P (c • x) ∈ V
      have hx0 : residue P x = 0 := (residue_eq_zero_iff x).mpr (hJm hxJ)
      have hsmul (a : P) (m : Ω[P⁄R]) : a • ((1 : ResidueField P) ⊗ₜ[P] m) =
          residue P a • ((1 : ResidueField P) ⊗ₜ[P] m) := by
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul,
          mul_one, mul_one, ResidueField.algebraMap_eq]
      rw [smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
        TensorProduct.tmul_smul, hsmul, hsmul, hx0, zero_smul, add_zero]
      exact Submodule.smul_mem _ _ hx
  have hgV : Submodule.span (ResidueField P) (Set.range fun k ↦ φ (g k)) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hJV (g k) (hgJ ▸ Ideal.subset_span ⟨k, rfl⟩)
  have h1 : p ≤ Module.finrank (ResidueField P) V := by
    have := Submodule.finrank_mono hgV
    rwa [finrank_span_eq_card hgli, Fintype.card_fin] at this
  have h2 : Module.finrank (ResidueField P) V ≤ r := by
    have := finrank_range_le_card (R := ResidueField P) (fun i ↦ φ (f i))
    rw [Fintype.card_fin] at this
    exact this
  -- Krull's height theorem: `r = ht J ≤ p`
  have h3 : r ≤ p := by
    obtain ⟨P₀, hP₀, -⟩ := Ideal.exists_minimalPrimes_le hJm
    have h4 : J.height ≤ P₀.height := by
      rw [Ideal.height_eq_inf_minimalPrimes]
      exact iInf₂_le P₀ hP₀
    have h5 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
      (s := Finset.univ.image g) (p := P₀) (by
        rwa [Finset.coe_image, Finset.coe_univ, Set.image_univ, hgJ])
    have h6 : (Finset.univ.image g).card ≤ p := Finset.card_image_le.trans (by simp)
    have := (h4.trans h5).trans (by exact_mod_cast h6 : (((Finset.univ.image g).card : ℕ) :
      ℕ∞) ≤ p)
    rw [hht] at this
    exact_mod_cast this
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  change r = Module.finrank (ResidueField P) V
  omega

namespace KummerAlgebra

variable (R : Type*) [CommRing R] {ι κ : Type*} (n : ι → ℕ)

/-- The substitution `tᵢ ↦ Tᵢ^{nᵢ}`, `sⱼ ↦ sⱼ` of `R[t, s]` into `R[T, s]`. -/
noncomputable def powAlgHom : MvPolynomial (ι ⊕ κ) R →ₐ[R] MvPolynomial (ι ⊕ κ) R :=
  MvPolynomial.aeval (Sum.elim (fun i ↦ MvPolynomial.X (Sum.inl i) ^ n i)
    (fun j ↦ MvPolynomial.X (Sum.inr j)))

@[simp]
lemma powAlgHom_inl (i : ι) :
    powAlgHom (κ := κ) R n (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X (Sum.inl i) ^ n i := by
  simp [powAlgHom]

@[simp]
lemma powAlgHom_inr (j : κ) :
    powAlgHom (ι := ι) R n (MvPolynomial.X (Sum.inr j)) = MvPolynomial.X (Sum.inr j) := by
  simp [powAlgHom]

/-- The map `R[tᵢ, sⱼ][Tᵢ]/(Tᵢ^{nᵢ} - tᵢ) → R[Tᵢ, sⱼ]`, `tᵢ ↦ Tᵢ^{nᵢ}`. -/
noncomputable def toMvPolynomial :
    KummerAlgebra n (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (ι ⊕ κ) R)) →ₐ[R]
      MvPolynomial (ι ⊕ κ) R :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aevalTower (powAlgHom R n)
    (fun i ↦ MvPolynomial.X (Sum.inl i))) fun a ha ↦ by
      induction ha using Submodule.span_induction with
      | mem _ h =>
        obtain ⟨i, rfl⟩ := h
        simp [MvPolynomial.aevalTower_X, MvPolynomial.aevalTower_C]
      | zero => simp
      | add _ _ _ _ h₁ h₂ => simp [h₁, h₂]
      | smul c _ _ h => simp [h]

lemma toMvPolynomial_T (i : ι) :
    toMvPolynomial (κ := κ) R n (T n _ i) = MvPolynomial.X (Sum.inl i) := by
  rw [toMvPolynomial, T, Ideal.Quotient.liftₐ_apply]
  exact (Ideal.Quotient.lift_mk _ _ _).trans (MvPolynomial.aevalTower_X _ _ _)

lemma toMvPolynomial_algebraMap (m : MvPolynomial (ι ⊕ κ) R) :
    toMvPolynomial R n (algebraMap (MvPolynomial (ι ⊕ κ) R)
      (KummerAlgebra n (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (ι ⊕ κ) R))) m) =
      powAlgHom R n m := by
  rw [toMvPolynomial, IsScalarTower.algebraMap_apply (MvPolynomial (ι ⊕ κ) R)
    (MvPolynomial ι (MvPolynomial (ι ⊕ κ) R)), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.liftₐ_apply]
  exact (Ideal.Quotient.lift_mk _ _ _).trans (MvPolynomial.aevalTower_C _ _ _)

/-- `R[tᵢ, sⱼ][Tᵢ]/(Tᵢ^{nᵢ} - tᵢ)` is the polynomial ring `R[Tᵢ, sⱼ]`. -/
noncomputable def mvPolynomialEquiv :
    KummerAlgebra n (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (ι ⊕ κ) R)) ≃ₐ[R]
      MvPolynomial (ι ⊕ κ) R :=
  AlgEquiv.ofAlgHom (toMvPolynomial R n)
    (MvPolynomial.aeval (Sum.elim (T n _) fun j ↦ algebraMap (MvPolynomial (ι ⊕ κ) R)
      (KummerAlgebra n (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (ι ⊕ κ) R)))
        (MvPolynomial.X (Sum.inr j))))
    (MvPolynomial.algHom_ext fun
      | Sum.inl i => by simp [toMvPolynomial_T]
      | Sum.inr j => by simp [toMvPolynomial_algebraMap])
    (by
      let ψ := MvPolynomial.aeval (R := R) (Sum.elim (T n _) fun j ↦ algebraMap
        (MvPolynomial (ι ⊕ κ) R)
        (KummerAlgebra n (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (ι ⊕ κ) R)))
        (MvPolynomial.X (Sum.inr j)))
      have hM : ((ψ.comp (toMvPolynomial R n)).comp (IsScalarTower.toAlgHom R
          (MvPolynomial (ι ⊕ κ) R)
          (KummerAlgebra n (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (ι ⊕ κ) R))))) =
          IsScalarTower.toAlgHom R (MvPolynomial (ι ⊕ κ) R)
            (KummerAlgebra n (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (ι ⊕ κ) R))) := by
        refine MvPolynomial.algHom_ext fun
          | Sum.inl i => ?_
          | Sum.inr j => ?_
        · rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
            toMvPolynomial_algebraMap, powAlgHom_inl, map_pow]
          simp only [ψ, MvPolynomial.aeval_X, Sum.elim_inl]
          exact T_pow n _ i
        · rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
            toMvPolynomial_algebraMap, powAlgHom_inr]
          simp only [ψ, MvPolynomial.aeval_X, Sum.elim_inr]
      refine Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext' (AlgHom.ext fun m ↦ ?_)
        fun i ↦ ?_)
      · exact DFunLike.congr_fun hM m
      · change ψ (toMvPolynomial R n (T n _ i)) = T n _ i
        rw [toMvPolynomial_T]
        simp [ψ])

end KummerAlgebra

/-- XIII.5.4, smoothness part: let `A` be finitely presented over a noetherian ring `R`, smooth at
a prime `q` containing `f₁, …, f_r`, such that `V(f)` is smooth over `R` at `q` of codimension `r`.
Then `A' = A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` is smooth over `R` at every prime over `q`. The `dfᵢ(x)` are
linearly independent (`linearIndependent_of_formallySmooth_quotient`), so `(f, h)` are étale
coordinates at `q` for suitable `h` (II.4.11); then `A'_q` is the base change of the étale
`R[t, s] → A_q` along `R[t, s] → R[T, s]`, `tᵢ ↦ Tᵢ^{nᵢ}`, which is smooth over `R`. -/
theorem isSmoothAt_of_algEquiv_kummerAlgebra {R A : Type u} [CommRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] {r : ℕ} (f : Fin r → A)
    (n : Fin r → ℕ) (q : Ideal A) [q.IsPrime] (hfq : ∀ i, f i ∈ q) (hsm : Algebra.IsSmoothAt R q)
    (hY : FormallySmooth R (Localization.AtPrime q ⧸
      (Ideal.span (Set.range f)).map (algebraMap A (Localization.AtPrime q))))
    (hht : ((Ideal.span (Set.range f)).map (algebraMap A (Localization.AtPrime q))).height = r)
    (S : Type u) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
    (σ₀ : S ≃ₐ[A] KummerAlgebra n f)
    (Q : Ideal S) [Q.IsPrime] (hQ : Q.LiesOver q) : Algebra.IsSmoothAt R Q := by
  classical
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have : FormallySmooth R (Localization.AtPrime q) := hsm
  have : Module.Free (Localization.AtPrime q) Ω[Localization.AtPrime q⁄R] :=
    SGA.SGA1.ExposeII.free_kaehler_of_formallySmooth (A := R) (B := Localization.AtPrime q)
  let f' : Fin r → Localization.AtPrime q := fun i ↦ algebraMap A _ (f i)
  have hJ : (Ideal.span (Set.range f)).map (algebraMap A (Localization.AtPrime q)) =
      Ideal.span (Set.range f') := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hJ] at hY hht
  have hf' (i : Fin r) : f' i ∈ maximalIdeal (Localization.AtPrime q) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q (f i)).mpr (hfq i)
  have hli := linearIndependent_of_formallySmooth_quotient f' hf' hY hht
  obtain ⟨q', h, het⟩ :=
    (SGA.SGA1.ExposeII.linearIndependent_iff_exists_formallyEtale (R := R) f').mp hli
  -- `M = R[t, s] → A_q` is formally étale
  let : Algebra (MvPolynomial (Fin r ⊕ Fin q') R) (Localization.AtPrime q) :=
    (MvPolynomial.aeval (Sum.elim f' h)).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin r ⊕ Fin q') R) (Localization.AtPrime q) :=
    .of_algHom (MvPolynomial.aeval (Sum.elim f' h))
  have : Algebra.FormallyEtale (MvPolynomial (Fin r ⊕ Fin q') R) (Localization.AtPrime q) := het
  -- `KM = M[Tᵢ]/(Tᵢ^{nᵢ} - tᵢ) = R[T, s]` is smooth over `R`
  have : FormallySmooth R
      (KummerAlgebra n (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin r ⊕ Fin q') R))) :=
    FormallySmooth.of_equiv (KummerAlgebra.mvPolynomialEquiv R n).symm
  have : FormallySmooth R
      (KummerAlgebra n (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin r ⊕ Fin q') R)) ⊗[
        MvPolynomial (Fin r ⊕ Fin q') R] Localization.AtPrime q) :=
    FormallySmooth.comp R
      (KummerAlgebra n (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin r ⊕ Fin q') R))) _
  -- `KM ⊗_M A_q ≅ A_q ⊗_A A'`
  have hff : (fun i ↦ algebraMap (MvPolynomial (Fin r ⊕ Fin q') R) (Localization.AtPrime q)
      (MvPolynomial.X (Sum.inl i))) = f' := funext fun i ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  let e3 : KummerAlgebra n (fun i ↦ algebraMap (MvPolynomial (Fin r ⊕ Fin q') R)
      (Localization.AtPrime q) (MvPolynomial.X (Sum.inl i))) ≃ₐ[Localization.AtPrime q]
      KummerAlgebra n f' := hff ▸ AlgEquiv.refl
  let e4 := ((Algebra.TensorProduct.comm (MvPolynomial (Fin r ⊕ Fin q') R)
    (KummerAlgebra n (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin r ⊕ Fin q') R)))
    (Localization.AtPrime q)).restrictScalars R).trans
    (((KummerAlgebra.baseChangeEquiv n _ (Localization.AtPrime q)).trans
      (e3.trans ((KummerAlgebra.baseChangeEquiv n f (Localization.AtPrime q)).symm.trans
        (Algebra.TensorProduct.congr AlgEquiv.refl σ₀.symm)))).restrictScalars R)
  have : FormallySmooth R (Localization.AtPrime q ⊗[A] S) :=
    FormallySmooth.of_equiv (A := KummerAlgebra n
      (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin r ⊕ Fin q') R)) ⊗[
        MvPolynomial (Fin r ⊕ Fin q') R] Localization.AtPrime q) e4
  -- `A_q ⊗_A A'` is the localization of `A'` at `A - q`
  let Bp := Localization (Algebra.algebraMapSubmonoid S q.primeCompl)
  have hpush : Algebra.IsPushout A (Localization.AtPrime q) S Bp :=
    (Algebra.isPushout_of_isLocalization q.primeCompl (Localization.AtPrime q) S Bp).symm
  have : IsScalarTower R (Localization.AtPrime q) Bp := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime q),
      ← IsScalarTower.algebraMap_apply A (Localization.AtPrime q) Bp,
      ← IsScalarTower.algebraMap_apply R A Bp]
  have : FormallySmooth R Bp := FormallySmooth.of_equiv (A := Localization.AtPrime q ⊗[A] S)
    ((Algebra.IsPushout.equiv A (Localization.AtPrime q) S Bp).restrictScalars R)
  -- `S_Q` is a localization of `Bp`
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid S q.primeCompl : Set S) Q := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsQ
    apply hs
    rw [hQ.over]
    exact hsQ
  let Q' := Q.map (algebraMap S Bp)
  have : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Bp Q ‹_› hdisj
  have hQQ : Q'.comap (algebraMap S Bp) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint _ Bp ‹_› hdisj
  have : FormallyEtale Bp (Localization.AtPrime Q') :=
    FormallyEtale.of_isLocalization Q'.primeCompl
  have : FormallySmooth R (Localization.AtPrime Q') := FormallySmooth.comp R Bp _
  have hL : IsLocalization.AtPrime (Localization.AtPrime Q') (Q'.comap (algebraMap S Bp)) :=
    inferInstance
  have : IsLocalization.AtPrime (Localization.AtPrime Q') Q := by
    convert hL using 2
    exact hQQ.symm
  let e' : Localization.AtPrime Q ≃ₐ[S] Localization.AtPrime Q' :=
    IsLocalization.algEquiv Q.primeCompl _ _
  exact FormallySmooth.of_equiv (e'.restrictScalars R).symm

/-- XIII.5.4, smoothness part: `RootAdjunctionSmoothStatement`. -/
theorem rootAdjunctionSmoothStatement : RootAdjunctionSmoothStatement.{u} :=
  fun _ _ _ _ _ _ _ _ f n q _ _ hfq hsm hY hht Q _ hQ ↦
    isSmoothAt_of_algEquiv_kummerAlgebra f n q hfq hsm hY hht _ AlgEquiv.refl Q hQ

end RootAdjunctionSmooth

end SGA.SGA1.ExposeXIII
