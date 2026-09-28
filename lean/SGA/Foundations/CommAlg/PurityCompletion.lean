/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.ZariskisMainTheorem
import SGA.Foundations.CommAlg.Purity
import SGA.Foundations.CompleteLocalQuasiFinite
import SGA.Foundations.CompletionDimension
import SGA.Foundations.Dimension.Integral

/-!
# Completion and base change for the purity theorem

General facts used in the proof of purity for quasi-finite algebras
(`SGA.Foundations.CommAlg.PurityQuasiFinite`) and in the reduction of purity to complete regular
local rings (`SGA.Foundations.CommAlg.PurityInduction`):

* `IsRegularLocalRing.adicCompletion`: the completion of a regular local ring is regular of the same
  dimension.
* `Algebra.IsEtaleAt.baseChange`: étaleness at a prime is stable under base change.
* `eq_of_comap_includeRight_eq`, `comap_algebraMap_eq_maximalIdeal_of_comap_includeRight`: primes
  of `Â ⊗_A S` over the closed point.
* `Ideal.height_comap_le_of_quasiFiniteAt`: a quasi-finite extension of a normal domain does not
  lower heights (Zariski's main theorem and going down).
* `isWeaklyRegular_localization_tensorProduct`: regular sequences under flat base change of local
  rings.
* `exists_notMem_forall_isEtaleAt`: a neighbourhood of a quasi-finite point on which the algebra is
  étale away from the point.
-/

universe u

open IsLocalRing RingTheory.Sequence

section Completion

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]

/-- The completion of a regular local ring is a regular local ring of the same dimension. -/
theorem IsRegularLocalRing.adicCompletion :
    IsRegularLocalRing (AdicCompletion (maximalIdeal A) A) ∧
      ringKrullDim (AdicCompletion (maximalIdeal A) A) = ringKrullDim A := by
  classical
  let Â := AdicCompletion (maximalIdeal A) A
  obtain ⟨rs, hlen, hspan, hreg⟩ := IsRegularLocalRing.exists_isRegular_ofList_eq_maximalIdeal
    (R := A)
  have hreg' : IsWeaklyRegular Â (rs.map (algebraMap A Â)) := hreg.1.of_flat
  have hmax : maximalIdeal Â = Ideal.ofList (rs.map (algebraMap A Â)) := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_ofList, hspan]
  have hmem : ∀ r ∈ rs.map (algebraMap A Â), r ∈ maximalIdeal Â := fun r hr ↦ by
    rw [hmax]; exact Ideal.subset_span hr
  have hge : ((rs.length : ℕ) : WithBot ℕ∞) ≤ ringKrullDim Â := by
    have h1 := Ideal.length_le_depth hmem hreg'
    rw [List.length_map] at h1
    exact (WithBot.coe_le_coe.mpr h1).trans (IsLocalRing.depth_le_ringKrullDim (M := Â))
  have hdim : ringKrullDim Â = ringKrullDim A :=
    le_antisymm (IsLocalRing.ringKrullDim_adicCompletion_le (A := A)) (hlen ▸ hge)
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Â ?_, hdim⟩
  rw [hdim, ← hlen, hmax, Ideal.ofList]
  have hfin : {r | r ∈ rs.map (algebraMap A Â)}.Finite := (rs.map (algebraMap A Â)).finite_toSet
  refine WithBot.coe_le_coe.mpr (Nat.cast_le.mpr ?_)
  refine (Submodule.spanFinrank_span_le_ncard_of_finite hfin).trans ?_
  calc {r | r ∈ rs.map (algebraMap A Â)}.ncard
      = (rs.map (algebraMap A Â)).toFinset.card := by
        rw [← Set.ncard_coe_finset]; congr 1; ext; simp
    _ ≤ (rs.map (algebraMap A Â)).length := List.toFinset_card_le _
    _ = rs.length := List.length_map _

end Completion

section BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
  (T : Type u) [CommRing T] [Algebra R T]

open scoped TensorProduct in
/-- Étaleness at a prime is preserved by base change. -/
theorem Algebra.IsEtaleAt.baseChange (P : Ideal S) [P.IsPrime] [Algebra.IsEtaleAt R P]
    (Q : Ideal (T ⊗[R] S)) [Q.IsPrime]
    (hQ : Q.comap Algebra.TensorProduct.includeRight.toRingHom = P) :
    Algebra.IsEtaleAt T Q := by
  obtain ⟨h, hhP, hEt⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) P
  let e := IsLocalization.Away.tensorProductEquivTMulRight R T h (Localization.Away h)
  have : Algebra.Etale T (Localization.Away ((1 : T) ⊗ₜ[R] h)) := Algebra.Etale.of_equiv e
  have hsub := (Algebra.basicOpen_subset_etaleLocus_iff_etale (R := T)).mpr this
  refine hsub (show (⟨Q, ‹_›⟩ : PrimeSpectrum (T ⊗[R] S)) ∈
    PrimeSpectrum.basicOpen ((1 : T) ⊗ₜ[R] h) from fun hmem ↦ hhP ?_)
  rw [← hQ]
  exact hmem

end BaseChange

section Fibre

open scoped TensorProduct

/-- If every element of `Â` is congruent modulo `I` to an element of `A`, a prime of `Â ⊗_A S`
containing `I` is determined by its contraction to `S`. -/
theorem eq_of_comap_includeRight_eq {A Â S : Type*} [CommRing A] [CommRing Â] [CommRing S]
    [Algebra A Â] [Algebra A S] (I : Ideal Â)
    (hsurj : ∀ a : Â, ∃ a₀ : A, a - algebraMap A Â a₀ ∈ I) {Q Q' : Ideal (Â ⊗[A] S)}
    [Q.IsPrime] [Q'.IsPrime]
    (hQ : I ≤ Q.comap Algebra.TensorProduct.includeLeftRingHom)
    (hQ' : I ≤ Q'.comap Algebra.TensorProduct.includeLeftRingHom)
    (h : Q.comap Algebra.TensorProduct.includeRight.toRingHom =
      Q'.comap Algebra.TensorProduct.includeRight.toRingHom) : Q = Q' := by
  let J : Ideal (Â ⊗[A] S) := I.map Algebra.TensorProduct.includeLeftRingHom
  have key : ∀ t : Â ⊗[A] S, ∃ s : S, t - (1 : Â) ⊗ₜ s ∈ J := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a s =>
      obtain ⟨a₀, ha⟩ := hsurj a
      refine ⟨a₀ • s, ?_⟩
      have e1 : (1 : Â) ⊗ₜ[A] (a₀ • s) = (algebraMap A Â a₀) ⊗ₜ[A] s := by
        rw [← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      have : a ⊗ₜ[A] s - (1 : Â) ⊗ₜ (a₀ • s) =
          Algebra.TensorProduct.includeLeftRingHom (a - algebraMap A Â a₀) *
            ((1 : Â) ⊗ₜ s) := by
        rw [e1, ← TensorProduct.sub_tmul, Algebra.TensorProduct.includeLeftRingHom_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact J.mul_mem_right _ (Ideal.mem_map_of_mem _ ha)
    | add x y hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨s', hs'⟩ := hy
      refine ⟨s + s', ?_⟩
      rw [TensorProduct.tmul_add]
      convert J.add_mem hs hs' using 1
      ring
  have hJQ : J ≤ Q := Ideal.map_le_iff_le_comap.mpr hQ
  have hJQ' : J ≤ Q' := Ideal.map_le_iff_le_comap.mpr hQ'
  have H : ∀ {P P' : Ideal (Â ⊗[A] S)}, J ≤ P → J ≤ P' →
      P.comap Algebra.TensorProduct.includeRight.toRingHom =
        P'.comap Algebra.TensorProduct.includeRight.toRingHom → P ≤ P' := by
    intro P P' hP hP' hPP' t ht
    obtain ⟨s, hs⟩ := key t
    have h1 : (1 : Â) ⊗ₜ[A] s ∈ P := by
      have := P.sub_mem ht (hP hs)
      rwa [sub_sub_cancel] at this
    have h2 : s ∈ P'.comap Algebra.TensorProduct.includeRight.toRingHom := by
      rw [← hPP']; exact h1
    have := P'.add_mem (hP' hs) (show (1 : Â) ⊗ₜ[A] s ∈ P' from h2)
    rwa [sub_add_cancel] at this
  exact le_antisymm (H hJQ hJQ' h) (H hJQ' hJQ h.symm)

end Fibre

section Height

/-- Zariski's main theorem and going down: let `S` be a finite type algebra over a normal domain
`A`, which is a domain containing `A`, and quasi-finite at a prime `q`. Then the height of `q` is at
least the height of its contraction to `A` (the dimension formula for `S_q`). -/
theorem Ideal.height_comap_le_of_quasiFiniteAt {A S : Type u} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing S] [IsDomain S] [Algebra A S] [FaithfulSMul A S]
    [Algebra.FiniteType A S] (q : Ideal S) [q.IsPrime] [Algebra.QuasiFiniteAt A q] :
    (q.comap (algebraMap A S)).height ≤ q.height := by
  obtain ⟨r, hrq, hr, H⟩ :=
    Algebra.zariskisMainProperty_iff.mp (Algebra.ZariskisMainProperty.of_finiteType (R := A) q)
  let C := integralClosure A S
  let qC : Ideal C := q.comap C.val.toRingHom
  have : qC.IsPrime := Ideal.comap_isPrime _ _
  let Sq := Localization.AtPrime q
  let _ : Algebra C Sq := ((algebraMap S Sq).comp C.val.toRingHom).toAlgebra
  have hinj : Function.Injective (algebraMap S Sq) :=
    IsLocalization.injective Sq (Ideal.primeCompl_le_nonZeroDivisors q)
  have hloc : IsLocalization.AtPrime Sq qC := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · rintro ⟨c, hc⟩
      exact IsLocalization.map_units Sq (⟨c.1, hc⟩ : q.primeCompl)
    · intro z
      obtain ⟨⟨s, u⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
      obtain ⟨m, hm⟩ := H s
      obtain ⟨m', hm'⟩ := H u
      have hs : IsIntegral A (r ^ (m + m') * s) := by
        have : r ^ (m + m') * s = (r ^ m * s) * r ^ m' := by ring
        rw [this]; exact hm.mul (hr.pow m')
      have hu : IsIntegral A (r ^ (m + m') * u) := by
        have : r ^ (m + m') * (u : S) = r ^ m * (r ^ m' * u) := by ring
        rw [this]; exact (hr.pow m).mul hm'
      refine ⟨⟨⟨_, hs⟩, ⟨⟨_, hu⟩, ?_⟩⟩, ?_⟩
      · change r ^ (m + m') * u ∉ q
        exact fun h ↦ (Ideal.IsPrime.mul_mem_iff_mem_or_mem inferInstance).mp h |>.elim
          (fun h' ↦ hrq (Ideal.IsPrime.mem_of_pow_mem inferInstance _ h')) u.2
      · change IsLocalization.mk' Sq s u * algebraMap S Sq (r ^ (m + m') * u) =
          algebraMap S Sq (r ^ (m + m') * s)
        rw [map_mul, mul_left_comm, IsLocalization.mk'_spec, ← map_mul, mul_comm]
    · intro c c' h
      refine ⟨1, ?_⟩
      simp only [OneMemClass.coe_one, one_mul]
      exact Subtype.ext (hinj h)
  have h1 : ringKrullDim Sq = q.height := IsLocalization.AtPrime.ringKrullDim_eq_height q Sq
  have h2 : ringKrullDim Sq = qC.height := IsLocalization.AtPrime.ringKrullDim_eq_height qC Sq
  have hq : qC.height = q.height := WithBot.coe_injective (h2.symm.trans h1)
  -- going down for the integral extension `A ⊆ C`
  have : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr fun a b hab ↦
    (FaithfulSMul.algebraMap_injective A S) (congrArg Subtype.val hab)
  have : Algebra.IsIntegral A C := inferInstanceAs (Algebra.IsIntegral A (integralClosure A S))
  have : IsDomain C := inferInstanceAs (IsDomain (integralClosure A S))
  have : Algebra.HasGoingDown A C := inferInstance
  rw [← hq, Ideal.height_eq_height_under_of_hasGoingDown (R := A) qC]
  apply le_of_eq
  congr 1

end Height

section RegularTransfer

open scoped TensorProduct

/-- Let `Â` be a flat `A`-algebra, `S` an `A`-algebra and `Q` a prime of `Â ⊗_A S` over a prime
`q` of `S`. A regular sequence of elements of `A` on `S_q` stays regular on `(Â ⊗_A S)_Q`: the
latter is a localization of the flat base change `Â ⊗_A S_q`. -/
theorem isWeaklyRegular_localization_tensorProduct {A Â S : Type u} [CommRing A] [CommRing Â]
    [CommRing S] [Algebra A Â] [Module.Flat A Â] [Algebra A S] (q : Ideal S) [q.IsPrime]
    {rs : List A} (hreg : IsWeaklyRegular (Localization.AtPrime q) rs)
    (Q : Ideal (Â ⊗[A] S)) [Q.IsPrime]
    (hQ : Q.comap Algebra.TensorProduct.includeRight.toRingHom = q) :
    IsWeaklyRegular (Localization.AtPrime Q) (rs.map (algebraMap A Â)) := by
  let Sq := Localization.AtPrime q
  let T := Â ⊗[A] S
  let TB := Â ⊗[A] Sq
  let TQ := Localization.AtPrime Q
  -- the base change `Â ⊗_A S_q`
  have hTB : IsWeaklyRegular TB (rs.map (algebraMap A Â)) :=
    hreg.of_flat_of_isBaseChange (TensorProduct.isBaseChange A Sq Â)
  -- `Â ⊗_A S_q` is a localization of `T`
  let _ : Algebra T TB :=
    (Algebra.TensorProduct.map (AlgHom.id A Â) (IsScalarTower.toAlgHom A S Sq)).toAlgebra
  have : IsScalarTower Â T TB :=
    .of_algebraMap_eq fun a ↦ by
      change a ⊗ₜ[A] (1 : Sq) = Algebra.TensorProduct.map (AlgHom.id A Â)
        (IsScalarTower.toAlgHom A S Sq) (a ⊗ₜ[A] (1 : S))
      simp
  let M' : Submonoid T := q.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := Â))
  have : IsLocalization M' TB :=
    IsLocalization.tensorProduct_tensorProduct_right A Â q.primeCompl Sq
      (by ext; simp [RingHom.algebraMap_toAlgebra])
  have hle : M' ≤ Q.primeCompl := by
    rintro _ ⟨s, hs, rfl⟩ hsQ
    apply hs
    rw [← hQ]
    exact hsQ
  let _ : Algebra TB TQ := IsLocalization.localizationAlgebraOfSubmonoidLe TB TQ M' Q.primeCompl hle
  have : IsScalarTower T TB TQ :=
    IsLocalization.localization_isScalarTower_of_submonoid_le TB TQ M' Q.primeCompl hle
  have hL : IsLocalization (Q.primeCompl.map (algebraMap T TB)) TQ :=
    IsLocalization.isLocalization_of_submonoid_le TB TQ M' Q.primeCompl hle
  have : IsScalarTower Â TB TQ := IsScalarTower.of_algebraMap_eq (R := Â) (S := TB) (A := TQ)
      fun a ↦ by
    have e1 : algebraMap Â TQ a = algebraMap T TQ (algebraMap Â T a) :=
      IsScalarTower.algebraMap_apply Â T TQ a
    have e2 : algebraMap Â TB a = algebraMap T TB (algebraMap Â T a) :=
      IsScalarTower.algebraMap_apply Â T TB a
    rw [e1, e2, ← IsScalarTower.algebraMap_apply T TB TQ]
  have h1 : IsWeaklyRegular TB ((rs.map (algebraMap A Â)).map (algebraMap Â TB)) :=
    (isWeaklyRegular_map_algebraMap_iff (R := Â) (S := TB) (M := TB) _).mpr hTB
  have h2 := h1.of_isLocalization TQ (Q.primeCompl.map (algebraMap T TB))
  rw [List.map_map] at h2
  have h3 : IsWeaklyRegular TQ ((rs.map (algebraMap A Â)).map (algebraMap Â TQ)) := by
    have hl : (rs.map (algebraMap A Â)).map (algebraMap Â TQ) =
        (rs.map (algebraMap A Â)).map (⇑(algebraMap TB TQ) ∘ ⇑(algebraMap Â TB)) := by
      congr 1
      exact funext fun a ↦ IsScalarTower.algebraMap_apply Â TB TQ a
    rw [hl]
    exact h2
  exact (isWeaklyRegular_map_algebraMap_iff (R := Â) (S := TQ) (M := TQ) _).mp h3

end RegularTransfer



section Neighbourhood

/-- Let `S` be of finite type over a noetherian local ring `A`, quasi-finite at a prime `q` over
`𝔪_A` and étale over `A` at the primes strictly contained in `q`. Then there is `f ∉ q` such that
`S` is étale over `A` at every prime `P ≠ q` of `D(f)`, and `q` is the only point of `D(f)` over
`𝔪_A`. -/
theorem exists_notMem_forall_isEtaleAt {A S : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing S] [Algebra A S] [Algebra.FiniteType A S] (q : Ideal S)
    [hqp : q.IsPrime] [q.LiesOver (maximalIdeal A)] [Algebra.QuasiFiniteAt A q]
    (hbelow : ∀ (P : Ideal S) [P.IsPrime], P ≤ q → P ≠ q → Algebra.IsEtaleAt A P) :
    ∃ f ∉ q, (∀ (P : Ideal S) [P.IsPrime], f ∉ P → P ≠ q → Algebra.IsEtaleAt A P) ∧
      ∀ (P : Ideal S) [P.IsPrime], f ∉ P → P.comap (algebraMap A S) = maximalIdeal A → P = q := by
  classical
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing A S
  have : Algebra.FinitePresentation A S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hqA : q.comap (algebraMap A S) = maximalIdeal A := (Ideal.over_def q (maximalIdeal A)).symm
  obtain ⟨f₁, hf₁q, hf₁⟩ := Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver (maximalIdeal A) q
  -- the non-étale locus is closed; its components through `q` are `{q}`
  let Z : Set (PrimeSpectrum S) := (Algebra.etaleLocus A S)ᶜ
  have hZ : IsClosed Z := Algebra.isOpen_etaleLocus.isClosed_compl
  let J := PrimeSpectrum.vanishingIdeal Z
  have hJfin := Ideal.finite_minimalPrimes_of_isNoetherianRing S J
  let T₂ := {Q ∈ J.minimalPrimes | Q ≠ q}
  have hT₂ : T₂.Finite := hJfin.subset fun Q hQ ↦ hQ.1
  have hc : ∀ Q ∈ T₂, ∃ c ∈ Q, c ∉ q := by
    rintro Q ⟨hQ, hne⟩
    by_contra! hle
    have : Q.IsPrime := hQ.1.1
    have hQZ : (⟨Q, this⟩ : PrimeSpectrum S) ∈ Z := by
      rw [← hZ.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
        PrimeSpectrum.mem_zeroLocus]
      exact hQ.1.2
    exact hQZ (hbelow Q hle hne)
  choose! c hcQ hcq using hc
  let f₂ := ∏ Q ∈ hT₂.toFinset, c Q
  have hf₂q : f₂ ∉ q := by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨Q, hQ, hcQ'⟩
    exact hcq Q (hT₂.mem_toFinset.mp hQ) hcQ'
  have hfuniq : ∀ (P : Ideal S) [P.IsPrime], f₁ * f₂ ∉ P →
      P.comap (algebraMap A S) = maximalIdeal A → P = q := by
    intro P _ hfP hPA
    by_contra hne
    have : P.LiesOver (maximalIdeal A) := ⟨hPA.symm⟩
    exact hfP (P.mul_mem_right _ (hf₁ P ‹_› hne this))
  refine ⟨f₁ * f₂, fun h' ↦ (hqp.mul_mem_iff_mem_or_mem.mp h').elim hf₁q hf₂q, ?_, hfuniq⟩
  intro P _ hfP hPq
  by_contra hnet
  have hPZ : (⟨P, ‹_›⟩ : PrimeSpectrum S) ∈ Z := hnet
  have hJP : J ≤ P := fun s hs ↦ (PrimeSpectrum.mem_vanishingIdeal Z s).mp hs _ hPZ
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hJP
  by_cases hQq : Q = q
  · rw [hQq] at hQP
    have hPA : P.comap (algebraMap A S) = maximalIdeal A := by
      refine ((maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.comap _).ne_top ?_).symm
      rw [← hqA]
      exact Ideal.comap_mono hQP
    exact hPq (hfuniq P hfP hPA)
  · exact hfP (P.mul_mem_left _ (hQP (Ideal.mem_of_dvd _
      (Finset.dvd_prod_of_mem c (hT₂.mem_toFinset.mpr ⟨hQ, hQq⟩)) (hcQ Q ⟨hQ, hQq⟩))))

end Neighbourhood

section CompletionBaseChange

open scoped TensorProduct

variable {A S : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing S]
  [Algebra A S]

local notation "Â" => AdicCompletion (maximalIdeal A) A

omit [Algebra A S] in
/-- Every element of the completion `Â` is congruent to an element of `A` modulo `𝔪_Â`. -/
theorem AdicCompletion.exists_sub_mem_maximalIdeal (a : Â) :
    ∃ a₀ : A, a - algebraMap A Â a₀ ∈ maximalIdeal Â := by
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ (maximalIdeal A) a)
  refine ⟨a₀, ?_⟩
  rw [AdicCompletion.maximalIdeal_eq_map,
    ← AdicCompletion.ker_evalOneₐ_eq_map _ (maximalIdeal A).fg_of_isNoetherianRing,
    RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, AlgHom.commutes, ← ha₀]
  exact sub_self _

/-- A prime of `Â ⊗_A S` whose contraction to `S` lies over `𝔪_A` lies over `𝔪_Â`. -/
theorem comap_algebraMap_eq_maximalIdeal_of_comap_includeRight (P : Ideal (Â ⊗[A] S))
    [P.IsPrime]
    (hP : (P.comap Algebra.TensorProduct.includeRight.toRingHom).comap (algebraMap A S) =
      maximalIdeal A) :
    P.comap (algebraMap Â (Â ⊗[A] S)) = maximalIdeal Â := by
  refine ((maximalIdeal.isMaximal Â).eq_of_le (Ideal.IsPrime.comap _).ne_top ?_).symm
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro a ha
  rw [← hP] at ha
  change algebraMap Â (Â ⊗[A] S) (algebraMap A Â a) ∈ P
  rw [← IsScalarTower.algebraMap_apply, ← Algebra.TensorProduct.includeRight.commutes a]
  exact ha

/-- Conversely, a prime of `Â ⊗_A S` over `𝔪_Â` has contraction to `S` over `𝔪_A`. -/
theorem comap_includeRight_eq_maximalIdeal_of_comap_algebraMap (P : Ideal (Â ⊗[A] S))
    [P.IsPrime] (hP : P.comap (algebraMap Â (Â ⊗[A] S)) = maximalIdeal Â) :
    (P.comap Algebra.TensorProduct.includeRight.toRingHom).comap (algebraMap A S) =
      maximalIdeal A := by
  rw [Ideal.comap_comap]
  refine ((maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.comap _).ne_top ?_).symm
  intro a ha
  change Algebra.TensorProduct.includeRight (algebraMap A S a) ∈ P
  rw [Algebra.TensorProduct.includeRight.commutes, IsScalarTower.algebraMap_apply A Â]
  change algebraMap A Â a ∈ P.comap (algebraMap Â (Â ⊗[A] S))
  rw [hP, AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ ha

end CompletionBaseChange
