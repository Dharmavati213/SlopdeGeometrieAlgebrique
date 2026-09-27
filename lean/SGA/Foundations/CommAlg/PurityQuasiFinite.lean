/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.ZariskisMainTheorem
import SGA.Foundations.CommAlg.PurityCompletion
import SGA.Foundations.CommAlg.PurityInduction
import SGA.Foundations.CompleteLocalQuasiFinite
import SGA.Foundations.CompletionDimension
import SGA.Foundations.Dimension.Integral

/-!
# Purity for quasi-finite algebras over a regular local ring

Let `A` be a regular local ring of dimension `≥ 2` and `B` a normal local domain, essentially of
finite type and quasi-finite over `A` (with `A ⊆ B` local). If `B` is étale over `A` at every
non-maximal prime, then `B` is étale over `A`
(`IsRegularLocalRing.formallyEtale_of_quasiFinite`; Stacks 0BMB, SGA 1 X.3.2, SGA 2 X.3.4). This
removes the finiteness hypothesis of
`IsRegularLocalRing.etale_of_isIntegrallyClosed_of_two_le_ringKrullDim`.

## Proof

* `B` has dimension `≥ 2` (Zariski's main theorem and going down,
  `Ideal.height_comap_le_of_quasiFiniteAt`), so it has depth `≥ 2` over `A`
  (`exists_finset_isWeaklyRegular_pair_of_isIntegrallyClosed`).
* The completion `Â` is regular of the same dimension (`IsRegularLocalRing.adicCompletion`) and
  faithfully flat over `A`. Write `B = S_q` with `S` of finite type. Over the complete ring `Â`,
  the local ring of `Â ⊗_A S` at the point `q'` over `q` and `𝔪_Â` is a localization of a finite
  `Â`-algebra (`IsLocalRing.exists_notMem_forall_le_and_finite`), so the finite case
  (`IsRegularLocalRing.etale_of_isWeaklyRegular_of_two_le_ringKrullDim`) applies
  (`IsRegularLocalRing.isEtaleAt_of_quasiFiniteAt`,
  `IsRegularLocalRing.isEtaleAt_adicCompletion_tensorProduct`).
* On a neighbourhood `D(f)` of `q` containing no other point over `𝔪_A` and on which `S` is étale
  away from `q` (`exists_notMem_forall_isEtaleAt`), `Â ⊗_A S_f` is étale over `Â`: at the points
  over `𝔪_Â` (only `q'`, `eq_of_comap_includeRight_eq`) by the above, elsewhere by base change
  (`Algebra.IsEtaleAt.baseChange`). Étaleness descends along the faithfully flat `A → Â`
  (`Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat`).
-/

universe u

open IsLocalRing RingTheory.Sequence

section Complete

variable {R T : Type u} [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  [CommRing T] [Algebra R T] [Algebra.FiniteType R T]

/-- Purity at a quasi-finite point over a complete regular local ring of dimension `≥ 2`. Let `T`
be of finite type over `R`, quasi-finite at a prime `Q` over `𝔪_R`, and `x, y ∈ 𝔪_R` a regular
sequence on `R` and on `T_Q`. If `T` is étale over `R` at the primes contained in `Q` which do not
lie over `𝔪_R`, then `T` is étale over `R` at `Q`: over the complete ring `R` the local ring
`T_Q` is a direct factor of a localization of `T` which is finite over `R`
(`IsLocalRing.exists_notMem_forall_le_and_finite`), and the finite case applies. -/
theorem IsRegularLocalRing.isEtaleAt_of_quasiFiniteAt (hdim : 2 ≤ ringKrullDim R) (Q : Ideal T)
    [Q.IsPrime] [Q.LiesOver (maximalIdeal R)] [Algebra.QuasiFiniteAt R Q] {x y : R}
    (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R) (hA : IsWeaklyRegular R [x, y])
    (hreg : IsWeaklyRegular (Localization.AtPrime Q) [x, y])
    (hU : ∀ (P : Ideal T) [P.IsPrime], P ≤ Q → P.comap (algebraMap R T) ≠ maximalIdeal R →
      Algebra.IsEtaleAt R P) :
    Algebra.IsEtaleAt R Q := by
  classical
  obtain ⟨e, he, hle, hfin⟩ := IsLocalRing.exists_notMem_forall_le_and_finite (A := R) Q
  let D := Localization.Away e
  have : Module.Finite R D := hfin D
  -- `D` is the localization of `T` at `Q`
  have hunit : ∀ s ∉ Q, IsUnit (algebraMap T D s) := by
    intro s hs
    by_contra hns
    obtain ⟨M, hM, hsM⟩ := exists_max_ideal_of_mem_nonunits hns
    have hP : (M.comap (algebraMap T D)).IsPrime := Ideal.comap_isPrime _ _
    have heP : e ∉ M.comap (algebraMap T D) := fun h ↦
      hM.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit e))
    exact hs (hle _ hP heP hsM)
  have hDQ : IsLocalization.AtPrime D Q :=
    IsLocalization.of_le (Submonoid.powers e) Q.primeCompl
      (Submonoid.powers_le.mpr he) fun s hs ↦ hunit s hs
  let eD : D ≃ₐ[T] Localization.AtPrime Q := IsLocalization.algEquiv Q.primeCompl _ _
  -- the regular sequence on `D`
  have hregD : IsWeaklyRegular D [x, y] :=
    ((eD.restrictScalars R).toLinearEquiv.isWeaklyRegular_congr [x, y]).mpr hreg
  -- `D` is étale over `R` away from `𝔪_R`
  have hUD : ∀ (P : Ideal D) [P.IsPrime], P.comap (algebraMap R D) ≠ maximalIdeal R →
      Algebra.IsEtaleAt R P := by
    intro P _ hPm
    let P' := P.comap (algebraMap T D)
    have hP'Q : P' ≤ Q := by
      intro s hs
      by_contra hsQ
      exact (Ideal.IsPrime.ne_top ‹_›) (P.eq_top_of_isUnit_mem hs (hunit s hsQ))
    have hP'm : P'.comap (algebraMap R T) ≠ maximalIdeal R := by
      rwa [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    have := hU P' hP'Q hP'm
    have hL : IsLocalization.AtPrime (Localization.AtPrime P) P' :=
      IsLocalization.isLocalization_atPrime_localization_atPrime (Submonoid.powers e) P
    let e' : Localization.AtPrime P' ≃ₐ[T] Localization.AtPrime P :=
      IsLocalization.algEquiv P'.primeCompl _ _
    exact Algebra.FormallyEtale.of_equiv (e'.restrictScalars R)
  have hEt : Algebra.Etale R D :=
    IsRegularLocalRing.etale_of_isWeaklyRegular_of_two_le_ringKrullDim hdim hx hy hA hregD hUD
  exact Algebra.FormallyEtale.of_equiv (eD.restrictScalars R)

end Complete

section Main

open scoped TensorProduct

variable {A S : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing S] [Algebra A S]
  [Algebra.FiniteType A S]

local notation "Â" => AdicCompletion (maximalIdeal A) A

/-- The completed case. Let `S` be of finite type over a regular local ring `A` of dimension
`≥ 2`, quasi-finite at a prime `q` over `𝔪_A`, étale over `A` at the primes strictly contained in
`q`, and `x, y ∈ 𝔪_A` a regular sequence on `A` and on `S_q`. Then `Â ⊗_A S` is étale over `Â`
at every prime `q'` over `q` and `𝔪_Â`. -/
theorem IsRegularLocalRing.isEtaleAt_adicCompletion_tensorProduct (hdim : 2 ≤ ringKrullDim A)
    (q : Ideal S) [q.IsPrime] [q.LiesOver (maximalIdeal A)] [Algebra.QuasiFiniteAt A q] {x y : A}
    (hxm : x ∈ maximalIdeal A) (hym : y ∈ maximalIdeal A) (hA : IsWeaklyRegular A [x, y])
    (hreg : IsWeaklyRegular (Localization.AtPrime q) [x, y])
    (hbelow : ∀ (P : Ideal S) [P.IsPrime], P ≤ q → P ≠ q → Algebra.IsEtaleAt A P)
    (q' : Ideal (Â ⊗[A] S)) [q'.IsPrime]
    (hq'S : q'.comap Algebra.TensorProduct.includeRight.toRingHom = q)
    (hq'Â : q'.comap (algebraMap Â (Â ⊗[A] S)) = maximalIdeal Â) :
    Algebra.IsEtaleAt Â q' := by
  have : Algebra.FinitePresentation A S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hqA : q.comap (algebraMap A S) = maximalIdeal A := (Ideal.over_def q (maximalIdeal A)).symm
  obtain ⟨hÂreg, hÂdim⟩ := IsRegularLocalRing.adicCompletion A
  have : IsRegularLocalRing Â := hÂreg
  rw [← hÂdim] at hdim
  have : q'.LiesOver (maximalIdeal Â) := ⟨hq'Â.symm⟩
  have : Algebra.QuasiFiniteAt Â q' := Algebra.QuasiFiniteAt.baseChange q q' hq'S.symm
  refine IsRegularLocalRing.isEtaleAt_of_quasiFiniteAt (R := Â) (T := Â ⊗[A] S) hdim q'
    (x := algebraMap A Â x) (y := algebraMap A Â y)
    (by rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.mem_map_of_mem _ hxm)
    (by rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.mem_map_of_mem _ hym)
    (hA.of_flat (S := Â)) (isWeaklyRegular_localization_tensorProduct q hreg q' hq'S) ?_
  intro P _ hPq hPm
  have hPSq : P.comap Algebra.TensorProduct.includeRight.toRingHom ≤ q :=
    hq'S ▸ Ideal.comap_mono hPq
  have hPSne : P.comap Algebra.TensorProduct.includeRight.toRingHom ≠ q := by
    intro heq
    apply hPm
    apply comap_algebraMap_eq_maximalIdeal_of_comap_includeRight
    rw [heq, hqA]
  have := hbelow _ hPSq hPSne
  exact Algebra.IsEtaleAt.baseChange Â _ P rfl

/-- Descent from the completion: in the situation of
`IsRegularLocalRing.isEtaleAt_adicCompletion_tensorProduct`, `S` is étale over `A` at `q`. -/
theorem IsRegularLocalRing.isEtaleAt_of_quasiFiniteAt_of_isWeaklyRegular
    (hdim : 2 ≤ ringKrullDim A) (q : Ideal S) [hqp : q.IsPrime] [q.LiesOver (maximalIdeal A)]
    [Algebra.QuasiFiniteAt A q] {x y : A} (hxm : x ∈ maximalIdeal A) (hym : y ∈ maximalIdeal A)
    (hA : IsWeaklyRegular A [x, y])
    (hreg : IsWeaklyRegular (Localization.AtPrime q) [x, y])
    (hbelow : ∀ (P : Ideal S) [P.IsPrime], P ≤ q → P ≠ q → Algebra.IsEtaleAt A P) :
    Algebra.IsEtaleAt A q := by
  classical
  have : Algebra.FinitePresentation A S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hqA : q.comap (algebraMap A S) = maximalIdeal A := (Ideal.over_def q (maximalIdeal A)).symm
  have : Module.FaithfullyFlat A Â := Module.FaithfullyFlat.of_flat_of_isLocalHom
  -- the point `q'` of `Â ⊗_A S` over `q` and the closed point of `Â`
  let κ := q.ResidueField
  have hmκ : ∀ a ∈ maximalIdeal A, algebraMap A κ a = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply A S κ, Ideal.algebraMap_residueField_eq_zero,
      ← Ideal.mem_comap, hqA]
    exact ha
  let fκ : Â →ₐ[A] κ := (Ideal.Quotient.liftₐ (maximalIdeal A) (Algebra.ofId A κ) hmκ).comp
    (AdicCompletion.evalOneₐ (maximalIdeal A))
  let φ : Â ⊗[A] S →ₐ[A] κ :=
    Algebra.TensorProduct.lift fκ (IsScalarTower.toAlgHom A S κ) fun _ _ ↦ Commute.all _ _
  let q' : Ideal (Â ⊗[A] S) := RingHom.ker φ.toRingHom
  have : q'.IsPrime := RingHom.ker_isPrime _
  have hq'S : q'.comap Algebra.TensorProduct.includeRight.toRingHom = q := by
    ext s
    change φ ((1 : Â) ⊗ₜ[A] s) = 0 ↔ s ∈ q
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact Ideal.algebraMap_residueField_eq_zero
  have hq'Â : q'.comap (algebraMap Â (Â ⊗[A] S)) = maximalIdeal Â := by
    apply comap_algebraMap_eq_maximalIdeal_of_comap_includeRight
    rw [hq'S, hqA]
  have hq'et := IsRegularLocalRing.isEtaleAt_adicCompletion_tensorProduct hdim q hxm hym hA hreg
    hbelow q' hq'S hq'Â
  -- a neighbourhood `D(f)` of `q` where `S` is étale away from `q`, with `q` alone over `𝔪_A`
  obtain ⟨f, hfq, hfet, hfuniq⟩ := exists_notMem_forall_isEtaleAt q hbelow
  -- `Â ⊗_A S_f` is étale over `Â`
  have hEtT : Algebra.Etale Â (Localization.Away ((1 : Â) ⊗ₜ[A] f)) := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale (R := Â)]
    intro Q hQ
    have hfQ : f ∉ Q.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom := hQ
    by_cases hQm : Q.asIdeal.comap (algebraMap Â (Â ⊗[A] S)) = maximalIdeal Â
    · have hPq := hfuniq _ hfQ (comap_includeRight_eq_maximalIdeal_of_comap_algebraMap _ hQm)
      have hQq' : Q.asIdeal = q' :=
        eq_of_comap_includeRight_eq (maximalIdeal Â) AdicCompletion.exists_sub_mem_maximalIdeal
          (hQm ▸ le_rfl) (hq'Â ▸ le_rfl) (hPq.trans hq'S.symm)
      have hQeq : Q = ⟨q', ‹_›⟩ := PrimeSpectrum.ext hQq'
      subst hQeq
      exact hq'et
    · have hPne : Q.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom ≠ q := by
        intro heq
        apply hQm
        apply comap_algebraMap_eq_maximalIdeal_of_comap_includeRight
        rw [heq, hqA]
      have := hfet _ hfQ hPne
      exact Algebra.IsEtaleAt.baseChange Â _ Q.asIdeal rfl
  have : Algebra.Etale Â (Â ⊗[A] Localization.Away f) :=
    Algebra.Etale.of_equiv
      (IsLocalization.Away.tensorProductEquivTMulRight A Â f (Localization.Away f)).symm
  have : Algebra.Etale A (Localization.Away f) :=
    Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat Â
  exact (Algebra.basicOpen_subset_etaleLocus_iff (R := A)).mpr inferInstance
    (show (⟨q, hqp⟩ : PrimeSpectrum S) ∈ PrimeSpectrum.basicOpen f from hfq)

end Main

section Purity

/-- **Zariski–Nagata purity for quasi-finite algebras** (Stacks 0BMB; SGA 1 X.3.2; SGA 2 X.3.4).
Let `A` be a regular local ring of dimension `≥ 2` and `A → B` an injective local homomorphism,
with `B` a normal local domain which is essentially of finite type and quasi-finite over `A`. If
`B` is étale over `A` at every non-maximal prime, then `B` is formally étale over `A`.

`B` has dimension `≥ 2` (Zariski's main theorem and going down), hence depth `≥ 2`, and a nonzero
`x ∈ 𝔪_A` extends to a sequence `x, y` regular on `A` and on `B`. After completing `A`, the local
ring of `Â ⊗_A B` at the point over the closed points is a factor of a finite `Â`-algebra, to which
the finite case applies; étaleness then descends along `A → Â` (faithfully flat) on a
neighbourhood of the closed point of a model of finite type of `B`. -/
theorem IsRegularLocalRing.formallyEtale_of_quasiFinite {A B : Type u} [CommRing A]
    [IsRegularLocalRing A] [CommRing B] [IsLocalRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [Algebra.QuasiFinite A B] (hinj : Function.Injective (algebraMap A B))
    (hdim : 2 ≤ ringKrullDim A)
    (h : ∀ (p : Ideal B) [p.IsPrime], p ≠ maximalIdeal B → Algebra.IsEtaleAt A p) :
    Algebra.FormallyEtale A B := by
  classical
  -- `B = S_q` with `S` of finite type over `A`
  let S := Algebra.EssFiniteType.subalgebra A B
  let q : Ideal S := (maximalIdeal B).comap (algebraMap S B)
  have hqp : q.IsPrime := Ideal.comap_isPrime _ _
  have hMq : Algebra.EssFiniteType.submonoid A B = q.primeCompl := by
    ext s
    change IsUnit (algebraMap S B s) ↔ algebraMap S B s ∉ maximalIdeal B
    exact IsLocalRing.notMem_maximalIdeal.symm
  have hBq : IsLocalization.AtPrime B q := by
    have := Algebra.EssFiniteType.isLocalization A B
    rwa [hMq] at this
  let eB : Localization.AtPrime q ≃ₐ[S] B := IsLocalization.algEquiv q.primeCompl _ _
  have : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  have hcomapB : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A := by
    refine ((maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.comap (algebraMap A B)).ne_top
      fun a ha ↦ ?_).symm
    rw [Ideal.mem_comap]
    exact (IsLocalRing.mem_maximalIdeal _).mpr
      (map_nonunit (algebraMap A B) a ((IsLocalRing.mem_maximalIdeal _).mp ha))
  have hqA : q.comap (algebraMap A S) = maximalIdeal A := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact hcomapB
  have : q.LiesOver (maximalIdeal A) := ⟨hqA.symm⟩
  have : Algebra.QuasiFiniteAt A q :=
    (Algebra.QuasiFinite.iff_of_algEquiv (eB.restrictScalars A)).mpr inferInstance
  -- `S` is étale over `A` at the primes strictly contained in `q`
  have hbelow : ∀ (P : Ideal S) [P.IsPrime], P ≤ q → P ≠ q → Algebra.IsEtaleAt A P := by
    intro P _ hPq hne
    have hdisj : Disjoint (q.primeCompl : Set S) P :=
      Set.disjoint_left.mpr fun s hs hsP ↦ hs (hPq hsP)
    let P' := P.map (algebraMap S B)
    have : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl B P ‹_› hdisj
    have hP' : P'.comap (algebraMap S B) = P :=
      IsLocalization.under_map_of_isPrime_disjoint q.primeCompl B ‹_› hdisj
    have hne' : P' ≠ maximalIdeal B := fun h' ↦ hne (by rw [← hP', h'])
    have := h P' hne'
    have hL0 := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization q.primeCompl
      (Localization.AtPrime P') P'
    have hL : IsLocalization.AtPrime (Localization.AtPrime P') P := by
      convert hL0 using 2; exact hP'.symm
    let e' : Localization.AtPrime P ≃ₐ[S] Localization.AtPrime P' :=
      IsLocalization.algEquiv P.primeCompl _ _
    exact Algebra.FormallyEtale.of_equiv (e'.restrictScalars A).symm
  -- `B` has dimension `≥ 2`, hence a regular sequence `x, y ∈ 𝔪_A`
  have : IsDomain S := inferInstanceAs (IsDomain (Algebra.EssFiniteType.subalgebra A B))
  have : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr fun a b hab ↦
    hinj (by rw [IsScalarTower.algebraMap_apply A S B, hab, ← IsScalarTower.algebraMap_apply])
  have hm2 : (2 : ℕ∞) ≤ (maximalIdeal A).height := by
    have := maximalIdeal_height_eq_ringKrullDim (R := A)
    rw [← this] at hdim
    exact WithBot.coe_le_coe.mp hdim
  have hheight : 2 ≤ q.height := by
    have h1 := Ideal.height_comap_le_of_quasiFiniteAt (A := A) q
    rw [hqA] at h1
    exact hm2.trans h1
  have hmB : (maximalIdeal B).height = q.height := by
    have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height q B
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at h1
    exact WithBot.coe_injective h1
  obtain ⟨x, hxm, hx0⟩ : ∃ x ∈ maximalIdeal A, x ≠ 0 := by
    by_contra! hc
    have : maximalIdeal A = ⊥ := eq_bot_iff.mpr fun x hx ↦ hc x hx
    rw [this, Ideal.height_bot] at hm2
    exact absurd hm2 (by decide)
  have h1A : ∀ P : Ideal A, P.IsPrime → P.height = 1 →
      P.comap (algebraMap A A) ≠ maximalIdeal A := by
    intro P _ hP hPm
    rw [Algebra.algebraMap_self, Ideal.comap_id] at hPm
    rw [hPm] at hP
    rw [hP] at hm2
    exact absurd hm2 (by decide)
  have h1 : ∀ P : Ideal B, P.IsPrime → P.height = 1 →
      P.comap (algebraMap A B) ≠ maximalIdeal A := by
    intro P hP hP1 hPm
    have hPB : P = maximalIdeal B :=
      Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) P (maximalIdeal B)
        (le_maximalIdeal hP.ne_top) (by
          change P.comap (algebraMap A B) = (maximalIdeal B).comap (algebraMap A B)
          rw [hPm, hcomapB])
    rw [hPB, hmB] at hP1
    rw [hP1] at hheight
    exact absurd hheight (by decide)
  obtain ⟨SA, hSA, hregA⟩ := exists_finset_isWeaklyRegular_pair_of_isIntegrallyClosed (B := A)
    (x := x) (by simpa using hx0) h1A
  obtain ⟨SB, hSB, hregB⟩ := exists_finset_isWeaklyRegular_pair_of_isIntegrallyClosed (B := B)
    ((map_ne_zero_iff _ hinj).mpr hx0) h1
  obtain ⟨y, hym, hyS⟩ := IsLocalRing.exists_mem_maximalIdeal_forall_notMem (SA ∪ SB)
    fun P hP ↦ (Finset.mem_union.mp hP).elim (hSA P) (hSB P)
  have hregSq : IsWeaklyRegular (Localization.AtPrime q) [x, y] :=
    ((eB.restrictScalars A).toLinearEquiv.isWeaklyRegular_congr [x, y]).mpr
      (hregB y fun P hP ↦ hyS P (Finset.mem_union_right _ hP))
  have hq : Algebra.IsEtaleAt A q :=
    IsRegularLocalRing.isEtaleAt_of_quasiFiniteAt_of_isWeaklyRegular hdim q hxm hym
      (hregA y fun P hP ↦ hyS P (Finset.mem_union_left _ hP)) hregSq hbelow
  exact Algebra.FormallyEtale.of_equiv (eB.restrictScalars A)

end Purity
