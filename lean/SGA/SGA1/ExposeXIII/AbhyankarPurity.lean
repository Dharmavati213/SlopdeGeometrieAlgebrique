/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.AbhyankarBasic

/-!
# SGA 1, Exposé XIII, 5.2–5.3: purity and the codimension-one input

The purity step of XIII.5.2 (SGA 2 X.3.4, XIV 1.11; `etale_integralClosure_of_forall_isEtaleAt`,
from Zariski–Nagata purity), the input in codimension one (X.3.6 over the discrete valuation rings
`A_(f_j)`, `isEtaleAt_integralClosure_of_isTamelyRamifiedAlong`), the extension part of 5.2 when
the `nᵢ` are nonzero in the residue fields `κ((f_j))`
(`exists_etale_kummerAlgebra_of_isTamelyRamifiedAlong`), and 5.2 and 5.3 in equal characteristic
(`absoluteAbhyankarAt_of_ringChar_eq`, `tameCoveringsOfStrictlyLocalAt_of_ringChar_eq`).
-/

universe u

open IsLocalRing
open scoped TensorProduct

namespace SGA.SGA1.ExposeXIII

variable {A : Type u} [CommRing A] {ι : Type*}

section HigherDimension

/-! ### XIII.5.2: the purity step

By purity of the branch locus (Zariski–Nagata, SGA 2 X.3.4 / XIV 1.11;
`IsRegularLocalRing.etale_of_isIntegrallyClosed_of_two_le_ringKrullDim`), an étale covering of
`U' = X' - V(t)` extends to `X'` as soon as its normalization is étale above the maximal points of
`V(t)`. -/

/-- Zariski–Nagata purity for a finite normal domain at a prime `p` of the base (Stacks 0BMB):
let `B` be a finite `A`-algebra which is a normal domain containing `A`, and `p` a prime of `A`
with `A_p` regular of dimension `≥ 2`. If `B` is étale over `A` above the primes strictly
contained in `p`, it is étale above `p`: `B_p` is a finite normal domain over `A_p`, étale over
the punctured spectrum (`IsRegularLocalRing.etale_of_isIntegrallyClosed_of_two_le_ringKrullDim`). -/
theorem isEtaleAt_of_isIntegrallyClosed {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [IsDomain B] [IsIntegrallyClosed B]
    (hinj : Function.Injective (algebraMap A B)) (p : Ideal A) [p.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime p)]
    (hdim : 2 ≤ ringKrullDim (Localization.AtPrime p))
    (hU : ∀ (q : Ideal B) [q.IsPrime], q.comap (algebraMap A B) ≤ p →
      q.comap (algebraMap A B) ≠ p → Algebra.IsEtaleAt A q)
    (q : Ideal B) [q.IsPrime] (hq : q.comap (algebraMap A B) = p) : Algebra.IsEtaleAt A q := by
  let M := p.primeCompl
  let Ap := Localization.AtPrime p
  let Bp := Localization (Algebra.algebraMapSubmonoid B M)
  have hM : Algebra.algebraMapSubmonoid B M ≤ nonZeroDivisors B := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ha ?_
    rw [(map_eq_zero_iff _ hinj).mp h0]
    exact zero_mem _
  have : IsDomain Bp := IsLocalization.isDomain_localization hM
  have : IsIntegrallyClosed Bp := isIntegrallyClosed_of_isLocalization (S := Bp) _ hM
  have hinjp : Function.Injective (algebraMap Ap Bp) :=
    localizationAlgebra_injective (M := M) (Rₘ := Ap) (Sₘ := Bp) hinj
  have hEt : Algebra.Etale Ap Bp := by
    refine IsRegularLocalRing.etale_of_isIntegrallyClosed_of_two_le_ringKrullDim hinjp hdim
      fun Q _ hQ ↦ ?_
    let q' := Q.comap (algebraMap B Bp)
    let P := Q.comap (algebraMap Ap Bp)
    have hq' : q'.comap (algebraMap A B) = P.comap (algebraMap A Ap) := by
      simp only [q', P, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    have hPle : P.comap (algebraMap A Ap) ≤ p := by
      exact (Ideal.comap_mono (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))).trans
        (IsLocalization.AtPrime.under_maximalIdeal Ap p).le
    have hPne : P.comap (algebraMap A Ap) ≠ p := by
      intro h
      apply hQ
      change P = _
      have h' : Ideal.map (algebraMap A Ap) (Ideal.comap (algebraMap A Ap) P) = P :=
        IsLocalization.map_under M Ap P
      rw [h] at h'
      rw [← h']
      exact IsLocalization.AtPrime.map_eq_maximalIdeal p Ap
    have := hU q' (hq' ▸ hPle) (hq' ▸ hPne)
    have e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Algebra.algebraMapSubmonoid B M) Q
    have : Algebra.FormallyEtale A (Localization.AtPrime Q) :=
      Algebra.FormallyEtale.of_equiv (e.restrictScalars A)
    have : Algebra.FormallyUnramified A Ap :=
      Algebra.FormallyUnramified.of_isLocalization M
    exact Algebra.FormallyEtale.of_restrictScalars (R := A)
  -- conclusion at `q`
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid B M : Set B) q := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsq
    apply hs
    rw [← hq]
    exact hsq
  let Q := q.map (algebraMap B Bp)
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Bp q ‹_› hdisj
  have hQq : Q.comap (algebraMap B Bp) = q :=
    IsLocalization.under_map_of_isPrime_disjoint _ Bp ‹_› hdisj
  have : Algebra.FormallyEtale A Ap := Algebra.FormallyEtale.of_isLocalization M
  have : Algebra.FormallyEtale A (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.comp A Ap _
  have hL : IsLocalization.AtPrime (Localization.AtPrime Q) (Q.comap (algebraMap B Bp)) :=
    inferInstance
  have : IsLocalization.AtPrime (Localization.AtPrime Q) q := by
    convert hL using 2; exact hQq.symm
  let e' : Localization.AtPrime q ≃ₐ[B] Localization.AtPrime Q :=
    IsLocalization.algEquiv q.primeCompl _ _
  exact Algebra.FormallyEtale.of_equiv (e'.restrictScalars A).symm

/-- Purity of the branch locus for a finite normal domain over a regular ring (Zariski–Nagata;
SGA 1 X.3.1, Stacks 0BMB): if `B` is a finite `A`-algebra which is a normal domain containing
the regular ring `A`, étale over `A` at the primes lying over primes of height `≤ 1`, then `B` is
étale over `A`. By induction on the height, using `isEtaleAt_of_isIntegrallyClosed`. -/
theorem etale_of_isIntegrallyClosed_of_forall_height_le_one {A B : Type u} [CommRing A]
    [IsRegularRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [IsDomain B]
    [IsIntegrallyClosed B] (hinj : Function.Injective (algebraMap A B))
    (h : ∀ (q : Ideal B) [q.IsPrime], (q.comap (algebraMap A B)).height ≤ 1 →
      Algebra.IsEtaleAt A q) :
    Algebra.Etale A B := by
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have key : ∀ n : ℕ, ∀ (q : Ideal B) [q.IsPrime],
      (q.comap (algebraMap A B)).height = n → Algebra.IsEtaleAt A q := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro q _ hqn
      by_cases hn : n ≤ 1
      · exact h q (by rw [hqn]; exact_mod_cast hn)
      have hdim : 2 ≤ ringKrullDim (Localization.AtPrime (q.comap (algebraMap A B))) := by
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height (q.comap (algebraMap A B))
          (Localization.AtPrime (q.comap (algebraMap A B))), hqn]
        have h2 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) :=
          WithBot.coe_le_coe.mpr (by exact_mod_cast (by omega : 2 ≤ n))
        exact h2
      refine isEtaleAt_of_isIntegrallyClosed hinj _ hdim (fun q' _ hle hne ↦ ?_) q rfl
      have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle hne)
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
        (Ideal.height_ne_top_of_isPrime (I := q'.comap (algebraMap A B)))
      rw [← hm, hqn] at hlt
      exact ih m (by exact_mod_cast hlt) q' hm.symm
  refine Algebra.etaleLocus_eq_univ_iff_etale.mp (Set.eq_univ_of_forall fun q ↦ ?_)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ideal.height_ne_top_of_isPrime (I := q.asIdeal.comap (algebraMap A B)))
  exact key n q.asIdeal hn.symm

/-- XIII.5.2, purity step (SGA 2 XIV 1.11; Zariski–Nagata): let `S` be a regular local ring,
`t ≠ 0` in `S` and `C` a finite étale `S[1/t]`-algebra. If the normalization `W` of `S` in `C` is
étale over `S` at every prime lying over a height-one prime of `V(t)` (the maximal points of
`V(t)`), then `W` is finite étale over `S` and `C = S[1/t] ⊗_S W`: the covering `Spec C` of
`Spec S[1/t]` extends to the étale covering `Spec W` of `Spec S`. -/
theorem etale_integralClosure_of_forall_isEtaleAt {S : Type u} [CommRing S]
    [IsRegularLocalRing S] {t : S} (ht : t ≠ 0) (C : Type u)
    [CommRing C] [Algebra S C] [Algebra (Localization.Away t) C]
    [IsScalarTower S (Localization.Away t) C] [Module.Finite (Localization.Away t) C]
    [Algebra.Etale (Localization.Away t) C]
    (h : ∀ (q : Ideal (integralClosure S C)) [q.IsPrime],
      t ∈ q.comap (algebraMap S (integralClosure S C)) →
      (q.comap (algebraMap S (integralClosure S C))).height = 1 → Algebra.IsEtaleAt S q) :
    Module.Finite S (integralClosure S C) ∧ Algebra.Etale S (integralClosure S C) ∧
      Nonempty (C ≃ₐ[Localization.Away t] Localization.Away t ⊗[S] integralClosure S C) := by
  classical
  have ht' := powers_le_nonZeroDivisors_of_noZeroDivisors ht
  have : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization ht'
  have : IsIntegrallyClosed (Localization.Away t) :=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers t) ht'
  -- `C` is the localization of `W` at `t`
  have hloc := integralClosure.isLocalization_powers t (Localization.Away t) C
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure S C)
      (Submonoid.powers t)) C := by
    rw [Algebra.algebraMapSubmonoid_powers]
    exact hloc
  have hpush := Algebra.isPushout_of_isLocalization (Submonoid.powers t) (Localization.Away t)
    (integralClosure S C) C
  have := hpush.symm
  suffices H : Module.Finite S (integralClosure S C) ∧ Algebra.Etale S (integralClosure S C) from
    ⟨H.1, H.2, ⟨(Algebra.IsPushout.equiv S (Localization.Away t) (integralClosure S C) C).symm⟩⟩
  -- `W` is étale over `S` at every prime over a prime of height `≤ 1`
  have : Algebra.FormallyEtale S (Localization.Away t) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  have : Algebra.FormallyEtale S C := Algebra.FormallyEtale.comp S (Localization.Away t) C
  have hW : ∀ (q : Ideal (integralClosure S C)) [q.IsPrime],
      (q.comap (algebraMap S (integralClosure S C))).height ≤ 1 → Algebra.IsEtaleAt S q := by
    intro q _ hq
    by_cases htq : t ∈ q.comap (algebraMap S (integralClosure S C))
    · refine h q htq (le_antisymm hq ?_)
      have : (⊥ : Ideal S).IsPrime := Ideal.isPrime_bot
      have hlt : (⊥ : Ideal S) < q.comap (algebraMap S (integralClosure S C)) :=
        bot_lt_iff_ne_bot.mpr fun h0 ↦ ht (by rw [h0] at htq; exact htq)
      have := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
      rw [Ideal.height_bot] at this
      exact Order.one_le_iff_pos.mpr this
    · have : Algebra.FormallyEtale S
          (Localization.Away (algebraMap S (integralClosure S C) t)) :=
        Algebra.FormallyEtale.of_equiv ((IsLocalization.algEquiv (Submonoid.powers
          (algebraMap S (integralClosure S C) t)) C _).restrictScalars S)
      exact (Algebra.basicOpen_subset_etaleLocus_iff (R := S)).mpr this
        (show (⟨q, inferInstance⟩ : PrimeSpectrum (integralClosure S C)) ∈
          PrimeSpectrum.basicOpen _ from htq)
  -- the total ring of fractions `L = C ⊗_{S[1/t]} K` of `C`, `K = Frac S`
  let g : Localization.Away t →+* FractionRing S :=
    IsLocalization.map _ (T := nonZeroDivisors S) (RingHom.id S) ht'
  let : Algebra (Localization.Away t) (FractionRing S) := g.toAlgebra
  have : IsScalarTower S (Localization.Away t) (FractionRing S) :=
    .of_algebraMap_eq fun s ↦ by
      exact (IsLocalization.map_eq (S := Localization.Away t) (Q := FractionRing S)
        (g := RingHom.id S) (T := nonZeroDivisors S) ht' s).symm
  have : IsFractionRing (Localization.Away t) (FractionRing S) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers t) _ _
  let : Algebra (FractionRing S) (C ⊗[Localization.Away t] FractionRing S) :=
    Algebra.TensorProduct.rightAlgebra
  let eL : FractionRing S ⊗[Localization.Away t] C ≃ₐ[FractionRing S]
      C ⊗[Localization.Away t] FractionRing S :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm _ _ _).toRingEquiv) fun _ ↦ rfl
  have : Algebra.Etale (FractionRing S) (C ⊗[Localization.Away t] FractionRing S) :=
    Algebra.Etale.of_equiv eL
  have : Module.Finite (FractionRing S) (C ⊗[Localization.Away t] FractionRing S) :=
    Module.Finite.equiv eL.toLinearEquiv
  have : IsArtinianRing (C ⊗[Localization.Away t] FractionRing S) :=
    IsArtinianRing.of_finite (FractionRing S) _
  have : IsReduced (C ⊗[Localization.Away t] FractionRing S) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing S) _
  have : IsScalarTower S (FractionRing S) (C ⊗[Localization.Away t] FractionRing S) :=
    .of_algebraMap_eq fun s ↦ by
      change algebraMap S C s ⊗ₜ[Localization.Away t] (1 : FractionRing S) =
        (1 : C) ⊗ₜ[Localization.Away t] algebraMap S (FractionRing S) s
      rw [IsScalarTower.algebraMap_apply S (Localization.Away t) C,
        IsScalarTower.algebraMap_apply S (Localization.Away t) (FractionRing S),
        ← mul_one (algebraMap (Localization.Away t) C _), ← Algebra.smul_def,
        TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  -- `W` is the normalization of `S` in `L`, since `C` is normal (I.9.5)
  have hCL : IsIntegrallyClosedIn C (C ⊗[Localization.Away t] FractionRing S) :=
    SGA.SGA1.ExposeI.isIntegrallyClosedIn_tensor_fractionRing (FractionRing S)
  have hinjCL := IsIntegralClosure.algebraMap_injective C C
    (C ⊗[Localization.Away t] FractionRing S)
  let Ψ : integralClosure S C ≃ₐ[S]
      integralClosure S (C ⊗[Localization.Away t] FractionRing S) :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom S C _).mapIntegralClosure
      ⟨fun x y hxy ↦ Subtype.ext (hinjCL (congrArg Subtype.val hxy)), fun y ↦ by
        obtain ⟨c, hc⟩ := (IsIntegralClosure.isIntegral_iff (A := C) (R := C)
          (B := C ⊗[Localization.Away t] FractionRing S)).mp (y.2.tower_top (A := C))
        refine ⟨⟨c, (isIntegral_algHom_iff (IsScalarTower.toAlgHom S C _) hinjCL).mp ?_⟩,
          Subtype.ext hc⟩
        rw [IsScalarTower.coe_toAlgHom', hc]
        exact y.2⟩
  -- `L` is a product of fields `F`, and `W` the product of the normalizations of `S` in the `F`
  let Φ := ((IsArtinianRing.equivPi (C ⊗[Localization.Away t] FractionRing S)).restrictScalars
    S).mapIntegralClosure.trans (integralClosure.piAlgEquiv S
      (fun M : MaximalSpectrum (C ⊗[Localization.Away t] FractionRing S) ↦
        C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal))
  let Θ := Ψ.trans Φ
  -- purity on each factor
  have key (M : MaximalSpectrum (C ⊗[Localization.Away t] FractionRing S)) :
      Module.Finite S (integralClosure S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal)) ∧
      Algebra.Etale S
        (integralClosure S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal)) := by
    let := Ideal.Quotient.field M.asIdeal
    have : Module.Finite (FractionRing S) (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ _ M.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have : Algebra.FormallyUnramified (FractionRing S)
        (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal) :=
      Algebra.FormallyUnramified.comp _ (C ⊗[Localization.Away t] FractionRing S) _
    have : Algebra.IsSeparable (FractionRing S)
        (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal) :=
      Algebra.FormallyUnramified.isSeparable _ _
    have hfin := IsIntegralClosure.finite S (FractionRing S)
      (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal)
      (integralClosure S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal))
    have : IsIntegrallyClosed
        (integralClosure S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal)) :=
      integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing S)
    have hinj : Function.Injective (algebraMap S
        (integralClosure S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal))) := by
      intro a b hab
      have := congrArg Subtype.val hab
      change algebraMap S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal) a =
        algebraMap S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal) b at this
      rw [IsScalarTower.algebraMap_apply S (FractionRing S), IsScalarTower.algebraMap_apply S
        (FractionRing S) (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal) b] at this
      exact IsFractionRing.injective S (FractionRing S) ((algebraMap _ _).injective this)
    refine ⟨hfin, etale_of_isIntegrallyClosed_of_forall_height_le_one hinj fun q _ hq ↦ ?_⟩
    -- the local ring of `q` is that of a prime of `W`
    have h1 := Ideal.bijective_localAlgHom_evalAlgHom (A := S)
      (L := fun M : MaximalSpectrum (C ⊗[Localization.Away t] FractionRing S) ↦
        integralClosure S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal)) M q
    have h3 := bijective_localAlgHom_algEquiv S Θ (q.comap (Pi.evalAlgHom S
      (fun M : MaximalSpectrum (C ⊗[Localization.Away t] FractionRing S) ↦
        integralClosure S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal)) M))
    refine Algebra.IsEtaleAt.of_bijective_localAlgHom _ q h1
      (Algebra.IsEtaleAt.of_bijective_localAlgHom _ _ h3 (hW _ ?_))
    change (((q.comap _).comap _).under S).height ≤ 1
    rwa [Ideal.under_comap_algHom, Ideal.under_comap_algHom]
  have : ∀ M : MaximalSpectrum (C ⊗[Localization.Away t] FractionRing S),
      Module.Finite S (integralClosure S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal)) :=
    fun M ↦ (key M).1
  have : ∀ M : MaximalSpectrum (C ⊗[Localization.Away t] FractionRing S),
      Algebra.Etale S (integralClosure S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal)) :=
    fun M ↦ (key M).2
  have : Algebra.FormallyEtale S (Π M : MaximalSpectrum (C ⊗[Localization.Away t] FractionRing S),
      integralClosure S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal)) :=
    (Algebra.FormallyEtale.pi_iff _).mpr fun M ↦ inferInstance
  have : Algebra.FinitePresentation S
      (Π M : MaximalSpectrum (C ⊗[Localization.Away t] FractionRing S),
        integralClosure S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale S (Π M : MaximalSpectrum (C ⊗[Localization.Away t] FractionRing S),
      integralClosure S (C ⊗[Localization.Away t] FractionRing S ⧸ M.asIdeal)) :=
    ⟨inferInstance, inferInstance⟩
  exact ⟨Module.Finite.equiv Θ.symm.toLinearEquiv, Algebra.Etale.of_equiv Θ.symm⟩

/-- XIII.5.2, reduction to codimension one (SGA: "we may restrict ourselves to the points `x̄'`
which project onto a maximal point of `Y'`", by SGA 2 XIV 1.11). Let `B` be a finite étale
`A[1/π]`-algebra and `S` a regular local `A`-algebra in which `π` is nonzero (in XIII.5.2: `A`
regular local, `π = ∏ fᵢ` and `S = A' = A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`, see
`KummerAlgebra.isRegularLocalRing`). If the normalization of `S` in `S ⊗_A B` is étale over `S`
above the height-one primes of `S` containing `π` (the maximal points of `Y' = V(π)`), then
`S ⊗_A B` extends to a finite étale `S`-algebra `W`: `S ⊗_A B = S[1/π] ⊗_S W`. -/
theorem exists_etale_of_forall_isEtaleAt {A : Type u} [CommRing A]
    (π : A) (B : Type u) [CommRing B] [Algebra A B] [Algebra (Localization.Away π) B]
    [IsScalarTower A (Localization.Away π) B] [Module.Finite (Localization.Away π) B]
    [Algebra.Etale (Localization.Away π) B] (S : Type u) [CommRing S] [Algebra A S]
    [IsRegularLocalRing S] (hπ : algebraMap A S π ≠ 0)
    (h : ∀ (q : Ideal (integralClosure S (S ⊗[A] B))) [q.IsPrime],
      algebraMap A S π ∈ q.comap (algebraMap S _) →
      (q.comap (algebraMap S _)).height = 1 → Algebra.IsEtaleAt S q) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra S W), Module.Finite S W ∧ Algebra.Etale S W ∧
      Nonempty (S ⊗[A] B ≃ₐ[S] Localization.Away (algebraMap A S π) ⊗[S] W) := by
  -- `S ⊗_A B = S[1/π] ⊗_{A[1/π]} B`
  let : Algebra (Localization.Away π) (Localization.Away (algebraMap A S π)) :=
    (Localization.awayMap (algebraMap A S) π).toAlgebra
  have : IsScalarTower A (Localization.Away π) (Localization.Away (algebraMap A S π)) :=
    .of_algebraMap_eq fun a ↦ by
      change _ = Localization.awayMap _ _ _
      simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq,
        ← IsScalarTower.algebraMap_apply]
  have : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers π))
      (Localization.Away (algebraMap A S π)) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  have := Algebra.isPushout_of_isLocalization (Submonoid.powers π) (Localization.Away π) S
    (Localization.Away (algebraMap A S π))
  let e : S ⊗[A] B ≃ₐ[S] Localization.Away (algebraMap A S π) ⊗[Localization.Away π] B :=
    Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
      (Algebra.IsPushout.cancelBaseChange A S (Localization.Away π)
        (Localization.Away (algebraMap A S π)) B).symm
      (fun _ _ _ _ ↦ by simp [Algebra.TensorProduct.tmul_mul_tmul])
      (by simp [Algebra.TensorProduct.one_def])
  -- purity
  obtain ⟨h1, h2, ⟨e'⟩⟩ := etale_integralClosure_of_forall_isEtaleAt hπ
    (Localization.Away (algebraMap A S π) ⊗[Localization.Away π] B) fun q _ hqt hqm ↦ by
    let E : integralClosure S (S ⊗[A] B) ≃ₐ[S] integralClosure S
        (Localization.Away (algebraMap A S π) ⊗[Localization.Away π] B) := e.mapIntegralClosure
    refine Algebra.IsEtaleAt.of_algEquiv (S' := integralClosure S
      (Localization.Away (algebraMap A S π) ⊗[Localization.Away π] B)) E q (h _ ?_ ?_)
    · rw [Ideal.mem_comap, Ideal.mem_comap]
      simpa using hqt
    · convert hqm using 2
      ext x
      rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap]
      simp
  exact ⟨_, _, _, h1, h2, ⟨e.trans (e'.restrictScalars S)⟩⟩

/-! ### XIII.5.2: the input in codimension one -/

open Polynomial

/-- Étaleness of normalizations under localization: let `S' = N⁻¹S` and `C' = N⁻¹C` for an
`S`-algebra `C`. If the normalization of `S'` in `C'` is formally étale over `S'`, then the
normalization of `S` in `C` is étale over `S` at every prime not meeting `N`. -/
theorem isEtaleAt_integralClosure_of_isLocalization {S S' C C' : Type*} [CommRing S]
    [CommRing S'] [CommRing C] [CommRing C'] [Algebra S S'] [Algebra S C] [Algebra S C']
    [Algebra C C'] [Algebra S' C'] [IsScalarTower S C C'] [IsScalarTower S S' C']
    (N : Submonoid S) [IsLocalization N S'] [IsLocalization (Algebra.algebraMapSubmonoid C N) C']
    [Algebra.FormallyEtale S' (integralClosure S' C')] (q : Ideal (integralClosure S C))
    [q.IsPrime] (hq : ∀ s ∈ N, algebraMap S (integralClosure S C) s ∉ q) :
    Algebra.IsEtaleAt S q := by
  let ψ : integralClosure S C →+* integralClosure S' C' :=
    { toFun x := ⟨algebraMap C C' x.1, (x.2.map (IsScalarTower.toAlgHom S C C')).tower_top⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' _ _ := Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' _ _ := Subtype.ext (map_add _ _ _) }
  let : Algebra (integralClosure S C) (integralClosure S' C') := ψ.toAlgebra
  have : IsScalarTower (integralClosure S C) (integralClosure S' C') C' :=
    ⟨fun x y z ↦ by
      rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
        mul_assoc]
      rfl⟩
  have : IsScalarTower S (integralClosure S C) (integralClosure S' C') :=
    .of_algebraMap_eq fun s ↦ Subtype.ext (by
      change algebraMap S C' s = algebraMap C C' (algebraMap S C s)
      rw [← IsScalarTower.algebraMap_apply])
  have hloc := IsLocalization.integralClosure (R := S) (S := C) (Rf := S') (Sf := C') N
  have hd : Disjoint (Algebra.algebraMapSubmonoid (integralClosure S C) N :
      Set (integralClosure S C)) (q : Set (integralClosure S C)) :=
    Set.disjoint_left.mpr fun _ ⟨s, hs, e⟩ hsq ↦ hq s hs (e ▸ hsq)
  have hq' := IsLocalization.isPrime_of_isPrime_disjoint _ (integralClosure S' C') q
    inferInstance hd
  have hL := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid (integralClosure S C) N)
    (Localization.AtPrime (q.map (algebraMap (integralClosure S C) (integralClosure S' C'))))
    (q.map (algebraMap (integralClosure S C) (integralClosure S' C')))
  have hc : (q.map (algebraMap (integralClosure S C) (integralClosure S' C'))).comap
      (algebraMap (integralClosure S C) (integralClosure S' C')) = q :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ inferInstance hd
  simp only [hc] at hL
  let e : Localization.AtPrime q ≃ₐ[integralClosure S C]
      Localization.AtPrime (q.map (algebraMap (integralClosure S C) (integralClosure S' C'))) :=
    IsLocalization.algEquiv q.primeCompl _ _
  have : Algebra.FormallyEtale S S' := Algebra.FormallyEtale.of_isLocalization N
  have : Algebra.FormallyEtale S
      (Localization.AtPrime (q.map (algebraMap (integralClosure S C) (integralClosure S' C')))) :=
    Algebra.FormallyEtale.comp S S' _
  exact Algebra.FormallyEtale.of_equiv (e.restrictScalars S).symm

/-- A ring isomorphism compatible with `algebraMap`, followed by an algebra isomorphism, is
compatible with `algebraMap`. -/
lemma ringEquiv_trans_algEquiv_commutes {R S' T U : Type*} [CommSemiring R] [Semiring S']
    [Semiring T] [Semiring U] [Algebra R S'] [Algebra R T] [Algebra R U] (g : S' ≃+* T)
    (e : T ≃ₐ[R] U) (hg : ∀ r, g (algebraMap R S' r) = algebraMap R T r) (r : R) :
    (g.trans e.toRingEquiv) (algebraMap R S' r) = algebraMap R U r := by
  rw [RingEquiv.trans_apply, hg]
  exact e.commutes r

/-- In a regular local ring, a member of a regular system of parameters is not a multiple of
another one. -/
theorem IsPartOfRegularSystemOfParameters.notMem_span_singleton {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {ι : Type*} [Finite ι] {f : ι → A}
    (hf : IsPartOfRegularSystemOfParameters f) {i j : ι} (hij : i ≠ j) :
    f i ∉ Ideal.span {f j} := by
  classical
  cases nonempty_fintype ι
  obtain ⟨k, g, hmax, hdim⟩ := hf
  intro hi
  let y : {l // l ≠ i} ⊕ Fin k → A := Sum.elim (fun l ↦ f l) g
  have hm : maximalIdeal A = Ideal.span (Set.range y) := by
    rw [hmax]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ (⟨l, rfl⟩ | ⟨l, rfl⟩)
      · by_cases hl : l = i
        · rw [hl]
          have hj : {f j} ⊆ Set.range y :=
            Set.singleton_subset_iff.mpr ⟨Sum.inl ⟨j, hij.symm⟩, rfl⟩
          exact Ideal.span_mono hj hi
        · exact Ideal.subset_span ⟨Sum.inl ⟨l, hl⟩, rfl⟩
      · exact Ideal.subset_span ⟨Sum.inr l, rfl⟩
    · rw [Ideal.span_le]
      rintro _ ⟨l | l, rfl⟩
      · exact Ideal.subset_span (Or.inl ⟨l.1, rfl⟩)
      · exact Ideal.subset_span (Or.inr ⟨l, rfl⟩)
  have h1 : (maximalIdeal A).spanFinrank ≤ Nat.card ({l // l ≠ i} ⊕ Fin k) := by
    rw [hm]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    rw [← Set.image_univ, ← Set.ncard_univ]
    exact Set.ncard_image_le (Set.toFinite _)
  have h2 : Nat.card {l // l ≠ i} + 1 = Nat.card ι := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
    have := Fintype.card_pos (α := ι) (h := ⟨i⟩)
    omega
  have h4 : ((maximalIdeal A).spanFinrank : WithBot ℕ∞) = ((Nat.card ι + k : ℕ) : WithBot ℕ∞) := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal, hdim]
  have h5 : (maximalIdeal A).spanFinrank = Nat.card ι + k := by exact_mod_cast h4
  rw [Nat.card_sum, Nat.card_fin] at h1
  omega

/-- The members of a regular system of parameters lie in the maximal ideal. -/
theorem IsPartOfRegularSystemOfParameters.span_singleton_le_maximalIdeal {A : Type*}
    [CommRing A] [IsLocalRing A] {ι : Type*} {f : ι → A}
    (hf : IsPartOfRegularSystemOfParameters f) (j : ι) : Ideal.span {f j} ≤ maximalIdeal A := by
  obtain ⟨k, g, hmax, -⟩ := hf
  rw [Ideal.span_le, Set.singleton_subset_iff, hmax]
  exact Ideal.subset_span (Or.inl ⟨j, rfl⟩)

/-- For `f` part of a regular system of parameters of a regular local ring `A`, `A/(f_j)` is a
regular local ring; in particular `(f_j)` is prime. -/
theorem IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {ι : Type*} [Finite ι] {f : ι → A}
    (hf : IsPartOfRegularSystemOfParameters f) (j : ι) :
    ∃ (_ : IsLocalRing (A ⧸ Ideal.span {f j})), IsRegularLocalRing (A ⧸ Ideal.span {f j}) := by
  classical
  cases nonempty_fintype ι
  obtain ⟨k, g, hmax, hk⟩ := hf
  let y : {l // l ≠ j} ⊕ Fin k → A := Sum.elim (fun l ↦ f l) g
  have hrange : Set.range f ∪ Set.range g = Set.range (fun _ : Unit ↦ f j) ∪ Set.range y := by
    ext a
    constructor
    · rintro (⟨l, rfl⟩ | ⟨l, rfl⟩)
      · by_cases hl : l = j
        · exact Or.inl ⟨(), by rw [hl]⟩
        · exact Or.inr ⟨Sum.inl ⟨l, hl⟩, rfl⟩
      · exact Or.inr ⟨Sum.inr l, rfl⟩
    · rintro (⟨-, rfl⟩ | ⟨l | l, rfl⟩)
      · exact Or.inl ⟨j, rfl⟩
      · exact Or.inl ⟨l.1, rfl⟩
      · exact Or.inr ⟨l, rfl⟩
  have h2 : Nat.card {l // l ≠ j} + 1 = Nat.card ι := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
    have := Fintype.card_pos (α := ι) (h := ⟨j⟩)
    omega
  obtain ⟨hl, hreg, -⟩ := IsRegularLocalRing.quotient_span_range (fun _ : Unit ↦ f j) y
    (hmax.trans (by rw [hrange])) (by
      rw [← hk, Nat.card_unique, Nat.card_sum, Nat.card_fin,
        show 1 + (Nat.card {l // l ≠ j} + k) = Nat.card ι + k by omega])
  rw [Set.range_const] at hl hreg
  exact ⟨hl, hreg⟩

/-- For `f` part of a regular system of parameters of a regular local ring, `(f_j)` is prime. -/
theorem IsPartOfRegularSystemOfParameters.isPrime_span_singleton {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {ι : Type*} [Finite ι] {f : ι → A}
    (hf : IsPartOfRegularSystemOfParameters f) (j : ι) : (Ideal.span {f j}).IsPrime := by
  obtain ⟨_, _⟩ := hf.isRegularLocalRing_quotient j
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

/-- For `f` part of a regular system of parameters of a regular local ring `A`, `(f_j)` is prime
and `A_(f_j)` is a discrete valuation ring with uniformizer `f_j`. -/
theorem IsPartOfRegularSystemOfParameters.isDiscreteValuationRing_localization {A : Type*}
    [CommRing A] [IsRegularLocalRing A] {ι : Type*} [Finite ι]
    {f : ι → A} (hf : IsPartOfRegularSystemOfParameters f) (j : ι) :
    ∃ _ : (Ideal.span {f j}).IsPrime,
      IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {f j})) := by
  have hp : (Ideal.span {f j}).IsPrime := hf.isPrime_span_singleton j
  refine ⟨hp, ?_⟩
  have hf0R : algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j) ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective _
      (Ideal.span {f j}).primeCompl_le_nonZeroDivisors)).mpr (hf.ne_zero j)
  have hRm : maximalIdeal (Localization.AtPrime (Ideal.span {f j})) =
      Ideal.span {algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j)} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {f j}), Ideal.map_span,
      Set.image_singleton]
  have hnf : ¬ IsField (Localization.AtPrime (Ideal.span {f j})) := fun h ↦ by
    have := (IsLocalRing.isField_iff_maximalIdeal_eq.mp h)
    rw [hRm, Ideal.span_singleton_eq_bot] at this
    exact hf0R this
  have hRp : (maximalIdeal (Localization.AtPrime (Ideal.span {f j}))).IsPrincipal := ⟨⟨_, hRm⟩⟩
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).mpr hRp

set_option maxHeartbeats 1600000 in
-- the instance problems on the localizations of `S ⊗_A B` are large
/-- XIII.5.2, the input in codimension one: let `A` be a regular local ring, `f₁, …, f_r` part of
a regular system of parameters, `B` a finite étale `A[1/∏ fᵢ]`-algebra tamely ramified along
`Σ div fᵢ` with ramification indices above `(fᵢ)` dividing `nᵢ`, the `nᵢ` nonzero in the residue
fields `κ((f_j))` (e.g. prime to the residue characteristic of `A`), and
`S ≅ A' = A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`. Then the normalization of `S` in `S ⊗_A B` is étale over `S`
above the height-one primes of `V(∏ Tᵢ)` (its maximal points). Such a prime lies over `(f_j)`
for some `j` (heights are preserved, `A → S` being integral with going down), and we apply X.3.6
over the discrete valuation ring `R = A_(f_j)`, in which the other `fᵢ` are units, so that
`A' ⊗_A R` is `R[T_j]/(T_j^{n_j} - f_j)` up to the finite étale factor
`R[Tᵢ, i ≠ j]/(Tᵢ^{nᵢ} - fᵢ)` (`formallyEtale_integralClosure_of_forall_isTamelyRamifiedAt`). -/
theorem isEtaleAt_integralClosure_of_isTamelyRamifiedAlong (A : Type u) [CommRing A]
    [IsRegularLocalRing A] {r : ℕ} (f : Fin r → A)
    (hf : IsPartOfRegularSystemOfParameters f) (B : Type u) [CommRing B] [Algebra A B]
    [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B)
    (n : Fin r → ℕ)
    (hdvd : ∀ (i : Fin r) (Q : Ideal (integralClosure A (FractionRing A ⊗[A] B))) [Q.IsPrime],
      Q.LiesOver (Ideal.span {f i}) → Q.ramificationIdx A ∣ n i)
    (hn0 : ∀ i j, (n i : A) ∉ Ideal.span {f j}) (S : Type u) [CommRing S] [Algebra A S]
    (σ₀ : S ≃ₐ[A] KummerAlgebra n f) (q : Ideal (integralClosure S (S ⊗[A] B)))
    [q.IsPrime]
    (hqt : algebraMap A S (∏ i, f i) ∈ q.comap (algebraMap S (integralClosure S (S ⊗[A] B))))
    (hqh : (q.comap (algebraMap S (integralClosure S (S ⊗[A] B)))).height = 1) :
    Algebra.IsEtaleAt S q := by
  classical
  have hnpos : ∀ i, 0 < n i := fun i ↦ Nat.pos_of_ne_zero fun h ↦ hn0 i i (by
    rw [h, Nat.cast_zero]; exact zero_mem _)
  have : Algebra.IsIntegral A (KummerAlgebra n f) := KummerAlgebra.isIntegral f hnpos
  have : Algebra.IsIntegral A S := ⟨fun x ↦ by
    simpa using (Algebra.IsIntegral.isIntegral (R := A) (σ₀ x)).map σ₀.symm.toAlgHom⟩
  -- the prime `q ∩ A` contains one of the `f j`
  have : (q.comap (algebraMap A (integralClosure S (S ⊗[A] B)))).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨j, -, hj⟩ : ∃ j ∈ Finset.univ,
      f j ∈ q.comap (algebraMap A (integralClosure S (S ⊗[A] B))) := by
    refine Ideal.IsPrime.prod_mem_iff.mp ?_
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A S]
    exact hqt
  have hf0 : f j ≠ 0 := hf.ne_zero j
  have hp : (Ideal.span {f j}).IsPrime := hf.isPrime_span_singleton j
  -- `q` lies over `(f_j)`
  have hqA : q.comap (algebraMap A (integralClosure S (S ⊗[A] B))) = Ideal.span {f j} := by
    have hle : Ideal.span {f j} ≤ q.comap (algebraMap A (integralClosure S (S ⊗[A] B))) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hj
    -- `A → S` is integral with going down, so `ht (q ∩ A) ≤ ht (q ∩ S) = 1`
    have : IsDomain (KummerAlgebra n f) := KummerAlgebra.isDomain hnpos hf
    have : IsDomain S := Function.Injective.isDomain σ₀.toRingEquiv.toRingHom σ₀.injective
    have : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr fun a b hab ↦
      KummerAlgebra.injective_algebraMap f hnpos (by rw [← σ₀.commutes, ← σ₀.commutes, hab])
    have hPQ : (q.comap (algebraMap S (integralClosure S (S ⊗[A] B)))).under A =
        q.comap (algebraMap A (integralClosure S (S ⊗[A] B))) := by
      rw [Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    have hht := Ideal.height_under_le_height_of_hasGoingDown (R := A)
      (q.comap (algebraMap S (integralClosure S (S ⊗[A] B))))
    rw [hqh, hPQ] at hht
    by_contra hne
    have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle (Ne.symm hne))
    have h0 : (⊥ : Ideal A) < Ideal.span {f j} :=
      bot_lt_iff_ne_bot.mpr (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hf0)
    have : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
    have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime h0
    rw [Ideal.height_bot] at h2
    exact absurd ((Order.one_le_iff_pos.mpr h2).trans_lt h1) (not_lt.mpr hht)
  -- the discrete valuation ring `R = A_(f₁)`, with fraction field `K = Frac A`
  have hf0R : algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j) ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective _
      (Ideal.span {f j}).primeCompl_le_nonZeroDivisors)).mpr hf0
  have hRm : maximalIdeal (Localization.AtPrime (Ideal.span {f j})) =
      Ideal.span {algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j)} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {f j}), Ideal.map_span,
      Set.image_singleton]
  have hnf : ¬ IsField (Localization.AtPrime (Ideal.span {f j})) := fun h ↦ by
    have := (IsLocalRing.isField_iff_maximalIdeal_eq.mp h)
    rw [hRm, Ideal.span_singleton_eq_bot] at this
    exact hf0R this
  have hRp : (maximalIdeal (Localization.AtPrime (Ideal.span {f j}))).IsPrincipal := ⟨⟨_, hRm⟩⟩
  have : IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {f j})) :=
    ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).mpr hRp
  have hπR : Irreducible (algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hRm
  have : Fact (Irreducible (algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j))) :=
    ⟨hπR⟩
  have : IsFractionRing (Localization.AtPrime (Ideal.span {f j})) (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Ideal.span {f j}).primeCompl _ _
  have : NeZero (n j) := ⟨(hnpos j).ne'⟩
  have hnR : ((n j : ℕ) : Localization.AtPrime (Ideal.span {f j})) ∉
      maximalIdeal (Localization.AtPrime (Ideal.span {f j})) := by
    rw [← map_natCast (algebraMap A (Localization.AtPrime (Ideal.span {f j}))),
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Ideal.span {f j})]
    exact hn0 j j
  -- `E = Frac A ⊗_A B` is finite étale over `Frac A`
  have hπK : IsUnit (algebraMap A (FractionRing A) (∏ i, f i)) := isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective A _)).mpr
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hf.ne_zero i))
  let : Algebra (Localization.Away (∏ i, f i)) (FractionRing A) :=
    (IsLocalization.Away.lift _ hπK).toAlgebra
  have : IsScalarTower A (Localization.Away (∏ i, f i)) (FractionRing A) :=
    .of_algebraMap_eq fun a ↦ (IsLocalization.Away.lift_eq _ hπK a).symm
  let eE : FractionRing A ⊗[Localization.Away (∏ i, f i)] B ≃ₐ[FractionRing A]
      FractionRing A ⊗[A] B :=
    AlgEquiv.ofRingEquiv (f := (IsLocalization.algebraTensorEquiv (Submonoid.powers (∏ i, f i))
      (Localization.Away (∏ i, f i)) (FractionRing A) B).toRingEquiv) fun _ ↦ rfl
  have : Algebra.Etale (FractionRing A) (FractionRing A ⊗[A] B) := Algebra.Etale.of_equiv eE
  have : Module.Finite (FractionRing A) (FractionRing A ⊗[A] B) :=
    Module.Finite.equiv eE.toLinearEquiv
  have : IsArtinianRing (FractionRing A ⊗[A] B) :=
    IsArtinianRing.of_finite (FractionRing A) _
  have : IsReduced (FractionRing A ⊗[A] B) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing A) _
  -- the normalization of `R` in `E` is the localization of that of `A`
  let ι : integralClosure A (FractionRing A ⊗[A] B) →+*
      integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B) :=
    { toFun x := ⟨x.1, x.2.tower_top⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  let : Algebra (integralClosure A (FractionRing A ⊗[A] B))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B)) :=
    ι.toAlgebra
  have : IsScalarTower (integralClosure A (FractionRing A ⊗[A] B))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B))
      (FractionRing A ⊗[A] B) := ⟨fun x y z ↦ mul_assoc (x : FractionRing A ⊗[A] B)
        (y : FractionRing A ⊗[A] B) z⟩
  have : IsScalarTower A (integralClosure A (FractionRing A ⊗[A] B))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid (FractionRing A ⊗[A] B)
      (Ideal.span {f j}).primeCompl) (FractionRing A ⊗[A] B) := by
    refine IsLocalization.of_le_isUnit ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [IsScalarTower.algebraMap_apply A (FractionRing A)]
    refine (isUnit_iff_ne_zero.mpr ?_).map _
    exact (map_ne_zero_iff _ (IsFractionRing.injective A _)).mpr fun h ↦ ha (h ▸ zero_mem _)
  have hloc := IsLocalization.integralClosure (R := A) (S := FractionRing A ⊗[A] B)
    (Rf := Localization.AtPrime (Ideal.span {f j})) (Sf := FractionRing A ⊗[A] B)
    (Ideal.span {f j}).primeCompl
  -- the primes of the normalization of `R` in `E` over `𝔪_R` are tame, with `e ∣ n`
  have hRtame : ∀ (Q' : Ideal (integralClosure (Localization.AtPrime (Ideal.span {f j}))
      (FractionRing A ⊗[A] B))) [Q'.IsPrime],
      Q'.LiesOver (maximalIdeal (Localization.AtPrime (Ideal.span {f j}))) →
      IsTamelyRamifiedAt (Localization.AtPrime (Ideal.span {f j})) Q' ∧
        Q'.ramificationIdx (Localization.AtPrime (Ideal.span {f j})) ∣ n j := by
    intro Q' _ hQ'
    have hQ'eq := IsLocalization.map_under (Algebra.algebraMapSubmonoid
      (integralClosure A (FractionRing A ⊗[A] B)) (Ideal.span {f j}).primeCompl) _ Q'
    have : (Q'.under (integralClosure A (FractionRing A ⊗[A] B))).IsPrime :=
      Ideal.comap_isPrime _ _
    have : (Q'.under (integralClosure A (FractionRing A ⊗[A] B))).LiesOver
        (Ideal.span {f j}) := ⟨by
      have e1 : (Q'.under (integralClosure A (FractionRing A ⊗[A] B))).under A = Q'.under A :=
        Ideal.under_under Q'
      have e2 : (Q'.under (Localization.AtPrime (Ideal.span {f j}))).under A = Q'.under A :=
        Ideal.under_under Q'
      rw [e1, ← e2, ← Ideal.over_def Q' (maximalIdeal (Localization.AtPrime (Ideal.span {f j}))),
        Localization.AtPrime.under_maximalIdeal]⟩
    have h1 := (isTamelyRamifiedAt_map_iff_of_isLocalization A (Ideal.span {f j})
      (Localization.AtPrime (Ideal.span {f j}))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B))
      (Q'.under (integralClosure A (FractionRing A ⊗[A] B)))).mpr (hB j _ inferInstance)
    have h2 := IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx
      (S := integralClosure A (FractionRing A ⊗[A] B)) (Ideal.span {f j})
      (Localization.AtPrime (Ideal.span {f j}))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B))
      (Q'.under (integralClosure A (FractionRing A ⊗[A] B)))
    have h3 := hdvd j (Q'.under (integralClosure A (FractionRing A ⊗[A] B))) inferInstance
    rw [← h2] at h3
    convert And.intro h1 h3 using 3 <;> exact hQ'eq.symm
  -- `S_R = S ⊗_A R ≅ R[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`, generated over `S₀ = R[T_j]/(T_j^{n_j} - f_j)` by
  -- the finite étale `R`-algebra `E = R[Tᵢ, i ≠ j]/(Tᵢ^{nᵢ} - fᵢ)`
  let : Algebra (Localization.AtPrime (Ideal.span {f j}))
      (S ⊗[A] Localization.AtPrime (Ideal.span {f j})) := Algebra.TensorProduct.rightAlgebra
  let κ : S ⊗[A] Localization.AtPrime (Ideal.span {f j}) ≃ₐ[
      Localization.AtPrime (Ideal.span {f j})] KummerAlgebra n
        (fun i ↦ algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f i)) :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm A S
        (Localization.AtPrime (Ideal.span {f j}))).toRingEquiv.trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl σ₀).trans
        (KummerAlgebra.baseChangeEquiv n f (Localization.AtPrime (Ideal.span {f j})))).toRingEquiv)
      (ringEquiv_trans_algEquiv_commutes _ _ fun r ↦ by
        change Algebra.TensorProduct.comm A S _ ((1 : S) ⊗ₜ r) = _
        rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply])
  let ιS : AdjoinRoot (X ^ n j - C (algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j)))
      →ₐ[Localization.AtPrime (Ideal.span {f j})] S ⊗[A] Localization.AtPrime (Ideal.span {f j}) :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (κ.symm (KummerAlgebra.T _ _ j)) (by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, ← map_pow, KummerAlgebra.T_pow, AlgEquiv.commutes,
        sub_eq_zero]
      rfl)
  let : Algebra (AdjoinRoot (X ^ n j - C (algebraMap A (Localization.AtPrime (Ideal.span {f j}))
      (f j)))) (S ⊗[A] Localization.AtPrime (Ideal.span {f j})) := ιS.toRingHom.toAlgebra
  have : IsScalarTower (Localization.AtPrime (Ideal.span {f j}))
      (AdjoinRoot (X ^ n j - C (algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j))))
      (S ⊗[A] Localization.AtPrime (Ideal.span {f j})) := IsScalarTower.of_algHom ιS
  have hunitR (i : {i // i ≠ j}) :
      IsUnit (algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f i)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ (Ideal.span {f j}) _).mpr
      (hf.notMem_span_singleton i.2)
  have hnunitR (i : {i // i ≠ j}) :
      IsUnit ((n i : ℕ) : Localization.AtPrime (Ideal.span {f j})) := by
    rw [← map_natCast (algebraMap A (Localization.AtPrime (Ideal.span {f j})))]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ (Ideal.span {f j}) _).mpr (hn0 i j)
  have : Algebra.Etale (Localization.AtPrime (Ideal.span {f j}))
      (KummerAlgebra (fun i : {i // i ≠ j} ↦ n i)
        (fun i ↦ algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f i))) :=
    KummerAlgebra.etale hnunitR hunitR
  have : Algebra.IsIntegral (Localization.AtPrime (Ideal.span {f j}))
      (KummerAlgebra (fun i : {i // i ≠ j} ↦ n i)
        (fun i ↦ algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f i))) :=
    KummerAlgebra.isIntegral _ fun i ↦ hnpos i
  have : Module.Finite (Localization.AtPrime (Ideal.span {f j}))
      (KummerAlgebra (fun i : {i // i ≠ j} ↦ n i)
        (fun i ↦ algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f i))) :=
    Algebra.IsIntegral.finite
  let γ : KummerAlgebra (fun i : {i // i ≠ j} ↦ n i)
      (fun i ↦ algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f i)) →ₐ[
        Localization.AtPrime (Ideal.span {f j})] S ⊗[A] Localization.AtPrime (Ideal.span {f j}) :=
    κ.symm.toAlgHom.comp (KummerAlgebra.lift (fun i ↦ KummerAlgebra.T _ _ i.1) fun i ↦
      KummerAlgebra.T_pow _ _ i.1)
  have hS' (s : S ⊗[A] Localization.AtPrime (Ideal.span {f j})) :
      s ∈ Algebra.adjoin (AdjoinRoot (X ^ n j - C (algebraMap A
        (Localization.AtPrime (Ideal.span {f j})) (f j)))) (Set.range γ) := by
    obtain ⟨x, rfl⟩ := κ.symm.surjective s
    have hx : x ∈ Algebra.adjoin (Localization.AtPrime (Ideal.span {f j}))
        (Set.range (KummerAlgebra.T n
          (fun i ↦ algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f i)))) := by
      rw [KummerAlgebra.adjoin_range_T]
      trivial
    have hle : (Algebra.adjoin (Localization.AtPrime (Ideal.span {f j}))
        (Set.range (KummerAlgebra.T n
          (fun i ↦ algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f i))))).map
        κ.symm.toAlgHom ≤ (Algebra.adjoin (AdjoinRoot (X ^ n j - C (algebraMap A
          (Localization.AtPrime (Ideal.span {f j})) (f j)))) (Set.range γ)).restrictScalars
            (Localization.AtPrime (Ideal.span {f j})) := by
      rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      by_cases hi : i = j
      · rw [hi]
        have : algebraMap (AdjoinRoot (X ^ n j - C (algebraMap A
            (Localization.AtPrime (Ideal.span {f j})) (f j))))
            (S ⊗[A] Localization.AtPrime (Ideal.span {f j})) (AdjoinRoot.root _) =
            κ.symm (KummerAlgebra.T _ _ j) := AdjoinRoot.liftAlgHom_root _ _ _ _
        change κ.symm (KummerAlgebra.T _ _ j) ∈ _
        rw [← this]
        exact Subalgebra.algebraMap_mem (R := AdjoinRoot (X ^ n j - C (algebraMap A
          (Localization.AtPrime (Ideal.span {f j})) (f j)))) (Algebra.adjoin _ (Set.range γ))
          (AdjoinRoot.root _)
      · exact Algebra.subset_adjoin ⟨KummerAlgebra.T _ _ ⟨i, hi⟩, by simp [γ]⟩
    exact hle ⟨x, hx, rfl⟩
  -- `C' = (S ⊗_A B)_{A - (f₁)}`, an algebra over `S ⊗_A R` and over `K`
  have hunitsR : ∀ y : (Ideal.span {f j}).primeCompl, IsUnit (Algebra.ofId A
      (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
        (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))) y) := by
    rintro ⟨a, ha⟩
    rw [Algebra.ofId_apply, IsScalarTower.algebraMap_apply A (S ⊗[A] B) (Localization
      (Algebra.algebraMapSubmonoid (S ⊗[A] B)
        (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))),
      IsScalarTower.algebraMap_apply A S (S ⊗[A] B)]
    exact IsLocalization.map_units _ ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem
      (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, ha⟩ : (Ideal.span {f j}).primeCompl)⟩ :
        Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl)⟩
  let gR : Localization.AtPrime (Ideal.span {f j}) →ₐ[A]
      Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
        (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl)) :=
    IsLocalization.liftAlgHom (M := (Ideal.span {f j}).primeCompl) hunitsR
  let lR : S ⊗[A] Localization.AtPrime (Ideal.span {f j}) →ₐ[S]
      Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
        (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl)) :=
    Algebra.TensorProduct.lift (Algebra.ofId S _) gR fun _ _ ↦ Commute.all _ _
  let : Algebra (S ⊗[A] Localization.AtPrime (Ideal.span {f j}))
      (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
        (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))) := lR.toRingHom.toAlgebra
  have : IsScalarTower S (S ⊗[A] Localization.AtPrime (Ideal.span {f j}))
      (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
        (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))) :=
    IsScalarTower.of_algHom lR
  let : Algebra (Localization.AtPrime (Ideal.span {f j}))
      (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
        (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))) := gR.toRingHom.toAlgebra
  have : IsScalarTower (Localization.AtPrime (Ideal.span {f j}))
      (S ⊗[A] Localization.AtPrime (Ideal.span {f j}))
      (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
        (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))) :=
    .of_algebraMap_eq fun r ↦ by
      change gR r = lR ((1 : S) ⊗ₜ r)
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  -- the `K`-algebra structure: the nonzero elements of `A` are units in `C'`
  have hπC : IsUnit (algebraMap A (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
      (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))) (f j)) := by
    have hπB : IsUnit (algebraMap A B (f j)) := by
      refine isUnit_of_dvd_unit (map_dvd (algebraMap A B)
        (Finset.dvd_prod_of_mem f (Finset.mem_univ j))) ?_
      rw [IsScalarTower.algebraMap_apply A (Localization.Away (∏ i, f i)) B]
      exact (IsLocalization.Away.algebraMap_isUnit _).map _
    rw [IsScalarTower.algebraMap_apply A (S ⊗[A] B), Algebra.TensorProduct.algebraMap_apply']
    exact (hπB.map (Algebra.TensorProduct.includeRight (R := A) (A := S))).map _
  have hunitsK : ∀ y : nonZeroDivisors A, IsUnit (algebraMap A
      (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
        (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))) y) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      ((map_ne_zero_iff _ (IsLocalization.injective _
        (Ideal.span {f j}).primeCompl_le_nonZeroDivisors)).mpr (nonZeroDivisors.ne_zero hy))
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hRm)
    have : algebraMap A (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
        (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))) y =
        gR (algebraMap A (Localization.AtPrime (Ideal.span {f j})) y) := (gR.commutes y).symm
    rw [this, hu, map_mul, map_pow, AlgHom.commutes]
    exact (u.isUnit.map gR).mul (hπC.pow k)
  let : Algebra (FractionRing A) (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
      (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))) :=
    (IsLocalization.lift hunitsK).toAlgebra
  have : IsScalarTower A (FractionRing A) (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
      (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))) :=
    .of_algebraMap_eq fun a ↦ (IsLocalization.lift_eq hunitsK a).symm
  have : IsScalarTower (Localization.AtPrime (Ideal.span {f j})) (FractionRing A)
      (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
        (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))) := by
    refine .of_algebraMap_eq' (IsLocalization.ringHom_ext (Ideal.span {f j}).primeCompl ?_)
    ext a
    change gR (algebraMap A _ a) = algebraMap (FractionRing A) _
      (algebraMap (Localization.AtPrime (Ideal.span {f j})) (FractionRing A) (algebraMap A _ a))
    rw [gR.commutes, ← IsScalarTower.algebraMap_apply A (Localization.AtPrime (Ideal.span {f j}))
      (FractionRing A), ← IsScalarTower.algebraMap_apply A (FractionRing A)]
  let β : FractionRing A ⊗[A] B →ₐ[FractionRing A] Localization (Algebra.algebraMapSubmonoid
      (S ⊗[A] B) (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl)) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ((IsScalarTower.toAlgHom A (S ⊗[A] B) _).comp
      Algebra.TensorProduct.includeRight) fun _ _ ↦ Commute.all _ _
  have hgen : ∀ c, c ∈ Algebra.adjoin (S ⊗[A] Localization.AtPrime (Ideal.span {f j}))
      (Set.range β) := by
    intro c
    obtain ⟨⟨x, ⟨_, s, hs, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid (S ⊗[A] B)
        (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl)) c
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    refine Subalgebra.mul_mem _ ?_ ?_
    · induction x using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Subalgebra.zero_mem _
      | tmul s' b =>
        rw [← mul_one s', ← one_mul b, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul]
        refine Subalgebra.mul_mem _ ?_ (Algebra.subset_adjoin ⟨1 ⊗ₜ b, by simp [β]⟩)
        have : algebraMap (S ⊗[A] B) (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
            (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))) (s' ⊗ₜ 1) =
            algebraMap (S ⊗[A] Localization.AtPrime (Ideal.span {f j})) _ (s' ⊗ₜ 1) := by
          change _ = lR (s' ⊗ₜ 1)
          rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
          rfl
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
      | add x y hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
    · obtain ⟨a, ha, rfl⟩ := hs
      have : IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
          (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))) (1 : S ⊗[A] B)
          ⟨algebraMap S (S ⊗[A] B) (algebraMap A S a), Algebra.mem_algebraMapSubmonoid_of_mem
            (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, ha⟩ : (Ideal.span {f j}).primeCompl)⟩ :
              Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl)⟩ =
          algebraMap (S ⊗[A] Localization.AtPrime (Ideal.span {f j})) _
            ((1 : S) ⊗ₜ IsLocalization.mk' _ (1 : A)
              (⟨a, ha⟩ : (Ideal.span {f j}).primeCompl)) := by
        rw [IsLocalization.mk'_eq_iff_eq_mul, map_one]
        change 1 = lR (1 ⊗ₜ _) * _
        rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul,
          ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← gR.commutes,
          ← map_mul, IsLocalization.mk'_spec, map_one, map_one]
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
  -- X.3.6 over `R`, with the finite étale factor `E`
  have := formallyEtale_integralClosure_of_forall_isTamelyRamifiedAt
    (Localization.AtPrime (Ideal.span {f j})) (FractionRing A)
    (algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j)) (n j) hnR
    (AdjoinRoot (X ^ n j - C (algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j))))
    AlgEquiv.refl _ (FractionRing A ⊗[A] B) hRtame
    (S ⊗[A] Localization.AtPrime (Ideal.span {f j})) γ hS' _ β hgen
  -- localization
  refine isEtaleAt_integralClosure_of_isLocalization (S' := S ⊗[A] Localization.AtPrime
    (Ideal.span {f j})) (C' := Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
      (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl)))
    (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl) q ?_
  rintro _ ⟨a, ha, rfl⟩ haq
  apply ha
  rw [← hqA]
  change a ∈ q.comap (algebraMap A (integralClosure S (S ⊗[A] B)))
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A S]
  exact haq

/-- XIII.5.2, existence part, for a regular local ring `A` and any number `r` of divisors: if
`B` is a finite étale `A[1/∏ fᵢ]`-algebra tamely ramified along `Σ div fᵢ`, the ramification
indices above `(fᵢ)` divide `nᵢ` and the `nᵢ` are nonzero in the residue fields `κ((f_j))` (e.g.
prime to the residue characteristic of `A`), then the restriction of `B` to
`U' = Spec A'[1/∏ fᵢ]`, `A' = A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`, extends to a finite étale `A'`-algebra
`W`. The proof combines X.3.6 at the maximal points of `V(∏ Tᵢ)`
(`isEtaleAt_integralClosure_of_isTamelyRamifiedAlong`) with purity
(`exists_etale_of_forall_isEtaleAt`). -/
theorem exists_etale_kummerAlgebra_of_isTamelyRamifiedAlong (A : Type u) [CommRing A]
    [IsRegularLocalRing A] {r : ℕ} (f : Fin r → A) (hf : IsPartOfRegularSystemOfParameters f)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B)
    (n : Fin r → ℕ)
    (hdvd : ∀ (i : Fin r) (Q : Ideal (integralClosure A (FractionRing A ⊗[A] B))) [Q.IsPrime],
      Q.LiesOver (Ideal.span {f i}) → Q.ramificationIdx A ∣ n i)
    (hp : ∀ i j, (n i : A) ∉ Ideal.span {f j}) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra (KummerAlgebra n f) W),
      Module.Finite (KummerAlgebra n f) W ∧ Algebra.Etale (KummerAlgebra n f) W ∧
      Nonempty (KummerAlgebra n f ⊗[A] B ≃ₐ[KummerAlgebra n f]
        Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)) ⊗[KummerAlgebra n f]
          W) := by
  have hnpos : ∀ i, 0 < n i := fun i ↦ Nat.pos_of_ne_zero fun h ↦ hp i i (by
    rw [h, Nat.cast_zero]; exact zero_mem _)
  have : IsRegularLocalRing (KummerAlgebra n f) := KummerAlgebra.isRegularLocalRing hnpos hf
  have hπ : algebraMap A (KummerAlgebra n f) (∏ i, f i) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (KummerAlgebra.injective_algebraMap f hnpos)]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hf.ne_zero i
  exact exists_etale_of_forall_isEtaleAt (∏ i, f i) B (KummerAlgebra n f) hπ
    fun q _ hqt hqh ↦ isEtaleAt_integralClosure_of_isTamelyRamifiedAlong A f hf B hB n hdvd hp
      (KummerAlgebra n f) AlgEquiv.refl q hqt hqh

/-- XIII.5.2 for a regular local ring `A`, existence part, with `nᵢ` the l.c.m. of the
ramification indices over `(fᵢ)`, assumed prime to the residue characteristic of `A` (in SGA this
is part of the conclusion; it holds when the `κ((fᵢ))` have the residue characteristic of `A`,
`absoluteAbhyankarAt_of_ringChar_eq`, and the assumption is removed in
`absoluteAbhyankar_extension`). -/
theorem absoluteAbhyankar_of_isRegularLocalRing (A : Type u) [CommRing A]
    [IsRegularLocalRing A] {r : ℕ} (f : Fin r → A) (hf : IsPartOfRegularSystemOfParameters f)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B)
    (n : Fin r → ℕ) (hn : ∀ i, IsLcmRamificationIndices (Ideal.span {f i}) B (n i))
    (hp : ∀ i, (n i : A) ∉ maximalIdeal A) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra (KummerAlgebra n f) W),
      Module.Finite (KummerAlgebra n f) W ∧ Algebra.Etale (KummerAlgebra n f) W ∧
      Nonempty (KummerAlgebra n f ⊗[A] B ≃ₐ[KummerAlgebra n f]
        Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)) ⊗[KummerAlgebra n f]
          W) :=
  exists_etale_kummerAlgebra_of_isTamelyRamifiedAlong A f hf B hB n
    (fun i Q _ hQ ↦ (hn i).1 Q hQ) fun i j h ↦ hp i (hf.span_singleton_le_maximalIdeal j h)

/-! ### XIII.5.3 -/

/-- If `A/I` has the characteristic of the residue field of the local ring `A`, an integer lies
in `I` iff it lies in the maximal ideal. -/
theorem natCast_mem_iff_of_ringChar_eq {A : Type*} [CommRing A] [IsLocalRing A] {I : Ideal A}
    (h : ringChar (A ⧸ I) = ringChar (ResidueField A)) (m : ℕ) :
    (m : A) ∈ I ↔ (m : A) ∈ maximalIdeal A := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec, h, ← ringChar.spec,
    ← map_natCast (residue A), residue_eq_zero_iff]

/-- If the local ring `A` has the characteristic of its residue field (e.g. `A` contains a field),
so has `A/I` for every proper ideal `I`. -/
theorem ringChar_quotient_eq_of_ringChar_eq {A : Type*} [CommRing A] [IsLocalRing A]
    (hchar : ringChar A = ringChar (ResidueField A)) {I : Ideal A} (hI : I ≤ maximalIdeal A) :
    ringChar (A ⧸ I) = ringChar (ResidueField A) := by
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hI)
  let ρ : A ⧸ I →+* ResidueField A :=
    Ideal.Quotient.lift _ (residue A) fun a ha ↦ (residue_eq_zero_iff a).mpr (hI ha)
  refine Nat.dvd_antisymm ?_ ?_
  · rw [← hchar]
    exact ringChar.dvd (by
      rw [← map_natCast (Ideal.Quotient.mk I), ringChar.Nat.cast_ringChar, map_zero])
  · exact ringChar.dvd (by rw [← map_natCast ρ, ringChar.Nat.cast_ringChar, map_zero])

set_option maxHeartbeats 800000 in
-- the instance problems on the normalizations of `A` and `A_(f_j)` are large
/-- XIII.5.2: for `B` tamely ramified along `div fᵢ` (with `A_(fᵢ)` a discrete valuation ring),
there is an integer `n` prime to the characteristic of `κ((fᵢ))` divisible by the ramification
indices of the primes above `(fᵢ)` (e.g. their product; the primes above `(fᵢ)` are finite in
number). -/
theorem exists_ramificationIdx_dvd_of_isTamelyRamifiedAlong {A : Type u} [CommRing A]
    [IsDomain A] {r : ℕ} (f : Fin r → A) (hf0 : ∀ i, f i ≠ 0) (B : Type u) [CommRing B]
    [Algebra A B] [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B) (j : Fin r)
    [(Ideal.span {f j}).IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {f j}))] :
    ∃ n : ℕ, (n : A) ∉ Ideal.span {f j} ∧
      ∀ (Q : Ideal (integralClosure A (FractionRing A ⊗[A] B))) [Q.IsPrime],
        Q.LiesOver (Ideal.span {f j}) → Q.ramificationIdx A ∣ n := by
  classical
  have : IsFractionRing (Localization.AtPrime (Ideal.span {f j})) (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Ideal.span {f j}).primeCompl _ _
  -- `E = Frac A ⊗_A B` is finite étale over `Frac A`
  have hπK : IsUnit (algebraMap A (FractionRing A) (∏ i, f i)) := isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective A _)).mpr
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hf0 i))
  let : Algebra (Localization.Away (∏ i, f i)) (FractionRing A) :=
    (IsLocalization.Away.lift _ hπK).toAlgebra
  have : IsScalarTower A (Localization.Away (∏ i, f i)) (FractionRing A) :=
    .of_algebraMap_eq fun a ↦ (IsLocalization.Away.lift_eq _ hπK a).symm
  let eE : FractionRing A ⊗[Localization.Away (∏ i, f i)] B ≃ₐ[FractionRing A]
      FractionRing A ⊗[A] B :=
    AlgEquiv.ofRingEquiv (f := (IsLocalization.algebraTensorEquiv (Submonoid.powers (∏ i, f i))
      (Localization.Away (∏ i, f i)) (FractionRing A) B).toRingEquiv) fun _ ↦ rfl
  have : Algebra.Etale (FractionRing A) (FractionRing A ⊗[A] B) := Algebra.Etale.of_equiv eE
  have : Module.Finite (FractionRing A) (FractionRing A ⊗[A] B) :=
    Module.Finite.equiv eE.toLinearEquiv
  have : IsArtinianRing (FractionRing A ⊗[A] B) :=
    IsArtinianRing.of_finite (FractionRing A) _
  have : IsReduced (FractionRing A ⊗[A] B) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing A) _
  -- the normalization of `R` in `E` is the localization of that of `A`
  let ι : integralClosure A (FractionRing A ⊗[A] B) →+*
      integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B) :=
    { toFun x := ⟨x.1, x.2.tower_top⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  let : Algebra (integralClosure A (FractionRing A ⊗[A] B))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B)) :=
    ι.toAlgebra
  have : IsScalarTower (integralClosure A (FractionRing A ⊗[A] B))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B))
      (FractionRing A ⊗[A] B) := ⟨fun x y z ↦ mul_assoc (x : FractionRing A ⊗[A] B)
        (y : FractionRing A ⊗[A] B) z⟩
  have : IsScalarTower A (integralClosure A (FractionRing A ⊗[A] B))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid (FractionRing A ⊗[A] B)
      (Ideal.span {f j}).primeCompl) (FractionRing A ⊗[A] B) := by
    refine IsLocalization.of_le_isUnit ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [IsScalarTower.algebraMap_apply A (FractionRing A)]
    refine (isUnit_iff_ne_zero.mpr ?_).map _
    exact (map_ne_zero_iff _ (IsFractionRing.injective A _)).mpr fun h ↦ ha (h ▸ zero_mem _)
  have hloc := IsLocalization.integralClosure (R := A) (S := FractionRing A ⊗[A] B)
    (Rf := Localization.AtPrime (Ideal.span {f j})) (Sf := FractionRing A ⊗[A] B)
    (Ideal.span {f j}).primeCompl
  -- the normalization of `R` in `E` is finite over `R`, with finitely many primes over `𝔪_R`
  have : Module.Finite (Localization.AtPrime (Ideal.span {f j}))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B)) := by
    let Φ := ((IsArtinianRing.equivPi (FractionRing A ⊗[A] B)).restrictScalars
      (Localization.AtPrime (Ideal.span {f j}))).mapIntegralClosure.trans
      (integralClosure.piAlgEquiv (Localization.AtPrime (Ideal.span {f j}))
        (fun M : MaximalSpectrum (FractionRing A ⊗[A] B) ↦ (FractionRing A ⊗[A] B) ⧸ M.asIdeal))
    have (M : MaximalSpectrum (FractionRing A ⊗[A] B)) :
        Module.Finite (Localization.AtPrime (Ideal.span {f j}))
          (integralClosure (Localization.AtPrime (Ideal.span {f j}))
            ((FractionRing A ⊗[A] B) ⧸ M.asIdeal)) := by
      let := Ideal.Quotient.field M.asIdeal
      exact integralClosure.finite (Localization.AtPrime (Ideal.span {f j})) (FractionRing A)
        ((FractionRing A ⊗[A] B) ⧸ M.asIdeal)
    exact Module.Finite.equiv Φ.symm.toLinearEquiv
  have : Fintype ((maximalIdeal (Localization.AtPrime (Ideal.span {f j}))).primesOver
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B))) :=
    Set.Finite.fintype (Algebra.QuasiFinite.finite_primesOver
      (S := integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B))
      (maximalIdeal (Localization.AtPrime (Ideal.span {f j}))))
  refine ⟨∏ q : (maximalIdeal (Localization.AtPrime (Ideal.span {f j}))).primesOver
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B)),
      q.1.ramificationIdx (Localization.AtPrime (Ideal.span {f j})), ?_, fun Q _ hQ ↦ ?_⟩
  · intro hmem
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime (Ideal.span {f j}))
      (Ideal.span {f j}), map_natCast, Nat.cast_prod] at hmem
    obtain ⟨q, -, hq⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    have := q.2.1
    have := q.2.2
    -- `q` is tamely ramified
    have hqeq := IsLocalization.map_under (Algebra.algebraMapSubmonoid
      (integralClosure A (FractionRing A ⊗[A] B)) (Ideal.span {f j}).primeCompl) _ q.1
    have : (q.1.under (integralClosure A (FractionRing A ⊗[A] B))).IsPrime :=
      Ideal.comap_isPrime _ _
    have : (q.1.under (integralClosure A (FractionRing A ⊗[A] B))).LiesOver
        (Ideal.span {f j}) := ⟨by
      have e1 : (q.1.under (integralClosure A (FractionRing A ⊗[A] B))).under A = q.1.under A :=
        Ideal.under_under q.1
      have e2 : (q.1.under (Localization.AtPrime (Ideal.span {f j}))).under A = q.1.under A :=
        Ideal.under_under q.1
      rw [e1, ← e2, ← Ideal.over_def q.1 (maximalIdeal (Localization.AtPrime (Ideal.span {f j}))),
        Localization.AtPrime.under_maximalIdeal]⟩
    have h1 := (isTamelyRamifiedAt_map_iff_of_isLocalization A (Ideal.span {f j})
      (Localization.AtPrime (Ideal.span {f j}))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B))
      (q.1.under (integralClosure A (FractionRing A ⊗[A] B)))).mpr (hB j _ inferInstance)
    have h2 : IsTamelyRamifiedAt (Localization.AtPrime (Ideal.span {f j}))
        (S := integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B))
        q.1 := by
      convert h1 using 2
      exact hqeq.symm
    rw [isTamelyRamifiedAt_iff_of_liesOver _ (maximalIdeal _)] at h2
    exact h2.1 ((natCast_mem_iff_residueField _ _ _).mp hq)
  · have := IsLocalization.AtPrime.isPrime_map_of_liesOver
      (integralClosure A (FractionRing A ⊗[A] B)) (Ideal.span {f j})
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B)) Q
    have := IsLocalization.AtPrime.liesOver_map_of_liesOver
      (S := integralClosure A (FractionRing A ⊗[A] B)) (Ideal.span {f j})
      (Localization.AtPrime (Ideal.span {f j}))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B)) Q
    have h := IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx
      (S := integralClosure A (FractionRing A ⊗[A] B)) (Ideal.span {f j})
      (Localization.AtPrime (Ideal.span {f j}))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B)) Q
    have h' := Finset.dvd_prod_of_mem (fun q : (maximalIdeal (Localization.AtPrime
      (Ideal.span {f j}))).primesOver (integralClosure (Localization.AtPrime (Ideal.span {f j}))
        (FractionRing A ⊗[A] B)) ↦ q.1.ramificationIdx (Localization.AtPrime (Ideal.span {f j})))
      (Finset.mem_univ ⟨Q.map (algebraMap (integralClosure A (FractionRing A ⊗[A] B))
        (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B))),
        inferInstance, inferInstance⟩)
    exact h ▸ h'

/-- XIII.5.2: the l.c.m. `nᵢ` of the ramification indices above `(fᵢ)` is nonzero in the residue
field `κ((fᵢ))` (it divides the product of these indices, which is, `B` being tame). -/
theorem natCast_notMem_of_isLcmRamificationIndices {A : Type u} [CommRing A]
    [IsRegularLocalRing A] {r : ℕ} (f : Fin r → A) (hf : IsPartOfRegularSystemOfParameters f)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B) (i : Fin r)
    {n : ℕ} (hn : IsLcmRamificationIndices (Ideal.span {f i}) B n) :
    (n : A) ∉ Ideal.span {f i} := by
  obtain ⟨_, _⟩ := hf.isDiscreteValuationRing_localization i
  obtain ⟨n', hn'p, hn'⟩ :=
    exists_ramificationIdx_dvd_of_isTamelyRamifiedAlong f hf.ne_zero B hB i
  obtain ⟨c, hc⟩ := hn.2 n' fun Q _ hQ ↦ hn' Q hQ
  intro hm
  apply hn'p
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hm

/-- XIII.5.2, existence part, with `nᵢ` the l.c.m. of the ramification indices above `(fᵢ)`: the
restriction of `V` to `U'` extends to an étale covering of `X'` as soon as each `nᵢ` is nonzero in
the residue fields `κ((f_j))`, `j ≠ i` (it is always nonzero in `κ((fᵢ))`,
`natCast_notMem_of_isLcmRamificationIndices`). In particular, for `r = 1` it extends in every
characteristic, without knowing that `n₁` is prime to the residue characteristic of `A`. -/
theorem exists_etale_kummerAlgebra_of_isLcmRamificationIndices (A : Type u) [CommRing A]
    [IsRegularLocalRing A] {r : ℕ} (f : Fin r → A) (hf : IsPartOfRegularSystemOfParameters f)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B)
    (n : Fin r → ℕ) (hn : ∀ i, IsLcmRamificationIndices (Ideal.span {f i}) B (n i))
    (hp : ∀ i j, i ≠ j → (n i : A) ∉ Ideal.span {f j}) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra (KummerAlgebra n f) W),
      Module.Finite (KummerAlgebra n f) W ∧ Algebra.Etale (KummerAlgebra n f) W ∧
      Nonempty (KummerAlgebra n f ⊗[A] B ≃ₐ[KummerAlgebra n f]
        Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)) ⊗[KummerAlgebra n f]
          W) := by
  refine exists_etale_kummerAlgebra_of_isTamelyRamifiedAlong A f hf B hB n
    (fun i Q _ hQ ↦ (hn i).1 Q hQ) fun i j ↦ ?_
  by_cases hij : i = j
  · subst hij
    exact natCast_notMem_of_isLcmRamificationIndices f hf B hB i (hn i)
  · exact hp i j hij

/-- XIII.5.3 for a regular strictly local ring `A`, assuming that the residue fields `κ((fᵢ))`
have the residue characteristic of `A` (which makes the l.c.m. of the ramification indices prime
to it; in general this is `exists_injective_kummerAlgebra_of_isStrictlyHenselian`): every
connected (integral) finite étale `A[1/∏ fᵢ]`-algebra `B` tamely ramified along `Σ div fᵢ` is a
quotient of a Kummer covering, i.e. embeds in `A[1/∏ fᵢ][Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` with the `nᵢ` prime
to the residue characteristic. By 5.2 (`exists_etale_kummerAlgebra_of_isTamelyRamifiedAlong`),
`A' ⊗_A B` extends to a finite étale `A'`-algebra `W`, `A' = A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`; as `A'` is local
and finite over the strictly henselian `A`, it is strictly henselian (Stacks 04GH,
`IsStrictlyHenselian.of_finite`), so `W` is a product of copies of `A'` and has a section, whence
`B → A' ⊗_A B → A'[1/∏ fᵢ]`, injective since `B` is a domain integral over `A[1/∏ fᵢ]`. -/
theorem exists_injective_kummerAlgebra_of_isRegularLocalRing (A : Type u) [CommRing A]
    [IsRegularLocalRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    {r : ℕ} (f : Fin r → A) (hf : IsPartOfRegularSystemOfParameters f)
    (hchar : ∀ i, ringChar (A ⧸ Ideal.span {f i}) = ringChar (ResidueField A))
    (B : Type u) [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B) :
    ∃ n : Fin r → ℕ, (∀ i, 0 < n i ∧ (n i : A) ∉ maximalIdeal A) ∧
      ∃ φ : B →ₐ[Localization.Away (∏ i, f i)]
          KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i)),
        Function.Injective φ := by
  classical
  -- the integers `nᵢ`
  have hn : ∀ i, ∃ n : ℕ, (n : A) ∉ Ideal.span {f i} ∧
      ∀ (Q : Ideal (integralClosure A (FractionRing A ⊗[A] B))) [Q.IsPrime],
        Q.LiesOver (Ideal.span {f i}) → Q.ramificationIdx A ∣ n := fun i ↦ by
    obtain ⟨_, _⟩ := hf.isDiscreteValuationRing_localization i
    exact exists_ramificationIdx_dvd_of_isTamelyRamifiedAlong f hf.ne_zero B hB i
  choose n hnp hdvd using hn
  have hn0 (i : Fin r) : (n i : A) ∉ maximalIdeal A :=
    (natCast_mem_iff_of_ringChar_eq (hchar i) (n i)).not.mp (hnp i)
  have hnpos (i : Fin r) : 0 < n i := Nat.pos_of_ne_zero fun h ↦ hnp i (by
    rw [h, Nat.cast_zero]; exact zero_mem _)
  refine ⟨n, fun i ↦ ⟨hnpos i, hn0 i⟩, ?_⟩
  -- `A' = A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` and the extension `W` of `A' ⊗_A B`
  obtain ⟨W, _, _, _, _, ⟨eW⟩⟩ :=
    exists_etale_kummerAlgebra_of_isTamelyRamifiedAlong A f hf B hB n hdvd
      fun i j h ↦ hn0 i (hf.span_singleton_le_maximalIdeal j h)
  have : IsRegularLocalRing (KummerAlgebra n f) := KummerAlgebra.isRegularLocalRing hnpos hf
  -- `A'` is local and finite over the strictly henselian `A`, hence strictly henselian
  have : Algebra.IsIntegral A (KummerAlgebra n f) := KummerAlgebra.isIntegral f hnpos
  have : Module.Finite A (KummerAlgebra n f) := Algebra.IsIntegral.finite
  have : IsStrictlyHenselian A := (isStrictlyHenselian_iff A).mpr ⟨inferInstance, inferInstance⟩
  have : IsStrictlyHenselian (KummerAlgebra n f) :=
    IsStrictlyHenselian.of_finite (A := A) (KummerAlgebra n f)
  -- `W` is nonzero, hence has a section `σ : W → A'`
  have : Nontrivial (KummerAlgebra n f ⊗[A] B) := by
    have hx (i : Fin r) : ∃ z : AlgebraicClosure (FractionRing B),
        z ^ n i = algebraMap B (AlgebraicClosure (FractionRing B)) (algebraMap A B (f i)) :=
      IsAlgClosed.exists_pow_nat_eq _ (hnpos i)
    choose z hz using hx
    let χ : KummerAlgebra n (fun i ↦ algebraMap A B (f i)) →ₐ[B]
        AlgebraicClosure (FractionRing B) := KummerAlgebra.lift z hz
    exact ((χ.toRingHom.comp (KummerAlgebra.baseChangeEquiv n f B).toRingHom).comp
      (Algebra.TensorProduct.comm A (KummerAlgebra n f) B).toRingHom).domain_nontrivial
  have : Nontrivial W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    have : Subsingleton (KummerAlgebra n f ⊗[A] B) := eW.toEquiv.subsingleton
    exact not_nontrivial _ ‹_›
  obtain ⟨m, ⟨eπ⟩⟩ := IsStrictlyHenselian.exists_algEquiv_pi (KummerAlgebra n f) W
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : Subsingleton W := eπ.toEquiv.subsingleton
      exact absurd ‹Nontrivial W› (not_nontrivial W)
    · exact hm
  let σ : W →ₐ[KummerAlgebra n f] KummerAlgebra n f :=
    (Pi.evalAlgHom (KummerAlgebra n f) (fun _ : Fin m ↦ KummerAlgebra n f) ⟨0, hm⟩).comp
      eπ.toAlgHom
  -- `Φ : B → A' ⊗_A B ≅ A'[1/∏ fᵢ] ⊗_{A'} W → A'[1/∏ fᵢ]`
  let Φ : B →+* Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)) :=
    ((Algebra.TensorProduct.rid (KummerAlgebra n f) (KummerAlgebra n f)
      (Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)))).toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id (KummerAlgebra n f)
        (Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)))) σ).toRingHom).comp
      (eW.toRingHom.comp (Algebra.TensorProduct.includeRight (R := A)
        (A := KummerAlgebra n f) (B := B)).toRingHom)
  have hΦ (a : A) : Φ (algebraMap A B a) = algebraMap (KummerAlgebra n f)
      (Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)))
      (algebraMap A (KummerAlgebra n f) a) := by
    have e1 : Algebra.TensorProduct.includeRight (R := A) (A := KummerAlgebra n f) (B := B)
        (algebraMap A B a) = Algebra.TensorProduct.includeLeft (S := KummerAlgebra n f)
          (algebraMap (KummerAlgebra n f) (KummerAlgebra n f)
            (algebraMap A (KummerAlgebra n f) a)) := by
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.algebraMap_self, RingHom.id_apply]
    change (Algebra.TensorProduct.rid (KummerAlgebra n f) (KummerAlgebra n f)
      (Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i))))
        ((Algebra.TensorProduct.map (AlgHom.id (KummerAlgebra n f)
          (Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)))) σ)
          (eW (Algebra.TensorProduct.includeRight (R := A) (A := KummerAlgebra n f) (B := B)
            (algebraMap A B a)))) = _
    rw [e1, AlgHom.commutes, AlgEquiv.commutes, AlgHom.commutes, AlgEquiv.commutes]
  -- `ψ : A'[1/∏ fᵢ] → A[1/∏ fᵢ][Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`
  let κ : KummerAlgebra n f →ₐ[A]
      KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i)) :=
    KummerAlgebra.lift (KummerAlgebra.T n _) fun i ↦ by
      rw [KummerAlgebra.T_pow, ← IsScalarTower.algebraMap_apply]
  have hκu : IsUnit (κ (algebraMap A (KummerAlgebra n f) (∏ i, f i))) := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A (Localization.Away (∏ i, f i))]
    exact (IsLocalization.Away.algebraMap_isUnit _).map _
  let ψ := IsLocalization.Away.lift (S := Localization.Away (algebraMap A (KummerAlgebra n f)
    (∏ i, f i))) _ hκu
  have hφA (a : A) : ψ (Φ (algebraMap A B a)) = algebraMap A
      (KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i))) a := by
    rw [hΦ, IsLocalization.Away.lift_eq]
    exact κ.commutes a
  have hext : (ψ.comp Φ).comp (algebraMap (Localization.Away (∏ i, f i)) B) =
      algebraMap (Localization.Away (∏ i, f i))
        (KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i))) :=
    IsLocalization.ringHom_ext (Submonoid.powers (∏ i, f i)) (RingHom.ext fun a ↦ by
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, hφA, ← IsScalarTower.algebraMap_apply])
  let φ : B →ₐ[Localization.Away (∏ i, f i)]
      KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i)) :=
    { ψ.comp Φ with commutes' := fun s ↦ DFunLike.congr_fun hext s }
  -- `φ` is injective: `B` is a domain, integral over `A[1/∏ fᵢ]`
  have hprod0 : ∏ i, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hf.ne_zero i
  have : IsDomain (Localization.Away (∏ i, f i)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hprod0)
  refine ⟨φ, (injective_iff_map_eq_zero φ).mpr fun x hx ↦ ?_⟩
  have hker : RingHom.ker φ = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := Localization.Away (∏ i, f i)) ?_
    refine eq_bot_iff.mpr fun s hs ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, φ.commutes] at hs
    exact (map_eq_zero_iff _ (KummerAlgebra.injective_algebraMap _ hnpos)).mp hs
  have : x ∈ RingHom.ker φ := hx
  rwa [hker] at this

/-! ### The statements in the proved cases -/

/-- XIII.5.2 for regular local rings of dimension one: `AbsoluteAbhyankarAt A 1`. -/
theorem absoluteAbhyankarAt_of_ringKrullDim_eq_one (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 1) : AbsoluteAbhyankarAt A 1 :=
  fun f hf B _ _ _ _ _ _ hB n hn ↦ absoluteAbhyankar_of_ringKrullDim_eq_one A hdim f hf B hB n hn

/-- XIII.5.2 (extension part) for every regular local ring `A` and every `r`:
`AbsoluteAbhyankarExtensionAt A r`. -/
theorem absoluteAbhyankarExtensionAt (A : Type u) [CommRing A] [IsRegularLocalRing A] (r : ℕ) :
    AbsoluteAbhyankarExtensionAt A r :=
  fun f hf B _ _ _ _ _ _ hB n hn hp ↦
    absoluteAbhyankar_of_isRegularLocalRing A f hf B hB n hn hp

/-- XIII.5.3 for strictly henselian regular local rings of dimension one:
`TameCoveringsOfStrictlyLocalAt A 1`. -/
theorem tameCoveringsOfStrictlyLocalAt_of_ringKrullDim_eq_one (A : Type u) [CommRing A]
    [IsRegularLocalRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    (hdim : ringKrullDim A = 1) : TameCoveringsOfStrictlyLocalAt A 1 :=
  fun f hf B _ _ _ _ _ _ _ hB ↦
    exists_injective_kummerAlgebra_of_ringKrullDim_eq_one A hdim f hf B hB

/-- XIII.5.3 for strictly henselian regular local rings of equal characteristic
(`char A = char κ`, e.g. `A` contains a field): `TameCoveringsOfStrictlyLocalAt A r` for every `r`.
(The hypothesis ensures that the residue fields `κ((fᵢ))` have the residue characteristic of
`A`, see `exists_injective_kummerAlgebra_of_isRegularLocalRing`.) -/
theorem tameCoveringsOfStrictlyLocalAt_of_ringChar_eq (A : Type u) [CommRing A]
    [IsRegularLocalRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    (hchar : ringChar A = ringChar (ResidueField A)) (r : ℕ) :
    TameCoveringsOfStrictlyLocalAt A r := by
  intro f hf B _ _ _ _ _ _ _ hB
  exact exists_injective_kummerAlgebra_of_isRegularLocalRing A f hf
    (fun i ↦ ringChar_quotient_eq_of_ringChar_eq hchar (hf.span_singleton_le_maximalIdeal i)) B hB

/-- XIII.5.2 for regular local rings of equal characteristic (`char A = char κ`):
`AbsoluteAbhyankarAt A r` for every `r`. The `nᵢ` are prime to the residue characteristic since
they divide the product of the ramification indices above `(fᵢ)`, which is prime to the
characteristic of `κ((fᵢ))` (`exists_ramificationIdx_dvd_of_isTamelyRamifiedAlong`), equal to that
of `κ`. -/
theorem absoluteAbhyankarAt_of_ringChar_eq (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hchar : ringChar A = ringChar (ResidueField A)) (r : ℕ) : AbsoluteAbhyankarAt A r := by
  intro f hf B _ _ _ _ _ _ hB n hn
  have hp (i : Fin r) : (n i : A) ∉ maximalIdeal A := by
    rw [← natCast_mem_iff_of_ringChar_eq (ringChar_quotient_eq_of_ringChar_eq hchar
      (hf.span_singleton_le_maximalIdeal i))]
    exact natCast_notMem_of_isLcmRamificationIndices f hf B hB i (hn i)
  exact ⟨hp, absoluteAbhyankar_of_isRegularLocalRing A f hf B hB n hn hp⟩

end HigherDimension

end SGA.SGA1.ExposeXIII
