/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Dimension.LocalDimension
import SGA.SGA1.ExposeII.Differentials
import SGA.SGA1.ExposeII.PermanenceSmooth

/-!
# SGA 1, Exposé II, II.5.1: étale coordinates over a field

Let `X = Spec S` be of finite type over a field `k`, `x` a point where `X` has dimension `n`
(`topologicalKrullDimAt`, `SGA.Foundations.Dimension`), and `f : X → 𝔸ⁿ_k` given by `f₁,…,fₙ`.
Then `f` is étale at `x` iff the `dfᵢ` form a basis of `Ω¹_{X/k}` at `x` iff they generate it
(`isEtaleAt_tfae`). The key step is SGA's: if the `dfᵢ` generate `Ω¹`, `f` is unramified at `x`,
hence at the generic point of a component of dimension `n` through `x`, which is then mapped to
the generic point of `𝔸ⁿ` ("dominant for reasons of dimension", computed with transcendence
degrees); so `𝒪_{f(x)} → 𝒪_x` is injective, and I.9.5 (ii) shows that it is flat.
-/

universe u

open IsLocalRing Algebra Cardinal KaehlerDifferential MvPolynomial Order
open scoped TensorProduct

namespace SGA.SGA1.ExposeII

/-- If `A` is unramified over `T` at `P` (over `q`), then `κ(P)` is finite over `κ(q)`, so they
have the same transcendence degree over a common base field `k`. -/
theorem trdeg_residueField_eq_of_isUnramifiedAt {k T A : Type u} [Field k] [CommRing T]
    [CommRing A] [Algebra k T] [Algebra T A] [Algebra k A] [IsScalarTower k T A]
    [EssFiniteType T A] (q : Ideal T) (P : Ideal A) [q.IsPrime] [P.IsPrime] [P.LiesOver q]
    [IsUnramifiedAt T P] : trdeg k P.ResidueField = trdeg k q.ResidueField := by
  let := Localization.AtPrime.algebraOfLiesOver q P
  have : Module.Finite q.ResidueField P.ResidueField := inferInstance
  have : IsScalarTower k q.ResidueField P.ResidueField := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply k T q.ResidueField,
      IsScalarTower.algebraMap_apply k A P.ResidueField,
      IsScalarTower.algebraMap_apply k T A]
    exact ((IsScalarTower.algebraMap_apply T q.ResidueField P.ResidueField _).symm.trans
      (IsScalarTower.algebraMap_apply T A P.ResidueField _)).symm
  have h := lift_trdeg_add_eq k q.ResidueField P.ResidueField
  rw [trdeg_eq_zero (R := q.ResidueField) (A := P.ResidueField), lift_zero, add_zero, lift_id,
    lift_id] at h
  exact h.symm

/-- A finitely presented algebra which is flat and unramified at a prime is étale there. -/
theorem isEtaleAt_of_flat_of_isUnramifiedAt {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [FinitePresentation R S] (Q : Ideal S) [Q.IsPrime] [IsUnramifiedAt R Q]
    (h : Module.Flat R (Localization.AtPrime Q)) : IsEtaleAt R Q := by
  have : EssFiniteType R (Localization.AtPrime Q) := .comp R S _
  have : FormallyUnramified (Q.under R).ResidueField
      ((Q.under R).ResidueField ⊗[R] Localization.AtPrime Q) := inferInstance
  have : FormallyEtale (Q.under R).ResidueField
      ((Q.under R).ResidueField ⊗[R] Localization.AtPrime Q) :=
    .of_formallyUnramified_of_field _ _
  have : IsSmoothAt R Q :=
    (isSmoothAt_iff_flat_and_formallySmooth_fiber (Q.under R) Q).mpr ⟨h, inferInstance⟩
  change FormallyEtale R (Localization.AtPrime Q)
  exact .of_formallyUnramified_and_formallySmooth

/-- II.5.1, (iii) ⇒ (i): let `S` be of finite type over a field `k` (a scheme `X`), `Q` a prime
of `S` (a point `x`) at which `Spec S` has dimension `n`, and `f : X → Spec k[t₁,…,tₙ]` given by
`fᵢ = image of tᵢ`. If the `dfᵢ` generate `Ω¹_{X/k}` at `x`, then `f` is étale at `x`. As in SGA:
`f` is unramified at `x` (II.4.1), hence at the generic point of a component of dimension `n`
through `x`, which is therefore mapped to the generic point of `𝔸ⁿ` (transcendence degrees);
so `k[t]_{f(x)} → 𝒪_x` is injective, and I.9.5 (ii) makes it flat. -/
theorem isEtaleAt_of_span_eq_top {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [FiniteType k S] {n : ℕ} [Algebra (MvPolynomial (Fin n) k) S]
    [IsScalarTower k (MvPolynomial (Fin n) k) S] (Q : Ideal S) [Q.IsPrime]
    (hn : topologicalKrullDimAt (PrimeSpectrum S) ⟨Q, ‹_›⟩ = n)
    (hspan : Submodule.span (Localization.AtPrime Q) (Set.range fun i ↦
      D k (Localization.AtPrime Q) (algebraMap (MvPolynomial (Fin n) k) _ (X i))) = ⊤) :
    IsEtaleAt (MvPolynomial (Fin n) k) Q := by
  have : IsScalarTower k (MvPolynomial (Fin n) k) (Localization.AtPrime Q) := .to₁₂₄ _ _ S _
  have : FinitePresentation k S := FinitePresentation.of_finiteType.mp inferInstance
  have : FinitePresentation (MvPolynomial (Fin n) k) S :=
    .of_restrict_scalars_finitePresentation k _ S
  have : IsNoetherianRing S := FiniteType.isNoetherianRing k S
  -- the `dfᵢ` generate `Ω¹` at `x`, so `f` is unramified at `x` (II.4.1)
  have hunr : IsUnramifiedAt (MvPolynomial (Fin n) k) Q := by
    refine formallyUnramified_of_mapBaseChange_surjective k _ _ ?_
    rw [← LinearMap.range_eq_top, _root_.eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨1 ⊗ₜ D k _ (X i), by simp⟩
  -- an irreducible component `V(𝔭)` through `x` of dimension `n`
  have hsup : (⨆ (p : PrimeSpectrum S) (_ : IsMin p) (_ : p ≤ ⟨Q, ‹_›⟩), coheight p) =
      (n : ℕ∞) := by
    rw [FiniteType.topologicalKrullDimAt_eq_iSup k] at hn
    exact_mod_cast hn
  obtain ⟨p, hpmin, hpQ, hp⟩ : ∃ p : PrimeSpectrum S, IsMin p ∧ p ≤ ⟨Q, ‹_›⟩ ∧
      coheight p = n := by
    by_contra! h
    obtain ⟨p₀, hp₀, hp₀Q⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ Q)
    have hmin (p : PrimeSpectrum S) (hp : p.asIdeal ∈ minimalPrimes S) : IsMin p :=
      fun x hx ↦ hp.2 ⟨x.2, bot_le⟩ hx
    have hle (p : PrimeSpectrum S) (hp : IsMin p) (hpQ : p ≤ ⟨Q, ‹_›⟩) : coheight p ≤ n :=
      hsup ▸ le_iSup₂_of_le p hp (le_iSup_of_le hpQ le_rfl)
    rcases n with _ | n
    · exact h ⟨p₀, hp₀.1.1⟩ (hmin _ hp₀) hp₀Q
        (nonpos_iff_eq_zero.mp (hle ⟨p₀, hp₀.1.1⟩ (hmin _ hp₀) hp₀Q))
    · have : (⨆ (p : PrimeSpectrum S) (_ : IsMin p) (_ : p ≤ ⟨Q, ‹_›⟩), coheight p) ≤ n :=
        iSup₂_le fun p hp ↦ iSup_le fun hpQ ↦ Order.le_of_lt_add_one (by
          exact_mod_cast lt_of_le_of_ne (hle p hp hpQ) (h p hp hpQ))
      rw [hsup] at this
      exact absurd this (by exact_mod_cast (Nat.lt_succ_self n).not_ge)
  -- `f` is unramified at the generic point `𝔭` of this component
  have hpu : IsUnramifiedAt (MvPolynomial (Fin n) k) p.asIdeal := by
    have hQ : (⟨Q, ‹_›⟩ : PrimeSpectrum S) ∈ unramifiedLocus (MvPolynomial (Fin n) k) S := hunr
    have hsp : p ⤳ ⟨Q, ‹_›⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hpQ
    exact hsp.mem_open isOpen_unramifiedLocus hQ
  -- so `κ(𝔭)` has transcendence degree `n` over `k`, as has the image of `𝔭` in `k[t]`: this
  -- image is the generic point ("dominant for reasons of dimension")
  have htr := trdeg_residueField_eq_of_isUnramifiedAt (k := k)
    (p.asIdeal.under (MvPolynomial (Fin n) k)) p.asIdeal
  have h1 := FiniteType.trdeg_residueField k p.asIdeal
  rw [← PrimeSpectrum.coheight_eq_ringKrullDim_quotient, hp, htr,
    FiniteType.trdeg_residueField k] at h1
  have hc : coheight (⟨p.asIdeal.under (MvPolynomial (Fin n) k), inferInstance⟩ :
      PrimeSpectrum (MvPolynomial (Fin n) k)) = n :=
    WithBot.coe_inj.mp ((PrimeSpectrum.coheight_eq_ringKrullDim_quotient _).trans h1)
  have h3 := MvPolynomial.height_add_coheight_eq (k := k)
    (⟨p.asIdeal.under (MvPolynomial (Fin n) k), inferInstance⟩ :
      PrimeSpectrum (MvPolynomial (Fin n) k))
  rw [hc] at h3
  have h0 : height (⟨p.asIdeal.under (MvPolynomial (Fin n) k), inferInstance⟩ :
      PrimeSpectrum (MvPolynomial (Fin n) k)) = 0 := by
    have h₀ : height (⟨p.asIdeal.under (MvPolynomial (Fin n) k), inferInstance⟩ :
        PrimeSpectrum (MvPolynomial (Fin n) k)) + n ≤ 0 + n := by rw [zero_add, h3]
    exact nonpos_iff_eq_zero.mp ((ENat.add_le_add_iff_right (ENat.natCast_ne_top n)).mp h₀)
  have hbot : p.asIdeal.under (MvPolynomial (Fin n) k) = ⊥ := by
    rw [← PrimeSpectrum.height_eq_orderHeight, Ideal.height_eq_zero_iff_eq_bot] at h0
    exact h0
  -- hence `k[t] → 𝒪_x` is injective
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime Q)) := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    rw [IsScalarTower.algebraMap_apply _ S, IsLocalization.map_eq_zero_iff Q.primeCompl] at ht
    obtain ⟨⟨s, hs⟩, hst⟩ := ht
    have hmem : algebraMap _ S t ∈ p.asIdeal :=
      (p.2.mem_or_mem (hst ▸ p.asIdeal.zero_mem)).resolve_left fun h ↦ hs (hpQ h)
    have : t ∈ p.asIdeal.under (MvPolynomial (Fin n) k) := hmem
    rwa [hbot, Ideal.mem_bot] at this
  -- I.9.5 (ii): an injective unramified local homomorphism over a normal ring is flat
  let := Localization.AtPrime.algebraOfLiesOver (Q.under (MvPolynomial (Fin n) k)) Q
  have hinjq : Function.Injective (algebraMap
      (Localization.AtPrime (Q.under (MvPolynomial (Fin n) k))) (Localization.AtPrime Q)) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, s, rfl⟩ :=
      IsLocalization.exists_mk'_eq (Q.under (MvPolynomial (Fin n) k)).primeCompl z
    have h' : algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime Q) a = 0 := by
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) k)
        (Localization.AtPrime (Q.under (MvPolynomial (Fin n) k))) (Localization.AtPrime Q),
        ← IsLocalization.mk'_spec (Localization.AtPrime (Q.under (MvPolynomial (Fin n) k))) a s,
        RingHom.map_mul, hz, zero_mul]
    rw [hinj (h'.trans (map_zero _).symm), IsLocalization.mk'_zero]
  have hle : (Q.under (MvPolynomial (Fin n) k)).primeCompl ≤ nonZeroDivisors _ :=
    Ideal.primeCompl_le_nonZeroDivisors _
  have : IsDomain (Localization.AtPrime (Q.under (MvPolynomial (Fin n) k))) :=
    IsLocalization.isDomain_localization hle
  have : IsIntegrallyClosed (MvPolynomial (Fin n) k) := isIntegrallyClosed_mvPolynomial k n
  have : IsIntegrallyClosed (Localization.AtPrime (Q.under (MvPolynomial (Fin n) k))) :=
    isIntegrallyClosed_of_isLocalization _ _ hle
  have : FormallyUnramified (Localization.AtPrime (Q.under (MvPolynomial (Fin n) k)))
      (Localization.AtPrime Q) := .localization_base (Q.under (MvPolynomial (Fin n) k)).primeCompl
  have : EssFiniteType (MvPolynomial (Fin n) k) (Localization.AtPrime Q) := .comp _ S _
  have : EssFiniteType (Localization.AtPrime (Q.under (MvPolynomial (Fin n) k)))
      (Localization.AtPrime Q) := .of_comp (MvPolynomial (Fin n) k) _ _
  have := SGA.SGA1.ExposeI.flat_of_injective_of_formallyUnramified hinjq
  have : Module.Flat (MvPolynomial (Fin n) k) (Localization.AtPrime Q) :=
    .trans _ (Localization.AtPrime (Q.under (MvPolynomial (Fin n) k))) _
  exact isEtaleAt_of_flat_of_isUnramifiedAt Q this

/-- II.5.1: let `S` be of finite type over a field `k`, `Q` a prime of `S` (a point `x` of
`X = Spec S`) at which `X` has dimension `n`, and `f : X → Spec k[t₁,…,tₙ]` defined by the images
`fᵢ` of the `tᵢ`. The following are equivalent: (i) `f` is étale at `x`; (ii) the `dfᵢ` form a
basis of `Ω¹_{X/k}` at `x`; (iii) the `dfᵢ` generate `Ω¹_{X/k}` at `x`. -/
theorem isEtaleAt_tfae {k S : Type u} [Field k] [CommRing S] [Algebra k S] [FiniteType k S]
    {n : ℕ} [Algebra (MvPolynomial (Fin n) k) S] [IsScalarTower k (MvPolynomial (Fin n) k) S]
    (Q : Ideal S) [Q.IsPrime] (hn : topologicalKrullDimAt (PrimeSpectrum S) ⟨Q, ‹_›⟩ = n) :
    List.TFAE [IsEtaleAt (MvPolynomial (Fin n) k) Q,
      LinearIndependent (Localization.AtPrime Q) (fun i ↦
          D k (Localization.AtPrime Q) (algebraMap (MvPolynomial (Fin n) k) _ (X i))) ∧
        Submodule.span (Localization.AtPrime Q) (Set.range fun i ↦
          D k (Localization.AtPrime Q) (algebraMap (MvPolynomial (Fin n) k) _ (X i))) = ⊤,
      Submodule.span (Localization.AtPrime Q) (Set.range fun i ↦
          D k (Localization.AtPrime Q) (algebraMap (MvPolynomial (Fin n) k) _ (X i))) = ⊤] := by
  have : IsScalarTower k (MvPolynomial (Fin n) k) (Localization.AtPrime Q) := .to₁₂₄ _ _ S _
  tfae_have 1 → 2 := fun h ↦ by
    have hE : FormallyEtale (MvPolynomial (Fin n) k) (Localization.AtPrime Q) := h
    have : FormallySmooth k (Localization.AtPrime Q) := .comp k (MvPolynomial (Fin n) k) _
    exact formallyEtale_mvPolynomial_iff.mp hE
  tfae_have 2 → 3 := And.right
  tfae_have 3 → 1 := isEtaleAt_of_span_eq_top Q hn
  tfae_finish

end SGA.SGA1.ExposeII
